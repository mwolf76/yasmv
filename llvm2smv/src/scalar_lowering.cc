#include "llvm2smv/scalar_lowering.hh"
#include "llvm2smv/model_writer.hh"
#include "llvm2smv/module_analysis.hh"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Verifier.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include <map>
#include <set>

namespace llvm2smv {
using namespace llvm;
using ts::Expr; using ts::Op; using ts::SymbolRef; using ts::Mode;
namespace {
std::string ir(const Value& v) { std::string s; raw_string_ostream out(s); v.print(out); return s; }
std::string moduleText(const Module& m) { std::string s; raw_string_ostream out(s); m.print(out, nullptr); return s; }
void require(bool ok, const std::string& message, const Instruction* i = nullptr)
{ if (!ok) throw ScalarError(message, i); }
unsigned width(const Type* t)
{
    require(t->isIntegerTy() && t->getIntegerBitWidth() <= 64, "Only scalar integers of 1..64 bits are admitted");
    return t->getIntegerBitWidth();
}
Expr bit(bool b) { return Expr::boolean(b); }
Expr number(unsigned w, uint64_t n) { return Expr::integer(ts::Type::word(w), APInt(w,n)); }
Expr constant(const APInt& n) { return Expr::integer(ts::Type::word(n.getBitWidth()), n); }
Expr v(SymbolRef s) { return Expr::variable(s); }
Expr binary(Op o, Expr a, Expr b) { return Expr::binary(o,a,b); }
Expr eq(Expr a, Expr b) { return binary(Op::Equal,a,b); }
bool isBit(const Expr& a, bool b) { return a.kind()==Expr::Kind::Boolean && a.booleanValue()==b; }
Expr no(Expr a) { return a.kind()==Expr::Kind::Boolean ? bit(!a.booleanValue()) : Expr::unary(Op::Not,a); }
Expr both(Expr a, Expr b)
{
    if (isBit(a,false) || isBit(b,false)) return bit(false);
    if (isBit(a,true)) return b;
    if (isBit(b,true)) return a;
    return binary(Op::And,a,b);
}
Expr either(Expr a, Expr b)
{
    if (isBit(a,true) || isBit(b,true)) return bit(true);
    if (isBit(a,false)) return b;
    if (isBit(b,false)) return a;
    return binary(Op::Or,a,b);
}
Expr neg(Expr a) { return Expr::unary(Op::Negate,a); }
Expr inv(Expr a) { return Expr::unary(Op::BitNot,a); }
Expr sign(Expr a) { return binary(Op::GreaterEqual,a,constant(APInt::getSignMask(a.type().width()))); }
Expr choose(Expr c, Expr a, Expr b) { return Expr::select(c,a,b); }
Expr asSigned(Expr a) { return Expr::cast(ts::Type::word(a.type().width(),true),a); }
Expr arithmeticRight(Expr a, Expr b)
{ return choose(sign(a),inv(binary(Op::ShiftRight,inv(a),b)),binary(Op::ShiftRight,a,b)); }
struct ValueExpr { Expr bits, poison; };
struct Slot { SymbolRef bits, poison; };

void attributes(const Function& f)
{
    static const std::set<std::string> strings{"frame-pointer", "no-trapping-math", "stack-protector-buffer-size", "target-cpu", "target-features", "tune-cpu"};
    for (unsigned index : f.getAttributes().indexes()) {
        for (Attribute a : f.getAttributes().getAttributes(index)) {
            bool ok = false;
            if (index == AttributeList::FunctionIndex) {
                if (a.isStringAttribute()) ok = strings.count(a.getKindAsString().str());
                else {
                    auto k = a.getKindAsEnum();
                    ok = k == Attribute::NoInline || k == Attribute::OptimizeNone || k == Attribute::NoUnwind
                        || k == Attribute::UWTable;
                }
            } else if (index == AttributeList::ReturnIndex) ok = a.hasAttribute(Attribute::NoUndef);
            require(ok, "Unhandled entry attribute: " + a.getAsString());
        }
    }
}
void checkMemory(const Instruction& i, const DataLayout& dl)
{
    const Value* pointer = nullptr; Type* type = nullptr; Align alignment(1);
    if (auto* load = dyn_cast<LoadInst>(&i)) {
        require(!load->isVolatile() && !load->isAtomic(), "Volatile/atomic loads are unsupported", &i);
        pointer = load->getPointerOperand(); type = load->getType(); alignment = load->getAlign();
    } else if (auto* store = dyn_cast<StoreInst>(&i)) {
        require(!store->isVolatile() && !store->isAtomic(), "Volatile/atomic stores are unsupported", &i);
        pointer = store->getPointerOperand(); type = store->getValueOperand()->getType(); alignment = store->getAlign();
    } else return;
    width(type);
    Type* objectType = nullptr; MaybeAlign objectAlign;
    if (auto* g = dyn_cast<GlobalVariable>(pointer)) {
        objectType = g->getValueType(); objectAlign = g->getAlign();
        require(!isa<StoreInst>(i) || !g->isConstant(), "Store to immutable global", &i);
    } else if (auto* a = dyn_cast<AllocaInst>(pointer)) {
        objectType = a->getAllocatedType(); objectAlign = a->getAlign();
    }
    require(objectType == type, "Memory access must address one whole, directly named scalar object", &i);
    require(alignment <= objectAlign.valueOrOne() || (!objectAlign && alignment <= dl.getABITypeAlign(type)),
        "Access alignment exceeds the scalar object's guaranteed alignment", &i);
}
void inspect(Function& f, bool normalized)
{
    attributes(f);
    const auto& dl = f.getParent()->getDataLayout();
    for (auto& b : f) for (auto& i : b) {
        if (auto* debug=dyn_cast<DbgInfoIntrinsic>(&i)) {
            require(debug->getNumOperandBundles()==0 && debug->getAttributes().isEmpty()
                && debug->getCallingConv()==CallingConv::C && !debug->isMustTailCall(),
                "Debug intrinsics with call-site attributes or operand bundles are unsupported", &i);
            continue;
        }
        SmallVector<std::pair<unsigned, MDNode*>,4> metadata;
        i.getAllMetadataOtherThanDebugLoc(metadata);
        for (auto [kind,node] : metadata) {
            bool debugLoop = kind == LLVMContext::MD_loop;
            if (debugLoop) for (const auto& operand : node->operands())
                debugLoop &= operand.get() == node || isa_and_nonnull<DILocation>(operand.get());
            require(debugLoop, "Unhandled instruction metadata (including progress assumptions)", &i);
        }
        if (!i.getType()->isVoidTy() && !isa<AllocaInst>(i)) width(i.getType());
        for (const Use& u : i.operands()) {
            require(!isa<UndefValue>(u.get()) || isa<PoisonValue>(u.get()), "undef is unsupported; initialize scalar locals explicitly", &i);
            if (isa<Constant>(u.get()) && u->getType()->isIntegerTy())
                require(isa<ConstantInt>(u.get()) || isa<PoisonValue>(u.get()), "Unsupported integer constant expression", &i);
        }
        switch (i.getOpcode()) {
        case Instruction::Add: case Instruction::Sub: case Instruction::Mul:
        case Instruction::UDiv: case Instruction::SDiv: case Instruction::URem: case Instruction::SRem:
        case Instruction::Shl: case Instruction::LShr: case Instruction::AShr:
        case Instruction::And: case Instruction::Or: case Instruction::Xor:
        case Instruction::ICmp: case Instruction::Trunc: case Instruction::ZExt: case Instruction::SExt:
        case Instruction::Select: case Instruction::Freeze: case Instruction::PHI:
        case Instruction::Br: case Instruction::Switch: case Instruction::Ret: case Instruction::Unreachable:
            break;
        case Instruction::Load: case Instruction::Store: checkMemory(i,dl); break;
        case Instruction::Alloca: {
            auto& a = cast<AllocaInst>(i);
            require(!normalized && &b == &f.getEntryBlock() && a.getAddressSpace() == 0 && a.isStaticAlloca()
                && cast<ConstantInt>(a.getArraySize())->isOne() && isAllocaPromotable(&a),
                "Only promotable entry-block scalar allocas are admitted", &i);
            width(a.getAllocatedType()); break;
        }
        default: throw ScalarError("Unsupported scalar instruction: " + std::string(i.getOpcodeName()), &i);
        }
    }
}

class Lowering {
public:
    Lowering(Module& module, Function& function) : module(module), function(function) {}
    json::Object run(const std::string& inputHash);
private:
    Module& module; Function& function; ts::Model model;
    std::map<const Value*,Slot> slots;
    std::map<const Instruction*,std::string> locations;
    std::map<const Instruction*,SymbolRef> choices;
    std::optional<ts::Type> pcType; SymbolRef pc; std::optional<Slot> returned;
    ValueExpr read(const Value* value) const;
    Slot allocate(const Value& value, std::string key, Mode mode, std::optional<APInt> initial);
    Expr label(const std::string& name) const { return Expr::literal(*pcType,name); }
    Expr at(const Instruction& i) const { return eq(v(pc),label(locations.at(&i))); }
    const Instruction* first(const BasicBlock& b) const;
    const Instruction* next(const Instruction& i) const;
    std::vector<ts::Write> edge(const BasicBlock& from, const BasicBlock& to) const;
    void step(const Instruction& i, const std::string& suffix, Expr guard, std::vector<ts::Write> writes, Expr ub);
    void result(const Instruction& i, ValueExpr value, Expr ub);
    void lower(const Instruction& i);
    ValueExpr integer(const BinaryOperator& i, Expr& ub) const;
};
Slot Lowering::allocate(const Value& value, std::string key, Mode mode, std::optional<APInt> initial)
{
    Type* type = isa<GlobalVariable>(value) ? cast<GlobalVariable>(value).getValueType() : value.getType();
    unsigned w = width(type);
    // Global names are arbitrary LLVM byte strings: use disjoint namespaces
    // rather than a suffix that could collide with another global's name.
    auto poisonKey=isa<GlobalVariable>(value) ? "global-poison."+value.getName().str() : key+".poison";
    Slot slot{model.variable(key,ts::Type::word(w),mode,initial ? constant(*initial) : number(w,0)),
        model.variable(poisonKey,ts::Type::boolean(),mode,bit(false))};
    slots.emplace(&value,slot); return slot;
}
ValueExpr Lowering::read(const Value* value) const
{
    if (auto* c = dyn_cast<ConstantInt>(value)) return {constant(c->getValue()),bit(false)};
    if (isa<PoisonValue>(value)) return {number(width(value->getType()),0),bit(true)};
    auto found = slots.find(value);
    require(found != slots.end(), "Value has no admitted scalar definition: " + ir(*value));
    return {v(found->second.bits),v(found->second.poison)};
}
const Instruction* Lowering::first(const BasicBlock& b) const
{
    for (const auto& i : b) if (!isa<PHINode>(i) && !isa<DbgInfoIntrinsic>(i)) return &i;
    throw ScalarError("Block has no executable terminator");
}
const Instruction* Lowering::next(const Instruction& i) const
{
    auto* n = i.getNextNode(); while (n && isa<DbgInfoIntrinsic>(n)) n=n->getNextNode();
    require(n, "Missing instruction successor", &i); return n;
}
std::vector<ts::Write> Lowering::edge(const BasicBlock& from, const BasicBlock& to) const
{
    std::vector<ts::Write> writes{{pc,label(locations.at(first(to)))}};
    for (const auto& phi : to.phis()) {
        auto incoming = read(phi.getIncomingValueForBlock(&from));
        const auto& slot = slots.at(&phi);
        writes.push_back({slot.bits,incoming.bits}); writes.push_back({slot.poison,incoming.poison});
    }
    return writes;
}
void Lowering::step(const Instruction& i, const std::string& suffix, Expr guard, std::vector<ts::Write> writes, Expr ub)
{
    if (!isBit(ub,true) && !isBit(guard,false))
        model.step(locations.at(&i)+suffix, both(at(i),both(no(ub),guard)),std::move(writes));
}
void Lowering::result(const Instruction& i, ValueExpr value, Expr ub)
{
    const auto& slot=slots.at(&i);
    step(i,".execute",bit(true),{{slot.bits,value.bits},{slot.poison,value.poison},
        {pc,label(locations.at(next(i)))}},ub);
}
ValueExpr Lowering::integer(const BinaryOperator& i, Expr& ub) const
{
    auto a=read(i.getOperand(0)), b=read(i.getOperand(1));
    unsigned w=width(i.getType()); auto z=number(w,0), one=number(w,1);
    Expr p=either(a.poison,b.poison), r=z;
    unsigned op=i.getOpcode();
    // A constant multiplier admits exact precomputed bounds, avoiding a
    // division circuit in every transition of common compiled C loops.
    auto* multiplier=dyn_cast<ConstantInt>(i.getOperand(1));
    Expr multiplicand=a.bits;
    if (!multiplier) { multiplier=dyn_cast<ConstantInt>(i.getOperand(0)); multiplicand=b.bits; }
    auto constantOverflow = [&](bool signedMath) {
        const auto& c=multiplier->getValue();
        if (c.isZero()) return bit(false);
        if (!signedMath) return binary(Op::Greater,multiplicand,constant(APInt::getAllOnes(w).udiv(c)));
        auto wide=c.sext(128), lo=APInt::getSignedMinValue(w).sext(128), hi=APInt::getSignedMaxValue(w).sext(128);
        auto lower=(c.isNegative() ? hi : lo).sdiv(wide);
        auto upper=(c.isNegative() ? lo : hi).sdiv(wide);
        if (lower.slt(lo)) lower=lo;
        if (upper.sgt(hi)) upper=hi;
        return either(binary(Op::Less,asSigned(multiplicand),asSigned(constant(lower.trunc(w)))),
            binary(Op::Greater,asSigned(multiplicand),asSigned(constant(upper.trunc(w)))));
    };
    if (op==Instruction::Add || op==Instruction::Sub || op==Instruction::Mul) {
        r=binary(op==Instruction::Add ? Op::Add : op==Instruction::Sub ? Op::Sub : Op::Mul,a.bits,b.bits);
        if (op==Instruction::Mul && multiplier) {
            auto c=multiplier->getValue();
            if (c.isZero()) r=z;
            else {
                bool negative=c.isNegative();
                auto magnitude=negative ? -c : c;
                if (magnitude.isPowerOf2()) {
                    unsigned shift=magnitude.logBase2();
                    r=shift ? binary(Op::ShiftLeft,multiplicand,number(w,shift)) : multiplicand;
                    if (negative) r=neg(r);
                }
            }
        }
        if (i.hasNoUnsignedWrap()) {
            Expr overflow=bit(false);
            if (op==Instruction::Add) overflow=binary(Op::Less,r,a.bits);
            else if (op==Instruction::Sub) overflow=binary(Op::Less,a.bits,b.bits);
            else if (multiplier) overflow=constantOverflow(false);
            else overflow=both(no(eq(a.bits,z)),binary(Op::Greater,b.bits,
                binary(Op::Div,constant(APInt::getAllOnes(w)),choose(eq(a.bits,z),one,a.bits))));
            p=either(p,overflow);
        }
        if (i.hasNoSignedWrap()) {
            Expr overflow=bit(false);
            if (op!=Instruction::Mul) overflow=both(op==Instruction::Add ? eq(sign(a.bits),sign(b.bits)) : no(eq(sign(a.bits),sign(b.bits))),
                no(eq(sign(r),sign(a.bits))));
            else if (multiplier) overflow=constantOverflow(true);
            else {
                auto aa=choose(sign(a.bits),neg(a.bits),a.bits), bb=choose(sign(b.bits),neg(b.bits),b.bits);
                auto limit=choose(no(eq(sign(a.bits),sign(b.bits))),constant(APInt::getSignMask(w)),constant(APInt::getSignedMaxValue(w)));
                overflow=both(no(eq(aa,z)),binary(Op::Greater,bb,binary(Op::Div,limit,choose(eq(aa,z),one,aa))));
            }
            p=either(p,overflow);
        }
    } else if (op==Instruction::And || op==Instruction::Or || op==Instruction::Xor) {
        r=binary(op==Instruction::And ? Op::BitAnd : op==Instruction::Or ? Op::BitOr : Op::BitXor,a.bits,b.bits);
        if (auto* disjoint=dyn_cast<PossiblyDisjointInst>(&i); disjoint && disjoint->isDisjoint())
            p=either(p,no(eq(binary(Op::BitAnd,a.bits,b.bits),z)));
    } else if (op==Instruction::Shl || op==Instruction::LShr || op==Instruction::AShr) {
        auto valid=binary(Op::Less,b.bits,number(w,w));
        auto amount=choose(valid,b.bits,z);
        r=op==Instruction::AShr ? arithmeticRight(a.bits,amount) : binary(op==Instruction::Shl ? Op::ShiftLeft : Op::ShiftRight,a.bits,amount);
        p=either(p,no(valid));
        if (op==Instruction::Shl) {
            if (i.hasNoUnsignedWrap()) p=either(p,no(eq(binary(Op::ShiftRight,r,amount),a.bits)));
            if (i.hasNoSignedWrap()) p=either(p,no(eq(arithmeticRight(r,amount),a.bits)));
        } else if (i.isExact()) p=either(p,no(eq(binary(Op::ShiftLeft,r,amount),a.bits)));
    } else {
        bool signedOp=op==Instruction::SDiv || op==Instruction::SRem;
        bool remainder=op==Instruction::SRem || op==Instruction::URem;
        ub=either(b.poison,eq(b.bits,z));
        if (signedOp) ub=either(ub,both(either(a.poison,eq(a.bits,constant(APInt::getSignedMinValue(w)))),eq(b.bits,constant(APInt::getAllOnes(w)))));
        auto divisor=choose(eq(b.bits,z),one,b.bits);
        auto aa=signedOp ? choose(sign(a.bits),neg(a.bits),a.bits) : a.bits;
        auto bb=signedOp ? choose(sign(divisor),neg(divisor),divisor) : divisor;
        r=binary(remainder ? Op::Rem : Op::Div,aa,bb);
        if (signedOp) r=choose(remainder ? sign(a.bits) : no(eq(sign(a.bits),sign(divisor))),neg(r),r);
        if (!remainder && i.isExact()) p=either(p,no(eq(binary(Op::Rem,aa,bb),z)));
    }
    return {r,p};
}
void Lowering::lower(const Instruction& i)
{
    Expr ub=bit(false);
    if (auto* op=dyn_cast<BinaryOperator>(&i)) { auto value=integer(*op,ub); result(i,value,ub); }
    else if (auto* cmp=dyn_cast<ICmpInst>(&i)) {
        auto a=read(cmp->getOperand(0)), b=read(cmp->getOperand(1));
        Expr lhs=cmp->isSigned() ? asSigned(a.bits) : a.bits, rhs=cmp->isSigned() ? asSigned(b.bits) : b.bits;
        Op op=Op::Equal;
        switch (cmp->getPredicate()) {
        case CmpInst::ICMP_EQ: op=Op::Equal; break; case CmpInst::ICMP_NE: op=Op::NotEqual; break;
        case CmpInst::ICMP_ULT: case CmpInst::ICMP_SLT: op=Op::Less; break;
        case CmpInst::ICMP_ULE: case CmpInst::ICMP_SLE: op=Op::LessEqual; break;
        case CmpInst::ICMP_UGT: case CmpInst::ICMP_SGT: op=Op::Greater; break;
        case CmpInst::ICMP_UGE: case CmpInst::ICMP_SGE: op=Op::GreaterEqual; break;
        default: throw ScalarError("Invalid integer predicate", &i);
        }
        result(i,{choose(binary(op,lhs,rhs),number(1,1),number(1,0)),either(a.poison,b.poison)},ub);
    } else if (auto* c=dyn_cast<CastInst>(&i)) {
        auto a=read(c->getOperand(0));
        if (c->getOpcode()==Instruction::SExt) a.bits=asSigned(a.bits);
        if (c->getOpcode()==Instruction::ZExt && c->hasNonNeg()) a.poison=either(a.poison,sign(a.bits));
        result(i,{Expr::cast(ts::Type::word(width(c->getType())),a.bits),a.poison},ub);
    } else if (auto* s=dyn_cast<SelectInst>(&i)) {
        auto c=read(s->getCondition()), a=read(s->getTrueValue()), b=read(s->getFalseValue());
        auto condition=eq(c.bits,number(1,1));
        result(i,{choose(condition,a.bits,b.bits),either(c.poison,choose(condition,a.poison,b.poison))},ub);
    } else if (auto* f=dyn_cast<FreezeInst>(&i)) {
        auto a=read(f->getOperand(0));
        result(i,{choose(a.poison,v(choices.at(&i)),a.bits),bit(false)},ub);
    } else if (auto* load=dyn_cast<LoadInst>(&i)) result(i,read(load->getPointerOperand()),ub);
    else if (auto* store=dyn_cast<StoreInst>(&i)) {
        auto a=read(store->getValueOperand()); const auto& target=slots.at(store->getPointerOperand());
        step(i,".store",bit(true),{{target.bits,a.bits},{target.poison,a.poison},{pc,label(locations.at(next(i)))}},ub);
    } else if (auto* branch=dyn_cast<BranchInst>(&i)) {
        if (branch->isUnconditional()) step(i,".jump",bit(true),edge(*i.getParent(),*branch->getSuccessor(0)),ub);
        else {
            auto c=read(branch->getCondition()); ub=c.poison; auto condition=eq(c.bits,number(1,1));
            step(i,".true",condition,edge(*i.getParent(),*branch->getSuccessor(0)),ub);
            step(i,".false",no(condition),edge(*i.getParent(),*branch->getSuccessor(1)),ub);
        }
    } else if (auto* sw=dyn_cast<SwitchInst>(&i)) {
        auto c=read(sw->getCondition()); ub=c.poison; Expr other=bit(true); unsigned index=0;
        for (const auto& item : sw->cases()) {
            auto guard=eq(c.bits,constant(item.getCaseValue()->getValue())); other=both(other,no(guard));
            step(i,".case"+std::to_string(index++),guard,edge(*i.getParent(),*item.getCaseSuccessor()),ub);
        }
        step(i,".default",other,edge(*i.getParent(),*sw->getDefaultDest()),ub);
    } else if (auto* ret=dyn_cast<ReturnInst>(&i)) {
        std::vector<ts::Write> writes{{pc,label("DONE")}};
        if (ret->getReturnValue()) {
            auto a=read(ret->getReturnValue());
            if (function.hasRetAttribute(Attribute::NoUndef)) ub=a.poison;
            writes.push_back({returned->bits,a.bits}); writes.push_back({returned->poison,a.poison});
        }
        step(i,".return",bit(true),std::move(writes),ub);
    } else if (isa<UnreachableInst>(i)) ub=bit(true);
    else throw ScalarError("Internal unhandled instruction", &i);
    if (!isBit(ub,false)) model.step(locations.at(&i)+".ub",both(at(i),ub),{{pc,label("ERROR")}});
}
json::Object Lowering::run(const std::string& inputHash)
{
    std::vector<std::string> labels{"DONE","ERROR"}; unsigned bi=0;
    for (const auto& b : function) {
        unsigned ii=0;
        for (const auto& i : b) {
            if (isa<DbgInfoIntrinsic>(i)) continue;
            auto key="b"+std::to_string(bi)+".i"+std::to_string(ii++);
            if (!i.getType()->isVoidTy()) allocate(i,"ssa."+key,Mode::State,std::nullopt);
            if (isa<PHINode>(i)) continue;
            locations.emplace(&i,key); labels.push_back(key);
            if (isa<FreezeInst>(i)) choices[&i]=model.variable("choice."+key,ts::Type::word(width(i.getType())),Mode::Choice,std::nullopt);
        }
        ++bi;
    }
    pcType=ts::Type::enumeration("pc",std::move(labels));
    pc=model.variable("pc",*pcType,Mode::State,label(locations.at(first(function.getEntryBlock()))));
    if (!function.getReturnType()->isVoidTy()) {
        unsigned w=width(function.getReturnType());
        returned=Slot{model.variable("return",ts::Type::word(w),Mode::State,number(w,0)),
            model.variable("return.poison",ts::Type::boolean(),Mode::State,bit(false))};
    }
    for (const auto& g : module.globals()) allocate(g,"global."+g.getName().str(),g.isConstant() ? Mode::Frozen : Mode::State,
        cast<ConstantInt>(g.getInitializer())->getValue());
    for (const auto& b : function) for (const auto& i : b)
        if (!isa<PHINode>(i) && !isa<DbgInfoIntrinsic>(i)) lower(i);
    model.property("terminated",eq(v(pc),label("DONE")));
    model.property("runtime_error",eq(v(pc),label("ERROR")));
    if (returned) model.property("return_defined",both(eq(v(pc),label("DONE")),no(v(returned->poison))));
    return ts::artifact(model,{{"lowering","scalar-v1"},{"normalization","checked-scalar-mem2reg-v1"},
        {"input_ir_sha256",inputHash},{"normalized_ir_sha256",ts::sha256(moduleText(module))},
        {"entry",function.getName().str()},{"target_triple",module.getTargetTriple()},
        {"data_layout",module.getDataLayoutStr()},{"environment","closed-module; no interposition; no external calls"},
        {"semantics","LLVM18 scalar bitvectors and poison; error sink at admitted UB; undef rejected"}},"llvm18-scalar-v1");
}
} // namespace
ScalarError::ScalarError(std::string message, const Instruction* instruction)
    : std::runtime_error(message), issue(diagnostic("unsupported-scalar",message))
{
    if (instruction) {
        issue["instruction"]=json::Object{{"ir",ir(*instruction)}};
        issue["function"]=instruction->getFunction()->getName().str();
        if (auto loc=instruction->getDebugLoc()) issue["source"]=json::Object{
            {"file",loc->getFilename().str()},{"line",loc.getLine()},{"column",loc.getCol()}};
    }
}
json::Object lowerScalar(Module& module, StringRef entry)
{
    module.setModuleIdentifier(""); // The IR storage path is not semantic provenance.
    auto inputHash=ts::sha256(moduleText(module));
    for (const auto& node : module.named_metadata())
        require(node.getName()=="llvm.dbg.cu" || node.getName()=="llvm.module.flags" || node.getName()=="llvm.ident",
            "Unhandled named module metadata: "+node.getName().str());
    require(!module.getDataLayoutStr().empty(),"An explicit target DataLayout is required");
    Triple triple(module.getTargetTriple());
    require(triple.isOSLinux() && (triple.getArch()==Triple::aarch64 || triple.getArch()==Triple::x86_64)
        && module.getDataLayout().isLittleEndian() && module.getDataLayout().getPointerSizeInBits(0)==64,
        "Scalar baseline requires explicit little-endian Linux aarch64/x86_64 with 64-bit pointers");
    require(module.getModuleInlineAsm().empty() && module.alias_empty() && module.ifunc_empty(),"Module asm, aliases, and resolvers are unsupported");
    for (auto& g : module.globals()) {
        SmallVector<std::pair<unsigned,MDNode*>,4> metadata;
        g.getAllMetadata(metadata);
        for (auto [kind,node] : metadata) { (void)node; require(kind==LLVMContext::MD_dbg,"Unhandled global metadata: "+g.getName().str()); }
        require(g.getAddressSpace()==0 && !g.isThreadLocal() && !g.isExternallyInitialized() && !g.hasComdat()
            && !g.hasSection() && (g.hasExternalLinkage() || g.hasInternalLinkage() || g.hasPrivateLinkage()),
            "Unsupported scalar global storage/linkage: "+g.getName().str());
        width(g.getValueType());
        require(g.hasInitializer() && isa<ConstantInt>(g.getInitializer()),"Scalar globals require concrete integer initializers: "+g.getName().str());
    }
    auto* f=module.getFunction(entry);
    require(f && !f->isDeclaration(),"The entry must name a defined function");
    require(f->arg_empty() && !f->isVarArg() && f->getCallingConv()==CallingConv::C && !f->hasPersonalityFn()
        && !f->hasPrefixData() && !f->hasPrologueData(),"Entry requires a zero-argument C calling convention and no exceptional ABI");
    if (!f->getReturnType()->isVoidTy()) width(f->getReturnType());
    inspect(*f,false);
    SmallVector<AllocaInst*,8> allocas;
    for (auto& i : f->getEntryBlock()) if (auto* a=dyn_cast<AllocaInst>(&i)) allocas.push_back(a);
    DominatorTree dom(*f); PromoteMemToReg(allocas,dom);
    std::string errors; raw_string_ostream stream(errors);
    bool invalid=verifyModule(module,&stream);
    require(!invalid,"Normalization produced invalid LLVM IR: "+errors);
    inspect(*f,true);
    return Lowering(module,*f).run(inputHash);
}
}
