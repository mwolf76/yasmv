#include "llvm2smv/scalar_lowering.hh"
#include "llvm2smv/model_writer.hh"
#include "llvm2smv/memory_model.hh"
#include "llvm2smv/module_analysis.hh"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include <functional>
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
            } else ok = a.hasAttribute(Attribute::NoUndef) || a.hasAttribute(Attribute::SExt) || a.hasAttribute(Attribute::ZExt);
            require(ok, "Unhandled entry attribute: " + a.getAsString());
        }
    }
}
enum class Hook { None, Assert, Assume, Error, Nondet, Defined, EndObject };
Hook hook(const Function& f)
{
    auto name=f.getName();
    if (name=="__VERIFIER_assert") return Hook::Assert;
    if (name=="__VERIFIER_assume") return Hook::Assume;
    if (name=="__VERIFIER_error") return Hook::Error;
    if (name=="__llvm2smv_end_object") return Hook::EndObject;
    if (name.starts_with("__llvm2smv_defined_")) return Hook::Defined;
    static const std::map<std::string,unsigned> widths{{"bool",1},{"char",8},{"uchar",8},
        {"short",16},{"ushort",16},{"int",32},{"uint",32},{"long",64},{"ulong",64},
        {"longlong",64},{"ulonglong",64}};
    if (name.starts_with("__VERIFIER_nondet_")) {
        auto it=widths.find(name.drop_front(18).str());
        require(it!=widths.end() && f.getReturnType()->isIntegerTy(it->second), "Unknown nondeterministic hook or incorrect return width");
        return Hook::Nondet;
    }
    return Hook::None;
}
void admittedType(Type* t,bool memory) { if(memory) MemoryModel::widths(t); else width(t); }
void signature(const Function& f,bool memory=false)
{
    SmallVector<std::pair<unsigned,MDNode*>,4> metadata;
    f.getAllMetadata(metadata);
    for (auto [kind,node] : metadata) { (void)node; require(kind==LLVMContext::MD_dbg,"Unhandled function metadata"); }
    require(!f.isVarArg() && f.getCallingConv()==CallingConv::C && !f.hasPersonalityFn()
        && !f.hasPrefixData() && !f.hasPrologueData() && !f.hasGC() && !f.hasComdat() && !f.hasSection()
        && f.getAddressSpace()==0 && (f.hasExternalLinkage() || f.hasInternalLinkage() || f.hasPrivateLinkage()),
        "Only ordinary C function signatures/linkage are supported");
    require(f.getReturnType()->isVoidTy() || f.getReturnType()->isIntegerTy() || (memory && f.getReturnType()->isPointerTy()),"Aggregate function ABI is unsupported");
    for(auto& arg:f.args()) require(arg.getType()->isIntegerTy() || (memory && arg.getType()->isPointerTy()),"Aggregate function ABI is unsupported");
    if (!f.getReturnType()->isVoidTy()) admittedType(f.getReturnType(),memory);
    for (const auto& arg : f.args()) admittedType(arg.getType(),memory);
    attributes(f);
    auto h=hook(f);
    if (h==Hook::None) require(!f.isDeclaration(),"Unknown external function: "+f.getName().str());
    else {
        require(f.isDeclaration(),"Verifier hooks must be declarations, not overridden definitions");
        bool unary=h==Hook::Assert || h==Hook::Assume || h==Hook::Defined || h==Hook::EndObject;
        require(f.arg_size()==(unary ? 1u : 0u) && (h==Hook::Nondet ? f.getReturnType()->isIntegerTy() : f.getReturnType()->isVoidTy()),
            "Incorrect verifier hook signature");
        if (h==Hook::Assert || h==Hook::Assume) require(f.getArg(0)->getType()->isIntegerTy(32),"Verifier predicates take an i32 argument");
    }
}
void callContract(const CallInst& call,bool memory)
{
    auto* callee=call.getCalledFunction();
    require(callee && call.getFunctionType()==callee->getFunctionType() && !call.isMustTailCall()
        && call.getCallingConv()==CallingConv::C && call.getNumOperandBundles()==0,
        "Only direct, type-matched C calls without operand bundles are supported", &call);
    signature(*callee,memory);
    for (unsigned index : call.getAttributes().indexes()) for (Attribute a : call.getAttributes().getAttributes(index)) {
        bool ok=index==AttributeList::FunctionIndex ? a.hasAttribute(Attribute::NoUnwind) :
            a.hasAttribute(Attribute::NoUndef) || a.hasAttribute(Attribute::SExt) || a.hasAttribute(Attribute::ZExt);
        require(ok,"Unhandled call-site attribute: "+a.getAsString(),&call);
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
void inspect(Function& f, bool normalized, bool memory)
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
        if (!i.getType()->isVoidTy() && !isa<AllocaInst>(i)) admittedType(i.getType(),memory);
        for (const Use& u : i.operands()) {
            require(!isa<UndefValue>(u.get()) || isa<PoisonValue>(u.get()), "undef is unsupported; initialize scalar locals explicitly", &i);
            if (isa<Constant>(u.get()) && u->getType()->isIntegerTy())
                require(isa<ConstantInt>(u.get()) || isa<PoisonValue>(u.get()), "Unsupported integer constant expression", &i);
        }
        if(auto* cmp=dyn_cast<ICmpInst>(&i); cmp && cmp->getOperand(0)->getType()->isPointerTy())
            require(!cmp->isSigned(),"Signed pointer ordering is unsupported",&i);
        switch (i.getOpcode()) {
        case Instruction::Add: case Instruction::Sub: case Instruction::Mul:
        case Instruction::UDiv: case Instruction::SDiv: case Instruction::URem: case Instruction::SRem:
        case Instruction::Shl: case Instruction::LShr: case Instruction::AShr:
        case Instruction::And: case Instruction::Or: case Instruction::Xor:
        case Instruction::ICmp: case Instruction::Trunc: case Instruction::ZExt: case Instruction::SExt:
        case Instruction::Freeze:
            require(i.getType()->isIntegerTy(),"Pointer/aggregate freeze is unsupported",&i); break;
        case Instruction::GetElementPtr:
            require(memory,"GEP requires memory lowering",&i); MemoryModel::widths(cast<GetElementPtrInst>(i).getSourceElementType()); break;
        case Instruction::ExtractValue: case Instruction::InsertValue:
            require(memory,"Aggregate instructions require memory lowering",&i); break;
        case Instruction::Select: case Instruction::PHI:
        case Instruction::Br: case Instruction::Switch: case Instruction::Ret: case Instruction::Unreachable:
            break;
        case Instruction::Load: case Instruction::Store:
            if(!memory) checkMemory(i,dl);
            else if(auto* load=dyn_cast<LoadInst>(&i)) require(!load->isAtomic() && !load->isVolatile(),"Atomic/volatile memory is unsupported",&i);
            else { auto& store=cast<StoreInst>(i); require(!store.isAtomic() && !store.isVolatile(),"Atomic/volatile memory is unsupported",&i); }
            break;
        case Instruction::Call: {
            auto& call=cast<CallInst>(i);
            if(memory && (isa<MemIntrinsic>(i) || (isa<IntrinsicInst>(i) && (cast<IntrinsicInst>(i).getIntrinsicID()==Intrinsic::lifetime_start || cast<IntrinsicInst>(i).getIntrinsicID()==Intrinsic::lifetime_end)))) {
                require(!call.isMustTailCall() && call.getNumOperandBundles()==0 && call.getCallingConv()==CallingConv::C,"Unsupported intrinsic call convention/bundles",&i);
                require(call.getCalledFunction()->getAttributes()==Intrinsic::getAttributes(i.getContext(),cast<IntrinsicInst>(i).getIntrinsicID()),
                    "Additional memory-intrinsic declaration attributes are unsupported",&i);
                if(auto* mem=dyn_cast<MemIntrinsic>(&i)) {
                    require(!mem->isVolatile() && (mem->getIntrinsicID()==Intrinsic::memset || mem->getIntrinsicID()==Intrinsic::memcpy || mem->getIntrinsicID()==Intrinsic::memmove),"Unsupported memory intrinsic",&i);
                    width(mem->getLength()->getType());
                } else {
                    auto* a=dyn_cast<AllocaInst>(call.getArgOperand(1)); auto* length=dyn_cast<ConstantInt>(call.getArgOperand(0));
                    require(a && length && (length->isMinusOne() || length->getZExtValue()==dl.getTypeAllocSize(a->getAllocatedType()).getFixedValue()*cast<ConstantInt>(a->getArraySize())->getZExtValue()),"Lifetime intrinsics must cover one whole directly named stack object",&i);
                }
                for(unsigned index:call.getAttributes().indexes()) for(Attribute attr:call.getAttributes().getAttributes(index))
                    require(index!=AttributeList::FunctionIndex && attr.hasAttribute(Attribute::Alignment),"Unhandled memory-intrinsic call-site attribute",&i);
                break;
            }
            callContract(call,memory);
            require(!normalized || hook(*call.getCalledFunction())!=Hook::None,"Call was not inlined",&i);
            break;
        }
        case Instruction::Alloca: {
            auto& a = cast<AllocaInst>(i);
            require((memory || !normalized) && (normalized || &b == &f.getEntryBlock()) && a.getAddressSpace() == 0 && isa<ConstantInt>(a.getArraySize())
                && !a.isUsedWithInAlloca() && !a.isSwiftError()
                && !cast<ConstantInt>(a.getArraySize())->isZero() && cast<ConstantInt>(a.getArraySize())->getValue().ule(4096)
                && (memory || (cast<ConstantInt>(a.getArraySize())->isOne() && isAllocaPromotable(&a))),
                "Allocas require positive fixed sizes in original entry blocks; scalar mode also requires promotion", &i);
            admittedType(a.getAllocatedType(),memory); break;
        }
        default: throw ScalarError("Unsupported scalar instruction: " + std::string(i.getOpcodeName()), &i);
        }
    }
}

// Unlike InlineFunction's clone-and-prune path, preserve even unused UB sites.
void inlineExact(CallInst& call)
{
    auto& callee=*call.getCalledFunction();
    auto& caller=*call.getFunction();
    ValueToValueMapTy map;
    for (auto& arg : callee.args()) map[&arg]=call.getArgOperand(arg.getArgNo());
    SmallVector<BasicBlock*,16> blocks;
    for (auto& b : callee) {
        auto* clone=CloneBasicBlock(&b,map,".inline",&caller);
        map[&b]=clone; blocks.push_back(clone);
    }
    std::map<const DILocation*,DILocation*> cache;
    std::function<DILocation*(DILocation*)> append = [&](DILocation* loc) {
        if (!loc) return call.getDebugLoc().get();
        auto found=cache.find(loc);
        if (found!=cache.end()) return found->second;
        auto* result=DILocation::get(caller.getContext(),loc->getLine(),loc->getColumn(),loc->getScope(),
            append(loc->getInlinedAt()),loc->isImplicitCode());
        cache[loc]=result; return result;
    };
    SmallVector<ReturnInst*,4> returns;
    for (auto* b : blocks) for (auto& i : *b) {
        RemapInstruction(&i,map,RF_NoModuleLevelChanges);
        if (auto loc=i.getDebugLoc(); loc && call.getDebugLoc())
            i.setDebugLoc(append(loc.get()));
        if (auto* ret=dyn_cast<ReturnInst>(&i)) returns.push_back(ret);
    }
    auto* before=call.getParent();
    auto* after=before->splitBasicBlock(call.getNextNode(),"call.continue");
    before->getTerminator()->eraseFromParent();
    auto* jump=BranchInst::Create(blocks.front(),before); jump->setDebugLoc(call.getDebugLoc());
    if (!call.getType()->isVoidTy()) {
        if (returns.empty()) call.replaceAllUsesWith(PoisonValue::get(call.getType()));
        else {
            auto* phi=PHINode::Create(call.getType(),returns.size(),"call.result",&after->front());
            phi->setDebugLoc(call.getDebugLoc());
            for (auto* ret : returns) phi->addIncoming(ret->getReturnValue(),ret->getParent());
            call.replaceAllUsesWith(phi);
        }
    }
    for (auto* ret : returns) {
        auto* branch=BranchInst::Create(after,ret); branch->setDebugLoc(ret->getDebugLoc()); ret->eraseFromParent();
    }
    call.eraseFromParent();
}

// Validate every syntactically reachable body before normalization changes it.
void normalizeCalls(Function& entry,bool memory)
{
    std::map<Function*,unsigned> colors;
    std::vector<Function*> closure;
    std::function<void(Function&,unsigned)> visit = [&](Function& f,unsigned depth) {
        require(depth<256,"Call-graph inspection depth budget exceeded");
        require(colors[&f]!=1,"Recursive call graphs require a later milestone");
        if (colors[&f]==2) return;
        colors[&f]=1; signature(f,memory); inspect(f,false,memory); closure.push_back(&f);
        for (auto& b : f) for (auto& i : b) if (auto* call=dyn_cast<CallInst>(&i)) {
            if (isa<IntrinsicInst>(i)) continue;
            auto& callee=*call->getCalledFunction();
            if (hook(callee)==Hook::None) visit(callee,depth+1);
        }
        colors[&f]=2;
    };
    visit(entry,0);
    // Preserve noundef boundaries explicitly; inlining must not erase these UB sites.
    auto defined = [&](Value* value, Instruction* before, DebugLoc loc) {
        auto& m=*entry.getParent();
        auto type=FunctionType::get(Type::getVoidTy(m.getContext()),{value->getType()},false);
        auto fn=m.getOrInsertFunction("__llvm2smv_defined_"+(value->getType()->isIntegerTy() ? std::to_string(width(value->getType())) : std::string("ptr")),type);
        IRBuilder<> builder(before); builder.SetCurrentDebugLocation(loc); builder.CreateCall(fn,{value});
    };
    for (auto* f : closure) {
        SmallVector<AllocaInst*,8> allocas;
        for (auto& i : f->getEntryBlock()) if (auto* a=dyn_cast<AllocaInst>(&i); a && isAllocaPromotable(a)) {
            bool lifetime=false;
            for(auto* user:a->users()) if(auto* call=dyn_cast<IntrinsicInst>(user))
                lifetime |= call->getIntrinsicID()==Intrinsic::lifetime_start || call->getIntrinsicID()==Intrinsic::lifetime_end;
            if(!lifetime) allocas.push_back(a);
        }
        DominatorTree dom(*f); PromoteMemToReg(allocas,dom);
        inspect(*f,false,memory);
        for (auto& arg : f->args()) if (arg.hasAttribute(Attribute::NoUndef))
            defined(&arg,&*f->getEntryBlock().getFirstInsertionPt(),{});
        SmallVector<Instruction*,16> original;
        for (auto& b : *f) for (auto& i : b) original.push_back(&i);
        for (auto* i : original) {
            if (auto* ret=dyn_cast<ReturnInst>(i)) {
                if(f->hasRetAttribute(Attribute::NoUndef)) defined(ret->getReturnValue(),ret,ret->getDebugLoc());
                if(memory) for(auto& block:*f) for(auto& item:block) if(auto* a=dyn_cast<AllocaInst>(&item)) {
                    auto type=FunctionType::get(Type::getVoidTy(f->getContext()),{a->getType()},false);
                    auto fn=f->getParent()->getOrInsertFunction("__llvm2smv_end_object",type);
                    IRBuilder<> builder(ret); builder.SetCurrentDebugLocation(ret->getDebugLoc()); builder.CreateCall(fn,{a});
                }
            }
            if (auto* call=dyn_cast<CallInst>(i); call && !isa<IntrinsicInst>(i)) {
                for (unsigned n=0;n<call->arg_size();++n) if (call->paramHasAttr(n,Attribute::NoUndef))
                    defined(call->getArgOperand(n),call,call->getDebugLoc());
                if (call->hasRetAttr(Attribute::NoUndef)) defined(call,call->getNextNode(),call->getDebugLoc());
            }
        }
    }
    unsigned expansions=0;
    while (true) {
        CallInst* target=nullptr; size_t count=0;
        for (auto& b : entry) for (auto& i : b) {
            ++count;
            if (auto* call=dyn_cast<CallInst>(&i); call && !isa<DbgInfoIntrinsic>(i) && !call->getCalledFunction()->isDeclaration()) target=call;
        }
        require(count<=100000 && expansions<=10000,"Inlining translation budget exceeded");
        if (!target) break;
        inlineExact(*target); ++expansions;
    }
}
json::Object source(const Instruction& i)
{
    json::Array chain;
    for (auto* loc=i.getDebugLoc().get();loc;loc=loc->getInlinedAt()) {
        std::string function;
        if (auto* scope=dyn_cast<DILocalScope>(loc->getScope())) if (auto* sub=scope->getSubprogram()) function=sub->getName().str();
        chain.push_back(json::Object{{"file",loc->getFilename().str()},{"directory",loc->getDirectory().str()},
            {"line",loc->getLine()},{"column",loc->getColumn()},{"function",function}});
    }
    return json::Object{{"ir",ir(i)},{"inline_chain",std::move(chain)}};
}

class Lowering {
public:
    Lowering(Module& module, Function& function, bool addressable, MemoryLimits limits) : module(module), function(function), addressable(addressable), limits(limits) {}
    json::Object run(const std::string& inputHash);
private:
    Module& module; Function& function; ts::Model model;
    std::map<const Value*,Slot> slots;
    bool addressable; MemoryLimits limits; std::unique_ptr<MemoryModel> memory;
    std::map<const Value*,std::vector<Slot>> compound;
    std::vector<Slot> returnCells;
    Pieces readCells(const Value*) const;
    std::vector<Slot> allocateCells(const Value&,const std::string&);
    std::vector<ts::Write> cellWrites(const Value&,const Pieces&) const;
    void memoryStep(const Instruction&,MemoryEffect);
    void cellsResult(const Instruction&,const Pieces&,Expr);
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
std::vector<Slot> Lowering::allocateCells(const Value& value,const std::string& key)
{
    if(value.getType()->isIntegerTy()) return {allocate(value,key,Mode::State,std::nullopt)};
    std::vector<Slot> out; unsigned index=0;
    for(auto w:memory->valueWidths(value.getType())) {
        auto name=key+".cell."+std::to_string(index++);
        out.push_back({model.variable(name,ts::Type::word(w),Mode::State,number(w,0)),model.variable(name+".poison",ts::Type::boolean(),Mode::State,bit(false))});
    }
    compound[&value]=out; return out;
}
Pieces Lowering::readCells(const Value* value) const
{
    if(value->getType()->isIntegerTy()) return {read(value)};
    if(auto* c=dyn_cast<Constant>(value)) return memory->constant(c);
    Pieces out; for(auto& slot:compound.at(value)) out.push_back({v(slot.bits),v(slot.poison)});
    return value->getType()->isPointerTy() ? memory->knownAddress(value,std::move(out)) : out;
}
std::vector<ts::Write> Lowering::cellWrites(const Value& value,const Pieces& pieces) const
{
    auto dest=value.getType()->isIntegerTy() ? std::vector<Slot>{slots.at(&value)} : compound.at(&value);
    std::vector<ts::Write> writes;
    require(dest.size()==pieces.size(),"Mismatched compound value representation");
    for(unsigned j=0;j<dest.size();++j) { writes.push_back({dest[j].bits,pieces[j].bits}); writes.push_back({dest[j].poison,pieces[j].poison}); }
    return writes;
}
void Lowering::cellsResult(const Instruction& i,const Pieces& pieces,Expr ub)
{
    auto writes=cellWrites(i,pieces); writes.push_back({pc,label(locations.at(next(i)))});
    step(i,".execute",bit(true),std::move(writes),ub);
}
void Lowering::memoryStep(const Instruction& i,MemoryEffect effect)
{
    auto stop=either(effect.error,either(effect.unsupported,effect.bound));
    if(!i.getType()->isVoidTy()) { auto writes=cellWrites(i,effect.value); effect.writes.insert(effect.writes.end(),writes.begin(),writes.end()); }
    effect.writes.push_back({pc,label(locations.at(next(i)))});
    step(i,".memory",bit(true),std::move(effect.writes),stop);
    if(!isBit(effect.error,false)) model.step(locations.at(&i)+".memory-error",both(at(i),effect.error),{{pc,label("ERROR")}});
    if(!isBit(effect.unsupported,false)) model.step(locations.at(&i)+".memory-unsupported",both(at(i),both(no(effect.error),effect.unsupported)),{{pc,label("UNSUPPORTED_MEMORY")}});
    if(!isBit(effect.bound,false)) model.step(locations.at(&i)+".memory-bound",both(at(i),both(no(either(effect.error,effect.unsupported)),effect.bound)),{{pc,label("MEMORY_BOUND")}});
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
        auto incoming=cellWrites(phi,readCells(phi.getIncomingValueForBlock(&from)));
        writes.insert(writes.end(),incoming.begin(),incoming.end());
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
    if(memory) {
        if(auto* a=dyn_cast<AllocaInst>(&i)) { memoryStep(i,memory->allocate(*a)); return; }
        if(auto* load=dyn_cast<LoadInst>(&i)) { memoryStep(i,memory->load(readCells(load->getPointerOperand()),load->getType(),load->getAlign())); return; }
        if(auto* store=dyn_cast<StoreInst>(&i)) { memoryStep(i,memory->store(readCells(store->getPointerOperand()),store->getValueOperand()->getType(),readCells(store->getValueOperand()),store->getAlign())); return; }
        if(auto* g=dyn_cast<GetElementPtrInst>(&i)) {
            std::vector<ValueExpr> indices;
            for(auto& index:g->indices()) {
                auto value=read(index.get());
                // Retain the stored SSA value/poison, but discard bits that the
                // defining extension proves redundant for signed GEP indexing.
                if(auto* c=dyn_cast<CastInst>(index.get())) {
                    unsigned from=c->getSrcTy()->getIntegerBitWidth();
                    if(c->getOpcode()==Instruction::ZExt && from<63)
                        value.bits=Expr::cast(ts::Type::word(from+1),value.bits);
                    else if(c->getOpcode()==Instruction::SExt)
                        value.bits=Expr::cast(ts::Type::word(from),value.bits);
                }
                indices.push_back(value);
            }
            MemoryEffect effect; effect.value=memory->gep(*cast<GEPOperator>(g),readCells(g->getPointerOperand()),indices,&effect.unsupported);
            memoryStep(i,std::move(effect)); return;
        }
        if(auto* e=dyn_cast<ExtractValueInst>(&i)) {
            auto all=readCells(e->getAggregateOperand()); auto start=MemoryModel::fieldIndex(e->getAggregateOperand()->getType(),e->getIndices());
            auto count=MemoryModel::widths(e->getType()).size(); cellsResult(i,Pieces(all.begin()+start,all.begin()+start+count),ub); return;
        }
        if(auto* e=dyn_cast<InsertValueInst>(&i)) {
            auto all=readCells(e->getAggregateOperand()), insert=readCells(e->getInsertedValueOperand()); auto start=MemoryModel::fieldIndex(e->getType(),e->getIndices());
            std::copy(insert.begin(),insert.end(),all.begin()+start); cellsResult(i,all,ub); return;
        }
        if(auto* mem=dyn_cast<MemIntrinsic>(&i)) {
            MemoryEffect effect;
            if(auto* set=dyn_cast<MemSetInst>(mem)) { auto fill=read(set->getValue()); effect=memory->transfer(readCells(mem->getDest()),{},read(mem->getLength()),true,&fill,mem->getDestAlign().valueOrOne().value()); }
            else { auto* copy=cast<MemTransferInst>(mem); effect=memory->transfer(readCells(mem->getDest()),readCells(copy->getSource()),read(mem->getLength()),isa<MemMoveInst>(mem),nullptr,mem->getDestAlign().valueOrOne().value(),copy->getSourceAlign().valueOrOne().value()); }
            memoryStep(i,std::move(effect)); return;
        }
        if(auto* intrinsic=dyn_cast<IntrinsicInst>(&i)) {
            memoryStep(i,memory->lifetime(readCells(intrinsic->getArgOperand(1)),intrinsic->getIntrinsicID()==Intrinsic::lifetime_start)); return;
        }
    }
    if (auto* call=dyn_cast<CallInst>(&i)) {
        auto h=hook(*call->getCalledFunction());
        if(h==Hook::EndObject) { memoryStep(i,memory->lifetime(readCells(call->getArgOperand(0)),false)); return; }
        if(h==Hook::Defined && !call->getArgOperand(0)->getType()->isIntegerTy()) {
            for(auto& part:readCells(call->getArgOperand(0))) ub=either(ub,part.poison);
            step(i,".defined",bit(true),{{pc,label(locations.at(next(i)))}},ub);
            model.step(locations.at(&i)+".ub",both(at(i),ub),{{pc,label("ERROR")}}); return;
        }
        if (h==Hook::Nondet) result(i,{v(choices.at(&i)),bit(false)},ub);
        else if (h==Hook::Error) step(i,".assertion",bit(true),{{pc,label("ASSERT."+locations.at(&i))}},ub);
        else {
            auto a=read(call->getArgOperand(0)); ub=a.poison;
            auto condition=h==Hook::Defined ? bit(true) : no(eq(a.bits,number(a.bits.type().width(),0)));
            step(i,".continue",condition,{{pc,label(locations.at(next(i)))}},ub);
            if (h!=Hook::Defined) step(i,".excluded",no(condition),{{pc,label(h==Hook::Assume ? "ASSUMED_OUT" : "ASSERT."+locations.at(&i))}},ub);
        }
    }
    else if (auto* op=dyn_cast<BinaryOperator>(&i)) { auto value=integer(*op,ub); result(i,value,ub); }
    else if (auto* cmp=dyn_cast<ICmpInst>(&i)) {
        if(cmp->getOperand(0)->getType()->isPointerTy()) {
            MemoryEffect effect; effect.value={memory->compare(cmp->getPredicate(),readCells(cmp->getOperand(0)),readCells(cmp->getOperand(1)),effect.unsupported)};
            memoryStep(i,std::move(effect)); return;
        }
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
        auto c=read(s->getCondition()); auto yes=readCells(s->getTrueValue()), noValue=readCells(s->getFalseValue());
        auto condition=eq(c.bits,number(1,1)); Pieces out;
        for(unsigned j=0;j<yes.size();++j) out.push_back({choose(condition,yes[j].bits,noValue[j].bits),either(c.poison,choose(condition,yes[j].poison,noValue[j].poison))});
        cellsResult(i,out,ub);
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
            auto values=readCells(ret->getReturnValue());
            for(unsigned j=0;j<values.size();++j) {
                if(function.hasRetAttribute(Attribute::NoUndef)) ub=either(ub,values[j].poison);
                writes.push_back({returnCells[j].bits,values[j].bits}); writes.push_back({returnCells[j].poison,values[j].poison});
            }
        }
        step(i,".return",bit(true),std::move(writes),ub);
    } else if (isa<UnreachableInst>(i)) ub=bit(true);
    else throw ScalarError("Internal unhandled instruction", &i);
    if (!isBit(ub,false)) model.step(locations.at(&i)+".ub",both(at(i),ub),{{pc,label("ERROR")}});
}
json::Object Lowering::run(const std::string& inputHash)
{
    if(addressable) memory=std::make_unique<MemoryModel>(model,module,function,limits);
    std::vector<std::string> labels{"DONE","ERROR","ASSUMED_OUT","UNSUPPORTED_MEMORY","MEMORY_BOUND"}; unsigned bi=0;
    for (const auto& b : function) {
        unsigned ii=0;
        for (const auto& i : b) {
            if (isa<DbgInfoIntrinsic>(i)) continue;
            auto key="b"+std::to_string(bi)+".i"+std::to_string(ii++);
            if (!i.getType()->isVoidTy()) allocateCells(i,"ssa."+key);
            if (isa<PHINode>(i)) continue;
            locations.emplace(&i,key); labels.push_back(key);
            if (auto* call=dyn_cast<CallInst>(&i); call && (hook(*call->getCalledFunction())==Hook::Assert || hook(*call->getCalledFunction())==Hook::Error))
                labels.push_back("ASSERT."+key);
            if (isa<FreezeInst>(i) || (isa<CallInst>(i) && hook(*cast<CallInst>(i).getCalledFunction())==Hook::Nondet)) choices[&i]=model.variable("choice."+key,ts::Type::word(width(i.getType())),Mode::Choice,std::nullopt);
        }
        ++bi;
    }
    pcType=ts::Type::enumeration("pc",std::move(labels));
    pc=model.variable("pc",*pcType,Mode::State,label(locations.at(first(function.getEntryBlock()))));
    if (!function.getReturnType()->isVoidTy()) {
        unsigned w=width(function.getReturnType());
        returned=Slot{model.variable("return",ts::Type::word(w),Mode::State,number(w,0)),
            model.variable("return.poison",ts::Type::boolean(),Mode::State,bit(false))};
        returnCells={*returned};
    }
    if(!memory) for (const auto& g : module.globals()) allocate(g,"global."+g.getName().str(),g.isConstant() ? Mode::Frozen : Mode::State,
        cast<ConstantInt>(g.getInitializer())->getValue());
    for (const auto& b : function) for (const auto& i : b)
        if (!isa<PHINode>(i) && !isa<DbgInfoIntrinsic>(i)) lower(i);
    model.property("terminated",eq(v(pc),label("DONE")));
    model.property("runtime_error",eq(v(pc),label("ERROR")));
    if (returned) model.property("return_defined",both(eq(v(pc),label("DONE")),no(v(returned->poison))));
    Expr failed=bit(false);
    json::Object locationsJson;
    for (const auto& block : function) for (const auto& item : block) {
        auto* instruction=&item;
        auto found=locations.find(instruction);
        if (found==locations.end()) continue;
        const auto& key=found->second;
        auto record=source(*instruction);
        record["key"]=key;
        if (auto* call=dyn_cast<CallInst>(instruction)) {
            auto h=hook(*call->getCalledFunction());
            record["hook"]=call->getCalledFunction()->getName().str();
            if (h==Hook::Assert || h==Hook::Error) {
                auto failure=eq(v(pc),label("ASSERT."+key)); failed=either(failed,failure);
                auto property="assertion."+key;
                model.property(property,no(failure));
                record["assertion_property"]=ts::propertyName(property);
            }
            if (h==Hook::Nondet) record["choice_symbol"]=ts::symbolName(choices.at(instruction)->key);
        }
        locationsJson[ts::literalName(*pcType,key)]=std::move(record);
    }
    model.property("memory_supported",no(eq(v(pc),label("UNSUPPORTED_MEMORY"))));
    model.property("memory_within_bound",no(eq(v(pc),label("MEMORY_BOUND"))));
    model.property("assertion_failed",failed);
    model.property("safe",no(either(failed,eq(v(pc),label("ERROR")))));
    model.property("assumed_out",eq(v(pc),label("ASSUMED_OUT")));
    model.property("progress_goal",either(eq(v(pc),label("DONE")),eq(v(pc),label("ASSUMED_OUT"))));
    return ts::artifact(model,{{"lowering",memory ? "memory-v1" : "scalar-v2"},{"normalization",memory ? "checked-inline-memory-v1" : "checked-inline-mem2reg-v2"},
        {"input_ir_sha256",inputHash},{"normalized_ir_sha256",ts::sha256(moduleText(module))},
        {"entry",function.getName().str()},{"target_triple",module.getTargetTriple()},
        {"data_layout",module.getDataLayoutStr()},{"environment","closed-module; no interposition; verifier-hooks-v1"},
        {"semantics",memory ? "LLVM18 integers; opaque object pointers; strict uninitialized-read diagnostics; memory coverage required" : "LLVM18 scalar bitvectors and poison; error sink at admitted UB; undef rejected"}},memory ? "llvm18-memory-v1" : "llvm18-scalar-v2",std::move(locationsJson),memory ? memory->describe() : json::Object{});
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
json::Object lowerScalar(Module& module, StringRef entry, MemoryLimits limits)
{
    for (auto& f : module) require(!f.getName().starts_with("__llvm2smv_"),"Reserved internal runtime name");
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
        MemoryModel::widths(g.getValueType());
        require(g.hasInitializer(),"Globals require concrete initializers: "+g.getName().str());
    }
    auto* f=module.getFunction(entry);
    require(f && !f->isDeclaration(),"The entry must name a defined function");
    require(f->arg_empty() && !f->isVarArg() && f->getCallingConv()==CallingConv::C && !f->hasPersonalityFn()
        && !f->hasPrefixData() && !f->hasPrologueData(),"Entry requires a zero-argument C calling convention and no exceptional ABI");
    if (!f->getReturnType()->isVoidTy()) width(f->getReturnType());
    bool addressable=false;
    for(auto& g:module.globals()) addressable |= !g.getValueType()->isIntegerTy() || !isa<ConstantInt>(g.getInitializer());
    for(auto& fn:module) if(!fn.isDeclaration())
        for(auto& arg:fn.args()) addressable |= arg.getType()->isPointerTy();
    for(auto& fn:module) for(auto& block:fn) for(auto& i:block) {
        if(auto* a=dyn_cast<AllocaInst>(&i)) {
            auto* count=dyn_cast<ConstantInt>(a->getArraySize());
            addressable |= !a->getAllocatedType()->isIntegerTy() || !count || !count->isOne() || !isAllocaPromotable(a);
        }
        else if(!i.getType()->isVoidTy() && !i.getType()->isIntegerTy()) addressable=true;
        if(auto* load=dyn_cast<LoadInst>(&i)) addressable |= !isa<GlobalVariable>(load->getPointerOperand()) && !isa<AllocaInst>(load->getPointerOperand());
        if(auto* store=dyn_cast<StoreInst>(&i)) addressable |= !isa<GlobalVariable>(store->getPointerOperand()) && !isa<AllocaInst>(store->getPointerOperand());
        if(auto* cmp=dyn_cast<ICmpInst>(&i)) addressable |= cmp->getOperand(0)->getType()->isPointerTy();
        if(auto* ret=dyn_cast<ReturnInst>(&i); ret && ret->getReturnValue()) addressable |= ret->getReturnValue()->getType()->isPointerTy();
        auto indirectType=[&](Value* pointer,Type* accessed) {
            if(auto* g=dyn_cast<GlobalVariable>(pointer)) return g->getValueType()!=accessed;
            if(auto* a=dyn_cast<AllocaInst>(pointer)) return a->getAllocatedType()!=accessed;
            return true;
        };
        if(auto* load=dyn_cast<LoadInst>(&i)) addressable |= indirectType(load->getPointerOperand(),load->getType());
        if(auto* store=dyn_cast<StoreInst>(&i)) addressable |= indirectType(store->getPointerOperand(),store->getValueOperand()->getType());
        if(isa<MemIntrinsic>(i)) addressable=true;
        if(auto* intr=dyn_cast<IntrinsicInst>(&i)) addressable |= intr->getIntrinsicID()==Intrinsic::lifetime_start || intr->getIntrinsicID()==Intrinsic::lifetime_end;
    }
    normalizeCalls(*f,addressable);
    std::string errors; raw_string_ostream stream(errors);
    bool invalid=verifyModule(module,&stream);
    require(!invalid,"Normalization produced invalid LLVM IR: "+errors);
    inspect(*f,true,addressable);
    return Lowering(module,*f,addressable,limits).run(inputHash);
}
}
