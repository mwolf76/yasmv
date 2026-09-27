#include "llvm2smv/memory_model.hh"
#include "llvm2smv/scalar_lowering.hh"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IntrinsicInst.h"
#include <functional>

namespace llvm2smv {
using namespace llvm;
using namespace ts;
namespace {
Expr b(bool x) { return Expr::boolean(x); }
Expr n(uint64_t x,unsigned w=64) { return Expr::integer(ts::Type::word(w),APInt(w,x)); }
Expr v(SymbolRef s) { return Expr::variable(s); }
Expr op(Op o,Expr x,Expr y) {
    if(o==Op::Equal && x.kind()==Expr::Kind::Boolean && y.kind()==Expr::Kind::Boolean) return b(x.booleanValue()==y.booleanValue());
    if(x.kind()==Expr::Kind::Integer && y.kind()==Expr::Kind::Integer) {
        auto a=x.bits(),d=y.bits(); bool sign=x.type().isSigned();
        switch(o) {
        case Op::Add: return Expr::integer(x.type(),a+d);
        case Op::Sub: return Expr::integer(x.type(),a-d);
        case Op::Mul: return Expr::integer(x.type(),a*d);
        case Op::BitAnd: return Expr::integer(x.type(),a&d);
        case Op::BitOr: return Expr::integer(x.type(),a|d);
        case Op::ShiftLeft: return Expr::integer(x.type(),a.shl(d.getLimitedValue(a.getBitWidth())));
        case Op::ShiftRight: return Expr::integer(x.type(),sign ? a.ashr(d.getLimitedValue(a.getBitWidth())) : a.lshr(d.getLimitedValue(a.getBitWidth())));
        case Op::Equal: return b(a==d);
        case Op::Less: return b(sign ? a.slt(d) : a.ult(d));
        case Op::LessEqual: return b(sign ? a.sle(d) : a.ule(d));
        case Op::GreaterEqual: return b(sign ? a.sge(d) : a.uge(d));
        default: break;
        }
    }
    if(x.kind()==Expr::Kind::Integer && x.bits().isZero()) {
        if(o==Op::Add || o==Op::BitOr) return y;
        if(o==Op::Mul || o==Op::BitAnd) return x;
    }
    if(y.kind()==Expr::Kind::Integer && y.bits().isZero()) {
        if(o==Op::Add || o==Op::Sub || o==Op::BitOr || o==Op::ShiftLeft || o==Op::ShiftRight) return x;
        if(o==Op::Mul || o==Op::BitAnd) return y;
    }
    if(o==Op::Mul && y.kind()==Expr::Kind::Integer && y.bits().isPowerOf2())
        return op(Op::ShiftLeft,x,Expr::integer(y.type(),APInt(y.type().width(),y.bits().logBase2())));
    return Expr::binary(o,x,y);
}
Expr eq(Expr x,Expr y) { return op(Op::Equal,x,y); }
Expr no(Expr x) { return x.kind()==Expr::Kind::Boolean ? b(!x.booleanValue()) : Expr::unary(Op::Not,x); }
Expr all(Expr x,Expr y) {
    if(x.kind()==Expr::Kind::Boolean) return x.booleanValue() ? y : x;
    if(y.kind()==Expr::Kind::Boolean) return y.booleanValue() ? x : y;
    return op(Op::And,x,y);
}
Expr any(Expr x,Expr y) {
    if(x.kind()==Expr::Kind::Boolean) return x.booleanValue() ? x : y;
    if(y.kind()==Expr::Kind::Boolean) return y.booleanValue() ? y : x;
    return op(Op::Or,x,y);
}
Expr sel(Expr c,Expr x,Expr y) { return c.kind()==Expr::Kind::Boolean ? (c.booleanValue() ? x : y) : Expr::select(c,x,y); }
Expr cast(Expr x,unsigned w,bool sign=false) {
    if(x.kind()==Expr::Kind::Integer) return Expr::integer(ts::Type::word(w,sign),x.type().isSigned() ? x.bits().sextOrTrunc(w) : x.bits().zextOrTrunc(w));
    return Expr::cast(ts::Type::word(w,sign),x);
}
Expr poison(const Pieces& p) { Expr r=b(false); for(auto& x:p) r=any(r,x.poison); return r; }
void need(bool ok,const char* s) { if(!ok) throw ScalarError(s); }
bool containsPointer(llvm::Type* t) {
    if(t->isPointerTy()) return true;
    if(auto* a=dyn_cast<ArrayType>(t)) return containsPointer(a->getElementType());
    if(auto* s=dyn_cast<StructType>(t)) { for(auto* e:s->elements()) if(containsPointer(e)) return true; }
    return false;
}
}
std::vector<unsigned> MemoryModel::widths(llvm::Type* t,unsigned offsetWidth)
{
    if(t->isIntegerTy()) { need(t->getIntegerBitWidth()<=64,"Memory values require integer widths <=64"); return {t->getIntegerBitWidth()}; }
    if(t->isPointerTy()) { need(t->getPointerAddressSpace()==0,"Only address space zero is supported"); return {8,offsetWidth,8}; }
    std::vector<unsigned> out;
    auto append=[&](llvm::Type* e){ auto ws=widths(e,offsetWidth); need(out.size()+ws.size()<=1024,"Aggregate scalarization budget exceeded"); out.insert(out.end(),ws.begin(),ws.end()); };
    if(auto* a=dyn_cast<ArrayType>(t)) { need(a->getNumElements()<=1024,"Array scalarization budget exceeded"); for(unsigned i=0;i<a->getNumElements();++i) append(a->getElementType()); }
    else if(auto* s=dyn_cast<StructType>(t)) { need(!s->isOpaque(),"Opaque structure layout is unsupported"); for(auto* e:s->elements()) append(e); }
    else throw ScalarError("Unsupported memory value type");
    return out;
}
unsigned MemoryModel::fieldIndex(llvm::Type* t,ArrayRef<unsigned> indices)
{
    unsigned offset=0;
    for(unsigned i:indices) {
        if(auto* a=dyn_cast<ArrayType>(t)) { offset+=i*widths(a->getElementType()).size(); t=a->getElementType(); }
        else { auto* s=cast<StructType>(t); for(unsigned j=0;j<i;++j) offset+=widths(s->getElementType(j)).size(); t=s->getElementType(i); }
    }
    return offset;
}
unsigned MemoryModel::size(llvm::Type* t) const
{
    widths(t); auto s=module.getDataLayout().getTypeAllocSize(t);
    need(!s.isScalable() && s.getFixedValue()<=limits.bytes,"Object exceeds the configured memory-byte budget");
    return s.getFixedValue();
}
MemoryModel::Byte MemoryModel::blank() const { return {n(0,8),n(0,8),n(0,8),n(0,8),n(0,offsetWidth),n(0,8),n(0,8)}; }
const MemoryModel::Object& MemoryModel::object(const Value* value) const
{
    for(auto& o:objects) if(o.source==value) return o;
    throw ScalarError("Pointer has no modeled object");
}
MemoryModel::MemoryModel(Model& m,Module& mod,Function& f,MemoryLimits lim,const std::map<const Instruction*,unsigned>& owners):model(m),module(mod),limits(lim)
{
    need(limits.bytes>0 && limits.bytes<=4096 && limits.generations>0 && limits.generations<=255,"Memory budgets must be positive (at most 4096 bytes)");
    need(limits.dynamicBytes>0 && limits.dynamicBytes<=4096,"Dynamic stack capacity must be 1..4096 bytes per allocation site");
    need(module.getDataLayout().getIndexSizeInBits(0)==64 && !module.getDataLayout().isNonIntegralAddressSpace(0),"Memory baseline requires integral 64-bit pointer indices");
    offsetWidth=1; for(unsigned bytes=limits.bytes;bytes;bytes>>=1) ++offsetWidth;
    unsigned total=0;
    auto add=[&](const Value& value,llvm::Type* type,unsigned count,uint64_t align,bool writable,bool stack,unsigned frame,bool dynamic) {
        auto bytes=dynamic ? std::min(limits.dynamicBytes,limits.bytes) : uint64_t(size(type))*count;
        need(bytes>0 && bytes<=limits.bytes && total+bytes<=limits.bytes,"Static object storage exceeds the configured memory-byte budget (or is zero-sized)");
        total+=bytes;
        need(objects.size()<255,"Object identity budget exceeded (255 objects)");
        objects.push_back({&value,unsigned(objects.size()+1),unsigned(bytes),frame,dynamic,align,writable,stack,{},{},{},{},{}});
        tags |= containsPointer(type);
    };
    for(auto& g:module.globals()) add(g,g.getValueType(),1,(g.getAlign() ? g.getAlign()->value() : module.getDataLayout().getABITypeAlign(g.getValueType()).value()),!g.isConstant(),false,0,false);
    for(auto& block:f) for(auto& i:block) {
        if(auto* a=dyn_cast<AllocaInst>(&i)) {
            auto* count=dyn_cast<ConstantInt>(a->getArraySize());
            add(*a,a->getAllocatedType(),count ? count->getZExtValue() : 0,a->getAlign().value(),true,true,owners.at(a),!count);
        }
        if(auto* l=dyn_cast<LoadInst>(&i)) tags |= containsPointer(l->getType());
        if(auto* s=dyn_cast<StoreInst>(&i)) tags |= containsPointer(s->getValueOperand()->getType());
    }
    for(auto& o:objects) {
        auto key="memory."+std::to_string(o.id);
        o.live=model.variable(key+".live",ts::Type::boolean(),Mode::State,b(!o.stack));
        o.allocated=model.variable(key+".allocated",ts::Type::boolean(),Mode::State,b(!o.stack));
        if(o.dynamic) o.extent=model.variable(key+".extent",ts::Type::word(offsetWidth),Mode::State,n(0,offsetWidth));
        o.generation=model.variable(key+".generation",ts::Type::word(8),Mode::State,n(0,8));
        std::vector<Byte> initial(o.size,blank());
        if(auto* g=dyn_cast<GlobalVariable>(o.source)) initial=encode(g->getValueType(),constant(g->getInitializer()));
        for(unsigned i=0;i<o.size;++i) {
            auto& x=initial.at(i);
            std::vector<Expr> fields{x.data,x.initialized,x.poison};
            if(tags) fields.insert(fields.end(),{x.object,x.offset,x.generation,x.fragment});
            std::vector<SymbolRef> bytes;
            for(unsigned field=0;field<fields.size();++field)
                bytes.push_back(model.variable(key+".byte."+std::to_string(i)+"."+std::to_string(field),fields[field].type(),Mode::State,fields[field]));
            o.bytes.push_back(std::move(bytes));
        }
    }
    for(auto& block:f) for(auto& i:block) if(auto* call=dyn_cast<IntrinsicInst>(&i); call && call->getIntrinsicID()==Intrinsic::stacksave) {
        auto& snapshot=saves[call];
        auto key="stack.save."+std::to_string(saves.size());
        for(auto& o:objects) if(o.stack && o.frame==owners.at(call))
            snapshot.push_back({o.id,model.variable(key+"."+std::to_string(o.id),ts::Type::word(8),Mode::State,n(0,8))});
    }
}
Pieces MemoryModel::knownAddress(const Value* value,Pieces p) const
{
    if(isa<GlobalVariable>(value) || isa<AllocaInst>(value)) { p[0].bits=n(object(value).id,8); p[1].bits=n(0,offsetWidth); return p; }
    if(auto* g=dyn_cast<GEPOperator>(value)) {
        auto base=knownAddress(g->getPointerOperand(),p);
        if(base[0].bits.kind()==Expr::Kind::Integer) p[0].bits=base[0].bits;
        APInt offset(64,0);
        if(base[1].bits.kind()==Expr::Kind::Integer && g->accumulateConstantOffset(module.getDataLayout(),offset))
            p[1].bits=n((base[1].bits.bits().sext(64)+offset).trunc(offsetWidth).getZExtValue(),offsetWidth);
    }
    return p;
}
Pieces MemoryModel::constant(const Constant* c) const
{
    if(auto* i=dyn_cast<ConstantInt>(c)) return {{Expr::integer(ts::Type::word(i->getBitWidth()),i->getValue()),b(false)}};
    if(isa<PoisonValue>(c)) { Pieces out; for(auto w:valueWidths(c->getType())) out.push_back({n(0,w),b(true)}); return out; }
    need(!isa<UndefValue>(c),"Explicit undef memory values are unsupported");
    if(isa<ConstantPointerNull>(c)) return {{n(0,8),b(false)},{n(0,offsetWidth),b(false)},{n(0,8),b(false)}};
    if(auto* g=dyn_cast<GlobalVariable>(c)) return {{n(object(g).id,8),b(false)},{n(0,offsetWidth),b(false)},{n(0,8),b(false)}};
    if(auto* gepOp=dyn_cast<GEPOperator>(c)) {
        auto base=constant(cast<Constant>(gepOp->getPointerOperand())); std::vector<ValueExpr> indices;
        for(auto& index:gepOp->indices()) indices.push_back(constant(cast<Constant>(index.get())).at(0));
        return gep(*gepOp,base,indices);
    }
    if(auto* ce=dyn_cast<ConstantExpr>(c)) {
        need(ce->getOpcode()==Instruction::BitCast && ce->getType()->isPointerTy(),"Unsupported memory constant expression");
        return constant(cast<Constant>(ce->getOperand(0)));
    }
    Pieces out;
    if(isa<ConstantAggregateZero>(c)) { for(auto w:valueWidths(c->getType())) out.push_back({n(0,w),b(false)}); return out; }
    auto add=[&](Constant* x) { auto p=constant(x); out.insert(out.end(),p.begin(),p.end()); };
    if(auto* a=dyn_cast<ArrayType>(c->getType())) for(unsigned i=0;i<a->getNumElements();++i) add(c->getAggregateElement(i));
    else if(auto* s=dyn_cast<StructType>(c->getType())) for(unsigned i=0;i<s->getNumElements();++i) add(c->getAggregateElement(i));
    else throw ScalarError("Unsupported memory initializer");
    return out;
}
MemoryModel::Byte MemoryModel::readByte(const Object& o,unsigned i) const
{
    auto& a=o.bytes.at(i); auto x=blank(); x.data=v(a[0]); x.initialized=v(a[1]); x.poison=v(a[2]);
    if(tags) { x.object=v(a[3]); x.offset=v(a[4]); x.generation=v(a[5]); x.fragment=v(a[6]); } return x;
}
MemoryModel::Byte MemoryModel::chooseByte(Expr c,const Byte& a,const Byte& d) const
{
    return {sel(c,a.data,d.data),sel(c,a.initialized,d.initialized),sel(c,a.poison,d.poison),
        sel(c,a.object,d.object),sel(c,a.offset,d.offset),sel(c,a.generation,d.generation),sel(c,a.fragment,d.fragment)};
}
Expr MemoryModel::identity(const Pieces& p,const Object& o,bool live) const
{
    auto match=eq(p[0].bits,n(o.id,8));
    match=all(match,eq(p[2].bits,v(o.generation)));
    return live ? all(match,v(o.live)) : match;
}
Expr MemoryModel::extent(const Object& o) const { return o.dynamic ? v(o.extent) : n(o.size,offsetWidth); }
Expr MemoryModel::valid(const Pieces& p,Expr count,uint64_t align,bool writing) const
{
    Expr ok=b(false);
    for(auto& o:objects) {
        if((writing && !o.writable) || align>o.alignment) continue;
        Expr inside=b(false);
        if(!o.dynamic && count.kind()==Expr::Kind::Integer) {
            if(count.bits().ule(o.size)) inside=op(Op::LessEqual,p[1].bits,n(o.size-count.bits().getZExtValue(),offsetWidth));
        } else if(count.kind()==Expr::Kind::Integer) {
            if(count.bits().ule(o.size)) inside=all(op(Op::LessEqual,p[1].bits,extent(o)),op(Op::LessEqual,cast(count,offsetWidth),op(Op::Sub,extent(o),p[1].bits)));
        } else inside=all(op(Op::LessEqual,p[1].bits,extent(o)),op(Op::LessEqual,count,cast(op(Op::Sub,extent(o),p[1].bits),64)));
        auto aligned=eq(op(Op::BitAnd,p[1].bits,n(align-1,offsetWidth)),n(0,offsetWidth));
        ok=any(ok,all(identity(p,o,true),all(inside,aligned)));
    }
    return all(no(poison(p)),ok);
}
Expr MemoryModel::inRange(const Pieces& p) const
{
    Expr ok=all(eq(p[0].bits,n(0,8)),all(eq(p[1].bits,n(0,offsetWidth)),eq(p[2].bits,n(0,8))));
    for(auto& o:objects) ok=any(ok,all(eq(p[0].bits,n(o.id,8)),op(Op::LessEqual,p[1].bits,extent(o))));
    return ok;
}
Expr MemoryModel::unknownExtent(const Pieces& p) const
{
    // Reallocation can change a dynamic object's size. Do not use the new
    // extent to decide inbounds/comparison semantics for an older generation.
    Expr unknown=b(false);
    for(auto& o:objects) if(o.dynamic)
        unknown=any(unknown,all(eq(p[0].bits,n(o.id,8)),no(eq(p[2].bits,v(o.generation)))));
    return all(no(poison(p)),unknown);
}
MemoryModel::Byte MemoryModel::readAt(const Pieces& p,Expr index) const
{
    auto result=blank();
    // Address cases are disjoint. OR masked fields instead of building a deep
    // conditional chain; the latter explodes in the backend's decision diagrams.
    for(auto& o:objects) for(unsigned i=0;i<o.size;++i) {
        auto item=chooseByte(all(eq(p[0].bits,n(o.id,8)),eq(index,n(i,offsetWidth))),readByte(o,i),blank());
        result={op(Op::BitOr,result.data,item.data),op(Op::BitOr,result.initialized,item.initialized),
            op(Op::BitOr,result.poison,item.poison),op(Op::BitOr,result.object,item.object),
            op(Op::BitOr,result.offset,item.offset),op(Op::BitOr,result.generation,item.generation),
            op(Op::BitOr,result.fragment,item.fragment)};
    }
    return result;
}
void MemoryModel::writeByte(MemoryEffect& e,const Object& o,unsigned index,const Byte& x) const
{
    std::vector<Expr> fields{x.data,x.initialized,x.poison};
    if(tags) fields.insert(fields.end(),{x.object,x.offset,x.generation,x.fragment});
    for(unsigned j=0;j<fields.size();++j) {
        if(fields[j].kind()==Expr::Kind::Variable && fields[j].symbol()==o.bytes[index][j]) continue;
        e.writes.push_back({o.bytes[index][j],fields[j]});
    }
}
void MemoryModel::encodeInto(llvm::Type* t,const Pieces& values,unsigned& at,std::vector<Byte>& bytes,unsigned start) const
{
    if(t->isIntegerTy()) {
        auto value=values.at(at++); unsigned w=t->getIntegerBitWidth();
        for(unsigned j=0;j<(w+7)/8;++j) {
            auto& x=bytes.at(start+j); unsigned mask=(1u<<std::min(8u,w-8*j))-1;
            x.data=cast(j ? op(Op::ShiftRight,value.bits,n(8*j,w)) : value.bits,8);
            x.initialized=n(mask,8); x.poison=sel(value.poison,n(mask,8),n(0,8));
        }
    } else if(t->isPointerTy()) {
        auto p=Pieces(values.begin()+at,values.begin()+at+3); at+=3;
        for(unsigned j=0;j<8;++j) {
            auto& x=bytes.at(start+j); x.initialized=n(255,8); x.poison=sel(poison(p),n(255,8),n(0,8));
            x.object=p[0].bits; x.offset=p[1].bits; x.generation=p[2].bits;
            auto null=all(eq(p[0].bits,n(0,8)),all(eq(p[1].bits,n(0,offsetWidth)),eq(p[2].bits,n(0,8))));
            x.fragment=sel(null,n(0,8),n(j+1,8));
        }
    } else if(auto* a=dyn_cast<ArrayType>(t)) {
        for(unsigned j=0;j<a->getNumElements();++j) encodeInto(a->getElementType(),values,at,bytes,start+j*size(a->getElementType()));
    } else {
        auto* s=cast<StructType>(t); auto* layout=module.getDataLayout().getStructLayout(s);
        for(unsigned j=0;j<s->getNumElements();++j) encodeInto(s->getElementType(j),values,at,bytes,start+layout->getElementOffset(j));
    }
}
std::vector<MemoryModel::Byte> MemoryModel::encode(llvm::Type* t,const Pieces& p) const
{ std::vector<Byte> out(size(t),blank()); unsigned at=0; encodeInto(t,p,at,out,0); return out; }
void MemoryModel::decodeFrom(llvm::Type* t,const std::vector<Byte>& bytes,unsigned start,Pieces& out,Expr& error,Expr& unsupported) const
{
    if(t->isIntegerTy()) {
        unsigned w=t->getIntegerBitWidth(); Expr value=n(0,w),p=b(false),opaque=b(false);
        for(unsigned j=0;j<(w+7)/8;++j) {
            auto& x=bytes.at(start+j); auto mask=n((1u<<std::min(8u,w-8*j))-1,8);
            error=any(error,no(eq(op(Op::BitAnd,x.initialized,mask),mask)));
            p=any(p,no(eq(op(Op::BitAnd,x.poison,mask),n(0,8))));
            opaque=any(opaque,no(eq(x.fragment,n(0,8))));
            auto part=cast(x.data,w); if(j) part=op(Op::ShiftLeft,part,n(j*8,w)); value=op(Op::BitOr,value,part);
        }
        unsupported=any(unsupported,all(opaque,no(p)));
        out.push_back({value,p});
    } else if(t->isPointerTy()) {
        auto& base=bytes.at(start); Expr matching=b(true),zero=b(true),p=b(false);
        for(unsigned j=0;j<8;++j) {
            auto& x=bytes.at(start+j); error=any(error,no(eq(x.initialized,n(255,8)))); p=any(p,no(eq(x.poison,n(0,8))));
            matching=all(matching,all(eq(x.fragment,n(j+1,8)),all(eq(x.object,base.object),all(eq(x.offset,base.offset),eq(x.generation,base.generation)))));
            zero=all(zero,all(eq(x.fragment,n(0,8)),eq(x.data,n(0,8))));
        }
        p=any(p,no(any(matching,zero)));
        out.insert(out.end(),{{sel(zero,n(0,8),base.object),p},{sel(zero,n(0,offsetWidth),base.offset),p},{sel(zero,n(0,8),base.generation),p}});
    } else if(auto* a=dyn_cast<ArrayType>(t)) {
        for(unsigned j=0;j<a->getNumElements();++j) decodeFrom(a->getElementType(),bytes,start+j*size(a->getElementType()),out,error,unsupported);
    } else {
        auto* s=cast<StructType>(t); auto* layout=module.getDataLayout().getStructLayout(s);
        for(unsigned j=0;j<s->getNumElements();++j) decodeFrom(s->getElementType(j),bytes,start+layout->getElementOffset(j),out,error,unsupported);
    }
}
Pieces MemoryModel::decode(llvm::Type* t,const std::vector<Byte>& bytes,Expr& error,Expr& unsupported) const
{ Pieces out; decodeFrom(t,bytes,0,out,error,unsupported); return out; }
MemoryEffect MemoryModel::load(const Pieces& ptr,llvm::Type* t,Align align) const
{
    MemoryEffect e; unsigned count=module.getDataLayout().getTypeStoreSize(t).getFixedValue();
    need(count>0,"Zero-sized typed accesses are unsupported");
    e.error=no(valid(ptr,n(count),align.value(),false)); std::vector<Byte> bytes;
    for(unsigned j=0;j<count;++j) bytes.push_back(readAt(ptr,op(Op::Add,ptr[1].bits,n(j,offsetWidth))));
    e.value=decode(t,bytes,e.error,e.unsupported); return e;
}
MemoryEffect MemoryModel::store(const Pieces& ptr,llvm::Type* t,const Pieces& value,Align align) const
{
    MemoryEffect e; auto bytes=encode(t,value); unsigned count=module.getDataLayout().getTypeStoreSize(t).getFixedValue();
    need(count>0,"Zero-sized typed accesses are unsupported");
    e.error=no(valid(ptr,n(count),align.value(),true));
    for(auto& o:objects) for(unsigned j=0;j<o.size;++j) {
        auto x=readByte(o,j);
        for(unsigned k=0;k<count && k<=j;++k) x=chooseByte(all(eq(ptr[0].bits,n(o.id,8)),eq(ptr[1].bits,n(j-k,offsetWidth))),bytes[k],x);
        writeByte(e,o,j,x);
    }
    return e;
}
MemoryEffect MemoryModel::allocate(const AllocaInst& a,ValueExpr count)
{
    auto& o=object(&a); MemoryEffect e; auto generation=op(Op::Add,v(o.generation),n(1,8));
    e.bound=op(Op::GreaterEqual,v(o.generation),n(limits.generations,8));
    e.capacity=v(o.allocated);
    if(o.dynamic) {
        unsigned stride=size(a.getAllocatedType()); need(stride>0,"Zero-sized dynamic allocation elements are unsupported");
        e.error=count.poison;
        e.unsupported=eq(count.bits,n(0,count.bits.type().width()));
        e.capacity=any(e.capacity,op(Op::Greater,cast(count.bits,64),n(o.size/stride)));
        e.writes.push_back({o.extent,op(Op::Mul,cast(count.bits,offsetWidth),n(stride,offsetWidth))});
    }
    e.value={{n(o.id,8),b(false)},{n(0,offsetWidth),b(false)},{generation,b(false)}};
    bool lifetimeMarked=false;
    for(auto* user:a.users()) if(auto* intrinsic=dyn_cast<IntrinsicInst>(user))
        lifetimeMarked |= intrinsic->getIntrinsicID()==Intrinsic::lifetime_start;
    e.writes.insert(e.writes.end(),{{o.live,b(!lifetimeMarked)},{o.generation,generation},{o.allocated,b(true)}});
    for(unsigned j=0;j<o.size;++j) writeByte(e,o,j,blank());
    return e;
}
MemoryEffect MemoryModel::endFrame(unsigned frame) const
{
    MemoryEffect e;
    for(auto& o:objects) if(o.stack && o.frame==frame) {
        e.writes.push_back({o.live,b(false)}); e.writes.push_back({o.allocated,b(false)});
    }
    return e;
}
MemoryEffect MemoryModel::saveStack(const CallInst& call) const
{
    MemoryEffect e; e.value={{n(0,8),b(false)},{n(0,offsetWidth),b(false)},{n(0,8),b(false)}};
    for(auto [id,saved]:saves.at(&call)) e.writes.push_back({saved,v(objects.at(id-1).generation)});
    return e;
}
MemoryEffect MemoryModel::restoreStack(const CallInst& call) const
{
    auto* saved=dyn_cast<CallInst>(call.getArgOperand(0));
    need(saved && saves.count(saved),"Stack restore requires a directly retained stacksave token");
    MemoryEffect e;
    for(auto [id,generation]:saves.at(saved)) {
        auto& o=objects.at(id-1); auto keep=eq(v(o.generation),v(generation));
        e.writes.push_back({o.live,all(v(o.live),keep)});
        e.writes.push_back({o.allocated,all(v(o.allocated),keep)});
    }
    return e;
}
MemoryEffect MemoryModel::lifetime(const Pieces& ptr,bool start) const
{
    MemoryEffect e; Expr found=b(false);
    for(auto& o:objects) if(o.stack) {
        auto matches=all(v(o.allocated),all(identity(ptr,o,false),eq(ptr[1].bits,n(0,offsetWidth)))); found=any(found,matches);
        e.writes.push_back({o.live,sel(matches,b(start),v(o.live))});
        if(start) for(unsigned j=0;j<o.size;++j) writeByte(e,o,j,chooseByte(matches,blank(),readByte(o,j)));
    }
    e.error=any(poison(ptr),no(found)); return e;
}
MemoryEffect MemoryModel::transfer(const Pieces& dest,const Pieces& src,ValueExpr length,bool move,const ValueExpr* fill,uint64_t destAlign,uint64_t srcAlign) const
{
    MemoryEffect e; auto count=cast(length.bits,64),nonzero=no(eq(count,n(0)));
    auto ok=valid(dest,count,destAlign,true); if(!fill) ok=all(ok,valid(src,count,srcAlign,false));
    if(!fill && !move) {
        auto same=all(eq(dest[0].bits,src[0].bits),eq(dest[2].bits,src[2].bits));
        auto overlap=all(op(Op::Less,dest[1].bits,op(Op::Add,src[1].bits,cast(count,offsetWidth))),op(Op::Less,src[1].bits,op(Op::Add,dest[1].bits,cast(count,offsetWidth))));
        ok=all(ok,no(all(same,all(no(eq(dest[1].bits,src[1].bits)),overlap))));
    }
    e.error=any(length.poison,all(nonzero,no(ok)));
    for(auto& o:objects) for(unsigned j=0;j<o.size;++j) {
        auto delta=op(Op::Sub,n(j,offsetWidth),dest[1].bits);
        auto inside=all(eq(dest[0].bits,n(o.id,8)),all(op(Op::LessEqual,dest[1].bits,n(j,offsetWidth)),op(Op::Less,cast(delta,64),count)));
        auto x=blank();
        if(fill) { x.data=cast(fill->bits,8); x.initialized=n(255,8); x.poison=sel(fill->poison,n(255,8),n(0,8)); }
        else x=readAt(src,op(Op::Add,src[1].bits,delta));
        writeByte(e,o,j,chooseByte(inside,x,readByte(o,j)));
    }
    return e;
}
Pieces MemoryModel::gep(const GEPOperator& g,const Pieces& base,const std::vector<ValueExpr>& indices,Expr* unsupported) const
{
    need(!g.getInRangeIndex(),"GEP inrange restrictions are unsupported");
    // Bound the mathematical intermediate width from index widths and ABI
    // strides. This preserves 64-bit wrap/overflow when it is possible while
    // avoiding wide arithmetic for, e.g., a zero-extended Boolean array index.
    APInt magnitude(128,1); magnitude <<= offsetWidth-1;
    auto* layoutType=g.getSourceElementType();
    for(unsigned j=0;j<indices.size();++j) {
        if(j && isa<StructType>(layoutType)) {
            auto* s=cast<StructType>(layoutType); unsigned field=cast<ConstantInt>(g.getOperand(j+1))->getZExtValue();
            magnitude+=module.getDataLayout().getStructLayout(s)->getElementOffset(field); layoutType=s->getElementType(field);
        } else {
            if(j) layoutType=cast<ArrayType>(layoutType)->getElementType();
            auto index=indices[j].bits;
            APInt term=index.kind()==Expr::Kind::Integer ? index.bits().sext(128).abs() : APInt::getOneBitSet(128,index.type().width()-1);
            magnitude+=term*module.getDataLayout().getTypeAllocSize(layoutType).getFixedValue();
        }
        if(magnitude.getActiveBits()>=64) break; // Saturate before the 128-bit bound could overflow.
    }
    unsigned mathWidth=std::min(64u,magnitude.getActiveBits()+1);
    auto p=base; Expr bad=poison(base); llvm::Type* t=g.getSourceElementType();
    if(g.isInBounds()) bad=any(bad,no(inRange(p)));
    p[1].bits=cast(cast(p[1].bits,offsetWidth,true),mathWidth);
    auto range64=[&](const Pieces& pointer) {
        auto narrow=pointer; narrow[1].bits=cast(pointer[1].bits,offsetWidth);
        auto representable=eq(pointer[1].bits,cast(cast(narrow[1].bits,offsetWidth,true),mathWidth));
        return all(representable,inRange(narrow));
    };
    for(unsigned j=0;j<indices.size();++j) {
        auto index=indices[j]; bad=any(bad,index.poison); Expr delta=n(0,mathWidth);
        if(j && isa<StructType>(t)) {
            auto* s=cast<StructType>(t); auto* c=cast<ConstantInt>(g.getOperand(j+1)); unsigned field=c->getZExtValue();
            delta=n(module.getDataLayout().getStructLayout(s)->getElementOffset(field),mathWidth); t=s->getElementType(field);
        } else {
            if(j) t=cast<ArrayType>(t)->getElementType();
            auto signedIndex=cast(cast(index.bits,index.bits.type().width(),true),mathWidth,true);
            auto stride=module.getDataLayout().getTypeAllocSize(t).getFixedValue();
            need(stride<=INT64_MAX,"GEP stride exceeds signed offset representation");
            delta=op(Op::Mul,cast(signedIndex,mathWidth),n(stride,mathWidth));
            if(g.isInBounds() && mathWidth==64 && stride>1) {
                auto lo=APInt::getSignedMinValue(mathWidth).sdiv(APInt(mathWidth,stride));
                auto hi=APInt::getSignedMaxValue(mathWidth).sdiv(APInt(mathWidth,stride));
                bad=any(bad,any(op(Op::Less,signedIndex,Expr::integer(ts::Type::word(mathWidth,true),lo)),op(Op::Greater,signedIndex,Expr::integer(ts::Type::word(mathWidth,true),hi))));
            }
        }
        auto sum=op(Op::Add,p[1].bits,delta);
        if(g.isInBounds() && mathWidth==64) {
            auto sign=[&](Expr x){ return op(Op::Less,cast(x,mathWidth,true),cast(n(0,mathWidth),mathWidth,true)); };
            bad=any(bad,all(eq(sign(p[1].bits),sign(delta)),no(eq(sign(sum),sign(p[1].bits)))));
        }
        p[1].bits=sum;
        if(g.isInBounds()) bad=any(bad,no(range64(p)));
    }
    auto narrow=cast(p[1].bits,offsetWidth);
    auto tooWide=all(no(bad),no(eq(p[1].bits,cast(cast(narrow,offsetWidth,true),mathWidth))));
    if(unsupported) *unsupported=any(tooWide,g.isInBounds() ? unknownExtent(base) : b(false));
    else need(tooWide.kind()==Expr::Kind::Boolean && !tooWide.booleanValue(),"Constant pointer displacement exceeds supported offset range");
    p[1].bits=narrow;
    for(auto& x:p) x.poison=bad;
    return p;
}
ValueExpr MemoryModel::compare(CmpInst::Predicate predicate,const Pieces& a,const Pieces& d,Expr& unsupported) const
{
    auto same=all(eq(a[0].bits,d[0].bits),eq(a[2].bits,d[2].bits)); Expr result=b(false);
    if(predicate==CmpInst::ICMP_EQ || predicate==CmpInst::ICMP_NE) {
        auto isNull=[&](const Pieces& p) { return all(eq(p[0].bits,n(0,8)),all(eq(p[1].bits,n(0,offsetWidth)),eq(p[2].bits,n(0,8)))); };
        auto cross=all(all(no(isNull(a)),no(isNull(d))),no(same));
        auto nullOutside=any(all(isNull(a),no(inRange(d))),all(isNull(d),no(inRange(a))));
        unsupported=all(no(any(poison(a),poison(d))),any(cross,nullOutside));
        result=all(same,eq(a[1].bits,d[1].bits)); if(predicate==CmpInst::ICMP_NE) result=no(result);
    } else {
        unsupported=all(no(any(poison(a),poison(d))),no(all(same,all(inRange(a),inRange(d)))));
        Op operation=predicate==CmpInst::ICMP_ULT ? Op::Less : predicate==CmpInst::ICMP_ULE ? Op::LessEqual : predicate==CmpInst::ICMP_UGT ? Op::Greater : Op::GreaterEqual;
        result=op(operation,cast(a[1].bits,offsetWidth,true),cast(d[1].bits,offsetWidth,true));
    }
    unsupported=any(unsupported,any(unknownExtent(a),unknownExtent(d)));
    return {sel(result,n(1,1),n(0,1)),any(poison(a),poison(d))};
}
json::Object MemoryModel::describe() const
{
    json::Array list;
    for(auto& o:objects) list.push_back(json::Object{{"id",o.id},{"name",o.source->getName().str()},{"bytes",o.size},
        {"alignment",o.alignment},{"stack",o.stack},{"frame",o.frame},{"dynamic",o.dynamic},{"writable",o.writable},{"key","memory."+std::to_string(o.id)}});
    return json::Object{{"policy","opaque-provenance-bytes-v1; strict-uninitialized-read"},{"byte_budget",limits.bytes},{"offset_bits",offsetWidth},{"object_limit",255},
        {"dynamic_stack_bytes",limits.dynamicBytes},{"allocations_per_site_per_frame",1},{"allocation_generations",limits.generations},{"objects",std::move(list)}};
}
}
