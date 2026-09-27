#ifndef LLVM2SMV_MEMORY_MODEL_HH
#define LLVM2SMV_MEMORY_MODEL_HH
#include "llvm2smv/transition_system.hh"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/JSON.h"

namespace llvm2smv {
struct ValueExpr { ts::Expr bits, poison; };
using Pieces = std::vector<ValueExpr>;
struct MemoryLimits { unsigned bytes = 128, generations = 4, stackDepth = 8, dynamicBytes = 16; };
struct MemoryEffect {
    Pieces value;
    std::vector<ts::Write> writes;
    ts::Expr error = ts::Expr::boolean(false);
    ts::Expr unsupported = ts::Expr::boolean(false);
    ts::Expr bound = ts::Expr::boolean(false);
    ts::Expr capacity = ts::Expr::boolean(false);
};
// Opaque pointers are three words (object, signed byte offset, allocation generation).
// Offset storage covers the byte budget; larger defined GEP displacements are
// reported as unsupported, never silently truncated into a usable address.
// Storage uses canonical bytes, initialized/poison bit masks, and copyable pointer tags.
class MemoryModel {
public:
    MemoryModel(ts::Model&, llvm::Module&, llvm::Function&, MemoryLimits, const std::map<const llvm::Instruction*,unsigned>&);
    static std::vector<unsigned> widths(llvm::Type*, unsigned offsetWidth = 64);
    std::vector<unsigned> valueWidths(llvm::Type* t) const { return widths(t,offsetWidth); }
    static unsigned fieldIndex(llvm::Type*, llvm::ArrayRef<unsigned>);
    Pieces knownAddress(const llvm::Value*, Pieces) const;
    Pieces constant(const llvm::Constant*) const;
    Pieces gep(const llvm::GEPOperator&, const Pieces&, const std::vector<ValueExpr>&, ts::Expr* unsupported = nullptr) const;
    ValueExpr compare(llvm::CmpInst::Predicate, const Pieces&, const Pieces&, ts::Expr& unsupported) const;
    MemoryEffect allocate(const llvm::AllocaInst&, ValueExpr count);
    MemoryEffect endFrame(unsigned) const;
    MemoryEffect saveStack(const llvm::CallInst&) const;
    MemoryEffect restoreStack(const llvm::CallInst&) const;
    MemoryEffect load(const Pieces&, llvm::Type*, llvm::Align) const;
    MemoryEffect store(const Pieces&, llvm::Type*, const Pieces&, llvm::Align) const;
    MemoryEffect lifetime(const Pieces&, bool start) const;
    MemoryEffect transfer(const Pieces& dest, const Pieces& src, ValueExpr length, bool move, const ValueExpr* fill, uint64_t destAlign = 1, uint64_t srcAlign = 1) const;
    llvm::json::Object describe() const;
private:
    struct Byte {
        ts::Expr data, initialized, poison, object, offset, generation, fragment;
    };
    struct Object {
        const llvm::Value* source;
        unsigned id, size, frame;
        bool dynamic;
        uint64_t alignment;
        bool writable, stack;
        ts::SymbolRef live, generation, allocated, extent;
        std::vector<std::vector<ts::SymbolRef>> bytes;
    };
    ts::Model& model;
    llvm::Module& module;
    MemoryLimits limits;
    bool tags = false;
    unsigned offsetWidth = 2;
    std::vector<Object> objects;
    std::map<const llvm::CallInst*,std::vector<std::pair<unsigned,ts::SymbolRef>>> saves;
    ts::Expr extent(const Object&) const;
    unsigned size(llvm::Type*) const;
    const Object& object(const llvm::Value*) const;
    Byte blank() const;
    Byte readByte(const Object&, unsigned) const;
    Byte chooseByte(ts::Expr, const Byte&, const Byte&) const;
    Byte readAt(const Pieces&, ts::Expr) const;
    void writeByte(MemoryEffect&, const Object&, unsigned, const Byte&) const;
    ts::Expr identity(const Pieces&, const Object&, bool live) const;
    ts::Expr valid(const Pieces&, ts::Expr count, uint64_t align, bool writing) const;
    ts::Expr inRange(const Pieces&) const;
    ts::Expr unknownExtent(const Pieces&) const;
    std::vector<Byte> encode(llvm::Type*, const Pieces&) const;
    Pieces decode(llvm::Type*, const std::vector<Byte>&, ts::Expr&, ts::Expr&) const;
    void encodeInto(llvm::Type*, const Pieces&, unsigned&, std::vector<Byte>&, unsigned) const;
    void decodeFrom(llvm::Type*, const std::vector<Byte>&, unsigned, Pieces&, ts::Expr&, ts::Expr&) const;
};
}
#endif
