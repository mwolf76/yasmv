#include "llvm2smv/type_translator.hh"
#include "llvm2smv/smv_writer.hh"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace llvm2smv;

std::unique_ptr<SMVType> TypeTranslator::translateType(Type* Ty)
{
    if (auto* IntTy = dyn_cast<IntegerType>(Ty)) {
        return translateIntegerType(IntTy);
    }

    if (auto* ArrTy = dyn_cast<ArrayType>(Ty)) {
        return translateArrayType(ArrTy);
    }

    if (auto* PtrTy = dyn_cast<PointerType>(Ty)) {
        return translatePointerType(PtrTy);
    }

    if (auto* StructTy = dyn_cast<StructType>(Ty)) {
        return translateStructType(StructTy);
    }

    // Default: treat unknown types as integers
    errs() << "Warning: Unknown type, treating as uint" << DefaultIntWidth << "\n";
    return std::make_unique<SMVIntegerType>(DefaultIntWidth, false);
}

std::unique_ptr<SMVType> TypeTranslator::translateIntegerType(IntegerType* IntTy)
{
    unsigned BitWidth = IntTy->getBitWidth();

    // Special case for i1 (boolean)
    if (BitWidth == 1) {
        return std::make_unique<SMVBooleanType>();
    }

    // For now, assume unsigned integers
    // TODO: Add heuristics or metadata to determine signedness
    return std::make_unique<SMVIntegerType>(BitWidth, false);
}

std::unique_ptr<SMVType> TypeTranslator::translateArrayType(ArrayType* ArrTy)
{
    uint64_t NumElements = ArrTy->getNumElements();
    auto ElementType = translateType(ArrTy->getElementType());

    return std::make_unique<SMVArrayType>(std::move(ElementType), NumElements);
}

std::unique_ptr<SMVType> TypeTranslator::translatePointerType(PointerType* PtrTy)
{
    // For now, treat pointers as integers (addresses)
    // This is a simplification - real implementation would need memory modeling
    return std::make_unique<SMVIntegerType>(DefaultIntWidth, false);
}

std::unique_ptr<SMVType> TypeTranslator::translateStructType(StructType* StructTy)
{
    // For now, we don't support structs directly
    // Would need to flatten or create separate variables for each field
    errs() << "Warning: Struct types not yet supported, using integer\n";
    return std::make_unique<SMVIntegerType>(DefaultIntWidth, false);
}
