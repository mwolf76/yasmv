#ifndef LLVM2SMV_TYPETRANSLATOR_H
#define LLVM2SMV_TYPETRANSLATOR_H

#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Type.h"
#include <memory>

namespace llvm2smv {

    class SMVType;

    /// Translates LLVM types to SMV types
    class TypeTranslator {
    public:
        TypeTranslator(unsigned DefaultIntWidth = 32)
            : DefaultIntWidth(DefaultIntWidth)
        {}

        /// Translate an LLVM type to SMV type
        std::unique_ptr<SMVType> translateType(llvm::Type* Ty);

        /// Set the default integer width for unbounded integers
        void setDefaultIntWidth(unsigned Width)
        {
            DefaultIntWidth = Width;
        }

    private:
        unsigned DefaultIntWidth;

        std::unique_ptr<SMVType> translateIntegerType(llvm::IntegerType* IntTy);
        std::unique_ptr<SMVType> translateArrayType(llvm::ArrayType* ArrTy);
        std::unique_ptr<SMVType> translatePointerType(llvm::PointerType* PtrTy);
        std::unique_ptr<SMVType> translateStructType(llvm::StructType* StructTy);
    };

} // namespace llvm2smv

#endif // LLVM2SMV_TYPETRANSLATOR_H
