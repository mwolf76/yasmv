#ifndef LLVM2SMV_EXPRTRANSLATOR_H
#define LLVM2SMV_EXPRTRANSLATOR_H

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include <map>
#include <memory>

namespace llvm2smv {

    class SMVExpr;
    class SMVModule;

    /// Translates LLVM values and instructions to SMV expressions
    class ExprTranslator {
    public:
        explicit ExprTranslator(SMVModule& Module)
            : Module(Module)
        {}

        /// Translate an LLVM value to SMV expression
        std::unique_ptr<SMVExpr> translateValue(llvm::Value* V);

        /// Translate an LLVM instruction to SMV expression(s)
        void translateInstruction(llvm::Instruction* I);

        /// Map SSA values to SMV variable names
        void mapValue(llvm::Value* V, const std::string& Name)
        {
            ValueMap[V] = Name;
        }

        /// Get the SMV name for an LLVM value
        std::string getValueName(llvm::Value* V);

    private:
        SMVModule& Module;
        std::map<llvm::Value*, std::string> ValueMap;
        unsigned TempCounter = 0;

        // Instruction translators
        std::unique_ptr<SMVExpr> translateBinaryOp(llvm::BinaryOperator* BO);
        std::unique_ptr<SMVExpr> translateICmp(llvm::ICmpInst* ICmp);
        std::unique_ptr<SMVExpr> translateSelect(llvm::SelectInst* SI);
        std::unique_ptr<SMVExpr> translatePHI(llvm::PHINode* PHI);
        std::unique_ptr<SMVExpr> translateLoad(llvm::LoadInst* LI);
        void translateStore(llvm::StoreInst* SI);

        // Constant translators
        std::unique_ptr<SMVExpr> translateConstant(llvm::Constant* C);

        // Helper to generate unique temporary names
        std::string genTempName();
    };

} // namespace llvm2smv

#endif // LLVM2SMV_EXPRTRANSLATOR_H
