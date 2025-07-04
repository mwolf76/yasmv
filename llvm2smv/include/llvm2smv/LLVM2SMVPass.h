#ifndef LLVM2SMV_PASS_H
#define LLVM2SMV_PASS_H

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "SMVWriter.h"
#include <memory>

namespace llvm2smv {

    /// Main LLVM pass that converts LLVM IR to SMV
    class LLVM2SMVPass: public llvm::ModulePass {
    public:
        static char ID;

        LLVM2SMVPass()
            : ModulePass(ID)
            , OS(nullptr)
        {}
        explicit LLVM2SMVPass(llvm::raw_ostream& OS)
            : ModulePass(ID)
            , OS(&OS)
        {}

        bool runOnModule(llvm::Module& M) override;

        void getAnalysisUsage(llvm::AnalysisUsage& AU) const override
        {
            AU.setPreservesAll();
        }

    private:
        llvm::raw_ostream* OS;
        std::unique_ptr<SMVModule> CurrentModule;

        void translateFunction(llvm::Function& F);
        void translateGlobalVariables(llvm::Module& M);
    };

} // namespace llvm2smv

#endif // LLVM2SMV_PASS_H
