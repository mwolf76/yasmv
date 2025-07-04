#include "llvm2smv/llvm2smv_pass.hh"
#include "llvm2smv/expr_translator.hh"
#include "llvm2smv/smv_writer.hh"
#include "llvm2smv/type_translator.hh"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace llvm2smv;

char LLVM2SMVPass::ID = 0;

bool LLVM2SMVPass::runOnModule(Module& M)
{
    if (!OS) {
        OS = &outs();
    }

    // For now, we'll translate the module as a single SMV module
    CurrentModule = std::make_unique<SMVModule>(M.getName());

    // First, translate global variables
    translateGlobalVariables(M);

    // Find the main function as entry point
    Function* MainFunc = M.getFunction("main");
    if (!MainFunc) {
        errs() << "Warning: No main function found\n";
        // Try to find any function
        for (Function& F : M) {
            if (!F.isDeclaration()) {
                MainFunc = &F;
                break;
            }
        }
    }

    // Translate functions
    for (Function& F : M) {
        if (!F.isDeclaration()) {
            translateFunction(F);
        }
    }

    // Write the SMV module
    CurrentModule->write(*OS);

    return false; // We don't modify the module
}

void LLVM2SMVPass::translateGlobalVariables(Module& M)
{
    TypeTranslator TT;

    for (GlobalVariable& GV : M.globals()) {
        // Skip external globals
        if (GV.isDeclaration()) continue;

        std::string Name = GV.getName().str();
        Type* Ty = GV.getValueType();

        auto SMVTy = TT.translateType(Ty);
        CurrentModule->addVariable(Name, std::move(SMVTy));

        // Handle initialization
        if (GV.hasInitializer()) {
            Constant* Init = GV.getInitializer();
            // TODO: Translate initializer to SMV expression
            // For now, just initialize to zero
            if (Init->isNullValue()) {
                CurrentModule->addInit(makeBinary("=",
                                                  makeVariable(Name),
                                                  makeConstant(int64_t(0))));
            }
        }
    }
}

void LLVM2SMVPass::translateFunction(Function& F)
{
    // Add program counter for this function
    std::vector<std::string> PCStates;
    PCStates.push_back("ENTRY_" + F.getName().str());

    // Collect all basic blocks
    for (BasicBlock& BB : F) {
        PCStates.push_back(BB.getName().str());
    }
    PCStates.push_back("EXIT_" + F.getName().str());

    auto PCType = std::make_unique<SMVEnumType>(PCStates);
    CurrentModule->addVariable("pc_" + F.getName().str(), std::move(PCType));

    // Initialize PC to entry
    CurrentModule->addInit(makeBinary("=",
                                      makeVariable("pc_" + F.getName().str()),
                                      makeVariable("ENTRY_" + F.getName().str())));

    // Create expression translator
    ExprTranslator ET(*CurrentModule);
    TypeTranslator TT;

    // Translate function arguments as variables
    for (Argument& Arg : F.args()) {
        std::string ArgName = Arg.getName().str();
        if (ArgName.empty()) {
            ArgName = "arg" + std::to_string(Arg.getArgNo());
        }

        auto ArgType = TT.translateType(Arg.getType());
        CurrentModule->addVariable(ArgName, std::move(ArgType));
        ET.mapValue(&Arg, ArgName);
    }

    // Translate each basic block
    for (BasicBlock& BB : F) {
        // Skip phi nodes initially - they'll be handled specially
        for (Instruction& I : BB) {
            if (isa<PHINode>(&I)) continue;

            // Map instruction to a variable name
            if (!I.getType()->isVoidTy()) {
                std::string InstName = I.getName().str();
                if (InstName.empty()) {
                    InstName = "tmp_" + std::to_string(reinterpret_cast<uintptr_t>(&I));
                }
                ET.mapValue(&I, InstName);

                // Add variable for this instruction
                auto InstType = TT.translateType(I.getType());
                CurrentModule->addVariable(InstName, std::move(InstType));
            }

            // Translate the instruction
            ET.translateInstruction(&I);
        }
    }

    // TODO: Add control flow transitions between basic blocks
    // For now, just add a simple transition to exit
    CurrentModule->addTrans(
        makeBinary("!=",
                   makeVariable("pc_" + F.getName().str()),
                   makeVariable("EXIT_" + F.getName().str())),
        makeBinary(":=",
                   makeVariable("pc_" + F.getName().str()),
                   makeVariable("EXIT_" + F.getName().str())));
}
