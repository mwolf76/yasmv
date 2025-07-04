#include "llvm2smv/llvm2smv_pass.hh"
#include "llvm2smv/expr_translator.hh"
#include "llvm2smv/smv_writer.hh"
#include "llvm2smv/type_translator.hh"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cctype>

using namespace llvm;
using namespace llvm2smv;

char LLVM2SMVPass::ID = 0;

bool LLVM2SMVPass::runOnModule(Module& M)
{
    if (!OS) {
        OS = &outs();
    }

    // For now, we'll translate the module as a single SMV module
    // Clean the module name to be a valid SMV identifier
    std::string CleanName = M.getName().str();
    if (CleanName.empty()) {
        CleanName = "main_module";
    }
    // Replace invalid characters with underscores
    std::replace_if(CleanName.begin(), CleanName.end(), [](char c) { return !std::isalnum(c); }, '_');
    CurrentModule = std::make_unique<SMVModule>(CleanName);

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
        auto Var = std::make_unique<SMVVariable>(Name, std::move(SMVTy));
        Var->Modifiers.push_back("#inertial");
        CurrentModule->addVariable(std::move(Var));

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

    // Collect all basic blocks, giving them names if they don't have any
    int bbCounter = 0;
    for (BasicBlock& BB : F) {
        std::string bbName = BB.getName().str();
        if (bbName.empty()) {
            bbName = "BB" + std::to_string(bbCounter++);
        }
        PCStates.push_back(bbName);
    }
    PCStates.push_back("EXIT_" + F.getName().str());

    auto PCType = std::make_unique<SMVEnumType>(PCStates);
    auto PCVar = std::make_unique<SMVVariable>("pc_" + F.getName().str(), std::move(PCType));
    PCVar->Modifiers.push_back("#inertial");
    CurrentModule->addVariable(std::move(PCVar));

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
        auto ArgVar = std::make_unique<SMVVariable>(ArgName, std::move(ArgType));
        ArgVar->Modifiers.push_back("#inertial");
        CurrentModule->addVariable(std::move(ArgVar));
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
                    static int tmpCounter = 0;
                    InstName = "tmp_" + std::to_string(tmpCounter++);
                }
                ET.mapValue(&I, InstName);

                // Add variable for this instruction
                auto InstType = TT.translateType(I.getType());
                auto InstVar = std::make_unique<SMVVariable>(InstName, std::move(InstType));
                InstVar->Modifiers.push_back("#inertial");
                CurrentModule->addVariable(std::move(InstVar));
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
