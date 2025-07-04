#include "llvm2smv/expr_translator.hh"
#include "llvm2smv/smv_writer.hh"
#include "llvm/IR/Constants.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace llvm2smv;

std::unique_ptr<SMVExpr> ExprTranslator::translateValue(Value* V)
{
    // Check if it's a constant
    if (auto* C = dyn_cast<Constant>(V)) {
        return translateConstant(C);
    }

    // Otherwise, it should be mapped to a variable
    return makeVariable(getValueName(V));
}

std::string ExprTranslator::getValueName(Value* V)
{
    auto It = ValueMap.find(V);
    if (It != ValueMap.end()) {
        return It->second;
    }

    // Generate a name if not found
    if (V->hasName()) {
        return V->getName().str();
    }

    return genTempName();
}

std::string ExprTranslator::genTempName()
{
    return "tmp_" + std::to_string(TempCounter++);
}

void ExprTranslator::translateInstruction(Instruction* I)
{
    if (auto* BO = dyn_cast<BinaryOperator>(I)) {
        auto Expr = translateBinaryOp(BO);
        // Add assignment for this instruction
        Module.addTrans(makeBinary("=",
                                   makeNext(makeVariable(getValueName(I))),
                                   std::move(Expr)));
    } else if (auto* ICmp = dyn_cast<ICmpInst>(I)) {
        auto Expr = translateICmp(ICmp);
        Module.addTrans(makeBinary("=",
                                   makeNext(makeVariable(getValueName(I))),
                                   std::move(Expr)));
    } else if (auto* SI = dyn_cast<StoreInst>(I)) {
        translateStore(SI);
    } else if (auto* LI = dyn_cast<LoadInst>(I)) {
        auto Expr = translateLoad(LI);
        Module.addTrans(makeBinary("=",
                                   makeNext(makeVariable(getValueName(I))),
                                   std::move(Expr)));
    }
    // TODO: Add more instruction types
}

std::unique_ptr<SMVExpr> ExprTranslator::translateBinaryOp(BinaryOperator* BO)
{
    auto LHS = translateValue(BO->getOperand(0));
    auto RHS = translateValue(BO->getOperand(1));

    StringRef Op;
    switch (BO->getOpcode()) {
        case Instruction::Add:
            Op = "+";
            break;
        case Instruction::Sub:
            Op = "-";
            break;
        case Instruction::Mul:
            Op = "*";
            break;
        case Instruction::SDiv:
        case Instruction::UDiv:
            Op = "/";
            break;
        case Instruction::SRem:
        case Instruction::URem:
            Op = "%";
            break;
        case Instruction::And:
            Op = "&";
            break;
        case Instruction::Or:
            Op = "|";
            break;
        case Instruction::Xor:
            Op = "^";
            break;
        case Instruction::Shl:
            Op = "<<";
            break;
        case Instruction::LShr:
        case Instruction::AShr:
            Op = ">>";
            break;
        default:
            errs() << "Warning: Unknown binary operator\n";
            Op = "+";
    }

    return makeBinary(Op, std::move(LHS), std::move(RHS));
}

std::unique_ptr<SMVExpr> ExprTranslator::translateICmp(ICmpInst* ICmp)
{
    auto LHS = translateValue(ICmp->getOperand(0));
    auto RHS = translateValue(ICmp->getOperand(1));

    StringRef Op;
    switch (ICmp->getPredicate()) {
        case ICmpInst::ICMP_EQ:
            Op = "=";
            break;
        case ICmpInst::ICMP_NE:
            Op = "!=";
            break;
        case ICmpInst::ICMP_UGT:
        case ICmpInst::ICMP_SGT:
            Op = ">";
            break;
        case ICmpInst::ICMP_UGE:
        case ICmpInst::ICMP_SGE:
            Op = ">=";
            break;
        case ICmpInst::ICMP_ULT:
        case ICmpInst::ICMP_SLT:
            Op = "<";
            break;
        case ICmpInst::ICMP_ULE:
        case ICmpInst::ICMP_SLE:
            Op = "<=";
            break;
        default:
            errs() << "Warning: Unknown comparison predicate\n";
            Op = "=";
    }

    return makeBinary(Op, std::move(LHS), std::move(RHS));
}

std::unique_ptr<SMVExpr> ExprTranslator::translateLoad(LoadInst* LI)
{
    // For now, just load from the pointer variable
    // In a real implementation, we'd need memory modeling
    return translateValue(LI->getPointerOperand());
}

void ExprTranslator::translateStore(StoreInst* SI)
{
    auto Value = translateValue(SI->getValueOperand());
    auto Ptr = SI->getPointerOperand();

    // For now, treat store as assignment to the pointed variable
    Module.addTrans(makeBinary("=",
                               makeNext(makeVariable(getValueName(Ptr))),
                               std::move(Value)));
}

std::unique_ptr<SMVExpr> ExprTranslator::translateConstant(Constant* C)
{
    if (auto* CI = dyn_cast<ConstantInt>(C)) {
        if (CI->getBitWidth() == 1) {
            return makeConstant(CI->isOne());
        }
        return makeConstant(CI->getSExtValue());
    }

    if (isa<ConstantPointerNull>(C)) {
        return makeConstant(int64_t(0));
    }

    // Default
    errs() << "Warning: Unknown constant type\n";
    return makeConstant(int64_t(0));
}
