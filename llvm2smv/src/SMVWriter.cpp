#include "llvm2smv/SMVWriter.h"
#include <algorithm>

using namespace llvm;
using namespace llvm2smv;

// SMVIntegerType implementation
void SMVIntegerType::print(raw_ostream& OS) const
{
    if (IsSigned) {
        OS << "int";
    } else {
        OS << "uint";
    }
    if (Width != 32) { // Only print width if not default
        OS << Width;
    }
}

// SMVEnumType implementation
void SMVEnumType::print(raw_ostream& OS) const
{
    OS << "{ ";
    for (size_t i = 0; i < Values.size(); ++i) {
        if (i > 0) OS << ", ";
        OS << Values[i];
    }
    OS << " }";
}

// SMVArrayType implementation
void SMVArrayType::print(raw_ostream& OS) const
{
    ElementType->print(OS);
    OS << "[" << Size << "]";
}

// SMVModule implementation
void SMVModule::addVariable(StringRef Name, std::unique_ptr<SMVType> Type)
{
    Variables.push_back(std::make_unique<SMVVariable>(Name, std::move(Type)));
}

void SMVModule::addVariable(std::unique_ptr<SMVVariable> Var)
{
    Variables.push_back(std::move(Var));
}

void SMVModule::addInit(std::unique_ptr<SMVExpr> Expr)
{
    InitConstraints.push_back(std::move(Expr));
}

void SMVModule::addTrans(std::unique_ptr<SMVExpr> Expr)
{
    TransConstraints.push_back(std::move(Expr));
}

void SMVModule::addTrans(std::unique_ptr<SMVExpr> Guard,
                         std::unique_ptr<SMVExpr> Assignment)
{
    auto GuardedTrans = makeGuardedTrans(std::move(Guard), std::move(Assignment));
    TransConstraints.push_back(std::move(GuardedTrans));
}

void SMVModule::addInvar(std::unique_ptr<SMVExpr> Expr)
{
    InvarConstraints.push_back(std::move(Expr));
}

void SMVModule::addDefine(StringRef Name, std::unique_ptr<SMVExpr> Expr)
{
    Defines[Name.str()] = std::move(Expr);
}

void SMVModule::write(raw_ostream& OS) const
{
    OS << "MODULE " << Name << "\n\n";

    // Write variables
    if (!Variables.empty()) {
        // Group variables by modifiers
        std::map<std::string, std::vector<const SMVVariable*>> GroupedVars;

        for (const auto& Var : Variables) {
            std::string ModifierKey;
            for (const auto& Mod : Var->Modifiers) {
                if (!ModifierKey.empty()) ModifierKey += " ";
                ModifierKey += Mod;
            }
            GroupedVars[ModifierKey].push_back(Var.get());
        }

        // Write each group (C++20 structured bindings)
        for (const auto& [modifier, vars] : GroupedVars) {
            if (!modifier.empty()) {
                OS << modifier << "\n";
            }
            OS << "VAR\n";
            for (const auto* var : vars) {
                OS << "    " << var->Name << " : ";
                var->Type->print(OS);
                OS << ";\n";
            }
            OS << "\n";
        }
    }

    // Write defines (C++20 structured bindings)
    if (!Defines.empty()) {
        OS << "DEFINE\n";
        for (const auto& [name, expr] : Defines) {
            OS << "    " << name << " := ";
            expr->print(OS);
            OS << ";\n";
        }
        OS << "\n";
    }

    // Write init constraints
    if (!InitConstraints.empty()) {
        OS << "INIT\n    ";
        for (size_t i = 0; i < InitConstraints.size(); ++i) {
            if (i > 0) OS << " &&\n    ";
            InitConstraints[i]->print(OS);
        }
        OS << ";\n\n";
    }

    // Write invariants
    for (const auto& Invar : InvarConstraints) {
        OS << "INVAR\n    ";
        Invar->print(OS);
        OS << ";\n\n";
    }

    // Write transitions
    for (const auto& Trans : TransConstraints) {
        OS << "TRANS\n    ";
        Trans->print(OS);
        OS << ";\n\n";
    }
}

// Expression implementations
class ConstantExpr: public SMVExpr {
    int64_t Value;
    bool IsBool;

public:
    ConstantExpr(int64_t Value)
        : Value(Value)
        , IsBool(false)
    {}
    ConstantExpr(bool Value)
        : Value(Value)
        , IsBool(true)
    {}

    ExprKind getKind() const override
    {
        return EK_Constant;
    }

    void print(raw_ostream& OS) const override
    {
        if (IsBool) {
            OS << (Value ? "TRUE" : "FALSE");
        } else {
            OS << Value;
        }
    }

    std::unique_ptr<SMVExpr> clone() const override
    {
        if (IsBool) {
            return std::make_unique<ConstantExpr>(static_cast<bool>(Value));
        }
        return std::make_unique<ConstantExpr>(Value);
    }
};

class VariableExpr: public SMVExpr {
    std::string Name;

public:
    explicit VariableExpr(StringRef Name)
        : Name(Name)
    {}

    ExprKind getKind() const override
    {
        return EK_Variable;
    }

    void print(raw_ostream& OS) const override
    {
        OS << Name;
    }

    std::unique_ptr<SMVExpr> clone() const override
    {
        return std::make_unique<VariableExpr>(Name);
    }
};

class NextExpr: public SMVExpr {
    std::unique_ptr<SMVExpr> Expr;

public:
    explicit NextExpr(std::unique_ptr<SMVExpr> Expr)
        : Expr(std::move(Expr))
    {}

    ExprKind getKind() const override
    {
        return EK_Next;
    }

    void print(raw_ostream& OS) const override
    {
        OS << "next(";
        Expr->print(OS);
        OS << ")";
    }

    std::unique_ptr<SMVExpr> clone() const override
    {
        return std::make_unique<NextExpr>(Expr->clone());
    }
};

class BinaryExpr: public SMVExpr {
    std::string Op;
    std::unique_ptr<SMVExpr> LHS, RHS;

public:
    BinaryExpr(StringRef Op, std::unique_ptr<SMVExpr> LHS,
               std::unique_ptr<SMVExpr> RHS)
        : Op(Op)
        , LHS(std::move(LHS))
        , RHS(std::move(RHS))
    {}

    ExprKind getKind() const override
    {
        return EK_Binary;
    }

    void print(raw_ostream& OS) const override
    {
        bool NeedParens = (Op != "=" && Op != ":=" && Op != "&&" && Op != "||");
        if (NeedParens) OS << "(";
        LHS->print(OS);
        OS << " " << Op << " ";
        RHS->print(OS);
        if (NeedParens) OS << ")";
    }

    std::unique_ptr<SMVExpr> clone() const override
    {
        return std::make_unique<BinaryExpr>(Op, LHS->clone(), RHS->clone());
    }
};

class GuardedTransExpr: public SMVExpr {
    std::unique_ptr<SMVExpr> Guard;
    std::unique_ptr<SMVExpr> Assignment;

public:
    GuardedTransExpr(std::unique_ptr<SMVExpr> Guard,
                     std::unique_ptr<SMVExpr> Assignment)
        : Guard(std::move(Guard))
        , Assignment(std::move(Assignment))
    {}

    ExprKind getKind() const override
    {
        return EK_GuardedTrans;
    }

    void print(raw_ostream& OS) const override
    {
        Guard->print(OS);
        OS << " ?:\n        ";
        Assignment->print(OS);
    }

    std::unique_ptr<SMVExpr> clone() const override
    {
        return std::make_unique<GuardedTransExpr>(Guard->clone(),
                                                  Assignment->clone());
    }
};

// Factory functions
std::unique_ptr<SMVExpr> llvm2smv::makeConstant(int64_t Value)
{
    return std::make_unique<ConstantExpr>(Value);
}

std::unique_ptr<SMVExpr> llvm2smv::makeConstant(bool Value)
{
    return std::make_unique<ConstantExpr>(Value);
}

std::unique_ptr<SMVExpr> llvm2smv::makeVariable(StringRef Name)
{
    return std::make_unique<VariableExpr>(Name);
}

std::unique_ptr<SMVExpr> llvm2smv::makeNext(std::unique_ptr<SMVExpr> Expr)
{
    return std::make_unique<NextExpr>(std::move(Expr));
}

std::unique_ptr<SMVExpr> llvm2smv::makeBinary(StringRef Op,
                                              std::unique_ptr<SMVExpr> LHS,
                                              std::unique_ptr<SMVExpr> RHS)
{
    return std::make_unique<BinaryExpr>(Op, std::move(LHS), std::move(RHS));
}

std::unique_ptr<SMVExpr> llvm2smv::makeGuardedTrans(std::unique_ptr<SMVExpr> Guard,
                                                    std::unique_ptr<SMVExpr> Assignment)
{
    return std::make_unique<GuardedTransExpr>(std::move(Guard),
                                              std::move(Assignment));
}
