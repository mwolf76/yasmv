#ifndef LLVM2SMV_SMVWRITER_H
#define LLVM2SMV_SMVWRITER_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace llvm2smv {

    // Forward declarations
    class SMVExpr;
    class SMVType;

    /// Represents an SMV variable
    struct SMVVariable {
        std::string Name;
        std::unique_ptr<SMVType> Type;
        std::vector<std::string> Modifiers; // #hidden, #input, etc.

        SMVVariable(llvm::StringRef Name, std::unique_ptr<SMVType> Type)
            : Name(Name)
            , Type(std::move(Type))
        {}
    };

    /// Represents an SMV module
    class SMVModule {
    public:
        explicit SMVModule(llvm::StringRef Name)
            : Name(Name)
        {}

        // Variable management
        void addVariable(llvm::StringRef Name, std::unique_ptr<SMVType> Type);
        void addVariable(std::unique_ptr<SMVVariable> Var);

        // Constraints
        void addInit(std::unique_ptr<SMVExpr> Expr);
        void addTrans(std::unique_ptr<SMVExpr> Expr);
        void addTrans(std::unique_ptr<SMVExpr> Guard, std::unique_ptr<SMVExpr> Assignment);
        void addInvar(std::unique_ptr<SMVExpr> Expr);
        void addDefine(llvm::StringRef Name, std::unique_ptr<SMVExpr> Expr);

        // Output
        void write(llvm::raw_ostream& OS) const;

    private:
        std::string Name;
        std::vector<std::unique_ptr<SMVVariable>> Variables;
        std::vector<std::unique_ptr<SMVExpr>> InitConstraints;
        std::vector<std::unique_ptr<SMVExpr>> TransConstraints;
        std::vector<std::unique_ptr<SMVExpr>> InvarConstraints;
        std::map<std::string, std::unique_ptr<SMVExpr>> Defines;
    };

    /// Base class for SMV types
    class SMVType {
    public:
        enum TypeKind {
            TK_Boolean,
            TK_Integer,
            TK_Enum,
            TK_Array
        };

        virtual ~SMVType() = default;
        virtual TypeKind getKind() const = 0;
        virtual void print(llvm::raw_ostream& OS) const = 0;
        virtual std::unique_ptr<SMVType> clone() const = 0;
    };

    /// Boolean type
    class SMVBooleanType: public SMVType {
    public:
        TypeKind getKind() const override
        {
            return TK_Boolean;
        }
        void print(llvm::raw_ostream& OS) const override
        {
            OS << "boolean";
        }
        std::unique_ptr<SMVType> clone() const override
        {
            return std::make_unique<SMVBooleanType>();
        }
    };

    /// Integer type (signed or unsigned)
    class SMVIntegerType: public SMVType {
    public:
        SMVIntegerType(unsigned Width, bool IsSigned)
            : Width(Width)
            , IsSigned(IsSigned)
        {}

        TypeKind getKind() const override
        {
            return TK_Integer;
        }
        void print(llvm::raw_ostream& OS) const override;
        std::unique_ptr<SMVType> clone() const override
        {
            return std::make_unique<SMVIntegerType>(Width, IsSigned);
        }

        unsigned getWidth() const
        {
            return Width;
        }
        bool isSigned() const
        {
            return IsSigned;
        }

    private:
        unsigned Width;
        bool IsSigned;
    };

    /// Enumerated type
    class SMVEnumType: public SMVType {
    public:
        explicit SMVEnumType(std::vector<std::string> Values)
            : Values(std::move(Values))
        {}

        TypeKind getKind() const override
        {
            return TK_Enum;
        }
        void print(llvm::raw_ostream& OS) const override;
        std::unique_ptr<SMVType> clone() const override
        {
            return std::make_unique<SMVEnumType>(Values);
        }

    private:
        std::vector<std::string> Values;
    };

    /// Array type
    class SMVArrayType: public SMVType {
    public:
        SMVArrayType(std::unique_ptr<SMVType> ElementType, unsigned Size)
            : ElementType(std::move(ElementType))
            , Size(Size)
        {}

        TypeKind getKind() const override
        {
            return TK_Array;
        }
        void print(llvm::raw_ostream& OS) const override;
        std::unique_ptr<SMVType> clone() const override
        {
            return std::make_unique<SMVArrayType>(ElementType->clone(), Size);
        }

    private:
        std::unique_ptr<SMVType> ElementType;
        unsigned Size;
    };

    /// Base class for SMV expressions
    class SMVExpr {
    public:
        enum ExprKind {
            EK_Constant,
            EK_Variable,
            EK_Binary,
            EK_Unary,
            EK_Next,
            EK_Case,
            EK_ArrayAccess,
            EK_GuardedTrans
        };

        virtual ~SMVExpr() = default;
        virtual ExprKind getKind() const = 0;
        virtual void print(llvm::raw_ostream& OS) const = 0;
        virtual std::unique_ptr<SMVExpr> clone() const = 0;
    };

    // Factory functions for creating SMV expressions
    std::unique_ptr<SMVExpr> makeConstant(int64_t Value);
    std::unique_ptr<SMVExpr> makeConstant(bool Value);
    std::unique_ptr<SMVExpr> makeVariable(llvm::StringRef Name);
    std::unique_ptr<SMVExpr> makeNext(std::unique_ptr<SMVExpr> Expr);
    std::unique_ptr<SMVExpr> makeBinary(llvm::StringRef Op,
                                        std::unique_ptr<SMVExpr> LHS,
                                        std::unique_ptr<SMVExpr> RHS);
    std::unique_ptr<SMVExpr> makeCase(std::vector<std::pair<std::unique_ptr<SMVExpr>,
                                                            std::unique_ptr<SMVExpr>>>
                                          Cases,
                                      std::unique_ptr<SMVExpr> Default);
    std::unique_ptr<SMVExpr> makeGuardedTrans(std::unique_ptr<SMVExpr> Guard,
                                              std::unique_ptr<SMVExpr> Assignment);

} // namespace llvm2smv

#endif // LLVM2SMV_SMVWRITER_H
