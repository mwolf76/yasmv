#ifndef YASMV_SOURCE_HH
#define YASMV_SOURCE_HH
#include <expr/expr.hh>
#include <jsoncpp/json/json.h>
#include <string>
#include <vector>
namespace source {
    struct Span {
        std::string file;
        unsigned line = 0, column = 0, end_line = 0, end_column = 0;
        Json::Value json() const;
    };
    struct Diagnostic {
        std::string severity = "error", code, message;
        Span primary;
        std::vector<Span> related;
        Json::Value json() const;
    };
    struct Constraint {
        std::string id, module, kind, explanation;
        expr::Expr_ptr expression;
        Span span;
        std::vector<std::string> parents;
        Json::Value json() const;
    };
    std::string print(expr::Expr_ptr);
    std::string digest(const std::string&);
    void begin(const std::string& path);
    const std::string& revision();
    const std::string& filename();
    void record(expr::Expr_ptr module, const std::string& kind, expr::Expr_ptr expression);
    void locate(expr::Expr_ptr module, const std::string& kind, expr::Expr_ptr expression, unsigned line, unsigned column, unsigned end_line, unsigned end_column);
    void generated(expr::Expr_ptr expression, expr::Expr_ptr variable, const std::vector<expr::Expr_ptr>& guards);
    std::vector<std::string> references(expr::Expr_ptr expression);
    std::string occurrence(expr::Expr_ptr module, const std::string& kind, size_t index, expr::Expr_ptr scope);
    void error(expr::Expr_ptr expression, const std::string& code, const std::string& message);
    void guard_conflict(expr::Expr_ptr p, expr::Expr_ptr q);
    std::vector<Constraint>& constraints();
    std::vector<Diagnostic>& diagnostics();
    Json::Value catalog();
} // namespace source
#endif
