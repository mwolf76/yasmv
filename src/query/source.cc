#include <boost/uuid/detail/sha1.hpp>
#include <expr/expr_mgr.hh>
#include <fstream>
#include <iomanip>
#include <query/runtime.hh>
#include <query/source.hh>
#include <sstream>
namespace source {
    static std::string file, rev, content;
    std::vector<Constraint>& constraints()
    {
        static std::vector<Constraint> v;
        return v;
    }
    std::vector<Diagnostic>& diagnostics()
    {
        static std::vector<Diagnostic> v;
        return v;
    }
    std::string print(expr::Expr_ptr e)
    {
        std::ostringstream out;
        if (e) out << e;
        return out.str();
    }
    std::string digest(const std::string& s)
    {
        boost::uuids::detail::sha1 hash;
        hash.process_bytes(s.data(), s.size());
        unsigned int d[5];
        hash.get_digest(d);
        std::ostringstream out;
        out << "sha1:";
        for (auto x : d)
            out << std::hex << std::setfill('0') << std::setw(8) << x;
        return out.str();
    }
    void begin(const std::string& path)
    {
        file = path;
        constraints().clear();
        diagnostics().clear();
        std::ifstream in(path, std::ios::binary);
        if (!in) throw std::invalid_argument("Cannot read model: " + path);
        std::ostringstream text;
        text << in.rdbuf();
        content = text.str();
        rev = digest(content);
        query::checkpoint(query::Phase::loading);
    }
    const std::string& revision()
    {
        return rev;
    }
    const std::string& contents() { return content; }
    const std::string& filename()
    {
        return file;
    }
    Json::Value Span::json() const
    {
        if (line == 0) return Json::Value();
        Json::Value v;
        v["file"] = file;
        v["line"] = line;
        v["column"] = column;
        v["end_line"] = end_line;
        v["end_column"] = end_column;
        return v;
    }
    Json::Value Diagnostic::json() const
    {
        Json::Value v;
        v["severity"] = severity;
        v["code"] = code;
        v["message"] = message;
        v["primary"] = primary.json();
        v["related"] = Json::arrayValue;
        for (const auto& s : related)
            v["related"].append(s.json());
        return v;
    }
    Json::Value Constraint::json() const
    {
        Json::Value v;
        v["id"] = id;
        v["module"] = module;
        v["kind"] = kind;
        v["expression"] = print(expression);
        v["span"] = span.json();
        v["explanation"] = explanation;
        v["parents"] = Json::arrayValue;
        for (const auto& p : parents)
            v["parents"].append(p);
        return v;
    }
    void record(expr::Expr_ptr module, const std::string& kind, expr::Expr_ptr e)
    {
        query::checkpoint(query::Phase::loading);
        Constraint c;
        c.id = "c" + std::to_string(constraints().size() + 1);
        c.module = print(module);
        c.kind = kind;
        c.expression = e;
        c.explanation = "Synthesized " + kind + " constraint";
        constraints().push_back(c);
    }
    void locate(expr::Expr_ptr module, const std::string& kind, expr::Expr_ptr e, unsigned line, unsigned col, unsigned el, unsigned ec)
    {
        for (auto it = constraints().rbegin(); it != constraints().rend(); ++it)
            if (it->module == print(module) && it->kind == kind && it->expression == e && !it->span.line) {
                it->span = { file, line, col + 1, el, ec + 1 };
                it->explanation.clear();
                return;
            }
        record(module, kind, e);
        locate(module, kind, e, line, col, el, ec);
    }
    static bool contains(expr::Expr_ptr root, expr::Expr_ptr needle)
    {
        if (!root) return false;
        if (root == needle) return true;
        auto& em = expr::ExprMgr::INSTANCE();
        if (em.is_constant(root) || em.is_identifier(root) || root->symb() == expr::QSTRING || root->symb() == expr::INSTANT) return false;
        return contains(root->lhs(), needle) || contains(root->rhs(), needle);
    }
    std::vector<std::string> references(expr::Expr_ptr e)
    {
        std::vector<std::string> ids;
        for (const auto& c : constraints())
            if (c.expression == e) ids.push_back(c.id);
        return ids;
    }
    std::string occurrence(expr::Expr_ptr module, const std::string& kind, size_t index, expr::Expr_ptr scope)
    {
        const auto original_index = index;
        for (const auto& c : constraints()) {
            if (c.module != print(module) || c.kind != kind || c.id.find('@') != std::string::npos) continue;
            if (index-- != 0) continue;
            if (print(scope).empty()) return c.id;
            auto instance = c;
            instance.id = c.id + "@" + print(scope);
            for (const auto& existing : constraints())
                if (existing.id == instance.id) return instance.id;
            instance.parents = { c.id };
            instance.span = {};
            instance.explanation = "Instantiate " + c.id + " in scope " + print(scope);
            constraints().push_back(instance);
            return instance.id;
        }
        return "environment:" + kind + ":" + std::to_string(original_index);
    }
    void generated(expr::Expr_ptr e, expr::Expr_ptr variable, const std::vector<expr::Expr_ptr>& guards)
    {
        if (constraints().empty()) return;
        auto& c = constraints().back();
        if (c.expression != e) return;
        c.id = "frame:" + c.module + ":" + print(variable);
        c.explanation = "Preserve " + print(variable) + " when no assignment guard holds";
        for (const auto& parent : constraints()) {
            if (parent.id == c.id) break;
            if (parent.module != c.module) continue;
            if (parent.kind == "declaration" && contains(variable, parent.expression)) c.parents.push_back(parent.id);
            if (parent.kind == "trans")
                for (auto g : guards)
                    if (contains(parent.expression, g)) {
                        c.parents.push_back(parent.id);
                        break;
                    }
        }
    }
    void error(expr::Expr_ptr e, const std::string& code, const std::string& message)
    {
        Diagnostic d;
        d.code = code;
        d.message = message;
        for (const auto& c : constraints())
            if (c.expression == e && c.span.line) {
                if (!d.primary.line)
                    d.primary = c.span;
                else
                    d.related.push_back(c.span);
            }
        diagnostics().push_back(d);
    }
    void guard_conflict(expr::Expr_ptr p, expr::Expr_ptr q)
    {
        Diagnostic d;
        d.code = "guard-conflict";
        d.message = "Inertial assignment guards overlap: " + print(p) + " and " + print(q);
        for (const auto& c : constraints())
            if (c.kind == "trans" && c.span.line && (contains(c.expression, p) || contains(c.expression, q))) {
                if (!d.primary.line)
                    d.primary = c.span;
                else
                    d.related.push_back(c.span);
            }
        diagnostics().push_back(d);
    }
    Json::Value catalog()
    {
        Json::Value v(Json::arrayValue);
        for (const auto& c : constraints())
            v.append(c.json());
        return v;
    }
} // namespace source
