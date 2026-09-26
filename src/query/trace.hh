#ifndef YASMV_TRACE_V1_HH
#define YASMV_TRACE_V1_HH
#include <query/query.hh>
namespace query::trace {
    void allocate_state(sat::Engine&, unsigned);
    witness::Witness_ptr decode(sat::Engine&, unsigned);
    Json::Value export_trace(witness::Witness&, const QuerySpec&, const Json::Value&);
    witness::Witness_ptr import_trace(const Json::Value&);
    QueryResult validate(const Json::Value&, const Json::Value&, QueryContext&, const std::string& request_id = "");
    void write_file(const std::string&, const Json::Value&);
    Json::Value read_file(const std::string&);
} // namespace query::trace
#endif
