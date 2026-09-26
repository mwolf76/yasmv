#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>
#include <csignal>
#include <fstream>
#include <opts/opts_mgr.hh>
#include <parse.hh>
#include <query/query.hh>
#include <query/trace.hh>

namespace {
    struct ModelFixture {
        ModelFixture()
        {
            const char* args[] = { "query-tests" };
            opts::OptsMgr::INSTANCE().parse_command_line(1, args);
            auto& mm = model::ModelMgr::INSTANCE();
            mm.begin_load();
            if (!parse::parseFile("tests/models/query.smv")) throw std::runtime_error("Fixture parse failed");
            if (!mm.analyze()) throw std::runtime_error("Fixture model validation failed");
        }
    };
    void load_model()
    {
        static ModelFixture fixture;
    }
    query::QuerySpec reach(unsigned depth = 1)
    {
        load_model();
        query::QuerySpec s;
        s.operation = query::Operation::reach;
        s.target = parse::parseExpression("x");
        s.limits.depth = depth;
        return s;
    }
} // namespace

BOOST_AUTO_TEST_CASE(typed_outcomes_and_serialization)
{
    auto s = reach(0);
    auto r = query::execute(s);
    BOOST_CHECK(r.status == query::ExecutionStatus::completed);
    BOOST_CHECK(r.outcome == query::Outcome::unreachable);
    BOOST_CHECK_EQUAL(r.scope, "through_depth");
    BOOST_CHECK_EQUAL(r.checked_depths.size(), 1);
    BOOST_CHECK_EQUAL(r.json()["outcome"].asString(), "unreachable");
    r = query::execute(reach());
    BOOST_REQUIRE(r.witness != nullptr);
    BOOST_CHECK(r.outcome == query::Outcome::reachable);
    query::QuerySpec v;
    v.operation = query::Operation::validate_trace;
    v.trace = r.trace;
    auto validation = query::execute(v);
    BOOST_CHECK(validation.outcome == query::Outcome::valid);
    BOOST_CHECK(validation.statistics["independent_constraints_checked"].asUInt() > 0);
    BOOST_CHECK(validation.statistics["variables"].asUInt64() > 0);
    BOOST_CHECK(validation.statistics.isMember("compile_ms"));
}

BOOST_AUTO_TEST_CASE(cancellation_at_work_boundaries_does_not_poison_next_query)
{
    for (auto phase : { query::Phase::compilation, query::Phase::encoding, query::Phase::solving, query::Phase::decoding }) {
        auto s = reach();
        query::QueryContext context(s.limits);
        context.checkpoint_hook = [&context, phase](query::Phase p) {if(p==phase)context.cancel(); };
        auto r = query::execute(s, context);
        BOOST_CHECK(r.status == query::ExecutionStatus::unknown);
        BOOST_CHECK(r.outcome == query::Outcome::none);
        BOOST_CHECK(r.reason == query::StopReason::cancelled);
        BOOST_CHECK(r.trace.isNull());
        auto next = query::execute(reach());
        BOOST_REQUIRE(next.outcome == query::Outcome::reachable);
    }
}

BOOST_AUTO_TEST_CASE(signal_notification_is_consumed_by_only_current_query)
{
    query::signal_handler(SIGINT);
    auto first = query::execute(reach());
    BOOST_CHECK(first.status == query::ExecutionStatus::unknown);
    BOOST_CHECK(first.reason == query::StopReason::cancelled);
    BOOST_CHECK(query::execute(reach()).outcome == query::Outcome::reachable);
}

BOOST_AUTO_TEST_CASE(branch_prefix_is_preserved)
{
    auto original = query::execute(reach()).trace;
    auto child = original;
    child["id"] = "branch";
    child["branch"]["parent_id"] = original["id"];
    child["branch"]["prefix_length"] = 1;
    Json::StreamWriterBuilder builder;
    builder["indentation"] = "";
    child["branch"]["parent_digest"] = source::digest(Json::writeString(builder, original));
    query::QuerySpec s;
    s.operation = query::Operation::validate_trace;
    s.trace = child;
    s.parent_trace = original;
    BOOST_CHECK(query::execute(s).outcome == query::Outcome::valid);
    s.trace["steps"][0]["values"]["x"] = true;
    auto mismatch = query::execute(s);
    BOOST_CHECK(mismatch.status == query::ExecutionStatus::error);
    BOOST_CHECK(mismatch.diagnostics.front().message.find("prefix") != std::string::npos);
}

BOOST_AUTO_TEST_CASE(original_query_assumptions_and_invalid_inputs)
{
    auto s = reach();
    s.assumptions.push_back(parse::parseExpression("!x"));
    BOOST_CHECK(query::execute(s).outcome == query::Outcome::unreachable);
    s.strategy = "invalid";
    BOOST_CHECK_EQUAL(query::execute(s).exit_code(), 2);
    s = reach();
    s.limits.conflicts = 0;
    auto r = query::execute(s);
    BOOST_CHECK_EQUAL(r.exit_code(), 3);
    BOOST_CHECK(r.reason == query::StopReason::conflict_budget);
}

BOOST_AUTO_TEST_CASE(internal_errors_remain_execution_failures)
{
    auto s = reach();
    query::QueryContext context(s.limits);
    context.checkpoint_hook = [](query::Phase) { throw std::runtime_error("Injected internal failure"); };
    auto r = query::execute(s, context);
    BOOST_CHECK_EQUAL(r.exit_code(), 4);
    BOOST_CHECK(r.outcome == query::Outcome::none);
    BOOST_CHECK(r.trace.isNull());
}

BOOST_AUTO_TEST_CASE(shortest_and_proof_cancellation_never_publish_claims)
{
    load_model();
    query::QuerySpec spec;
    spec.operation = query::Operation::prove_property;
    spec.property["name"] = "tautology";
    spec.property["expression"] = "x || !x";
    spec.limits.depth = 2;
    auto proof = query::execute(spec);
    BOOST_REQUIRE(proof.outcome == query::Outcome::proven);
    BOOST_CHECK(proof.proof["verified"].asBool());
    // Three incremental base solves, then the induction step, then fresh checks.
    for (unsigned stop_at : { 1u, 4u, 5u, 8u }) {
        query::QueryContext context(spec.limits);
        unsigned calls = 0;
        context.checkpoint_hook = [&](query::Phase phase) {
            if (phase == query::Phase::solving && ++calls == stop_at) context.cancel();
        };
        auto interrupted = query::execute(spec, context);
        BOOST_CHECK(interrupted.status == query::ExecutionStatus::unknown);
        BOOST_CHECK(interrupted.proof.isNull());
        BOOST_CHECK(interrupted.trace.isNull());
        BOOST_CHECK(interrupted.optimality.isNull());
    }
    spec = reach(3);
    spec.operation = query::Operation::shortest_reach;
    query::QueryContext context(spec.limits);
    unsigned calls = 0;
    context.checkpoint_hook = [&](query::Phase phase) {
        if (phase == query::Phase::solving && ++calls == 2) context.cancel();
    };
    const auto interrupted = query::execute(spec, context);
    BOOST_CHECK(interrupted.status == query::ExecutionStatus::unknown);
    BOOST_CHECK(interrupted.optimality.isNull());
    BOOST_CHECK(query::execute(spec).optimality["certified"].asBool());
}
