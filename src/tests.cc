// test_main.cpp
#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE tests
#include <boost/test/unit_test.hpp>

/* tests placeholders */
BOOST_AUTO_TEST_SUITE(tests)
BOOST_AUTO_TEST_SUITE_END()

#include <common.hh>
#include <expr.hh>

// just for debugging purposes within gdb
static void pe(Expr_ptr e)
{ DEBUG << e << endl; }

static void pf(FQExpr& e)
{ DEBUG << e << endl; }

// logging subsystem settings
namespace axter {
    std::string get_log_prefix_format(const char*FileName,
                                      int LineNo, const char*FunctionName,
                                      ext_data levels_format_usage_data) {

        return ezlogger_format_policy::
            get_log_prefix_format(FileName, LineNo, FunctionName,
                                  levels_format_usage_data);
    }

    std::ostream& get_log_stream() {
        return ezlogger_output_policy::get_log_stream();
    }

    verbosity get_verbosity_level_tolerance() {
        return log_always; // log_very_rarely; //
    }
};
