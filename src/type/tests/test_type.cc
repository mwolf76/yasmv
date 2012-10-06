#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>

#include <expr.hh>
#include <expr_mgr.hh>
#include <expr_printer.hh>

#include <type.hh>
#include <type_mgr.hh>

BOOST_AUTO_TEST_SUITE(type)

BOOST_AUTO_TEST_CASE(ctors)
{
    TypeMgr& tm = TypeMgr::INSTANCE();

    Type_ptr bt = tm.find_boolean();

}

BOOST_AUTO_TEST_SUITE_END()
