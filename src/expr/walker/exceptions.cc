#include <expr/walker/exceptions.hh>
#include <expr/walker/typedefs.hh>

#include <sstream>
#include <string>

// raised when the walker has encountered an unsupported entry point
static std::string format_unsupported_entry_point(entry_point ep)
{
    std::ostringstream oss;

    oss
        << "encountered "
        << ep ;

    return oss.str();
}

UnsupportedEntryPoint::UnsupportedEntryPoint(entry_point ep)
    : ExprException("UnsupportedEntryPoint",
                    format_unsupported_entry_point(ep))
{}

// raised when the walker has encountered an unsupported operator
static std::string format_unsupported_operator(ExprType et)
{
    std::ostringstream oss;

    oss
        << "encountered "
        << et ;

    return oss.str();
}

UnsupportedOperator::UnsupportedOperator(ExprType et)
    : ExprException("UnsupportedOperator",
                    format_unsupported_operator(et))
{}


UnsupportedLeaf::UnsupportedLeaf()
    : ExprException(std::string("UnsupportedLeaf"))
{}

InternalError::InternalError(const std::string& message)
    : ExprException("InternalError", message)
{}


