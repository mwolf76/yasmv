#ifndef LOGGER_CC_INCLUDED
#define LOGGER_CC_INCLUDED

#include <logging.hh>

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

    // TODO: make this configurable
    verbosity get_verbosity_level_tolerance() {
        return log_default_verbosity_level;
    }

};

#else
#error This file must be included only once
#endif
