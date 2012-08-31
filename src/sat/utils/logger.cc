// logger.cc: Logging facilities
// Author: Alberto Griggio

#include "utils/logger.h"

namespace Minisat {

  Logger::~Logger() {}

  Logger &Logger::operator<<(const loglevel &lvl)
  {
    cur_output_level = lvl.level;
    return *this;
  }


  Logger &Logger::operator<<(const EndLog &)
  {
    if (output_level >= cur_output_level) {
      (*out) << std::endl;
    }
    cur_output_level = -1;
    return *this;
  }


  Logger &Logger::operator<<(const FlushLog &)
  {
    if (output_level >= cur_output_level) {
      out->flush();
    }
    return *this;
  }

  // Logger singleton instance
  Logger LoggerSingletonInstance;

} // namespace msat
