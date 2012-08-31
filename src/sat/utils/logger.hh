// -*- C++ -*-
// logger.h: Logging facilities
// Author: Alberto Griggio

#ifndef LOGGER_H_INCLUDED
#define LOGGER_H_INCLUDED

#include <iostream>
#include "utils/singleton.hh"

namespace Minisat {

  // markers to start a log message (setting the message level)...
  struct loglevel {
    int level;
    loglevel(int l): level(l) {}
  };

  // and ending the message (prints a newline and resets the output level).
  struct EndLog {};
  const EndLog endlog = EndLog();

  struct FlushLog {};
  const FlushLog flushlog = FlushLog();

  // expected usage:
  // Logger::get() << loglevel(4) << "This msg is at level 4" << endlog;

  class Logger: public Singleton<Logger> {
  public:
    static const int DEFAULT_OUTPUT_LEVEL = 0;

    Logger(std::ostream &o = std::cout)
    {
      output_level = DEFAULT_OUTPUT_LEVEL;
      cur_output_level = -1;
      out = &o;
    }
    virtual ~Logger();

    // A message is printed when message_ol < output_level
    int get_output_level() const { return output_level; }

    // Set the output level
    void set_output_level(int ol) { output_level = ol; }

    std::ostream &get_ostream() { return *out; }
    void set_ostream(std::ostream &o) { out = &o; }

    template<class T> Logger &operator<<(const T &msg);
    Logger &operator<<(const loglevel &lvl);
    Logger &operator<<(const EndLog&);
    Logger &operator<<(const FlushLog&);

  private:
    // The output level
    int output_level;
    // this is the level of the current message, set by *this << loglevel(n);
    int cur_output_level;
    std::ostream *out;
  };


  template<class T>
  Logger &Logger::operator<<(const T &msg)
  {
    if (output_level >= cur_output_level) {
      (*out) << msg;
    }
    return *this;
  }

} // namespace Minisat

#endif // LOGGER_H_INCLUDED
