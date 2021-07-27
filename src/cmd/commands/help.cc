/*
 * @file help.cc
 * @brief Command `help` class implementation.
 *
 * Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301 USA
 *
 **/

#include <cstdio>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <array>

#include <cstdlib>
#include <cstring>

#include <unistd.h>
#include <sys/wait.h>

#include <cmd/commands/commands.hh>
#include <cmd/commands/help.hh>

Help::Help(Interpreter& owner)
    : Command(owner)
    , f_topic(NULL)
{}

Help::~Help()
{
    if (f_topic)
        delete f_topic;

    f_topic = NULL;
}

void Help::set_topic(CommandTopic_ptr topic)
{
    f_topic = topic;
}

utils::Variant Help::operator()()
{
  if (f_topic) {

    int status;
    pid_t parent_pid;
    pid_t child_pid;

    // so the child can send a signal to the parent if needed
    parent_pid = getpid();

    switch(child_pid = fork()) {
    case -1:
      ERR
        << "[fork-exec-test] fork failed"
        << std::endl;
      exit(EXIT_FAILURE);
      break;

      case 0:
        f_topic->usage();

        // should't return
        ERR
          << "[fork-exec-test] exec failed"
          << std::endl;
        exit(EXIT_FAILURE);
        break;

    default:
      // no errors
      break;
    }

    // informational messages
    TRACE
      << "[fork-exec-test] parent PID: "
      << parent_pid
      << std::endl;

    TRACE
      << "[fork-exec-test] child PID: "
      << child_pid
      << std::endl;

    // wait for state changes in the child (aka for it to return)
    wait( &status );

    if (WIFEXITED(status)) {
      // no errors occurred in the child
      TRACE
        << "[fork-exec-test] print-argv terminated  normally"
        << std::endl;

      int exit_status = WEXITSTATUS(status);

      // which doesn't mean the program returned success (zero)
      TRACE
        << "[fork-exec-test] print-argv exit status: "
        << exit_status
        << std::endl;
    } else {
      // something went wrong
      WARN
        << "[fork-exec-test] print-argv wasn't executed"
        << std::endl;
    }

    TRACE
      << "[fork-exec-test] end"
      << std::endl;

    return utils::Variant(okMessage);
  } else {
    std::cout
      << "Available topics: " << std::endl
      << "- bmc" << std::endl
      << "- check-init" << std::endl
      << "- check-trans" << std::endl
      << "- clear" << std::endl
      << "- do" << std::endl
      << "- dump-model" << std::endl
      << "- dump-trace" << std::endl
      << "- dup-trace" << std::endl
      << "- echo" << std::endl
      << "- get" << std::endl
      << "- help" << std::endl
      << "- last" << std::endl
      << "- list-traces" << std::endl
      << "- on" << std::endl
      << "- pick-state" << std::endl
      << "- quit" << std::endl
      << "- reach" << std::endl
      << "- read-model" << std::endl
      << "- set" << std::endl
      << "- simulate" << std::endl
      << "- time" << std::endl
      << std::endl;

    return utils::Variant(okMessage);
  }
}

HelpTopic::HelpTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

HelpTopic::~HelpTopic()
{
    TRACE
        << "Destroyed help topic"
        << std::endl;
}

void HelpTopic::usage()
{ display_manpage("help"); }
