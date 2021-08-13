/**
 * @file read_trace.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler inteface for the `read-trace`
 * command.
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

#ifndef READ_TRACE_H
#define READ_TRACE_H

#include <cmd/command.hh>

#include <expr/atom.hh>

#include <witness/witness.hh>

namespace cmd {

    // -- command definitions --------------------------------------------------
    class ReadTrace: public Command {
    public:
        ReadTrace(Interpreter& owner);
        virtual ~ReadTrace();

        void set_input(pconst_char input);
        inline pconst_char input() const
        {
            return f_input;
        }

        utils::Variant virtual operator()();

    private:
        std::ostream& f_out;
        pchar f_input;

        bool check_requirements();
        bool parseJsonTrace(boost::filesystem::path& tracepath);
        bool parseYamlTrace(boost::filesystem::path& tracepath);
        bool parsePlainTrace(boost::filesystem::path& tracepath);

    };
    typedef ReadTrace* ReadTrace_ptr;

    class ReadTraceTopic: public CommandTopic {
    public:
        ReadTraceTopic(Interpreter& owner);
        virtual ~ReadTraceTopic();

        void virtual usage();
    };

    class ReadTraceWitness: public witness::Witness {
    public:
        ReadTraceWitness(expr::Atom id, expr::Atom desc);
    };

    class ReadTraceException: public Exception {
    public:
        ReadTraceException(const std::string& subtype,
                           const std::string& message = "")
            : Exception("ReadTraceException", subtype, message)
        {}
    };

} // namespace cmd

#endif /* READ_TRACE_H */
