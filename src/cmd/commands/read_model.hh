/**
 * @file read_model.hh
 * @brief Command-interpreter subsystem related classes and definitions.
 *
 * This header file contains the handler inteface for the `read-model`
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

#ifndef READ_MODEL_H
#define READ_MODEL_H

#include <cmd/command.hh>

// -- command definitions --------------------------------------------------
class ReadModel : public Command {

    pchar f_input;

public:
    ReadModel(Interpreter& owner);
    virtual ~ReadModel();

    void set_input(pconst_char input);
    inline pconst_char input() const
    { return f_input; }

    utils::Variant virtual operator()();
};
typedef ReadModel* ReadModel_ptr;

class ReadModelTopic : public CommandTopic {
public:
    ReadModelTopic(Interpreter& owner);
    virtual ~ReadModelTopic();

    void virtual usage();
};

#endif /* READ_MODEL_H */
