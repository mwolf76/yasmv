/**
 * @file read_model.cc
 * @brief Command `read-model` class implementation.
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

#include <cstdlib>
#include <cstring>

#include <cmd/commands/commands.hh>
#include <cmd/commands/read_model.hh>

#include <model/model_mgr.hh>

ReadModel::ReadModel(Interpreter& owner)
    : Command(owner)
    , f_input(NULL)
{}

ReadModel::~ReadModel()
{
    free(f_input);
    f_input = NULL;
}

void ReadModel::set_input(pconst_char input)
{
    if (input) {
        free(f_input);
        f_input = strdup(input);
    }
}

extern bool parseFile(pconst_char input); // in utils.cc
Variant ReadModel::operator()()
{

    if (! f_input) {
        WARN
            << "No input filename provided. (missing quotes?)"
            << std::endl;

        return Variant( "ERROR" );
    }

    // parsing
    bool hasErrors = parseFile(f_input);
    if (! hasErrors)
        hasErrors = ! ModelMgr::INSTANCE().analyze();

    return Variant( ! hasErrors ? okMessage : errMessage );
}

ReadModelTopic::ReadModelTopic(Interpreter& owner)
    : CommandTopic(owner)
{}

ReadModelTopic::~ReadModelTopic()
{
    TRACE
        << "Destroyed read-model topic"
        << std::endl;
}

void ReadModelTopic::usage()
{
    std::cout
        << "read-model <filename> - Reads a model from given filename[*].\n"
        << "[*] either in single or double quotes.\n" ;
}
