/**
 *  @file model.cc
 *
 *  Copyright (C) 2012 Marco Pensallorto < marco AT pensallorto DOT gmail DOT com >
 *
 *  This library is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public
 *  License as published by the Free Software Foundation; either
 *  version 2.1 of the License, or (at your option) any later version.
 *
 *  This library is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public
 *  License along with this library; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 **/
#include <type.hh>
#include <model.hh>

// WHY HERE?!?
ostream& operator<<(ostream& os, Exception& e)
{ return os << e.what(); }

Module& Model::add_module(Module& module)
{
    Expr_ptr name (module.name());

    DEBUG
        << "Added module: `"
        << name << "`"
        << endl;

    f_modules.insert( make_pair<Expr_ptr, Module_ptr>
                      (name, &module));

    return module;
}

Module& Model::module(Expr_ptr module_name)
{
    Modules::const_iterator i = f_modules.find(module_name);
    if (i == f_modules.end())
        throw ModuleNotFound(module_name);

    return *(i -> second);
}

Model::Model()
    : f_modules()
{
    DEBUG
        << "Initialized Model instance @"
        << this
        << endl;
}

Model::~Model()
{
    // TODO: free memory for symbols... (they've been allocated using new)
}

