/**
 * @file model/model.hh
 * @brief Model module, main container class declarations.
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

#ifndef MODEL_H
#define MODEL_H

#include <common/common.hh>

#include <model/exceptions.hh>
#include <model/typedefs.hh>

/* main container class */
class Model {
public:
    Model();
    ~Model();

    inline const Modules& modules() const
    { return f_modules; }

    Module& add_module(Module& module);
    Module& module(Expr_ptr module_name);

    /* topmost module in the model */
    Module& main_module();

    void autoIndexSymbol(Expr_ptr identifier);
    unsigned symbol_index(Expr_ptr identifier);

private:
    Modules f_modules;

    unsigned f_autoincrement;
    SymbolIndexMap f_symbol_index_map;
};

#endif /* MODEL_H */
