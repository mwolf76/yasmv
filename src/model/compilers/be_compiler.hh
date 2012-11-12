/**
 *  @file be_compiler.hh
 *  @brief Boolean compiler
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

#ifndef BE_COMPILER_H
#define BE_COMPILER_H

#include <compilers/compiler.hh>

/* Boolean Compiler is just a specialization of the Compiler class, a
   few extra checks are performed in the post-hook to ensure result is
   a boolean value (single 0-1 ADD) */
class BECompiler : public Compiler {

public:
    // toplevel
    ADD process(Expr_ptr ctx, Expr_ptr body, step_t time);

protected:
    void pre_hook();
    void post_hook();

};

#endif
