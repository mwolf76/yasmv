/**
 * @file type.hh
 * @brief Type system classes
 *
 * This header file contains the declarations and type definitions
 * required by YASMINE auto-generated parser and lexer.
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

#ifndef GRAMMAR_H
#define GRAMMAR_H

class GrammarException : public Exception {

    virtual const char* what() const throw() {
        std::ostringstream oss;
        oss
            << "Grammar exception: "
            << f_message
            << std::endl
            ;

        return (strdup(oss.str().c_str()));
    }

    std::string f_message;

public:
    GrammarException(const std::string &message)
        : f_message(message)
    {}

    virtual ~GrammarException() throw()
    {}
};

typedef enum {
    FORMAT_DEFAULT,
    FORMAT_BINARY,
    FORMAT_OCTAL,
    FORMAT_DECIMAL,
    FORMAT_HEXADECIMAL
} value_format_t;

#endif /* GRAMMAR_H */
