/**
   Copyright (C) 2010-2016 Marco Pensallorto

   This file is part of YASMINE.

   YASMINE is free software: you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   YASMINE is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with GNuSMV.  If not, see <http://www.gnu.org/licenses/>.
*/
#ifndef _GRAMMAR_H_
#define _GRAMMAR_H_

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

#endif /* _GRAMMAR_H_ */
