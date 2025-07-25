/**
 * @file type_mgr.cc
 * @brief Type Manager class implementation.
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

#include <opts/opts_mgr.hh>

#include <type.hh>
#include <type_mgr.hh>
#include <type_resolver.hh>

#include <symb/classes.hh>
#include <symb/typedefs.hh>

#include <utils/logging.hh>

namespace type {

    // static initialization
    TypeMgr_ptr TypeMgr::f_instance = NULL;

    TypeMgr::TypeMgr()
        : f_register()
        , f_em(expr::ExprMgr::INSTANCE())
        , f_resolver(*new TypeResolver(*this))
    {
    }

    /** Time */
    const TimeType_ptr TypeMgr::find_time()
    {
        expr::Expr_ptr descr {
            f_em.make_time_type()
        };
        TimeType_ptr res {
            dynamic_cast<TimeType_ptr>(lookup_type(descr))
        };

        if (res) {
            return res;
        }

        res = new TimeType(*this);
        register_type(descr, res);

        return res;
    }


    /** Booleans */
    const ScalarType_ptr TypeMgr::find_boolean()
    {
        expr::Expr_ptr descr {
            f_em.make_boolean_type()
        };
        ScalarType_ptr res {
            dynamic_cast<ScalarType_ptr>(lookup_type(descr))
        };

        if (res) {
            return res;
        }

        res = new BooleanType(*this);
        register_type(descr, res);

        return res;
    }

    const ArrayType_ptr TypeMgr::find_boolean_array(unsigned size)
    {
        expr::Expr_ptr descr {
            f_em.make_subscript(f_em.make_boolean_type(),
                                f_em.make_const(size))
        };
        ArrayType_ptr res {
            dynamic_cast<ArrayType_ptr>(lookup_type(descr))
        };

        if (res) {
            return res;
        }

        // new type, needs to be registered before returning
        res = new ArrayType(*this, find_boolean(), size);

        register_type(descr, res);
        return res;
    }

    /** Enums */
    const ScalarType_ptr TypeMgr::find_enum(expr::ExprSet& lits)
    {
        expr::Expr_ptr repr {
            em().make_enum_type(lits)
        };
        ScalarType_ptr res {
            dynamic_cast<ScalarType_ptr>(lookup_type(repr))
        };

        if (res) {
            return res;
        }

        // new type, needs to be registered before returning
        res = new EnumType(*this, lits);
        register_type(repr, res);

        value_t v;
        expr::ExprSet::const_iterator i;
        for (v = 0, i = lits.begin(); lits.end() != i; ++i, ++v) {

            const expr::Expr_ptr& expr {
                em().make_dot(em().make_empty(), *i)
            };

            symb::Literal_ptr literal { new symb::Literal(expr, res, v) };
            f_lits.insert(
                std::pair<expr::Expr_ptr, symb::Literal_ptr>(expr, literal));
        }

        return res;
    }

    const ArrayType_ptr TypeMgr::find_enum_array(expr::ExprSet& lits, unsigned size)
    {
        expr::Expr_ptr repr {
            f_em.make_subscript(f_em.make_enum_type(lits),
                                f_em.make_const(size))
        };
        ArrayType_ptr res {
            dynamic_cast<ArrayType_ptr>(lookup_type(repr))
        };

        if (res) {
            return res;
        }

        // new type, needs to be registered before returning
        res = new ArrayType(*this, find_enum(lits), size);

        register_type(repr, res);
        return res;
    }

    /** Constants */
    const ScalarType_ptr TypeMgr::find_constant(unsigned width)
    {
        expr::Expr_ptr descr {
            f_em.make_const_int_type(width)
        };
        ScalarType_ptr res {
            dynamic_cast<ScalarType_ptr>(lookup_type(descr))
        };

        if (res) {
            return res;
        }

        // new type, needs to be registered before returning
        res = new ConstantType(*this, width);

        register_type(descr, res);
        return res;
    }

    const StringType_ptr TypeMgr::find_string()
    {
        expr::Expr_ptr descr {
            f_em.make_string_type()
        };
        StringType_ptr res {
            dynamic_cast<StringType_ptr>(lookup_type(descr))
        };

        if (res) {
            return res;
        }

        res = new StringType(*this);
        register_type(descr, res);

        return res;
    }

    /** Unsigned algebraics */
    const ScalarType_ptr TypeMgr::find_unsigned(unsigned width)
    {
        expr::Expr_ptr descr {
            f_em.make_unsigned_int_type(width)
        };
        ScalarType_ptr res {
            dynamic_cast<ScalarType_ptr>(lookup_type(descr))
        };

        if (res) {
            return res;
        }

        // new type, needs to be registered before returning
        res = new UnsignedAlgebraicType(*this, width);

        register_type(descr, res);
        return res;
    }

    const ArrayType_ptr TypeMgr::find_unsigned_array(unsigned width, unsigned size)
    {
        expr::Expr_ptr descr {
            f_em.make_subscript(
                f_em.make_unsigned_int_type(width),
                f_em.make_const(size))
        };
        ArrayType_ptr res {
            dynamic_cast<ArrayType_ptr>(lookup_type(descr))
        };

        if (res) {
            return res;
        }

        // new type, needs to be registered before returning
        res = new ArrayType(*this, find_unsigned(width), size);

        register_type(descr, res);
        return res;
    }

    /** Signed algebraics */
    const ScalarType_ptr TypeMgr::find_signed(unsigned width)
    {
        expr::Expr_ptr descr {
            f_em.make_signed_int_type(width)
        };
        ScalarType_ptr res {
            dynamic_cast<ScalarType_ptr>(lookup_type(descr))
        };

        if (res) {
            return res;
        }

        // new type, needs to be registered before returning
        res = new SignedAlgebraicType(*this, width);

        register_type(descr, res);
        return res;
    }

    const ArrayType_ptr TypeMgr::find_signed_array(unsigned width, unsigned size)
    {
        expr::Expr_ptr descr {
            f_em.make_subscript(
                f_em.make_signed_int_type(width),
                f_em.make_const(size))
        };
        ArrayType_ptr res {
            dynamic_cast<ArrayType_ptr>(lookup_type(descr))
        };

        if (res) {
            return res;
        }

        // new type, needs to be registered before returning
        res = new ArrayType(*this, find_signed(width), size);

        register_type(descr, res);
        return res;
    }

    /** Instances */
    const ScalarType_ptr TypeMgr::find_instance(expr::Expr_ptr module, expr::Expr_ptr params)
    {
        expr::Expr_ptr repr {
            em().make_params(module, params)
        };
        ScalarType_ptr res {
            dynamic_cast<ScalarType_ptr>(lookup_type(repr))
        };

        if (!res) {
            // new type, needs to be registered before returning
            res = new InstanceType(*this, module, params);
            register_type(repr, res);
        }

        return res;
    }


    /** Typecasts */
    const Type_ptr TypeMgr::find_type_by_def(const expr::Expr_ptr expr)
    {
        assert(f_em.is_type(expr));

	if (f_em.is_boolean_type(expr)) {
	    return find_boolean();
	}

        if (f_em.is_unsigned_int(expr->lhs())) {
            return find_unsigned(expr->rhs()->value());
        }

        else if (f_em.is_signed_int(expr->lhs())) {
            return find_signed(expr->rhs()->value());
        }

        else {
            assert(false); /* unexpected */
        }

        return NULL;
    }


    /** Arrays */
    const ArrayType_ptr TypeMgr::find_array_type(ScalarType_ptr of, unsigned nelems)
    {
        expr::Expr_ptr descr {
            f_em.make_subscript(of->repr(),
                                f_em.make_const(nelems))
        };
        ArrayType_ptr res {
            dynamic_cast<ArrayType_ptr>(lookup_type(descr))
        };

        if (!res) {
            // new type, needs to be registered before returning
            res = new ArrayType(*this, of, nelems);
            register_type(descr, res);
        }

        return res;
    }


    // register a type
    void TypeMgr::register_type(const expr::Expr_ptr expr, Type_ptr vtype)
    {
        void* ptr { vtype };
        DEBUG
            << "Registering type `"
            << expr
            << "` at "
            << ptr
            << std::endl;

        assert((NULL != expr) && (NULL != vtype) && (!lookup_type(expr)));
        f_register[expr] = vtype;
    }

}; // namespace type
