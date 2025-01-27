#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
"""This module provides basic services to perform type checking and
reasoning about the type of formulae.

 * SimpleTypeChecker provides the pysmt.typing type of a formula
 * The functions assert_*_args are useful for testing the type of
   arguments of a given function.
"""
import pysmt.walkers as walkers
import pysmt.operators as op

from pysmt.typing import BOOL, REAL, INT, BVType, ArrayType, STRING, FPType, RM, RIntType
from pysmt.exceptions import PysmtTypeError


class SimpleTypeChecker(walkers.DagWalker):

    def __init__(self, env=None):
        walkers.DagWalker.__init__(self, env=env)
        self.be_nice = False

    def _get_key(self, formula, **kwargs):
        return formula

    def get_type(self, formula):
        """ Returns the pysmt.types type of the formula """
        res = self.walk(formula)
        if not self.be_nice and res is None:
            raise PysmtTypeError("The formula '%s' is not well-formed" \
                                 % str(formula))
        return res

    def walk_type_to_type(self, formula, args, type_in, type_out):
        assert formula is not None
        for x in args:
            if x is None or x != type_in:
                return None
        return type_out

    @walkers.handles(op.AND, op.OR, op.NOT, op.IMPLIES, op.IFF)
    def walk_bool_to_bool(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, BOOL, BOOL)

    def walk_real_to_bool(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, REAL, BOOL)

    @walkers.handles(op.TOREAL)
    def walk_int_to_real(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, INT, REAL)

    def walk_real_to_real(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, REAL, REAL)

    @walkers.handles(op.PLUS, op.MINUS, op.TIMES, op.DIV)
    def walk_realint_to_realint(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        rval = self.walk_type_to_type(formula, args, REAL, REAL)
        if rval is None:
            rval = self.walk_type_to_type(formula, args, INT, INT)
        return rval

    @walkers.handles(op.BV_ADD, op.BV_SUB, op.BV_NOT, op.BV_AND, op.BV_OR)
    @walkers.handles(op.BV_XOR, op.BV_NEG, op.BV_MUL)
    @walkers.handles(op.BV_UDIV, op.BV_UREM, op.BV_LSHL, op.BV_LSHR)
    @walkers.handles(op.BV_SDIV, op.BV_SREM, op.BV_ASHR)
    def walk_bv_to_bv(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        # We check that all children are BV and the same size
        target_bv_type = BVType(formula.bv_width())
        for a in args:
            if not a == target_bv_type:
                return None
        return target_bv_type

    @walkers.handles(op.STR_CONCAT, op.STR_REPLACE)
    def walk_str_to_str(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, STRING, STRING)

    @walkers.handles(op.STR_LENGTH, op.STR_TO_INT)
    def walk_str_to_int(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, STRING, INT)

    @walkers.handles(op.STR_CONTAINS, op.STR_PREFIXOF, op.STR_SUFFIXOF)
    def walk_str_to_bool(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, STRING, BOOL)

    @walkers.handles(op.INT_TO_STR)
    def walk_int_to_str(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, INT, STRING)

    def walk_bv_comp(self, formula, args, **kwargs):
        # We check that all children are BV and the same size
        a,b = args
        if a != b or (not a.is_bv_type()):
            return None
        return BVType(1)

    @walkers.handles(op.BV_ULT, op.BV_ULE, op.BV_SLT, op.BV_SLE)
    def walk_bv_to_bool(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        width = args[0].width
        for a in args[1:]:
            if (not a.is_bv_type()) or width != a.width:
                return None
        return BOOL

    def walk_bv_tonatural(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if args[0].is_bv_type():
            return INT
        return None

    def walk_bv_concat(self, formula, args, **kwargs):
        # Width of BV operators are computed at construction time.
        # The type-checker only verifies that they are indeed
        # correct.
        try:
            l_width = args[0].width
            r_width = args[1].width
            target_width = formula.bv_width()
        except AttributeError:
            return None
        if not l_width + r_width == target_width:
            return None
        return BVType(target_width)

    def walk_bv_extract(self, formula, args, **kwargs):
        arg = args[0]
        if not arg.is_bv_type():
            return None
        base_width = arg.width
        target_width = formula.bv_width()
        start = formula.bv_extract_start()
        end = formula.bv_extract_end()
        if start >= base_width or end >= base_width:
            return None
        if base_width < target_width:
            return None
        if target_width != (end-start+1):
            return None
        return BVType(target_width)

    @walkers.handles(op.BV_ROL, op.BV_ROR)
    def walk_bv_rotate(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        target_width = formula.bv_width()
        if target_width < formula.bv_rotation_step() or target_width < 0:
            return None
        if target_width != args[0].width:
            return None
        return BVType(target_width)

    @walkers.handles(op.BV_ZEXT, op.BV_SEXT)
    def walk_bv_extend(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        target_width = formula.bv_width()
        if target_width < args[0].width or target_width < 0:
            return None
        return BVType(target_width)

    def walk_equals(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if args[0].is_bool_type():
            raise PysmtTypeError("The formula '%s' is not well-formed."
                                 "Equality operator is not supported for Boolean"
                                 " terms. Use Iff instead." \
                                 % str(formula))
        elif args[0].is_bv_type():
            return self.walk_bv_to_bool(formula, args)
        return self.walk_type_to_type(formula, args, args[0], BOOL)

    @walkers.handles(op.LE, op.LT)
    def walk_math_relation(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if args[0].is_real_type():
            return self.walk_type_to_type(formula, args, REAL, BOOL)
        return self.walk_type_to_type(formula, args, INT, BOOL)

    def walk_ite(self, formula, args, **kwargs):
        assert formula is not None
        if None in args: return None
        if (args[0] == BOOL and args[1]==args[2]):
            return args[1]
        return None

    @walkers.handles(op.BOOL_CONSTANT)
    def walk_identity_bool(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return BOOL

    @walkers.handles(op.REAL_CONSTANT, op.ALGEBRAIC_CONSTANT)
    def walk_identity_real(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return REAL

    @walkers.handles(op.INT_CONSTANT)
    def walk_identity_int(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return INT

    @walkers.handles(op.STR_CONSTANT)
    def walk_identity_string(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return STRING

    @walkers.handles(op.BV_CONSTANT)
    def walk_identity_bv(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return BVType(formula.bv_width())

    @walkers.handles(op.FP_CONSTANT)
    def walk_identity_fp(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 3
        return FPType(formula.fp_eb(), formula.fp_sb())

    def walk_symbol(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 0
        return formula.symbol_type()

    @walkers.handles(op.FORALL, op.EXISTS)
    def walk_quantifier(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 1
        if args[0] == BOOL:
            return BOOL
        return None

    def walk_function(self, formula, args, **kwargs):
        name = formula.function_name()
        assert name.is_symbol()
        tp = name.symbol_type()
        assert tp.is_function_type()

        if len(args) != len(tp.param_types):
            return None

        for (arg, p_type) in zip(args, tp.param_types):
            if arg != p_type:
                return None

        return tp.return_type

    def walk_str_charat(self, formula, args, **kwargs):
        assert formula is not None
        if len(args) == 2 and \
           args[0].is_string_type() and \
           args[1].is_int_type():
            return STRING
        return None

    def walk_str_indexof(self, formula, args, **kwargs):
        assert formula is not None
        if len(args) == 3 and args[0].is_string_type() and \
           args[1].is_string_type() and args[2].is_int_type():
            return INT
        return None

    def walk_str_substr(self, formula, args, **kwargs):
        assert formula is not None
        if len(args) == 3 and args[0].is_string_type() and \
           args[1].is_int_type() and args[2].is_int_type():
            return STRING
        return None

    def walk_array_select(self, formula, args, **kwargs):
        assert formula is not None
        if None in args: return None
        if (args[0].is_array_type() and args[0].index_type==args[1]):
            return args[0].elem_type
        return None

    def walk_array_store(self, formula, args, **kwargs):
        assert formula is not None
        if None in args: return None
        if (args[0].is_array_type() and args[0].index_type==args[1] and
            args[0].elem_type==args[2]):
            return args[0]
        return None

    def walk_array_value(self, formula, args, **kwargs):
        assert formula is not None
        if None in args: return None

        default_type = args[0]
        idx_type = formula.array_value_index_type()
        for i, c in enumerate(args[1:]):
            if i % 2 == 0 and c != idx_type:
                return None # Wrong index type
            elif i % 2 == 1 and c != default_type:
                return None
        return ArrayType(idx_type, default_type)

    def walk_pow(self, formula, args, **kwargs):
        if args[0] != args[1]:
            return None
        # Exponent must be positive for INT
        if args[0].is_int_type() and formula.arg(1).constant_value() < 0 :
            return None
        return args[0]

    def walk_fp_constant(self, formula, args, **kwargs):
        sign = args[0]
        eb = args[1]
        sb = args[2]
        if sign.is_bv_type(1) and eb.is_bv_type() and sb.is_bv_type():
            return FPType(eb.width, sb.width + 1)
        else:
            return None

    @walkers.handles(op.FP_RNE, op.FP_RNA, op.FP_RTP, op.FP_RTN, op.FP_RTZ)
    def walk_fp_rm_const(self, formula, args, **kwargs):
        return RM

    def walk_fp_to_fp_body(self, args, ret_ty=None):
        target_type = args[0]
        for a in args[1:]:
            if not a == target_type:
                return None
        if target_type.is_fp_type():
            return target_type if ret_ty is None else ret_ty
        else:
            return None

    @walkers.handles(op.FP_ABS, op.FP_NEG, op.FP_REM, op.FP_MIN, op.FP_MAX)
    def walk_fp_op_wo_rnd(self, formula, args, **kwargs):
        return self.walk_fp_to_fp_body(args)

    @walkers.handles(op.FP_SQRT, op.FP_ROUND_TO_INTEGRAL, \
                     op.FP_ADD, op.FP_SUB, \
                     op.FP_MUL, op.FP_DIV, op.FP_FMA)
    def walk_fp_op_w_rnd(self, formula, args, **kwargs):
        if not args[0].is_rm_type():
            return None

        return self.walk_fp_to_fp_body(args[1:])

    @walkers.handles(op.FP_LEQ, op.FP_LT, op.FP_EQ, op.FP_IS_NORMAL, \
                     op.FP_IS_SUBNORMAL, op.FP_IS_ZERO, op.FP_IS_INFINITE, \
                     op.FP_IS_NAN, op.FP_IS_NEGATIVE, op.FP_IS_POSITIVE)
    def walk_fp_pred(self, formula, args, **kwargs):
        return self.walk_fp_to_fp_body(args, ret_ty=BOOL)

    @walkers.handles(op.BV_TO_FP)
    def walk_bv_to_fp(self, formula, args, **kwargs):
        if not args[0].is_bv_type() or args[0].width != formula.fp_eb() + formula.fp_sb():
            return None

        return FPType(formula.fp_eb(), formula.fp_sb())

    @walkers.handles(op.FP_TO_FP, op.REAL_TO_FP, op.INT_TO_FP, op.UINT_TO_FP)
    def walk_fp_to_fp(self, formula, args, **kwargs):
        if  not args[0].is_rm_type() or \
            not args[1].is_real_type() and not args[1].is_fp_type() and not args[1].is_bv_type():
            return None

        # TODO: Check the match between args and ret_ty
        return FPType(formula.fp_eb(), formula.fp_sb())

    @walkers.handles(op.FP_TO_UBV, op.FP_TO_SBV)
    def walk_fp_to_bv(self, formula, args, **kwargs):
        if not args[0].is_rm_type():
            return None
        if not args[1].is_fp_type():
            return None

        # TODO: Check the match between m, eb and sb
        return BVType(formula.bv_width())

    @walkers.handles(op.FP_TO_REAL)
    def walk_fp_to_real(self, formula, args, **kwargs):
        if not args[0].is_fp_type():
            return None
        return REAL

    # RealInterval

    def walk_rint_to_rint(self, args, ret_ty=None):
        target_type = args[0]
        for a in args[1:]:
            if not a == target_type:
                return None
            elif target_type.precision < 0:
                target_type.set_precision(a.precision)
            elif a.precision < 0:
                a.set_precision(target_type.precision)
        return target_type if ret_ty is None else ret_ty

    #def walk_p_rint_to_rint(self, args, ret_ty=None):
    #    if not args[0].is_int_type():
    #        return None
    #    #if not args[1].is_ri_type():
    #    #    return None
    #    for a in args[1:]:
    #        if not a.is_ri_type():
    #            return None
    #    return RINT if ret_ty is None else ret_ty

    @walkers.handles(op.RI_ABS, op.RI_ADD, op.RI_SUB, op.RI_SUB_E, op.RI_NEG, \
                     op.RI_MUL, op.RI_DIV)
    def walk_ri_op(self, formula, args, **kwargs):
        return self.walk_rint_to_rint(args)

    @walkers.handles(op.RI_IS_NAI, \
                     op.RI_GEQ, op.RI_GT, op.RI_FPEQ, \
                     op.RI_GEQ_N, op.RI_GT_N, op.RI_FPEQ_N, \
                     op.RI_FPIS, op.RI_IS, op.RI_EQ, op.RI_NEQ, \
                     op.RI_IS_PINF, op.RI_IS_NINF)
    def walk_ri_pred(self, formula, args, **kwargs):
        return self.walk_rint_to_rint(args, ret_ty=BOOL)

    @walkers.handles(op.RI_ITE)
    def walk_ri_ite(self, formula, args, **kwargs):
        if not args[0].is_bool_type():
            return None
        elif not args[1].is_ri_type():
            return None
        elif not args[2].is_ri_type():
            return None
        elif args[1].precision() != args[2].precision():
            return None
        return RIntType(args[1].precision)

    @walkers.handles(op.RI_PINF, op.RI_NINF, op.RI_ENTIRE, op.RI_ZERO, op.RI_NAI)
    def walk_ri_const_mp(self, formula, args, **kwargs):
        if  not args[0].is_int_type():
            return None
        else:
            return RIntType(formula.args()[0].constant_value())

    @walkers.handles(op.RI_TO_RI)
    def walk_ri_to_ri_from_ri(self, formula, args, **kwargs):
        if  not args[0].is_int_type():
            return None
        elif  not args[0].is_int_type() and not args[0].is_ri_type():
            return None
        return RIntType(formula.args()[0].constant_value())

    @walkers.handles(op.REAL_TO_RI)
    def walk_ri_to_ri(self, formula, args, **kwargs):
        if  not args[0].is_int_type():
            return None
        elif  not args[0].is_int_type() and not args[0].is_real_type():
            return None
        return RIntType(formula.args()[0].constant_value())

    @walkers.handles(op.RI_EXACT)
    def walk_ri_exact(self, formula, args, **kwargs):
        if  not args[0].is_int_type() and not args[0].is_real_type():
            return None
        return RIntType(formula.args()[0].constant_value())

    @walkers.handles(op.RI_L, op.RI_U)
    def walk_ri_lu(self, formula, args, **kwargs):
        if  not args[0].is_ri_type():
            return None
        return REAL

# EOC SimpleTypeChecker


def assert_no_boolean_in_args(args):
    """ Enforces that the elements in args are not of BOOL type."""
    for arg in args:
        if (arg.get_type() == BOOL):
            raise PysmtTypeError("Boolean Expressions are not allowed "
                                 "in arguments")


def assert_boolean_args(args):
    """ Enforces that the elements in args are of BOOL type. """
    for arg in args:
        t = arg.get_type()
        if (t != BOOL):
            raise PysmtTypeError("%s is not allowed in arguments" % t)


def assert_same_type_args(args):
    """ Enforces that all elements in args have the same type. """
    ref_t = args[0].get_type()
    for arg in args[1:]:
        t = arg.get_type()
        if (t != ref_t):
            raise PysmtTypeError("Arguments should be of the same type!\n" +
                             str([str((a, a.get_type())) for a in args]))


def assert_args_type_in(args, allowed_types):
    """ Enforces that the type of the arguments is an allowed type """
    for arg in args:
        t = arg.get_type()
        if (t not in allowed_types):
            raise PysmtTypeError(
                "Argument is of type %s, but one of %s was expected!\n" %
                (t, str(allowed_types)))
