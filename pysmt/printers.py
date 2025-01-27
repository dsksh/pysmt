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
from io import StringIO

import pysmt.operators as op
from pysmt.walkers import TreeWalker
from pysmt.walkers.generic import handles
from pysmt.utils import quote
from pysmt.constants import is_pysmt_fraction, is_pysmt_integer


class HRPrinter(TreeWalker):
    """Performs serialization of a formula in a human-readable way.

    E.g., Implies(And(Symbol(x), Symbol(y)), Symbol(z))  ~>   '(x * y) -> z'
    """

    def __init__(self, stream, env=None):
        TreeWalker.__init__(self, env=env)
        self.stream = stream
        self.write = self.stream.write

    def printer(self, f, threshold=None):
        """Performs the serialization of 'f'.

        Thresholding can be used to define how deep in the formula to
        go. After reaching the thresholded value, "..." will be
        printed instead. This is mainly used for debugging.
        """
        self.walk(f, threshold=threshold)

    def walk_threshold(self, formula):
        self.write("...")

    def walk_nary(self, formula, ops):
        self.write("(")
        args = formula.args()
        for s in args[:-1]:
            yield s
            self.write(ops)
        yield args[-1]
        self.write(")")

    def walk_quantifier(self, op_symbol, var_sep, sep, formula):
        if len(formula.quantifier_vars()) > 0:
            self.write("(")
            self.write(op_symbol)
            for s in formula.quantifier_vars()[:-1]:
                yield s
                self.write(var_sep)
            yield formula.quantifier_vars()[-1]
            self.write(sep)
            yield formula.arg(0)
            self.write(")")
        else:
            yield formula.arg(0)

    def walk_not(self, formula):
        self.write("(! ")
        yield formula.arg(0)
        self.write(")")

    def walk_symbol(self, formula):
        self.write(quote(formula.symbol_name(), style="'"))

    def walk_function(self, formula):
        yield formula.function_name()
        self.write("(")
        for p in formula.args()[:-1]:
            yield p
            self.write(", ")
        yield formula.args()[-1]
        self.write(")")

    def walk_real_constant(self, formula):
        assert is_pysmt_fraction(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))
        # TODO: Remove this once issue 113 in gmpy2 is solved
        v = formula.constant_value()
        n,d = v.numerator, v.denominator
        if formula.constant_value().denominator == 1:
            self.write("%s.0" % n)
        else:
            self.write("%s/%s" % (n, d))

    def walk_int_constant(self, formula):
        assert is_pysmt_integer(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))
        self.write(str(formula.constant_value()))

    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("True")
        else:
            self.write("False")

    def walk_bv_constant(self, formula):
        # This is the simplest SMT-LIB way of printing the value of a BV
        # self.write("(_ bv%d %d)" % (formula.bv_width(),
        #                             formula.constant_value()))
        self.write("%d_%d" % (formula.constant_value(),
                              formula.bv_width()))

    def walk_algebraic_constant(self, formula):
        self.write(str(formula.constant_value()))

    def walk_bv_extract(self, formula):
        yield formula.arg(0)
        self.write("[%d:%d]" % (formula.bv_extract_start(),
                                       formula.bv_extract_end()))

    def walk_bv_neg(self, formula):
        self.write("(- ")
        yield formula.arg(0)
        self.write(")")

    def walk_bv_ror(self, formula):
        self.write("(")
        yield formula.arg(0)
        self.write(" ROR ")
        self.write("%d)" % formula.bv_rotation_step())

    def walk_bv_rol(self, formula):
        self.write("(")
        yield formula.arg(0)
        self.write(" ROL ")
        self.write("%d)" % formula.bv_rotation_step())

    def walk_bv_zext(self, formula):
        self.write("(")
        yield formula.arg(0)
        self.write(" ZEXT ")
        self.write("%d)" % formula.bv_extend_step())

    def walk_bv_sext(self, formula):
        self.write("(")
        yield formula.arg(0)
        self.write(" SEXT ")
        self.write("%d)" % formula.bv_extend_step())

    def walk_ite(self, formula):
        self.write("(")
        yield formula.arg(0)
        self.write(" ? ")
        yield formula.arg(1)
        self.write(" : ")
        yield formula.arg(2)
        self.write(")")

    def walk_forall(self, formula):
        return self.walk_quantifier("forall ", ", ", " . ", formula)

    def walk_exists(self, formula):
        return self.walk_quantifier("exists ", ", ", " . ", formula)

    def walk_toreal(self, formula):
        self.write("ToReal(")
        yield formula.arg(0)
        self.write(")")

    def walk_str_constant(self, formula):
        assert (type(formula.constant_value()) == str ), \
            "The type was " + str(type(formula.constant_value()))
        self.write('"%s"' % formula.constant_value().replace('"', '""'))

    def walk_str_length(self,formula):
        self.write("str.len(" )
        self.walk(formula.arg(0))
        self.write(")")

    def walk_str_charat(self,formula, **kwargs):
        self.write("str.at(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_concat(self,formula, **kwargs):
        self.write("str.++(" )
        for arg in formula.args()[:-1]:
            self.walk(arg)
            self.write(", ")
        self.walk(formula.args()[-1])
        self.write(")")

    def walk_str_contains(self,formula, **kwargs):
        self.write("str.contains(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_indexof(self,formula, **kwargs):
        self.write("str.indexof(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_replace(self,formula, **kwargs):
        self.write("str.replace(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_substr(self,formula, **kwargs):
        self.write("str.substr(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_prefixof(self,formula, **kwargs):
        self.write("str.prefixof(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_suffixof(self,formula, **kwargs):
        self.write("str.suffixof(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_to_int(self,formula, **kwargs):
        self.write("str.to.int(" )
        self.walk(formula.arg(0))
        self.write(")")

    def walk_int_to_str(self,formula, **kwargs):
        self.write("int.to.str(" )
        self.walk(formula.arg(0))
        self.write(")")

    def walk_array_select(self, formula):
        yield formula.arg(0)
        self.write("[")
        yield formula.arg(1)
        self.write("]")

    def walk_array_store(self, formula):
        yield formula.arg(0)
        self.write("[")
        yield formula.arg(1)
        self.write(" := ")
        yield formula.arg(2)
        self.write("]")

    def walk_array_value(self, formula):
        self.write(str(self.env.stc.get_type(formula)))
        self.write("(")
        yield formula.array_value_default()
        self.write(")")
        assign = formula.array_value_assigned_values_map()
        # We sort the array value assigments in lexicographic order
        # for deterministic printing
        for k in sorted(assign, key=str):
            self.write("[")
            yield k
            self.write(" := ")
            yield assign[k]
            self.write("]")

    def walk_bv_tonatural(self, formula):
        self.write("bv2nat(")
        yield formula.arg(0)
        self.write(")")

    def walk_and(self, formula): return self.walk_nary(formula, " & ")
    def walk_or(self, formula): return self.walk_nary(formula, " | ")
    def walk_plus(self, formula): return self.walk_nary(formula, " + ")
    def walk_times(self, formula): return self.walk_nary(formula, " * ")
    def walk_div(self, formula): return self.walk_nary(formula, " / ")
    def walk_pow(self, formula): return self.walk_nary(formula, " ^ ")
    def walk_iff(self, formula): return self.walk_nary(formula, " <-> ")
    def walk_implies(self, formula): return self.walk_nary(formula, " -> ")
    def walk_minus(self, formula): return self.walk_nary(formula, " - ")
    def walk_equals(self, formula): return self.walk_nary(formula, " = ")
    def walk_le(self, formula): return self.walk_nary(formula, " <= ")
    def walk_lt(self, formula): return self.walk_nary(formula, " < ")
    def walk_bv_xor(self, formula): return self.walk_nary(formula, " xor ")
    def walk_bv_concat(self, formula): return self.walk_nary(formula, "::")
    def walk_bv_udiv(self, formula): return self.walk_nary(formula, " u/ ")
    def walk_bv_urem(self, formula): return self.walk_nary(formula, " u% ")
    def walk_bv_sdiv(self, formula): return self.walk_nary(formula, " s/ ")
    def walk_bv_srem(self, formula): return self.walk_nary(formula, " s% ")
    def walk_bv_sle(self, formula): return self.walk_nary(formula, " s<= ")
    def walk_bv_slt(self, formula): return self.walk_nary(formula, " s< ")
    def walk_bv_ule(self, formula): return self.walk_nary(formula, " u<= ")
    def walk_bv_ult(self, formula): return self.walk_nary(formula, " u< ")
    def walk_bv_lshl(self, formula): return self.walk_nary(formula, " << ")
    def walk_bv_lshr(self, formula): return self.walk_nary(formula, " >> ")
    def walk_bv_ashr(self, formula): return self.walk_nary(formula, " a>> ")
    def walk_bv_comp(self, formula): return self.walk_nary(formula, " bvcomp ")
    walk_bv_and = walk_and
    walk_bv_or = walk_or
    walk_bv_not = walk_not
    walk_bv_add = walk_plus
    walk_bv_mul = walk_times
    walk_bv_sub = walk_minus

    def walk_fp_op(self, formula, op):
        self.write(op)
        self.write("(")
        args = formula.args()
        for s in args[:-1]:
            yield s
            self.write(', ')
        yield args[-1]
        self.write(")")

    def walk_fp_constant(self, formula):
        #TODO: print special values
        return self.walk_fp_op(formula, 'fp')
    def walk_fp_rne(self, formula): self.write('RNE')
    def walk_fp_rna(self, formula): self.write('RNA')
    def walk_fp_rtp(self, formula): self.write('RTP')
    def walk_fp_rtn(self, formula): self.write('RTN')
    def walk_fp_rtz(self, formula): self.write('RTZ')
    def walk_fp_abs(self, formula): return self.walk_fp_op(formula, 'fp.abs')
    def walk_fp_neg(self, formula): return self.walk_fp_op(formula, 'fp.neg')
    def walk_fp_sqrt(self, formula): return self.walk_fp_op(formula, 'fp.sqrt')
    def walk_fp_round_to_integral(self, formula):
        return self.walk_fp_op(formula, 'fp.roundToIntegral')
    def walk_fp_add(self, formula): return self.walk_fp_op(formula, 'fp.add')
    def walk_fp_sub(self, formula): return self.walk_fp_op(formula, 'fp.sub')
    def walk_fp_mul(self, formula): return self.walk_fp_op(formula, 'fp.mul')
    def walk_fp_div(self, formula): return self.walk_fp_op(formula, 'fp.div')
    def walk_fp_fma(self, formula): return self.walk_fp_op(formula, 'fp.fma')
    def walk_fp_rem(self, formula): return self.walk_fp_op(formula, 'fp.rem')
    def walk_fp_min(self, formula): return self.walk_fp_op(formula, 'fp.min')
    def walk_fp_max(self, formula): return self.walk_fp_op(formula, 'fp.max')
    def walk_fp_leq(self, formula): return self.walk_fp_op(formula, 'fp.leq')
    def walk_fp_lt(self, formula): return self.walk_fp_op(formula, 'fp.lt')
    def walk_fp_eq(self, formula): return self.walk_fp_op(formula, 'fp.eq')
    def walk_fp_is_normal(self, formula):
        return self.walk_fp_op(formula, 'fp.isNormal')
    def walk_fp_is_subnormal(self, formula):
        return self.walk_fp_op(formula, 'fp.isSubnormal')
    def walk_fp_is_zero(self, formula):
        return self.walk_fp_op(formula, 'fp.isZero')
    def walk_fp_is_infinite(self, formula):
        return self.walk_fp_op(formula, 'fp.isInfinite')
    def walk_fp_is_nan(self, formula):
        return self.walk_fp_op(formula, 'fp.isNaN')
    def walk_fp_is_negative(self, formula):
        return self.walk_fp_op(formula, 'fp.isNegative')
    def walk_fp_is_positive(self, formula):
        return self.walk_fp_op(formula, 'fp.isPositive')

    def walk_fp_to_fp(self, formula):
        self.write("((_ to_fp %d %d) " % (formula.fp_eb(), formula.fp_sb()))
        yield formula.arg(0)
        self.write(" ")
        yield formula.arg(1)
        self.write(")")
    def walk_fp_to_fp_unsigned(self, formula):
        self.write("((_ to_fp_unsigned %d %d) " % (formula.fp_eb(), formula.fp_sb()))
        yield formula.arg(0)
        self.write(" ")
        yield formula.arg(1)
        self.write(")")
    def walk_bv_to_fp(self, formula):
        self.write("((_ to_fp %d %d) " % (formula.fp_eb(), formula.fp_sb()))
        yield formula.arg(0)
        self.write(")")
    def walk_real_to_fp(self, formula):
        self.write("((_ to_fp %d %d) " % (formula.fp_eb(), formula.fp_sb()))
        yield formula.arg(0)
        self.write(" ")
        yield formula.arg(1)
        self.write(")")

    def walk_fp_to_ubv(self, formula):
        self.write("((_ fp.to_ubv %d) " % (formula.bv_width()))
        yield formula.arg(0)
        self.write(" ")
        yield formula.arg(1)
        self.write(")")
    def walk_fp_to_sbv(self, formula):
        self.write("((_ fp.to_sbv %d) " % (formula.fp_m()))
        yield formula.arg(0)
        self.write(" ")
        yield formula.arg(1)
        self.write(")")
    def walk_fp_to_real(self, formula): return self.walk_fp_op(formula, "fp.to_real")

    # RealInterval

    def walk_ri_op(self, formula, op):
        self.write(op)
        self.write("(")
        args = formula.args()
        for s in args[:-1]:
            yield s
            self.write(', ')
        yield args[-1]
        self.write(")")

    def walk_ri_l(self, formula): return self.walk_ri_op(formula, "ri.l")
    def walk_ri_u(self, formula): return self.walk_ri_op(formula, "ri.u")
    def walk_ri_is_pinf(self, formula): return self.walk_ri_op(formula, "is_pinf")
    def walk_ri_is_ninf(self, formula): return self.walk_ri_op(formula, "is_ninf")
    def walk_ri_is_nai(self, formula): return self.walk_ri_op(formula, "is_nai")
    def walk_ri_add(self, formula): return self.walk_ri_op(formula, "ri.add")
    def walk_ri_sub(self, formula): return self.walk_ri_op(formula, "ri.sub")
    def walk_ri_sub_e(self, formula): return self.walk_ri_op(formula, "ri.sub_exact")
    def walk_ri_neg(self, formula): return self.walk_ri_op(formula, "ri.neg")
    def walk_ri_mul(self, formula): return self.walk_ri_op(formula, "ri.mul")
    def walk_ri_div(self, formula): return self.walk_ri_op(formula, "ri.div")
    def walk_ri_geq(self, formula): return self.walk_ri_op(formula, "ri.geq")
    def walk_ri_gt(self, formula): return self.walk_ri_op(formula, "ri.gt")
    def walk_ri_fpeq(self, formula): return self.walk_ri_op(formula, "ri.fpeq")
    def walk_ri_ite(self, formula): return self.walk_ri_op(formula, "ri.ite")
    def walk_ri_geq_n(self, formula): return self.walk_ri_op(formula, "ri.geq-")
    def walk_ri_gt_n(self, formula): return self.walk_ri_op(formula, "ri.gt-")
    def walk_ri_fpeq_n(self, formula): return self.walk_ri_op(formula, "ri.fpeq-")
    def walk_ri_fpis(self, formula): return self.walk_ri_op(formula, "ri.fpis")
    def walk_ri_is(self, formula): return self.walk_ri_op(formula, "ri.is")
    def walk_ri_eq(self, formula): return self.walk_ri_op(formula, "ri.eq")
    def walk_ri_neq(self, formula): return self.walk_ri_op(formula, "ri.neq")
    def walk_ri_zero(self, formula): return self.write("ri.zero")
    def walk_ri_entire(self, formula): return self.write("ri.entire")
    def walk_ri_nai(self, formula): return self.write("ri.nai")
    def walk_ri_to_ri(self, formula): return self.walk_ri_op(formula, "ri.to_ri")
    def walk_ri_exact(self, formula): return self.walk_ri_op(formula, "ri.exact")

#EOC HRPrinter


class HRSerializer(object):
    """Return the serialized version of the formula as a string."""

    PrinterClass = HRPrinter

    def __init__(self, environment=None):
        self.environment = environment

    def serialize(self, formula, printer=None, threshold=None):
        """Returns a string with the human-readable version of the formula.

        'printer' is the printer to call to perform the serialization.
        'threshold' is the thresholding value for the printing function.
        """
        buf = StringIO()
        if printer is None:
            p = self.PrinterClass(buf)
        else:
            p = printer(buf)

        p.printer(formula, threshold)
        res = buf.getvalue()
        buf.close()
        return res


class SmartPrinter(HRPrinter):
    """Better serialization allowing special printing of subformula.

    The formula is serialized according to the format defined in the
    HRPrinter. However, everytime a formula that is present in
    'subs' is found, this is replaced.

    E.g., subs  = {And(a,b): "ab"}

    Everytime that the subformula And(a,b) is found, "ab" will be
    printed instead of "a & b". This makes it possible to rename big
    subformulae, and provide better human-readable representation.
    """

    def __init__(self, stream, subs=None):
        HRPrinter.__init__(self, stream)
        if subs is None:
            self.subs = {}
        else:
            self.subs = subs

    def printer(self, f, threshold=None):
        self.walk(f, threshold=threshold)

    @handles(op.ALL_TYPES)
    def smart_walk(self, formula):
        if formula in self.subs:
            # Smarties contains a string.
            # In the future, we could allow for arbitrary function calls
            self.write(self.subs[formula])
        else:
            return HRPrinter.super(self, formula)

# EOC SmartPrinter

def smart_serialize(formula, subs=None, threshold=None):
    """Creates and calls a SmartPrinter to perform smart serialization."""
    buf = StringIO()
    p = SmartPrinter(buf, subs=subs)
    p.printer(formula, threshold=threshold)
    res = buf.getvalue()
    buf.close()
    return res
