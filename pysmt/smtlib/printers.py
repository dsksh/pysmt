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
from functools import partial

from six.moves import xrange, cStringIO

import pysmt.operators as op
from pysmt.environment import get_env
from pysmt.walkers import TreeWalker, DagWalker, handles
from pysmt.utils import quote


class SmtPrinter(TreeWalker):

    def __init__(self, stream, multi_prec=False):
        TreeWalker.__init__(self)
        self.stream = stream
        self.write = self.stream.write
        self.mgr = get_env().formula_manager
        self.multi_prec = multi_prec

    def printer(self, f):
        self.walk(f)

    def walk_threshold(self, formula):
        """This is a complete printer"""
        raise NotImplementedError

    def walk_nary(self, formula, operator, w_prec=False):
        self.write("(%s" % operator)

        args = formula.args()
        if w_prec and self.multi_prec:
            assert len(args) > 0 and args[0].get_type().is_ri_type()
            self.write(" %s" % args[0].get_type().precision)

        for s in args:
            self.write(" ")
            yield s
        self.write(")")

    def walk_and(self, formula): return self.walk_nary(formula, "and")
    def walk_or(self, formula): return self.walk_nary(formula, "or")
    def walk_not(self, formula): return self.walk_nary(formula, "not")
    def walk_implies(self, formula): return self.walk_nary(formula, "=>")
    def walk_iff(self, formula): return self.walk_nary(formula, "=")
    def walk_plus(self, formula): return self.walk_nary(formula, "+")
    def walk_minus(self, formula): return self.walk_nary(formula, "-")
    def walk_times(self, formula): return self.walk_nary(formula, "*")
    def walk_equals(self, formula): return self.walk_nary(formula, "=")
    def walk_le(self, formula): return self.walk_nary(formula, "<=")
    def walk_lt(self, formula): return self.walk_nary(formula, "<")
    def walk_ite(self, formula): return self.walk_nary(formula, "ite")
    def walk_toreal(self, formula): return self.walk_nary(formula, "to_real")
    def walk_div(self, formula): return self.walk_nary(formula, "/")
    def walk_pow(self, formula): return self.walk_nary(formula, "pow")
    def walk_bv_and(self, formula): return self.walk_nary(formula, "bvand")
    def walk_bv_or(self, formula): return self.walk_nary(formula, "bvor")
    def walk_bv_not(self, formula): return self.walk_nary(formula, "bvnot")
    def walk_bv_xor(self, formula): return self.walk_nary(formula, "bvxor")
    def walk_bv_add(self, formula): return self.walk_nary(formula, "bvadd")
    def walk_bv_sub(self, formula): return self.walk_nary(formula, "bvsub")
    def walk_bv_neg(self, formula): return self.walk_nary(formula, "bvneg")
    def walk_bv_mul(self, formula): return self.walk_nary(formula, "bvmul")
    def walk_bv_udiv(self, formula): return self.walk_nary(formula, "bvudiv")
    def walk_bv_urem(self, formula): return self.walk_nary(formula, "bvurem")
    def walk_bv_lshl(self, formula): return self.walk_nary(formula, "bvshl")
    def walk_bv_lshr(self, formula): return self.walk_nary(formula, "bvlshr")
    def walk_bv_ult(self, formula): return self.walk_nary(formula, "bvult")
    def walk_bv_ule(self, formula): return self.walk_nary(formula, "bvule")
    def walk_bv_slt(self, formula): return self.walk_nary(formula, "bvslt")
    def walk_bv_sle(self, formula): return self.walk_nary(formula, "bvsle")
    def walk_bv_concat(self, formula): return self.walk_nary(formula, "concat")
    def walk_bv_comp(self, formula): return self.walk_nary(formula, "bvcomp")
    def walk_bv_ashr(self, formula): return self.walk_nary(formula, "bvashr")
    def walk_bv_sdiv(self, formula): return self.walk_nary(formula, "bvsdiv")
    def walk_bv_srem(self, formula): return self.walk_nary(formula, "bvsrem")
    def walk_bv_tonatural(self, formula): return self.walk_nary(formula, "bv2nat")
    def walk_array_select(self, formula): return self.walk_nary(formula, "select")
    def walk_array_store(self, formula): return self.walk_nary(formula, "store")

    def walk_symbol(self, formula):
        self.write(quote(formula.symbol_name()))

    def walk_function(self, formula):
        return self.walk_nary(formula, quote(formula.function_name().symbol_name()))

    def walk_int_constant(self, formula):
        if formula.constant_value() < 0:
            self.write("(- " + str(-formula.constant_value()) + ")")
        else:
            self.write(str(formula.constant_value()))

    def walk_real_constant(self, formula):
        if formula.constant_value() < 0:
            template = "(- %s)"
        else:
            template = "%s"

        (n,d) = abs(formula.constant_value().numerator), \
                    formula.constant_value().denominator
        if d != 1:
            res = template % ( "(/ " + str(n) + " " + str(d) + ")" )
        else:
            res = template % (str(n) + ".0")

        self.write(res)

    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("true")
        else:
            self.write("false")

    def walk_bv_constant(self, formula):
        self.write("#b" + formula.bv_bin_str())

    def walk_str_constant(self, formula):
        self.write('"' + formula.constant_value().replace('"', '""') + '"')

    def walk_forall(self, formula):
        return self._walk_quantifier("forall", formula)

    def walk_exists(self, formula):
        return self._walk_quantifier("exists", formula)

    def _walk_quantifier(self, operator, formula):
        assert len(formula.quantifier_vars()) > 0
        self.write("(%s (" % operator)

        for s in formula.quantifier_vars():
            self.write("(")
            yield s
            self.write(" %s)" % s.symbol_type().as_smtlib(False))

        self.write(") ")
        yield formula.arg(0)
        self.write(")")

    def walk_bv_extract(self, formula):
        self.write("((_ extract %d %d) " % (formula.bv_extract_end(),
                                            formula.bv_extract_start()))
        yield formula.arg(0)
        self.write(")")

    @handles(op.BV_ROR, op.BV_ROL)
    def walk_bv_rotate(self, formula):
        if formula.is_bv_ror():
            rotate_type = "rotate_right"
        else:
            assert formula.is_bv_rol()
            rotate_type = "rotate_left"
        self.write("((_ %s %d) " % (rotate_type,
                                     formula.bv_rotation_step()))
        yield formula.arg(0)
        self.write(")")

    @handles(op.BV_ZEXT, op.BV_SEXT)
    def walk_bv_extend(self, formula):
        if formula.is_bv_zext():
            extend_type = "zero_extend"
        else:
            assert formula.is_bv_sext()
            extend_type = "sign_extend"
        self.write("((_ %s %d) " % (extend_type,
                                     formula.bv_extend_step()))
        yield formula.arg(0)
        self.write(")")

    def walk_str_length(self, formula):
        self.write("(str.len ")
        self.walk(formula.arg(0))
        self.write(")")

    def walk_str_charat(self,formula, **kwargs):
        self.write("( str.at " )
        self.walk(formula.arg(0))
        self.write(" ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_concat(self,formula, **kwargs):
        self.write("( str.++ " )
        for arg in formula.args():
            self.walk(arg)
            self.write(" ")
        self.write(")")

    def walk_str_contains(self,formula, **kwargs):
        self.write("( str.contains " )
        self.walk(formula.arg(0))
        self.write(" ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_indexof(self,formula, **kwargs):
        self.write("( str.indexof " )
        self.walk(formula.arg(0))
        self.write(" ")
        self.walk(formula.arg(1))
        self.write(" ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_replace(self,formula, **kwargs):
        self.write("( str.replace " )
        self.walk(formula.arg(0))
        self.write(" ")
        self.walk(formula.arg(1))
        self.write(" ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_substr(self,formula, **kwargs):
        self.write("( str.substr " )
        self.walk(formula.arg(0))
        self.write(" ")
        self.walk(formula.arg(1))
        self.write(" ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_prefixof(self,formula, **kwargs):
        self.write("( str.prefixof " )
        self.walk(formula.arg(0))
        self.write(" ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_suffixof(self,formula, **kwargs):
        self.write("( str.suffixof " )
        self.walk(formula.arg(0))
        self.write(" ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_to_int(self,formula, **kwargs):
        self.write("( str.to.int " )
        self.walk(formula.arg(0))
        self.write(")")

    def walk_int_to_str(self,formula, **kwargs):
        self.write("( int.to.str " )
        self.walk(formula.arg(0))
        self.write(")")

    def walk_array_value(self, formula):
        assign = formula.array_value_assigned_values_map()
        for _ in xrange(len(assign)):
            self.write("(store ")

        self.write("((as const %s) " % formula.get_type().as_smtlib(False))
        yield formula.array_value_default()
        self.write(")")

        for k in sorted(assign, key=str):
            self.write(" ")
            yield k
            self.write(" ")
            yield assign[k]
            self.write(")")

    # For FloatingPoint

    def walk_fp_constant(self, formula): return self.walk_nary(formula, "fp")
    def walk_fp_rne(self, formula): self.write("RNE")
    def walk_fp_rna(self, formula): self.write("RNA")
    def walk_fp_rtp(self, formula): self.write("RTP")
    def walk_fp_rtn(self, formula): self.write("RTN")
    def walk_fp_rtz(self, formula): self.write("RTZ")
    def walk_fp_abs(self, formula): return self.walk_nary(formula, "fp.abs")
    def walk_fp_neg(self, formula): return self.walk_nary(formula, "fp.neg")
    def walk_fp_add(self, formula): return self.walk_nary(formula, "fp.add")
    def walk_fp_sub(self, formula): return self.walk_nary(formula, "fp.sub")
    def walk_fp_mul(self, formula): return self.walk_nary(formula, "fp.mul")
    def walk_fp_div(self, formula): return self.walk_nary(formula, "fp.div")
    def walk_fp_fma(self, formula): return self.walk_nary(formula, "fp.fma")
    def walk_fp_sqrt(self, formula): return self.walk_nary(formula, "fp.sqrt")
    def walk_fp_rem(self, formula): return self.walk_nary(formula, "fp.rem")
    def walk_fp_round_to_integral(self, formula): return self.walk_nary(formula, "fp.roundToIntegral")
    def walk_fp_min(self, formula): return self.walk_nary(formula, "fp.min")
    def walk_fp_max(self, formula): return self.walk_nary(formula, "fp.max")
    def walk_fp_leq(self, formula): return self.walk_nary(formula, "fp.leq")
    def walk_fp_lt(self, formula): return self.walk_nary(formula, "fp.lt")
    def walk_fp_geq(self, formula): return self.walk_nary(formula, "fp.geq")
    def walk_fp_gt(self, formula): return self.walk_nary(formula, "fp.gt")
    def walk_fp_eq(self, formula): return self.walk_nary(formula, "fp.eq")
    def walk_fp_is_normal(self, formula): return self.walk_nary(formula, "fp.isNormal")
    def walk_fp_is_subnormal(self, formula): return self.walk_nary(formula, "fp.isSubnormal")
    def walk_fp_is_negative(self, formula): return self.walk_nary(formula, "fp.isNegative")
    def walk_fp_is_positive(self, formula): return self.walk_nary(formula, "fp.isPositive")

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
        self.write("((_ fp.to_sbv %d) " % (formula.bv_width()))
        yield formula.arg(0)
        self.write(" ")
        yield formula.arg(1)
        self.write(")")
    def walk_fp_to_real(self, formula): return self.walk_nary(formula, "fp.to_real")

    # RealInterval

    def walk_ri_l(self, formula): return self.walk_nary(formula, "ri.l")
    def walk_ri_u(self, formula): return self.walk_nary(formula, "ri.u")
    def walk_ri_is_pinf(self, formula): return self.walk_nary(formula, "is_pinf", w_prec=True)
    def walk_ri_is_ninf(self, formula): return self.walk_nary(formula, "is_ninf", w_prec=True)
    def walk_ri_is_nai(self, formula): return self.walk_nary(formula, "p_nan")
    def walk_ri_abs(self, formula): return self.walk_nary(formula, "ri.abs", w_prec=True)
    def walk_ri_add(self, formula): return self.walk_nary(formula, "ri.add", w_prec=True)
    def walk_ri_sub(self, formula): return self.walk_nary(formula, "ri.sub", w_prec=True)
    def walk_ri_sub_e(self, formula): return self.walk_nary(formula, "ri.sub_exact", w_prec=True)
    def walk_ri_neg(self, formula): return self.walk_nary(formula, "ri.neg", w_prec=True)
    def walk_ri_mul(self, formula): return self.walk_nary(formula, "ri.mul", w_prec=True)
    def walk_ri_div(self, formula): return self.walk_nary(formula, "ri.div", w_prec=True)
    def walk_ri_geq(self, formula): return self.walk_nary(formula, "ri.geq", w_prec=True)
    def walk_ri_gt(self, formula): return self.walk_nary(formula, "ri.gt", w_prec=True)
    #def walk_ri_eq(self, formula): 
    #    #return self.walk_nary(formula, "ri.eq+", w_prec=True)
    #    if ( (formula.args()[0].is_symbol() and not formula.args()[1].is_symbol()) or
    #            (not formula.args()[0].is_symbol() and formula.args()[1].is_symbol()) ):
    #        return self.walk_nary(formula, "=")
    #    else:            
    #        return self.walk_nary(formula, "ri.fpeq", w_prec=True)
    def walk_ri_fpeq(self, formula): return self.walk_nary(formula, "ri.fpeq", w_prec=True)
    def walk_ri_ite(self, formula): return self.walk_nary(formula, "ri.ite", w_prec=True)
    def walk_ri_geq_n(self, formula): return self.walk_nary(formula, "ri.lt", w_prec=True)
    def walk_ri_gt_n(self, formula): return self.walk_nary(formula, "ri.leq", w_prec=True)
    def walk_ri_fpeq_n(self, formula): return self.walk_nary(formula, "ri.fpneq", w_prec=True)
    def walk_ri_fpis(self, formula): return self.walk_nary(formula, "ri.fpis", w_prec=True)
    def walk_ri_is(self, formula): return self.walk_nary(formula, "ri.is", w_prec=True)
    def walk_ri_eq(self, formula): return self.walk_nary(formula, "ri.eq", w_prec=True)
    def walk_ri_neq(self, formula): return self.walk_nary(formula, "ri.neq", w_prec=True)

    def walk_ri_to_ri(self, formula): 
        if not self.multi_prec:
            self.write("(ri_to_ri ")
            yield formula.arg(1)
            self.write(")")
        else:
            self.write("(ri_to_ri ")
            yield formula.arg(0)
            self.write(" ")
            yield formula.arg(1)
            self.write(")")
    def walk_real_to_ri(self, formula): 
        if not self.multi_prec:
            self.write("(real_to_ri ")
            yield formula.arg(1)
            self.write(")")
        else:
            self.write("(real_to_ri ")
            yield formula.arg(0)
            self.write(" ")
            yield formula.arg(1)
            self.write(")")
    def walk_ri_exact(self, formula): 
        if not self.multi_prec:
            assert len(formula.args()) >= 1
            #self.write("(ri.exact %s)" % args[1])
            self.write("(ri.exact ")
            yield formula.arg(1)
            self.write(")")
        else:
            assert len(formula.args()) >= 2
            #self.write("(ri.exact %s %s)" % (args[0], args[1]))
            self.write("(ri.exact ")
            yield formula.arg(0)
            self.write(" ")
            yield formula.arg(1)
            self.write(")")

    def walk_ri_zero(self, formula): self.write("ri.zero")
    def walk_ri_pinf(self, formula): 
        if not self.multi_prec:
            self.write("ri.pinf")
        else:
            #self.write("(ri.pinf %s)" % formula.args()[0])
            self.write("(ri.pinf ")
            yield formula.arg(0)
            self.write(")")
    def walk_ri_ninf(self, formula): 
        if not self.multi_prec:
            self.write("ri.ninf")
        else:
            #self.write("(ri.ninf %s)" % formula.args()[0])
            self.write("(ri.ninf ")
            yield formula.arg(0)
            self.write(")")
    def walk_ri_entire(self, formula): 
        if not self.multi_prec:
            self.write("ri.entire")
        else:
            #self.write("(ri.entire %s)" % formula.args()[0])
            self.write("(ri.entire ")
            yield formula.arg(0)
            self.write(")")
    def walk_ri_nai(self, formula): 
        #self.write("ri.zero_nan")
        self.write("ri.ninf_nan")

    #def walk_ri_zero(self, formula): self.write("ri.zero")
    #def walk_ri_entire(self, formula): self.write("ri.entire")
    #def walk_ri_nai(self, formula): return self.write("ri.nai")
    #def walk_ri_to_ri(self, formula): return self.walk_nary(formula, "ri.to_ri", w_prec=True)
    #def walk_ri_exact(self, formula): return self.walk_nary(formula, "ri.exact")

class SmtDagPrinter(DagWalker):

    def __init__(self, stream, template=".def_%d", multi_prec=True):
        DagWalker.__init__(self, invalidate_memoization=True)
        self.stream = stream
        self.write = self.stream.write
        self.openings = 0
        self.name_seed = 0
        self.template = template
        self.names = None
        self.mgr = get_env().formula_manager
        self.multi_prec = multi_prec

    def _push_with_children_to_stack(self, formula, **kwargs):
        """Add children to the stack."""

        # Deal with quantifiers
        if formula.is_quantifier():
            # 1. We invoke the relevant function (walk_exists or
            #    walk_forall) to print the formula
            fun = self.functions[formula.node_type()]
            res = fun(formula, args=None, **kwargs)

            # 2. We memoize the result
            key = self._get_key(formula, **kwargs)
            self.memoization[key] = res
        else:
            DagWalker._push_with_children_to_stack(self, formula, **kwargs)

    def printer(self, f):
        self.openings = 0
        self.name_seed = 0
        self.names = set(quote(x.symbol_name()) for x in f.get_free_variables())

        key = self.walk(f)
        self.write(key)
        self.write(")" * self.openings)

    def _new_symbol(self):
        while (self.template % self.name_seed) in self.names:
            self.name_seed += 1
        res = (self.template % self.name_seed)
        self.name_seed += 1
        return res

    def walk_nary(self, formula, args, operator, w_prec=False):
        assert formula is not None

        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s (%s" % (sym, operator))

        args_ = formula.args()
        if w_prec and self.multi_prec:
            assert len(args_) > 0 and args_[0].get_type().is_ri_type()
            self.write(" %s" % args_[0].get_type().precision)

        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_and(self, formula, args):
        return self.walk_nary(formula, args, "and")

    def walk_or(self, formula, args):
        return self.walk_nary(formula, args, "or")

    def walk_not(self, formula, args):
        return self.walk_nary(formula, args, "not")

    def walk_implies(self, formula, args):
        return self.walk_nary(formula, args, "=>")

    def walk_iff(self, formula, args):
        return self.walk_nary(formula, args, "=")

    def walk_plus(self, formula, args):
        return self.walk_nary(formula, args, "+")

    def walk_minus(self, formula, args):
        return self.walk_nary(formula, args, "-")

    def walk_times(self, formula, args):
        return self.walk_nary(formula, args, "*")

    def walk_equals(self, formula, args): return self.walk_nary(formula, args, "=")
    def walk_le(self, formula, args):
        return self.walk_nary(formula, args, "<=")

    def walk_lt(self, formula, args):
        return self.walk_nary(formula, args, "<")

    def walk_ite(self, formula, args):
        return self.walk_nary(formula, args, "ite")

    def walk_toreal(self, formula, args):
        return self.walk_nary(formula, args, "to_real")

    def walk_div(self, formula, args):
        return self.walk_nary(formula, args, "/")

    def walk_pow(self, formula, args):
        return self.walk_nary(formula, args, "pow")

    def walk_bv_and(self, formula, args):
        return self.walk_nary(formula, args, "bvand")

    def walk_bv_or(self, formula, args):
        return self.walk_nary(formula, args, "bvor")

    def walk_bv_not(self, formula, args):
        return self.walk_nary(formula, args, "bvnot")

    def walk_bv_xor(self, formula, args):
        return self.walk_nary(formula, args, "bvxor")

    def walk_bv_add(self, formula, args):
        return self.walk_nary(formula, args, "bvadd")

    def walk_bv_sub(self, formula, args):
        return self.walk_nary(formula, args, "bvsub")

    def walk_bv_neg(self, formula, args):
        return self.walk_nary(formula, args, "bvneg")

    def walk_bv_mul(self, formula, args):
        return self.walk_nary(formula, args, "bvmul")

    def walk_bv_udiv(self, formula, args):
        return self.walk_nary(formula, args, "bvudiv")

    def walk_bv_urem(self, formula, args):

        return self.walk_nary(formula, args, "bvurem")
    def walk_bv_lshl(self, formula, args):
        return self.walk_nary(formula, args, "bvshl")

    def walk_bv_lshr(self, formula, args):
        return self.walk_nary(formula, args, "bvlshr")

    def walk_bv_ult(self, formula, args):
        return self.walk_nary(formula, args, "bvult")

    def walk_bv_ule(self, formula, args):
        return self.walk_nary(formula, args, "bvule")

    def walk_bv_slt(self, formula, args):
        return self.walk_nary(formula, args, "bvslt")

    def walk_bv_sle(self, formula, args):
        return self.walk_nary(formula, args, "bvsle")

    def walk_bv_concat(self, formula, args):
        return self.walk_nary(formula, args, "concat")

    def walk_bv_comp(self, formula, args):
        return self.walk_nary(formula, args, "bvcomp")

    def walk_bv_ashr(self, formula, args):
        return self.walk_nary(formula, args, "bvashr")

    def walk_bv_sdiv(self, formula, args):
        return self.walk_nary(formula, args, "bvsdiv")

    def walk_bv_srem(self, formula, args):
        return self.walk_nary(formula, args, "bvsrem")

    def walk_bv_tonatural(self, formula, args):
        return self.walk_nary(formula, args, "bv2nat")

    def walk_array_select(self, formula, args):
        return self.walk_nary(formula, args, "select")

    def walk_array_store(self, formula, args):
        return self.walk_nary(formula, args, "store")

    def walk_symbol(self, formula, **kwargs):
        return quote(formula.symbol_name())

    def walk_function(self, formula, args, **kwargs):
        return self.walk_nary(formula, args, quote(formula.function_name().symbol_name()))

    def walk_int_constant(self, formula, **kwargs):
        if formula.constant_value() < 0:
            return "(- " + str(-formula.constant_value()) + ")"
        else:
            return str(formula.constant_value())

    def walk_real_constant(self, formula, **kwargs):
        if formula.constant_value() < 0:
            template = "(- %s)"
        else:
            template = "%s"

        (n,d) = abs(formula.constant_value().numerator), \
                    formula.constant_value().denominator
        if d != 1:
            return template % ( "(/ " + str(n) + " " + str(d) + ")" )
        else:
            return template % (str(n) + ".0")

    def walk_bv_constant(self, formula, **kwargs):
        short_res = str(bin(formula.constant_value()))[2:]
        if formula.constant_value() >= 0:
            filler = "0"
        else:
            raise NotImplementedError
        res = short_res.rjust(formula.bv_width(), filler)
        return "#b" + res


    def walk_bool_constant(self, formula, **kwargs):
        if formula.constant_value():
            return "true"
        else:
            return "false"

    def walk_str_constant(self, formula, **kwargs):
        return '"' + formula.constant_value().replace('"', '""') + '"'

    def walk_forall(self, formula, args, **kwargs):
        return self._walk_quantifier("forall", formula, args)

    def walk_exists(self, formula, args, **kwargs):
        return self._walk_quantifier("exists", formula, args)

    def _walk_quantifier(self, operator, formula, args):
        assert args is None
        assert len(formula.quantifier_vars()) > 0
        sym = self._new_symbol()
        self.openings += 1

        self.write("(let ((%s (%s (" % (sym, operator))

        for s in formula.quantifier_vars():
            self.write("(")
            self.write(quote(s.symbol_name()))
            self.write(" %s)" % s.symbol_type().as_smtlib(False))
        self.write(") ")

        subprinter = SmtDagPrinter(self.stream)
        subprinter.printer(formula.arg(0))

        self.write(")))")
        return sym

    def walk_bv_extract(self, formula, args, **kwargs):
        assert formula is not None
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s ((_ extract %d %d)" % (sym,
                                                     formula.bv_extract_end(),
                                                     formula.bv_extract_start()))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    @handles(op.BV_SEXT, op.BV_ZEXT)
    def walk_bv_extend(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if formula.is_bv_zext():
            extend_type = "zero_extend"
        else:
            assert formula.is_bv_sext()
            extend_type = "sign_extend"

        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s ((_ %s %d)" % (sym, extend_type,
                                                formula.bv_extend_step()))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    @handles(op.BV_ROR, op.BV_ROL)
    def walk_bv_rotate(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if formula.is_bv_ror():
            rotate_type = "rotate_right"
        else:
            assert formula.is_bv_rol()
            rotate_type = "rotate_left"

        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s ((_ %s %d)" % (sym, rotate_type,
                                             formula.bv_rotation_step()))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_str_length(self, formula, args, **kwargs):
        return "(str.len %s)" % args[0]

    def walk_str_charat(self,formula, args,**kwargs):
        return "( str.at %s %s )" % (args[0], args[1])

    def walk_str_concat(self, formula, args, **kwargs):
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s (%s" % (sym, "str.++ " ))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_str_contains(self,formula, args, **kwargs):
        return "( str.contains %s %s)" % (args[0], args[1])

    def walk_str_indexof(self,formula, args, **kwargs):
        return "( str.indexof %s %s %s )" % (args[0], args[1], args[2])

    def walk_str_replace(self,formula, args, **kwargs):
        return "( str.replace %s %s %s )" % (args[0], args[1], args[2])

    def walk_str_substr(self,formula, args,**kwargs):
        return "( str.substr %s %s %s)" % (args[0], args[1], args[2])

    def walk_str_prefixof(self,formula, args,**kwargs):
        return "( str.prefixof %s %s )" % (args[0], args[1])

    def walk_str_suffixof(self,formula, args, **kwargs):
        return "( str.suffixof %s %s )" % (args[0], args[1])

    def walk_str_to_int(self,formula, args, **kwargs):
        return "( str.to.int %s )" % args[0]

    def walk_int_to_str(self,formula, args, **kwargs):
        return "( int.to.str %s )" % args[0]

    def walk_array_value(self, formula, args, **kwargs):
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s " % sym)

        for _ in xrange((len(args) - 1) // 2):
            self.write("(store ")

        self.write("((as const %s) " % formula.get_type().as_smtlib(False))
        self.write(args[0])
        self.write(")")

        for i, k in enumerate(args[1::2]):
            self.write(" ")
            self.write(k)
            self.write(" ")
            self.write(args[2*i + 2])
            self.write(")")
        self.write("))")
        return sym

    # For FloatingPoint

    def walk_fp_constant(self, formula, args): return self.walk_nary(formula, args, "fp")
    def walk_fp_rne(self, formula, args): return "RNE"
    def walk_fp_rna(self, formula, args): return "RNA"
    def walk_fp_rtp(self, formula, args): return "RTP"
    def walk_fp_rtn(self, formula, args): return "RTN"
    def walk_fp_rtz(self, formula, args): return "RTZ"
    def walk_fp_abs(self, formula, args): return self.walk_nary(formula, args, "fp.abs")
    def walk_fp_neg(self, formula, args): return self.walk_nary(formula, args, "fp.neg")
    def walk_fp_add(self, formula, args): return self.walk_nary(formula, args, "fp.add")
    def walk_fp_sub(self, formula, args): return self.walk_nary(formula, args, "fp.sub")
    def walk_fp_mul(self, formula, args): return self.walk_nary(formula, args, "fp.mul")
    def walk_fp_div(self, formula, args): return self.walk_nary(formula, args, "fp.div")
    def walk_fp_fma(self, formula, args): return self.walk_nary(formula, args, "fp.fma")
    def walk_fp_sqrt(self, formula, args): return self.walk_nary(formula, args, "fp.sqrt")
    def walk_fp_rem(self, formula, args): return self.walk_nary(formula, args, "fp.rem")
    def walk_fp_round_to_integral(self, formula, args): 
        return self.walk_nary(formula, args, "fp.roundToIntegral")
    def walk_fp_min(self, formula, args): return self.walk_nary(formula, args, "fp.min")
    def walk_fp_max(self, formula, args): return self.walk_nary(formula, args, "fp.max")
    def walk_fp_leq(self, formula, args): return self.walk_nary(formula, args, "fp.leq")
    def walk_fp_lt(self, formula, args): return self.walk_nary(formula, args, "fp.lt")
    def walk_fp_geq(self, formula, args): return self.walk_nary(formula, args, "fp.geq")
    def walk_fp_gt(self, formula, args): return self.walk_nary(formula, args, "fp.gt")
    def walk_fp_eq(self, formula, args): return self.walk_nary(formula, args, "fp.eq")
    def walk_fp_is_normal(self, formula, args): 
        return self.walk_nary(formula, args, "fp.isNormal")
    def walk_fp_is_subnormal(self, formula, args): 
        return self.walk_nary(formula, args, "fp.isSubnormal")
    def walk_fp_is_zero(self, formula, args): 
        return self.walk_nary(formula, args, "fp.isZero")
    def walk_fp_is_infinite(self, formula, args): 
        return self.walk_nary(formula, args, "fp.isInfinite")
    def walk_fp_is_nan(self, formula, args): 
        return self.walk_nary(formula, args, "fp.isNaN")
    def walk_fp_is_negative(self, formula, args): 
        return self.walk_nary(formula, args, "fp.isNegative")
    def walk_fp_is_positive(self, formula, args): 
        return self.walk_nary(formula, args, "fp.isPositive")

    def walk_fp_to_fp(self, formula, args):
        return "((_ to_fp %d %d) %s %s)" % (formula.fp_eb(), formula.fp_sb(), args[0], args[1])
    def walk_fp_to_fp_unsigned(self, formula, args):
        return "((_ to_fp_unsigned %d %d) %s %s)" % (formula.fp_eb(), formula.fp_sb(), args[0], args[1])
    def walk_bv_to_fp(self, formula, args):
        return "((_ to_fp %d %d) %s)" % (formula.fp_eb(), formula.fp_sb(), args[0])
    def walk_real_to_fp(self, formula, args):
        return "((_ to_fp %d %d) %s %s)" % (formula.fp_eb(), formula.fp_sb(), args[0], args[1])

    def walk_fp_to_ubv(self, formula, args):
        return "((_ fp.to_ubv %d) %s %s)" % (formula.bv_width(), args[0], args[1])
    def walk_fp_to_sbv(self, formula, args):
        return "((_ fp.to_sbv %d) %s %s)" % (formula.bv_width(), args[0], args[1])
    def walk_fp_to_real(self, formula, args): return self.walk_nary(formula, args, "fp.to_real")

    # For RealInterval

    def walk_ri_l(self, formula, args): return self.walk_nary(formula, args, "ri.l")
    def walk_ri_u(self, formula, args): return self.walk_nary(formula, args, "ri.u")
    def walk_ri_is_pinf(self, formula, args): return self.walk_nary(formula, args, "is_pinf", w_prec=True)
    def walk_ri_is_ninf(self, formula, args): return self.walk_nary(formula, args, "is_ninf", w_prec=True)
    def walk_ri_is_nai(self, formula, args): return self.walk_nary(formula, args, "p_nan")
    def walk_ri_abs(self, formula, args): return self.walk_nary(formula, args, "ri.abs", w_prec=False)
    def walk_ri_add(self, formula, args): return self.walk_nary(formula, args, "ri.add", w_prec=True)
    def walk_ri_sub(self, formula, args): return self.walk_nary(formula, args, "ri.sub", w_prec=True)
    def walk_ri_sub_e(self, formula, args): return self.walk_nary(formula, args, "ri.sub_exact", w_prec=True)
    def walk_ri_neg(self, formula, args): return self.walk_nary(formula, args, "ri.neg", w_prec=True)
    def walk_ri_mul(self, formula, args): return self.walk_nary(formula, args, "ri.mul", w_prec=True)
    def walk_ri_div(self, formula, args): return self.walk_nary(formula, args, "ri.div", w_prec=True)
    def walk_ri_geq(self, formula, args): return self.walk_nary(formula, args, "ri.geq", w_prec=True)
    def walk_ri_gt(self, formula, args): return self.walk_nary(formula, args, "ri.gt", w_prec=True)
    #def walk_ri_fpeq(self, formula, args): 
    #    #return self.walk_nary(formula, args, "ri.eq+", w_prec=True)
    #    if ( (formula.args()[0].is_symbol() and not formula.args()[1].is_symbol()) or
    #            (not formula.args()[0].is_symbol() and formula.args()[1].is_symbol()) ):
    #        return self.walk_nary(formula, args, "=")
    #    else:            
    #        return self.walk_nary(formula, args, "ri.fpeq", w_prec=True)
    def walk_ri_fpeq(self, formula, args): return self.walk_nary(formula, args, "ri.fpeq", w_prec=True)
    def walk_ri_ite(self, formula, args): return self.walk_nary(formula, args, "ri.ite", w_prec=True)
    def walk_ri_geq_n(self, formula, args): return self.walk_nary(formula, args, "ri.lt", w_prec=True)
    def walk_ri_gt_n(self, formula, args): return self.walk_nary(formula, args, "ri.leq", w_prec=True)
    def walk_ri_fpeq_n(self, formula, args): return self.walk_nary(formula, args, "ri.fpneq", w_prec=True)
    def walk_ri_fpis(self, formula, args): return self.walk_nary(formula, args, "ri.fpis", w_prec=True)
    def walk_ri_is(self, formula, args): return self.walk_nary(formula, args, "ri.is", w_prec=True)
    def walk_ri_eq(self, formula, args): return self.walk_nary(formula, args, "ri.eq", w_prec=True)
    def walk_ri_neq(self, formula, args): return self.walk_nary(formula, args, "ri.neq", w_prec=True)

    def walk_ri_to_ri(self, formula, args): 
        if not self.multi_prec:
            return "(ri_to_ri %s)" % args[1]
        else:
            return "(ri_to_ri %s %s)" % (args[0], args[1])
    def walk_real_to_ri(self, formula, args): 
        if not self.multi_prec:
            return "(real_to_ri %s)" % args[1]
        else:
            return "(real_to_ri %s %s)" % (args[0], args[1])
    def walk_ri_exact(self, formula, args): 
        if not self.multi_prec:
            assert len(args) >= 1
            return "(ri.exact %s)" % args[1]
        else:
            assert len(args) >= 2
            return "(ri.exact %s %s)" % (args[0], args[1])

    def walk_ri_zero(self, formula, args): return "ri.zero"
    def walk_ri_pinf(self, formula, args): 
        if not self.multi_prec:
            return "ri.pinf"
        else:
            return "(ri.pinf %s)" % args[0]
    def walk_ri_ninf(self, formula, args): 
        if not self.multi_prec:
            return "ri.ninf"
        else:
            return "(ri.ninf %s)" % args[0]
    def walk_ri_entire(self, formula, args): 
        if not self.multi_prec:
            return "ri.entire"
        else:
            return "(ri.entire %s)" % args[0]
    def walk_ri_nai(self, formula, args): 
        #return "ri.zero_nan"
        return "ri.ninf_nan"

def to_smtlib(formula, daggify=True):
    """Returns a Smt-Lib string representation of the formula.

    The daggify parameter can be used to switch from a linear-size
    representation that uses 'let' operators to represent the
    formula as a dag or a simpler (but possibly exponential)
    representation that expands the formula as a tree.

    See :py:class:`SmtPrinter`
    """
    buf = cStringIO()
    p = None
    if daggify:
        p = SmtDagPrinter(buf)
    else:
        p = SmtPrinter(buf)
    p.printer(formula)
    res = buf.getvalue()
    buf.close()
    return res
