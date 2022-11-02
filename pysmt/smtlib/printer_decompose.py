#
# Copyright 2021 Daisuke Ishii
#
from functools import partial

from six.moves import xrange, cStringIO

import pysmt.operators as op
from pysmt.environment import get_env
from pysmt.walkers import TreeWalker, DagWalker, handles
from pysmt.utils import quote, unquote
from pysmt.typing import INT, REAL, BOOL

class SmtDecomposePrinter(DagWalker):

    def __init__(self, stream, template=".def_%d", dplus=True, multi_prec=False):
        DagWalker.__init__(self, invalidate_memoization=True)
        self.stream = stream
        self.write = self.stream.write
        self.openings = 0
        self.name_seed = 0
        self.template = template
        self.names = None
        self.mgr = get_env().formula_manager
        self.dplus = dplus
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
        #self.openings = 0
        #self.name_seed = 0
        self.names = set(quote(x.symbol_name()) for x in f.get_free_variables())

        #key = self.walk(f)
        #self.write(key)
        #self.write(")" * self.openings)

        #do_write, key = self.walk(f)
        #if do_write:
        #    self.write(key)

        key = self.walk(f)
        return key

    def _new_symbol(self):
        while (self.template % self.name_seed) in self.names:
            self.name_seed += 1
        res = (self.template % self.name_seed)
        self.name_seed += 1
        return res

    def walk_nary(self, formula, args, operator):
        assert formula is not None
        sym = self._new_symbol()

        self.write("(declare-const %s %s)\n" % (sym, formula.get_type()))
        self.write("(assert (= %s (%s" % (sym, operator))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write(")))\n")
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

    def walk_equals(self, formula, args):
        return self.walk_nary(formula, args, "=")

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
        #return formula.symbol_name()

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
            res = template % ( "(/ " + str(n) + " " + str(d) + ")" )
        else:
            res = template % (str(n) + ".0")
        return res

    def walk_bv_constant(self, formula, **kwargs):
        short_res = str(bin(formula.constant_value()))[2:]
        if formula.constant_value() >= 0:
            filler = "0"
        else:
            raise NotImplementedError
        res = short_res.rjust(formula.bv_width(), filler)
        res = "#b" + res
        return res

    def walk_bool_constant(self, formula, **kwargs):
        if formula.constant_value():
            res = "true"
        else:
            res = "false"
        return res

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

        return "(let ((%s (%s (" % (sym, operator)

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

    def walk_fp_to_ubv(self, formula, args):
        return "((_ fp.to_ubv %d) %s %s)" % (formula.bv_width(), args[0], args[1])
    def walk_fp_to_sbv(self, formula, args):
        return "((_ fp.to_sbv %d) %s %s)" % (formula.bv_width(), args[0], args[1])
    def walk_fp_to_real(self, formula, args): return self.walk_nary(formula, args, "fp.to_real")

    # For RealInterval

    def walk_ri_l(self, formula, args): 
        if self.dplus:
            return "%s" % quote(unquote(args[0])+'.l')
        else:
            return args[0]
    def walk_ri_u(self, formula, args): 
        if self.dplus:
            return "%s" % quote(unquote(args[0])+'.u')
        else:
            return args[0]
    def walk_ri_is_pinf(self, formula, args): 
        if self.dplus:
            return "(is_pinf %s)" % (quote(unquote(args[0])+'.u'))
        else:
            return "(is_pinf %s)" % (args[0])
    def walk_ri_is_ninf(self, formula, args): 
        if self.dplus:
            return "(is_ninf %s)" % (quote(unquote(args[0])+'.l'))
        else:
            return "(is_ninf %s)" % (args[0])
    def walk_ri_is_nai(self, formula, args): 
        #if self.dplus:
        #    return "(p_nan %s)" % quote(unquote(args[0])+'.p_nan')
        #else:
        #    return "false"
        return "(p_nan %s)" % quote(unquote(args[0])+'.p_nan')

    def walk_nary_rint(self, formula, args, operator, w_prec=False):
        assert formula is not None
        sym = self._new_symbol()

        # Variable declarations.

        if self.dplus:
            self.write("(declare-const %s Real)\n" % (sym+'.l'))
            self.write("(declare-const %s Real)\n" % (sym+'.u'))
        else:
            self.write("(declare-const %s Real)\n" % sym)

        self.write("(declare-const %s Bool)\n" % (sym+'.p_nan'))

        # Lower bound.

        if self.dplus:
            self.write("(assert (= %s (%s.l" % (sym+'.l', operator))
        else:
            self.write("(assert (>= %s (%s.l" % (sym, operator))

        args_ = formula.args()
        if self.multi_prec:
            if w_prec:
                assert len(args_) > 0 and args_[0].get_type().is_int_type()
                self.write(" %s" % args_[0])
            else:
                assert len(args_) > 0 and args_[0].get_type().is_ri_type()
                self.write(" %d" % args_[0].get_type().precision)

        if w_prec:
            args__ = args[1:]
        else:
            args__ = args

        for s in args__:
            if self.dplus:
                self.write(" %s %s %s" % (quote(unquote(s)+'.l'), quote(unquote(s)+'.u'), quote(unquote(s)+'.p_nan')))
            else:
                self.write(" %s %s %s" % (s, s, quote(unquote(s)+'.p_nan')))
        self.write(")))\n")

        # Upper bound.

        if self.dplus:
            self.write("(assert (= %s (%s.u" % (sym+'.u', operator))
        else:
            self.write("(assert (<= %s (%s.u" % (sym, operator))

        if self.multi_prec:
            if w_prec:
                self.write(" %s" % args_[0])
            else:
                self.write(" %d" % args_[0].get_type().precision)

        for s in args__:
            if self.dplus:
                self.write(" %s %s %s" % (quote(unquote(s)+'.l'), quote(unquote(s)+'.u'), quote(unquote(s)+'.p_nan')))
            else:
                self.write(" %s %s %s" % (s, s, quote(unquote(s)+'.p_nan')))
        self.write(")))\n")

        # Is NaI.

        self.write("(assert (= %s (%s.p_nan" % (sym+'.p_nan', operator))

        if self.multi_prec:
            if w_prec:
                self.write(" %s" % args_[0])
            else:
                self.write(" %s" % args_[0].get_type().precision)

        for s in args__:
            if self.dplus:
                self.write(" %s %s %s" % (quote(unquote(s)+'.l'), quote(unquote(s)+'.u'), quote(unquote(s)+'.p_nan')))
            else:
                self.write(" %s %s %s" % (s, s, quote(unquote(s)+'.p_nan')))
        self.write(")))")
        self.write("\n")

        return sym

    def walk_ri_abs(self, formula, args): return self.walk_nary_rint(formula, args, "ri.abs")
    def walk_ri_add(self, formula, args): return self.walk_nary_rint(formula, args, "ri.add")
    def walk_ri_sub(self, formula, args): return self.walk_nary_rint(formula, args, "ri.sub")
    def walk_ri_sub_e(self, formula, args): return self.walk_nary_rint(formula, args, "ri.sub_exact")
    def walk_ri_neg(self, formula, args): return self.walk_nary_rint(formula, args, "ri.neg")
    def walk_ri_mul(self, formula, args): return self.walk_nary_rint(formula, args, "ri.mul")
    def walk_ri_div(self, formula, args): return self.walk_nary_rint(formula, args, "ri.div")

    def walk_nary_ri_rel(self, formula, args, operator):
        assert formula is not None
        sym = self._new_symbol()

        self.write("(declare-const %s %s)\n" % (sym, BOOL))

        self.write("(assert (= %s (%s" % (sym, operator))

        if self.multi_prec:
            args_ = formula.args()
            assert len(args_) > 0 and args_[0].get_type().is_ri_type()
            self.write(" %d" % args_[0].get_type().precision)

        for s in args:
            if self.dplus:
                self.write(" %s %s %s" % (quote(unquote(s)+'.l'), quote(unquote(s)+'.u'), quote(unquote(s)+'.p_nan')))
            else:
                self.write(" %s %s %s" % (s, s, quote(unquote(s)+'.p_nan')))
        self.write(")))")
        self.write("\n")

        return sym

    def walk_ri_geq(self, formula, args): return self.walk_nary_ri_rel(formula, args, "ri.geq")
    def walk_ri_gt(self, formula, args): return self.walk_nary_ri_rel(formula, args, "ri.gt")
    def walk_ri_fpeq(self, formula, args): return self.walk_nary_ri_rel(formula, args, "ri.fpeq")
    def walk_ri_ite(self, formula, args): return self.walk_nary_ri_rel(formula, args, "ri.ite")
    def walk_ri_geq_n(self, formula, args): return self.walk_nary_ri_rel(formula, args, "ri.lt")
    def walk_ri_gt_n(self, formula, args): return self.walk_nary_ri_rel(formula, args, "ri.leq")
    def walk_ri_fpeq_n(self, formula, args): return self.walk_nary_ri_rel(formula, args, "ri.fpneq")
    def walk_ri_fpis(self, formula, args): return self.walk_nary_ri_rel(formula, args, "ri.fpis")
    def walk_ri_is(self, formula, args): return self.walk_nary_ri_rel(formula, args, "ri.is")
    def walk_ri_eq(self, formula, args): return self.walk_nary_ri_rel(formula, args, "ri.eq")
    def walk_ri_neq(self, formula, args): return self.walk_nary_ri_rel(formula, args, "ri.neq")

    def walk_ri_zero(self, formula, args): return "ri.zero"
    def walk_ri_pinf(self, formula, args): 
        if not self.multi_prec:
            return "ri.pinf"
        else:
            #return "(ri.pinf %s)" % args[0]
            return self.walk_nary_rint(formula, args, "ri.pinf", w_prec=True)
    def walk_ri_ninf(self, formula, args):
        if not self.multi_prec:
            return "ri.ninf"
        else:
            #return "(ri.ninf %s)" % args[0]
            return self.walk_nary_rint(formula, args, "ri.ninf", w_prec=True)
    def walk_ri_entire(self, formula, args): 
        if not self.multi_prec:
            return "ri.entire"
        else:
            #return "(ri.entire %s)" % args[0]
            return self.walk_nary_rint(formula, args, "ri.entire", w_prec=True)
    def walk_ri_nai(self, formula, args): 
        #return "ri.zero_nan"
        return "ri.ninf_nan"

    def walk_ri_to_ri(self, formula, args): 
        assert formula is not None
        sym = self._new_symbol()

        # Variable declarations.

        if self.dplus:
            self.write("(declare-const %s Real)\n" % (sym+'.l'))
            self.write("(declare-const %s Real)\n" % (sym+'.u'))
            self.write("(assert (<= %s %s))\n" % (sym+'.l', sym+'.u'))
        else:
            self.write("(declare-const %s Real)\n" % sym)

        self.write("(declare-const %s Bool)\n" % (sym+'.p_nan'))

        # Lower bound.

        if self.dplus:
            self.write("(assert (= %s (ri_to_ri.l" % (sym+'.l'))
        else:
            self.write("(assert (>= %s (ri_to_ri.l" % (sym))

        if self.multi_prec:
            self.write(" %s" % args[0])

        # TODO
        if self.dplus and not formula.arg(1).is_constant():
            self.write(" %s" % quote(unquote(args[1])+'.l'))
        else:
            self.write(" %s" % args[1])
        self.write(")))\n")

        # Upper bound.

        if self.dplus:
            self.write("(assert (= %s (ri_to_ri.u" % (sym+'.u'))
        else:
            self.write("(assert (<= %s (ri_to_ri.u" % (sym))

        if self.multi_prec:
            self.write(" %s" % args[0])

        if self.dplus and not formula.arg(1).is_constant():
            self.write(" %s" % (quote(unquote(args[1])+'.u')))
        else:
            self.write(" %s" % args[1])
        self.write(")))\n")

        # Is NaI.

        self.write("(assert (= %s (ri_to_ri.p_nan" % (sym+'.p_nan'))
        if not formula.arg(1).is_constant():
            self.write(" %s" % quote(unquote(args[1])+'.p_nan'))
        else:
            # TODO
            self.write(" false")
        self.write(")))")
        self.write("\n")

        return sym

    def walk_real_to_ri(self, formula, args): 
        assert formula is not None
        sym = self._new_symbol()

        # Variable declarations.

        if self.dplus:
            self.write("(declare-const %s Real)\n" % (sym + '.l'))
            self.write("(declare-const %s Real)\n" % (sym + '.u'))
            self.write("(assert (<= %s %s))\n" % (sym+'.l', sym+'.u'))
        else:
            self.write("(declare-const %s Real)\n" % sym)

        self.write("(declare-const %s Bool)\n" % (sym+'.p_nan'))
        self.write("(assert (not %s))\n" % (sym+'.p_nan'))

        # Lower bound.

        if self.dplus:
            self.write("(assert (= %s (real_to_ri.l" % (sym+'.l'))
        else:
            self.write("(assert (>= %s (real_to_ri.l" % (sym))

        if self.multi_prec:
            self.write(" %d" % args[0])

        self.write(" %s" % args[1])
        self.write(")))\n")

        # Upper bound.

        if self.dplus:
            self.write("(assert (= %s (real_to_ri.u" % (sym+'.u'))
        else:
            self.write("(assert (<= %s (real_to_ri.u" % (sym))

        if self.multi_prec:
            self.write(" %s" % args[0])

        self.write(" %s" % args[1])
        self.write(")))\n")

        return sym

    def walk_ri_exact(self, formula, args): 
        assert formula is not None
        sym = self._new_symbol()

        if self.dplus:
            self.write("(declare-const %s %s)\n" % (sym+'.l', REAL))
            self.write("(declare-const %s %s)\n" % (sym+'.u', REAL))
            self.write("(assert (= %s %s))\n" % (sym+'.l', sym+'.u'))
        else:
            self.write("(declare-const %s %s)\n" % (sym, REAL))

        self.write("(declare-const %s.p_nan %s)\n" % (sym, BOOL))
        self.write("(assert (not %s))\n" % (sym+'.p_nan'))
    
        if self.dplus:
            self.write("(assert (= %s (ri.exact.l" % (sym+'.l'))
        else:
            self.write("(assert (= %s (ri.exact.l" % sym)

        self.write(" %s" % args[1])
        self.write(")))\n")
    
        return sym

def to_smtlib(formula):
    """Returns a Smt-Lib string representation of the formula.

    The daggify parameter can be used to switch from a linear-size
    representation that uses 'let' operators to represent the
    formula as a dag or a simpler (but possibly exponential)
    representation that expands the formula as a tree.

    See :py:class:`SmtPrinter`
    """
    buf = cStringIO()
    p = SmtDecomposePrinter(buf) 
    p.printer(formula)
    res = buf.getvalue()
    buf.close()
    return res

# eof
