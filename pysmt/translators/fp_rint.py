#
#  Copyright 2021 D. Ishii
#
"""The FpRintTranslator is used to convert FloatingPoint formulae into those of RealIntervals. 
"""

import warnings

from fractions import Fraction

import pysmt.walkers
import pysmt.typing as types
import pysmt.operators as op
import pysmt.smtlib.commands as smtcmd
from pysmt.environment import get_env
from pysmt.logics import QF_LRIA
from pysmt.smtlib.script import SmtLibScript, SmtLibCommand
from pysmt.rewritings import nnf
from pysmt.exceptions import (PysmtValueError, UnknownSmtLibCommandError)

class FpRintTranslator(pysmt.walkers.IdentityDagWalker):
    def __init__(self, dplus=False, decompose=False, doSetLogic=True):
        pysmt.walkers.IdentityDagWalker.__init__(self, env=get_env(), invalidate_memoization=True)
        self.mgr = get_env().formula_manager
        self.dplus = dplus 
        self.decompose = decompose
        self.doSetLogic = doSetLogic
        self.precs = []

    def check_prec(self, eb, sb):
        for i in range(len(self.precs)):
            eb1,sb1 = self.precs[i]
            if eb == eb1 and sb == sb1:
                return i
        self.precs.append((eb,sb))
        return len(self.precs) - 1

    def processF(self, formula):
        """Translate formulae in FloatingPoint into those in RealInterval.
        """
        ty = get_env().stc.get_type(formula)
        if ty.is_bool_type():
            #print(formula)
            formula = nnf(formula, get_env())
        return self.walk(formula)

    def gen_constraints(self, symb, p):
        constr = []

        #rel = self.mgr.Not(self.mgr.RIIsPinf(self.mgr.Int(0), symb))
        #constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
        #rel = self.mgr.Not(self.mgr.RIIsNinf(self.mgr.Int(0), symb))
        #constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )

        # FIXME
        #rel = self.mgr.Not(self.mgr.RIIsNaI(symb))
        if self.dplus:
            rel = self.mgr.Implies( self.mgr.RIIsNaI(symb), 
                    #self.mgr.And(
                    #  self.mgr.Equals( self.mgr.RILower(symb), 
                    #                   self.mgr.RILower(self.mgr.RIEntire(self.mgr.Int(p))) ),
                    #  self.mgr.Equals( self.mgr.RIUpper(symb), 
                    #                   self.mgr.RIUpper(self.mgr.RIEntire(self.mgr.Int(p))) ))
                    self.mgr.RIIS(symb, self.mgr.RIEntire(self.mgr.Int(p)))
                  )
        else:
            rel = self.mgr.Implies( self.mgr.RIIsNaI(symb), 
                    self.mgr.Equals(symb, self.mgr.RINaI(self.mgr.Int(p))) )
        constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )

        #if self.decompose:
        #    return constr

        #if self.dplus:
        #    # l = r_dn(u)
        #    rel = self.mgr.Equals(self.mgr.RILower(symb), self.mgr.Function(
        #                self.mgr.Symbol('ri.r_dn', types.FunctionType(types.REAL, [types.REAL])), 
        #                [self.mgr.RIUpper(symb)] ))
        #    constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )

        #if self.dplus:
        #    # l <= u
        #    rel = self.mgr.LE(self.mgr.RILower(symb), self.mgr.RIUpper(symb))
        #    constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
        #else:
        #    # l = u
        #    rel = self.mgr.Equals(self.mgr.RILower(symb), self.mgr.RIUpper(symb))
        #    constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )

        ## -max_value <= l/u
        #rel = self.mgr.LE( 
        #        self.mgr.Times( self.mgr.Real(-1),
        #                        self.mgr.Symbol('ri.max_value', types.REAL) ),
        #        self.mgr.RILower(symb) )
        #constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
        #rel = self.mgr.LE( 
        #        self.mgr.Times( self.mgr.Real(-1),
        #                        self.mgr.Symbol('ri.max_value', types.REAL) ),
        #        self.mgr.RIUpper(symb) )
        #constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
    
        ## l/u <= max_value
        #rel = self.mgr.LE( self.mgr.RILower(symb), 
        #        self.mgr.Symbol('ri.max_value', types.REAL) )
        #constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
        #rel = self.mgr.LE( self.mgr.RIUpper(symb), 
        #        self.mgr.Symbol('ri.max_value', types.REAL) )
        #constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
    
        return constr

    def processC(self, command):
        """Translate FloatingPoint formulae in a command into RealInterval formulae.
        """
    
        if command.name == smtcmd.ASSERT:
            return [SmtLibCommand(smtcmd.ASSERT, [self.processF(command.args[0])])]
    
        elif command.name == smtcmd.GET_VALUE:
            es = []
            for a in command.args:
                es.append( self.processF(a) )
            return [SmtLibCommand(smtcmd.GET_VALUE, es)]
    
        elif command.name == smtcmd.SET_LOGIC:
            if self.doSetLogic:
                return [SmtLibCommand(smtcmd.SET_LOGIC, [QF_LRIA])]
            else:
                return []

        elif command.name in [smtcmd.DECLARE_FUN, smtcmd.DECLARE_CONST]:
            es = []
            constr = []
            for a in command.args:
                if a.symbol_type().is_fp_type():
                    p = self.check_prec(a.fp_eb(), a.fp_sb())
                    symb = self.mgr._create_symbol(a.symbol_name(), types.RIntType(p))
                    es.append(symb)

                    #print("%s : RInt(%d)" % (a.symbol_name(), p))

                    # Add constraints for "normal" values.
                    constr.extend(self.gen_constraints(symb, p))

                elif a.symbol_type().is_function_type():
                    rt = a.symbol_type().return_type
                    if rt.is_fp_type():
                        p = self.check_prec(rt.exp_width, rt.sig_width)
                        rt = types.RIntType(p)

                    elif rt.is_rm_type():
                        # Ignore RM vars.
                        continue
    
                    pts = []
                    for t in a.symbol_type().param_types:
                        if t.is_fp_type():
                            p = self.check_prec(t.exp_width, t.sig_width)
                            pts.append(types.RIntType(p))
                        else:
                            pts.append(t)
    
                    symb = self.mgr._create_symbol(a.symbol_name(), types.FunctionType(rt, pts))

                    #print("%s : RInt(%d)" % (a.symbol_name(), p))

                    if rt.is_ri_type() and not pts:
                        p = self.check_prec(rt.exp_width, rt.sig_width)
                        constr.extend(self.gen_constraints(symb, p))

                    es.append(symb)

                else:
                    es.append(a)

            return [SmtLibCommand(command.name, es)] + constr

        elif command.name == smtcmd.DEFINE_FUN:
            es = []
            es.append(command.args[0])

            ps = []
            for a in command.args[1]:
                if a.symbol_type().is_fp_type():
                    p = self.check_prec(a.fp_eb(), a.fp_sb())
                    ps.append(self.mgr._create_symbol(a.symbol_name(), types.RIntType(p)))
                else:
                    ps.append(a)
            es.append(ps)

            rt = command.args[2]
            if rt.is_fp_type():
                p = self.check_prec(rt.exp_width, rt.sig_width)
                es.append(types.RIntType(p))
            elif rt.is_rm_type():
                # Ignore RM-valued functions.
                return []
            else:
                es.append(rt)

            es.append( self.processF(command.args[3]) )

            return [SmtLibCommand(smtcmd.DEFINE_FUN, es)]
    
        elif command.name == smtcmd.DEFINE_SORT:
            #raise UnknownSmtLibCommandError(command.name)
            return []

        else:
            return [command]

    def process(self, script):
        """Translate a script with vocabularies in FloatingPoint into a RealInterval script.
        """
    
        res = SmtLibScript()
        for cmd in script.commands:
            for c in self.processC(cmd):
                res.add_command(c)
    
        return self.precs, res

    # Walker handlers.

    def walk_not(self, formula, args, **kwargs):
        sf_as = args[0].args()
        if args[0].node_type() == op.RI_GEQ:
            return self.mgr.RIGEQN(sf_as[0], sf_as[1])
        elif args[0].node_type() == op.RI_GT:
            return self.mgr.RIGTN(sf_as[0], sf_as[1])
        elif (args[0].node_type() == op.RI_FPEQ or args[0].node_type() == op.RI_FPIS):
            sf_as[0].ri_set_alias(False)
            sf_as[1].ri_set_alias(False)

            #f1 = self.mgr.RIGTN(sf_as[0], sf_as[1])
            #f2 = self.mgr.RIGTN(sf_as[1], sf_as[0])
            #return self.mgr.Or(f1, f2)
            return self.mgr.RIFPEQN(sf_as[0], sf_as[1])
        elif (self.dplus and ( args[0].node_type() == op.RI_EQ or 
                               args[0].node_type() == op.RI_IS )):
            sf_as[0].ri_set_alias(False)
            sf_as[1].ri_set_alias(False)

            #f1 = self.mgr.RIGT(sf_as[0], sf_as[1])
            #f2 = self.mgr.RIGT(sf_as[1], sf_as[0])
            #return self.mgr.Or(f1, f2)
            return self.mgr.RINEQ(sf_as[0], sf_as[1])
        elif (not self.dplus and ( args[0].node_type() == op.RI_EQ or
                                   args[0].node_type() == op.RI_IS )):
            sf_as[0].ri_set_alias(False)
            sf_as[1].ri_set_alias(False)

            #f1 = self.mgr.RIGTN(sf_as[0], sf_as[1])
            #f2 = self.mgr.RIGTN(sf_as[1], sf_as[0])
            #return self.mgr.Or(f1, f2)
            return self.mgr.RINEQ(sf_as[0], sf_as[1])
        else:
            return self.mgr.Not(args[0])

    def walk_symbol(self, formula, args, **kwargs):
        ty = formula.symbol_type() 
        if ty.is_fp_type():
            p = self.check_prec(ty.exp_width, ty.sig_width)
            return self.mgr.Symbol(formula.symbol_name(), types.RIntType(p))

        elif ty.is_function_type():
            rt = ty.return_type
            if rt.is_fp_type():
                p = self.check_prec(rt.exp_width, rt.sig_width)
                rt = types.RIntType(p)

            pts = []
            for t in ty.param_types:
                if t.is_fp_type():
                    p = self.check_prec(t.exp_width, t.sig_width)
                    pts.append(types.RIntType(p))
                else:
                    pts.append(t)
            return self.mgr.Symbol(formula.symbol_name(), types.FunctionType(rt, pts))

        else:
            return self.mgr.Symbol(formula.symbol_name(),
                                   formula.symbol_type())

    @staticmethod
    def eval_fp_constant(fp_datum):
        sign = fp_datum[0].bv_unsigned_value()
        ev = fp_datum[1].bv_unsigned_value()
        eb = fp_datum[1].bv_width()
        sv = fp_datum[2].bv_unsigned_value()
        sb = fp_datum[2].bv_width()

        bias = 2**(eb-1) - 1

        if ev == 0:
            e = 2 - 2**(eb-1)
            is_normal = False
        elif ev == 2**eb - 1:
            #e = 2**(eb-1) - 1
            if sv == 0:
                return (Fraction(), sign == 0, sign == 1, False)
            else:
                return (Fraction(), False, False, True)
        else:
            e = ev - bias
            is_normal = True

        if e >= 0:
            num = 2**e
            denom = 1
        else:
            num = 1
            denom = 2**(-e)

        if is_normal:
            num *= (2**sb + sv)
        else:
            num *= sv

        denom *= 2**sb

        num *= (1-2*sign)

        #return (1-2*sign) * s * 2**e
        return (Fraction(num, denom), False, False, False)

    def walk_fp_constant(self, formula, args, **kwargs):
        eb = formula.fp_eb()
        sb = formula.fp_sb()
        p = self.check_prec(eb, sb)

        v, is_pinf, is_ninf, is_nan = FpRintTranslator.eval_fp_constant(args)
        if is_pinf:
            return self.mgr.RIPInf(self.mgr.Int(p))
        elif is_ninf:
            return self.mgr.RINInf(self.mgr.Int(p))
        elif is_nan:
            return self.mgr.RINaI(self.mgr.Int(p))
        else:
            return self.mgr.RIExact(self.mgr.Int(p), self.mgr.Real(v))

    def walk_equals(self, formula, args, **kwargs):
        #ty = get_env().stc.get_type(args[0])
        if args[0].get_type().is_ri_type():
            # Check for assignment cases.
            if self.dplus:
                if args[0].is_symbol() and not args[1].is_symbol():
                    args[0].ri_set_alias(True)
                    return self.mgr.RIIS(args[0], args[1])
                elif not args[0].is_symbol() and args[1].is_symbol():
                    args[1].ri_set_alias(True)
                    return self.mgr.RIIS(args[0], args[1])

            return self.mgr.RIEQ(args[0], args[1])
        else:
            return self.mgr.Equals(args[0], args[1])

    def walk_fp_eq(self, formula, args, **kwargs):
        #return self.walk_equals(formula, args)
        if args[0].get_type().is_ri_type():
            if self.dplus:
                # Check for assignment cases.
                if args[0].is_symbol() and not args[1].is_symbol():
                    args[0].ri_set_alias(True)
                    return self.mgr.RIFPIS(args[0], args[1])
                elif not args[0].is_symbol() and args[1].is_symbol():
                    args[1].ri_set_alias(True)
                    return self.mgr.RIFPIS(args[1], args[0])

            return self.mgr.RIFPEQ(args[0], args[1])
        else:
            return self.mgr.Equals(args[0], args[1])

    def walk_fp_leq(self, formula, args, **kwargs):
        return self.mgr.RIGEQ(args[1], args[0])

    def walk_fp_lt(self, formula, args, **kwargs):
        return self.mgr.RIGT(args[1], args[0])

    def walk_ite(self, formula, args, **kwargs):
        #if self.dplus:
        #    return self.mgr.RIITEP(args[0], args[1], args[2])
        #else:
        #    return self.mgr.RIITEN(args[0], args[1], args[2])
        #ty = get_env().stc.get_type(formula)
        ty = get_env().stc.get_type(args[1])
        if ty.is_ri_type():
            raise PysmtValueError("ite expressions of sort RInt are not supported.")

    def walk_fp_abs(self, formula, args, **kwargs):
        return self.mgr.RIAbs(args[0])

    def walk_fp_neg(self, formula, args, **kwargs):
        return self.mgr.RINeg(args[0])

    def walk_fp_add(self, formula, args, **kwargs):
        return self.mgr.RIAdd(args[1], args[2])

    def walk_fp_sub(self, formula, args, **kwargs):
        return self.mgr.RISub(args[1], args[2])

    def walk_fp_mul(self, formula, args, **kwargs):
        if args[1].node_type() == op.RI_EXACT and \
           args[1].args()[0].is_constant(types.REAL) and args[1].args()[0].constant_value == -1:
            return self.mgr.RINeg(args[2])
        elif args[2].node_type() == op.RI_EXACT and \
             args[2].args()[0].is_constant(types.REAL) and args[2].args()[0].constant_value() == -1:
            return self.mgr.RINeg(args[1])
        else:
            return self.mgr.RIMul(args[1], args[2])

    def walk_fp_div(self, formula, args, **kwargs):
        return self.mgr.RIDiv(args[1], args[2])

    def walk_fp_fma(self, formula, args, **kwargs):
        #raise PysmtValueError("operator fp.fma is not supported.")
        return self.mgr.RIAdd(self.mgr.RIMul(args[1], args[2]), args[3])

    def walk_fp_sqrt(self, formula, args, **kwargs):
        raise PysmtValueError("operator fp.sqrt is not supported.")

    def walk_fp_rem(self, formula, args, **kwargs):
        raise PysmtValueError("operator fp.rem is not supported.")

    def walk_fp_round_to_integral(self, formula, args, **kwargs): 
        raise PysmtValueError("operator fp.roundToIntegral is not supported.")

    def walk_fp_min(self, formula, args, **kwargs): 
        raise PysmtValueError("operator fp.min is not supported.")
    def walk_fp_max(self, formula, args, **kwargs): 
        raise PysmtValueError("operator fp.max is not supported.")

    def walk_fp_is_negative(self, formula, args, **kwargs):
        return self.mgr.RIGEQ(args[0], self.mgr.RIZero())

    def walk_fp_is_positive(self, formula, args, **kwargs):
        return self.mgr.RIGEQ(self.mgr.RIZero(), args[0])

    #def walk_fp_is_normal(self, formula, args): 
    #    return self.walk_nary(formula, args, "fp.isNormal")
    #def walk_fp_is_subnormal(self, formula, args): 
    #    return self.walk_nary(formula, args, "fp.isSubnormal")
    #def walk_fp_is_zero(self, formula, args): 
    #    return self.walk_nary(formula, args, "fp.isZero")
    #def walk_fp_is_infinite(self, formula, args): 
    #    return self.walk_nary(formula, args, "fp.isInfinite")
    #def walk_fp_is_nan(self, formula, args): 
    #    return self.walk_nary(formula, args, "fp.isNaN")
    #    return self.mgr.RIIsNaI(self

    def walk_bv_to_fp(self, formula, args):
        eb = formula.fp_eb()
        sb = formula.fp_sb()
        bs = args[0].bv_bin_str()
        datum = (self.mgr.BV(bs[0], 1), self.mgr.BV(bs[1:1+eb], eb), self.mgr.BV(bs[1+eb:], sb-1))
        v, is_pinf, is_ninf, is_nan = FpRintTranslator.eval_fp_constant(datum)
        p = self.check_prec(eb, sb)
        if is_pinf:
            return self.mgr.RIPInf(self.mgr.Int(p))
        elif is_ninf:
            return self.mgr.RINInf(self.mgr.Int(p))
        elif is_nan:
            return self.mgr.RINaI(self.mgr.Int(p))
        else:
            return self.mgr.RIExact(self.mgr.Int(p), self.mgr.Real(v))
    def walk_fp_to_fp(self, formula, args):
        #return "((_ to_fp %d %d) %s %s)" % (formula.fp_eb(), formula.fp_sb(), args[0], args[1])
        p = self.check_prec(formula.fp_eb(), formula.fp_sb())
        return self.mgr.RIToRi(self.mgr.Int(p), args[1])
    def walk_real_to_fp(self, formula, args):
        p = self.check_prec(formula.fp_eb(), formula.fp_sb())
        # TODO: ri.exact can be used when possible.
        return self.mgr.RealToRi(self.mgr.Int(p), args[1])
    def walk_int_to_fp(self, formula, args):
        p = self.check_prec(formula.fp_eb(), formula.fp_sb())
        # TODO
        return self.mgr.RealToRi(self.mgr.Int(p), self.mgr.Real(args[0].bv_signed_value()))
    def walk_uint_to_fp(self, formula, args):
        #return "((_ to_fp_unsigned %d %d) %s %s)" % (formula.fp_eb(), formula.fp_sb(), args[0], args[1])
        p = self.check_prec(formula.fp_eb(), formula.fp_sb())
        # TODO
        return self.mgr.RealToRi(self.mgr.Int(p), self.mgr.Real(args[0].bv_unsigned_value()))

    def walk_fp_to_ubv(self, formula, args):
        #return "((_ fp.to_ubv %d) %s %s)" % (formula.bv_width(), args[0], args[1])
        raise PysmtValueError("operator fp.to_ubv is not supported.")
    def walk_fp_to_sbv(self, formula, args):
        #return "((_ fp.to_sbv %d) %s %s)" % (formula.bv_width(), args[0], args[1])
        raise PysmtValueError("operator fp.to_sbv is not supported.")
    def walk_fp_to_real(self, formula, args): 
        #return self.walk_nary(formula, args, "fp.to_real")
        raise PysmtValueError("operator fp.to_real is not supported.")

# End of the Translator class.

# EOF
