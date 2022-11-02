#
#  Copyright 2021 D. Ishii
#
"""The RRintTranslator is used to convert Reals formulae into those of RealIntervals. 
"""

import warnings

import math

import pysmt.walkers
import pysmt.typing as types
import pysmt.operators as op
import pysmt.smtlib.commands as smtcmd
from pysmt.environment import get_env
from pysmt.logics import QF_LRIA
from pysmt.smtlib.script import SmtLibScript, SmtLibCommand
#from pysmt.smtlib.script_rint import rint_eb, rint_sb, config
from pysmt.rewritings import nnf
from pysmt.exceptions import PysmtValueError

class RRintTranslator(pysmt.walkers.IdentityDagWalker):
    def __init__(self, dplus=False, bi_eq=True, eb=11, sb=53, decompose=False, doSetLogic=True):
        pysmt.walkers.IdentityDagWalker.__init__(self, env=get_env(), invalidate_memoization=True)
        self.mgr = get_env().formula_manager
        self.dplus = dplus 
        self.bi_eq = bi_eq
        #config(eb, sb)
        self.eb = eb
        self.sb = sb
        self.decompose = decompose
        self.doSetLogic = doSetLogic

    def processF(self, formula):
        """Translate formulae in Reals into those in RealInterval.
        """
        ty = get_env().stc.get_type(formula)
        if ty.is_bool_type():
            formula = nnf(formula, get_env())
        return self.walk(formula)

    def gen_constraints(self, symb):
        constr = []

        # For 2nd xp...
        # # TODO: Many of the constraints might be unnatural to assume.
        # rel = self.mgr.Not(self.mgr.RIIsPinf(symb))
        # constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
        # rel = self.mgr.Not(self.mgr.RIIsNinf(symb))
        # constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
        # if self.dplus and self.decompose:
        #     rel = self.mgr.Not(self.mgr.RIIsNaI(symb))
        #     constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
        rel = self.mgr.Not(self.mgr.RIIsNaI(symb))
        constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )

        #if self.decompose:
        #    return constr

        #if self.dplus:
        #    # Asserted in script.py.
        #    #if symb.ri_is_alias():
        #    #    # l <= r_dn(u)
        #    #    rel = self.mgr.LE(self.mgr.RILower(symb), self.mgr.Function(
        #    #                self.mgr.Symbol('ri.r_dn', types.FunctionType(types.REAL, [types.REAL])), 
        #    #                [self.mgr.RIUpper(symb)] ))
        #    #    constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )

        #    # l <= u
        #    rel = self.mgr.LE(self.mgr.RILower(symb), self.mgr.RIUpper(symb))
        #    constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
        #else:
        #    # l = u
        #    rel = self.mgr.Equals(self.mgr.RILower(symb), self.mgr.RIUpper(symb))
        #    constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )

        # # -max_value <= l/u
        # rel = self.mgr.LE( 
        #         self.mgr.Times( self.mgr.Real(-1),
        #                         self.mgr.Symbol('ri.max_value', types.REAL) ),
        #         self.mgr.RILower(symb) )
        # constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
        # rel = self.mgr.LE( 
        #         self.mgr.Times( self.mgr.Real(-1),
        #                         self.mgr.Symbol('ri.max_value', types.REAL) ),
        #         self.mgr.RIUpper(symb) )
        # constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
    
        # # l/u <= max_value
        # rel = self.mgr.LE( self.mgr.RILower(symb), 
        #         self.mgr.Symbol('ri.max_value', types.REAL) )
        # constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
        # rel = self.mgr.LE( self.mgr.RIUpper(symb), 
        #         self.mgr.Symbol('ri.max_value', types.REAL) )
        # constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
    
        return constr

    def processC(self, command):
        """Translate Reals formulae in a command into RealInterval formulae.
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
                if a.symbol_type() == types.REAL:
                    symb = self.mgr._create_symbol(a.symbol_name(), types.RINT)
                    es.append(symb)

                    # Add constraints for "normal" values.
                    constr.extend(self.gen_constraints(symb))

                elif a.symbol_type().is_function_type():
                    rt = a.symbol_type().return_type
                    if rt == types.REAL:
                        rt = types.RINT
    
                    pts = []
                    for t in a.symbol_type().param_types:
                        if t == types.REAL:
                            pts.append(types.RINT)
                        else:
                            pts.append(t)
    
                    symb = self.mgr._create_symbol(a.symbol_name(), types.FunctionType(rt, pts))

                    if rt == types.RINT and not pts:
                        constr.extend(self.gen_constraints(symb))

                    es.append(symb)

                else:
                    es.append(a)

            return [SmtLibCommand(command.name, es)] + constr

        elif command.name == smtcmd.DEFINE_FUN:
            es = []
            es.append(command.args[0])

            ps = []
            for a in command.args[1]:
                if a.symbol_type() == types.REAL:
                    ps.append(self.mgr._create_symbol(a.symbol_name(), types.RINT))
                else:
                    ps.append(a)
            es.append(ps)

            if command.args[2] == types.REAL:
                es.append(types.RINT)
            else:
                es.append(command.args[2])

            es.append( self.processF(command.args[3]) )

            return [SmtLibCommand(smtcmd.DEFINE_FUN, es)]
    
        else:
            return [command]

    def process(self, script):
        """Translate a script with vocabularies in Reals into a RealInterval script.
        """
    
        res = SmtLibScript()
        for cmd in script.commands:
            for c in self.processC(cmd):
                res.add_command(c)
    
        return res

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

            #f1 = self.mgr.RIGEQN(sf_as[0], sf_as[1])
            #f2 = self.mgr.RIGEQN(sf_as[1], sf_as[0])
            #return self.mgr.Or(f1, f2)
            return self.mgr.RIFPEQN(sf_as[0], sf_as[1])
        elif (self.dplus and ( args[0].node_type() == op.RI_EQ or 
                               args[0].node_type() == op.RI_IS )):
            sf_as[0].ri_set_alias(False)
            sf_as[1].ri_set_alias(False)

            #f1 = self.mgr.RIGEQN(sf_as[0], sf_as[1])
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
        if formula.symbol_type() == types.REAL:
            return self.mgr.Symbol(formula.symbol_name(), types.RINT)

        elif formula.symbol_type().is_function_type():
            rt = formula.symbol_type().return_type
            if rt == types.REAL:
                rt = types.RINT

            pts = []
            for t in formula.symbol_type().param_types:
                if t == types.REAL:
                    pts.append(types.RINT)
                else:
                    pts.append(t)
            return self.mgr.Symbol(formula.symbol_name(), types.FunctionType(rt, pts))

        else:
            return self.mgr.Symbol(formula.symbol_name(),
                                   formula.symbol_type())

    def is_representable(self, num, denom):
        base = 2
        e = self.eb
        p = self.sb

        l2 = math.log2(denom)
        if not (denom == 1 or math.ceil(l2) == math.floor(l2)):
            return False

        while not (num <= base**p - 1 and denom <= base**(p-e)):
            if num > base**p - 1 and denom > base**(p-e):
                return False
            elif num > base**p - 1:
                if num % base != 0:
                    return False
                else:
                    num /= base
                    denom *= base
            else:
                if denom % base != 0:
                    return False
                else:
                    num *= base
                    denom /= base
        return True

    def walk_real_constant(self, formula, args, **kwargs):
        v = formula.constant_value()
        # The prec id will be given when type checking.
        if v == 0:
            return self.mgr.RIZero(self.mgr.Int(-1))
        elif self.is_representable(v.numerator, v.denominator):
            return self.mgr.RIExact(self.mgr.Int(-1), formula)
        else:
            return self.mgr.RealToRi(self.mgr.Int(-1), formula)

    def walk_equals(self, formula, args, **kwargs):
        ty = get_env().stc.get_type(args[0])
        if self.bi_eq and ty.is_ri_type():
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

    def walk_le(self, formula, args, **kwargs):
        return self.mgr.RIGEQ(args[1], args[0])

    def walk_lt(self, formula, args, **kwargs):
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

    def walk_plus(self, formula, args, **kwargs):
        #return self.mgr.RIAdd(args[0], args[1])
        s = args[0]
        for s1 in args[1:]:
            s = self.mgr.RIAdd(s, s1)
        return s

    def walk_minus(self, formula, args, **kwargs):
        if len(args) == 2 and len(args[0].args()) >= 2 and \
           args[0].node_type() == op.RI_EXACT and \
           args[0].arg(1).is_constant(types.REAL) and args[0].arg(1).constant_value == 0:
            return self.mgr.RINeg(args[1])
        else:
            #return self.mgr.RISub(args[0], args[1])
            s = args[0]
            for s1 in args[1:]:
                s = self.mgr.RISub(s, s1)
            return s

    def walk_times(self, formula, args, **kwargs):
        if len(args) == 2 and len(args[0].args()) >= 2 and \
           args[0].node_type() == op.RI_EXACT and \
           args[0].arg(1).is_constant(types.REAL) and args[0].arg(1).constant_value == -1:
            return self.mgr.RINeg(args[1])
        elif len(args) == 2 and len(args[1].args()) >= 2 and \
             args[1].node_type() == op.RI_EXACT and \
             args[1].arg(1).is_constant(types.REAL) and args[1].arg(1).constant_value() == -1:
            return self.mgr.RINeg(args[0])
        else:
            #return self.mgr.RIMul(args[0], args[1])
            s = args[0]
            for s1 in args[1:]:
                s = self.mgr.RIMul(s, s1)
            return s

    def walk_div(self, formula, args, **kwargs):
        #return self.mgr.RIDiv(args[0], args[1])
        s = args[0]
        for s1 in args[1:]:
            s = self.mgr.RIDiv(s, s1)
        return s

    def walk_pow(self, formula, args, **kwargs):
        #return self.mgr.Pow(args[0], args[1])
        raise UndefinedSymbolError(self.rm, op.POW)

# End of the Translator class.

# EOF
