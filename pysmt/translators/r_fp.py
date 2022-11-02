#
#  Copyright 2021 D. Ishii
#
"""The RFpTranslator is used to convert Reals formulae into those of FloatingPoint. 
"""

import warnings

import random

import pysmt.walkers
import pysmt.typing as types
import pysmt.operators as op
import pysmt.smtlib.commands as smtcmd
from pysmt.environment import get_env
from pysmt.logics import QF_FP
from pysmt.smtlib.script import SmtLibScript, SmtLibCommand
from pysmt.rewritings import nnf

class RFpTranslator(pysmt.walkers.IdentityDagWalker):
    def __init__(self, bi_eq=True, eb=11, sb=53, rm=op.FP_RNE, rmn=0, doRewrite=False, doSetLogic=True, doSkipToFp=False):
        pysmt.walkers.IdentityDagWalker.__init__(self, env=get_env(), invalidate_memoization=True)
        self.mgr = get_env().formula_manager
        self.bi_eq = bi_eq
        self.eb = eb
        self.sb = sb
        if rm == op.FP_RNE:
            self.rm = self.mgr.FPRNE()
        elif rm == op.FP_RNA:
            self.rm = self.mgr.FPRNA()
        elif rm == op.FP_RTP:
            self.rm = self.mgr.FPRTP()
        elif rm == op.FP_RTN:
            self.rm = self.mgr.FPRTN()
        elif rm == op.FP_RTZ:
            self.rm = self.mgr.FPRTZ()
        self.rmn = rmn
        self.rm_count = 0
        self.doRewrite = doRewrite
        self.doSetLogic = doSetLogic
        self.doSkipToFp = doSkipToFp

    def processF(self, formula):
        """Translate formulae in Reals into those in FloatingPoint.
        """
        if self.doRewrite:
            formula = nnf(formula, get_env())
        return self.walk(formula)

    def gen_constraints(self, symb):
        constr = []

        # For 2nd xp...
        # rel = self.mgr.Not(self.mgr.FPIsInfinite(symb))
        # constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
        rel = self.mgr.Not(self.mgr.FPIsNaN(symb))
        constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )

        return constr

    def processC(self, command):
        """Translate Reals formulae in a command into FloatingPoint formulae.
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
                cs = [SmtLibCommand(smtcmd.SET_LOGIC, [QF_FP])]
            else:
                cs = []

            if self.rmn > 0:
                for i in range(self.rmn):
                    es = [self.mgr._create_symbol("_rm%d" % i, types.RM)]
                    #cs.append( SmtLibCommand(smtcmd.DECLARE_CONST, es) )
                    cs.append( SmtLibCommand(smtcmd.DECLARE_FUN, es) )
            elif self.rmn < 0:
                es = [self.mgr._create_symbol("_rm0", types.RM)]
                #cs.append( SmtLibCommand(smtcmd.DECLARE_CONST, es) )
                cs.append( SmtLibCommand(smtcmd.DECLARE_FUN, es) )

            return cs

        elif command.name == smtcmd.SET_INFO:
            return []

        elif command.name in [smtcmd.DECLARE_FUN, smtcmd.DECLARE_CONST]:
            es = []
            constr = []
            for a in command.args:
                if a.symbol_type() == types.REAL:
                    sn = command.args[0].symbol_name()
                    if sn == "pi":
                        sn = "_pi"
                    symb = self.mgr._create_symbol(sn, types.FPType(self.eb, self.sb) )
                    es.append(symb)

                    # Add constraints for "normal" values.
                    constr.extend(self.gen_constraints(symb))

                elif a.symbol_type().is_function_type():
                    rt = a.symbol_type().return_type
                    if rt == types.REAL:
                        rt = types.FPType(self.eb, self.sb)
    
                    pts = []
                    for t in a.symbol_type().param_types:
                        if t == types.REAL:
                            pts.append(types.FPType(self.eb, self.sb))
                        else:
                            pts.append(t)
    
                    symb = self.mgr._create_symbol(a.symbol_name(), types.FunctionType(rt, pts))

                    if rt == types.FPType(self.eb, self.sb) and not pts:
                        constr.extend(self.gen_constraints(symb))

                    es.append(symb)
                else:
                    es.append(a)

            return [SmtLibCommand(command.name, es)] + constr

        elif command.name == smtcmd.DEFINE_FUN:
            es = []
            es.append(command.args[0])
            es.append(command.args[1])
            #es.append(command.args[2])
            es.append(types.FPType(self.eb, self.sb))
            es.append( self.processF(command.args[3]) )
            return [SmtLibCommand(smtcmd.DEFINE_FUN, es)]
    
        else:
            return [command]

    def process(self, script):
        """Translate a script with vocabularies in Reals into a FloatingPoint script.
        """
    
        res = SmtLibScript()
        for cmd in script.commands:
            for c in self.processC(cmd):
                res.add_command(c)
    
        return res

    def get_rm(self):
        self.rm_count += 1
        if self.rmn > 0:
            if self.rmn >= self.rm_count:
                return self.mgr.Symbol("_rm%d" % (self.rm_count-1), types.RM)
            else:
                i = random.randrange(self.rmn)
                return self.mgr.Symbol("_rm%d" % i, types.RM)
        elif self.rmn < 0:
            return self.mgr.Symbol("_rm0", types.RM)
        else:
            return self.rm 

    def reset_rm(self):
        self.rmn = self.rm_count
        self.rm_count = 0

    # Walker handlers.

    def walk_symbol(self, formula, args, **kwargs):
        #return self.mgr.Symbol(formula.symbol_name(),
        #                       #formula.symbol_type())
        if formula.symbol_type() == types.REAL:
            sn = formula.symbol_name()
            if sn == "pi":
                sn = "_pi"
            return self.mgr.Symbol(sn,
                                   types.FPType(self.eb, self.sb))
            #return self.mgr._create_symbol(formula.symbol_name(), 
            #                               types.FPType(self.eb, self.sb))
        else:
            return self.mgr.Symbol(formula.symbol_name(),
                                   formula.symbol_type())

    def walk_real_constant(self, formula, args, **kwargs):
        # Colibri does not support to use an RM variable here.
        if self.doSkipToFp:
            return self.mgr.FPToFp(self.eb, self.sb, self.rm, formula)
        else:
            return self.mgr.FPToFp(self.eb, self.sb, self.get_rm(), formula)

    def walk_equals(self, formula, args, **kwargs):
        ty = get_env().stc.get_type(args[0])
        if self.bi_eq and ty.is_fp_type():
            return self.mgr.FPEQ(args[0], args[1])
        else:
            return self.mgr.Equals(args[0], args[1])

    def walk_le(self, formula, args, **kwargs):
        return self.mgr.FPLEQ(args[0], args[1])

    def walk_lt(self, formula, args, **kwargs):
        return self.mgr.FPLT(args[0], args[1])

    def walk_plus(self, formula, args, **kwargs):
        #return self.mgr.FPAdd(self.get_rm(), args[0], args[1])
        s = args[0]
        for s1 in args[1:]:
            s = self.mgr.FPAdd(self.get_rm(), s, s1)
        return s

    def walk_minus(self, formula, args, **kwargs):
        if len(args) == 2 and len(args[0].args()) >= 2 and \
           args[0].arg(1).is_constant(types.REAL) and args[0].arg(1).constant_value == 0:
            return self.mgr.FPNeg(args[1])
        else:
            #return self.mgr.FPSub(self.get_rm(), args[0], args[1])
            s = args[0]
            for s1 in args[1:]:
                s = self.mgr.FPSub(self.get_rm(), s, s1)
            return s

    def walk_times(self, formula, args, **kwargs):
        if len(args) == 2 and len(args[0].args()) >= 2 and \
           args[0].arg(1).is_constant(types.REAL) and args[0].arg(1).constant_value == -1:
            return self.mgr.FPNeg(args[1])
        elif len(args) == 2 and len(args[1].args()) >= 2 and \
            args[1].arg(1).is_constant(types.REAL) and args[1].arg(1).constant_value() == -1:
            return self.mgr.FPNeg(args[0])
        else:
            #return self.mgr.FPMul(self.get_rm(), args[0], args[1])
            s = args[0]
            for s1 in args[1:]:
                s = self.mgr.FPMul(self.get_rm(), s, s1)
            return s

    def walk_div(self, formula, args, **kwargs):
        #return self.mgr.FPDiv(self.get_rm(), args[0], args[1])
        s = args[0]
        for s1 in args[1:]:
            s = self.mgr.FPDiv(self.get_rm(), s, s1)
        return s

    def walk_pow(self, formula, args, **kwargs):
        raise UndefinedSymbolError(self.get_rm(), op.POW)

# End of the Translator class.

# EOF
