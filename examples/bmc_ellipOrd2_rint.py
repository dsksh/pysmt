import sys

from pysmt.environment import get_env
from pysmt.shortcuts import Symbol, Not, And, Or, Implies
from pysmt.shortcuts import Equals, LE
from pysmt.shortcuts import Int, Real, Plus, Minus, Times, Div
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import REAL, INT, BOOL, RINT, FunctionType
import pysmt.logics as logics
import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import SmtLibScript
#from pysmt.smtlib.script_rint import config
from bmc_utils import get_arg_parser, def_alias, decl_const, serialize

def def_script(args):
    #config(args.eb, args.sb)
    mgr = get_env().formula_manager

    script = SmtLibScript()

    script.add(name=smtcmd.SET_LOGIC, args=[logics.QF_LRIA])

    s28_0 = def_alias(args, mgr, script, "s28_i", mgr.RIZero(Int(-1)))
    s29_0 = def_alias(args, mgr, script, "s29_i", mgr.RIZero(Int(-1)))

    #init = mgr.And( mgr.RIEQP(s28_0, mgr.RIZero(Int(-1))), mgr.RIEQP(s29_0, mgr.RIZero(Int(-1))) )
    #script.add(name=smtcmd.ASSERT, args=[init])
    
    for j in range(args.num_steps[0]):
        i = decl_const(args, mgr, script, "i%d" % j)

        ci = And( mgr.GE(Real(1.), mgr.RIUpper(i)), mgr.GE(mgr.RILower(i), Real(-1.)) )
        script.add(name=smtcmd.ASSERT, args=[ci])

        lv = mgr.RISub( mgr.RISub(
                mgr.RIMul(mgr.RealToRi(Int(-1), Real(0.058167)), i),
                mgr.RIMul(mgr.RealToRi(Int(-1), Real(1.4891)), s28_0) ),
                mgr.RIMul(mgr.RealToRi(Int(-1), Real(0.88367)), s29_0) )

        l = def_alias(args, mgr, script, "l%d" % j, lv)
        s28_1 = def_alias(args, mgr, script, "s28_%d" % j, l)
        s29_1 = def_alias(args, mgr, script, "s29_%d" % j, s28_0)

        o = Symbol("o%d" % j, BOOL)
        script.add(name=smtcmd.DECLARE_FUN, args=[o])

        co = o.Iff( mgr.RIGT( mgr.RISub(l, s29_0),
                              mgr.RealToRi(Int(-1), Real(args.thres)) ))
        script.add(name=smtcmd.ASSERT, args=[co])

        s28_0 = s28_1
        s29_0 = s29_1

    script.add(name=smtcmd.ASSERT, args=[o])

    script.add(name=smtcmd.CHECK_SAT, args=[])

    return script

if __name__ == "__main__":
    parser = get_arg_parser(0.3)
    args = parser.parse_args()

    script = def_script(args)
    serialize(args, script)

# eof
