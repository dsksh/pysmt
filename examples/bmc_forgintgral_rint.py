import sys

from pysmt.environment import get_env
from pysmt.shortcuts import Symbol, Not, And, Or, Implies
from pysmt.shortcuts import Equals, LE
from pysmt.shortcuts import Int, Real, Plus, Minus, Times, Div
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import FunctionType, REAL, INT, BOOL, RINT
import pysmt.logics as logics
import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import SmtLibScript
from bmc_utils import get_arg_parser, def_alias, decl_const, serialize

def def_script(args):
    mgr = get_env().formula_manager

    script = SmtLibScript()

    script.add(name=smtcmd.SET_LOGIC, args=[logics.QF_LRIA])

    s0 = def_alias(args, mgr, script, "si", mgr.RIZero(mgr.Int(-1)))

    for j in range(args.num_steps[0]):
        i = decl_const(args, mgr, script, "i%d" % j)

        ci = And( mgr.GE(mgr.RILower(i), Real(-1)), mgr.GE(Real(1), mgr.RIUpper(i)) )
        script.add(name=smtcmd.ASSERT, args=[ci])

        lv = mgr.RIAdd(i, mgr.RIMul(mgr.RealToRi(Int(-1), Real(0.9)), s0))
        l = def_alias(args, mgr, script, "l%d" % j, lv)

        s1 = def_alias(args, mgr, script, "s%d" % j, l)

        o = Symbol("o%d" % j, BOOL)
        script.add(name=smtcmd.DECLARE_FUN, args=[o])

        co = o.Iff( mgr.RIGT(l, mgr.RealToRi(Int(-1), Real(args.thres))) )
        script.add(name=smtcmd.ASSERT, args=[co])

        s0 = s1

    script.add(name=smtcmd.ASSERT, args=[o])
    script.add(name=smtcmd.CHECK_SAT, args=[])
    return script

if __name__ == "__main__":
    parser = get_arg_parser(3)
    args = parser.parse_args()

    script = def_script(args)
    serialize(args, script)

# eof
