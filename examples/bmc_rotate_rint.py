import sys
from math import cos, sin, pi

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

    #p1 = Real(0.1)
    #p2 = Real(0.9949874371)
    p1 = Real(0.5)
    p2 = Real(0.86602540303)

    s1_0 = def_alias(args, mgr, script, "si1", mgr.RealToRi(Int(-1), Real(cos(0))))
    s2_0 = def_alias(args, mgr, script, "si2", mgr.RealToRi(Int(-1), Real(sin(0))))
    #s1_0 = decl_const(args, mgr, script, "si1")
    #s2_0 = decl_const(args, mgr, script, "si2")

    #init = mgr.RIEQ( mgr.RIAdd( mgr.RIMul(s1_0, s1_0), mgr.RIMul(s2_0, s2_0)),
    #                 mgr.RealToRi(Int(-1), Real(1)) )
    #script.add(name=smtcmd.ASSERT, args=[init])

    for j in range(args.num_steps[0]):
        l1 = mgr.RIAdd( mgr.RIMul(mgr.RealToRi(Int(-1), p2), s1_0), 
                        mgr.RIMul(mgr.RINeg(mgr.RealToRi(Int(-1), p1)), s2_0) )
        s1_1 = def_alias(args, mgr, script, "s1_%d" % j, l1)

        l2 = mgr.RIAdd( mgr.RIMul(mgr.RealToRi(Int(-1), p2), s2_0), 
                        mgr.RIMul(mgr.RealToRi(Int(-1), p1), s1_0) )
        s2_1 = def_alias(args, mgr, script, "s2_%d" % j, l2)

        o = Symbol("o%d" % j, BOOL)
        script.add(name=smtcmd.DECLARE_FUN, args=[o])

        co = o.Iff( mgr.RIGT(s1_1, mgr.RealToRi(Int(-1), Real(args.thres))) )
        script.add(name=smtcmd.ASSERT, args=[co])

        s1_0 = s1_1
        s2_0 = s2_1

    script.add(name=smtcmd.ASSERT, args=[o])
    script.add(name=smtcmd.CHECK_SAT, args=[])
    return script

if __name__ == "__main__":
    parser = get_arg_parser(3)
    args = parser.parse_args()

    script = def_script(args)
    serialize(args, script)

# eof
