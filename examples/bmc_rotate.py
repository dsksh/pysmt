import sys
import argparse
from math import cos, sin, pi

from pysmt.environment import get_env
from pysmt.shortcuts import Symbol, Not, And, Or, Implies
from pysmt.shortcuts import Equals, LT, GT, GE
from pysmt.shortcuts import Int, Real, Plus, Minus, Times, Div
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import REAL, INT, BOOL
import pysmt.logics as logics
import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import SmtLibScript

def def_script(args):
    mgr = get_env().formula_manager

    script = SmtLibScript()

    script.add(name=smtcmd.SET_LOGIC, args=[logics.QF_LIRA])

    #p1 = Real(0.1)
    p1 = Real(0.5)

    #p2 = Symbol("p2", REAL) 
    #script.add(name=smtcmd.DECLARE_FUN, args=[p2])
    #p2c = And(LT(Real(0), p2), LT(p2, Real(1)))
    #script.add(name=smtcmd.ASSERT, args=[p2c])
    #p2 = Real(0.9949874371)
    p2 = Real(0.86602540303)

    s1_0 = Symbol("si1", REAL) 
    script.add(name=smtcmd.DECLARE_FUN, args=[s1_0])
    s2_0 = Symbol("si2", REAL) 
    script.add(name=smtcmd.DECLARE_FUN, args=[s2_0])

    init = s1_0.Equals(cos(0))
    script.add(name=smtcmd.ASSERT, args=[init])
    init = s2_0.Equals(sin(0))
    script.add(name=smtcmd.ASSERT, args=[init])

    #init = Equals(Plus(Times(s1_0, s1_0), Times(s2_0, s2_0)), Real(1))
    #script.add(name=smtcmd.ASSERT, args=[init])

    for j in range(args.num_steps[0]):
        l1 = Plus(Times(p2, s1_0), Times(Real(-1), p1, s2_0))
        s1_1 = Symbol("s1_%d" % j, REAL) 
        script.add(name=smtcmd.DECLARE_FUN, args=[s1_1])
        c1 = s1_1.Equals(l1)
        script.add(name=smtcmd.ASSERT, args=[c1])

        l2 = Plus(Times(p2, s2_0), Times(p1, s1_0))
        s2_1 = Symbol("s2_%d" % j, REAL) 
        script.add(name=smtcmd.DECLARE_FUN, args=[s2_1])
        c2 = s2_1.Equals(l2)
        script.add(name=smtcmd.ASSERT, args=[c2])

        o = Symbol("o%d" % j, BOOL)
        script.add(name=smtcmd.DECLARE_FUN, args=[o])

        co = o.Iff( GT(s1_1, Real(args.thres)) )
        script.add(name=smtcmd.ASSERT, args=[co])

        s1_0 = s1_1
        s2_0 = s2_1

    script.add(name=smtcmd.ASSERT, args=[o])
    script.add(name=smtcmd.CHECK_SAT, args=[])
    return script

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        usage="%(prog)s [OPTION] [# of steps]...",
        description="Generate an SMT-LIB formula for BMC."
    )
    parser.add_argument(
        "-v", "--version", action="version",
        version = f"{parser.prog} version 0.0.1" )

    parser.add_argument(
        "--thres", nargs='?', type=float, default=1 )

    parser.add_argument("num_steps", type=int, nargs=1)

    parser.add_argument(
        "--set-logic", dest='sl', action='store_true' )
    parser.add_argument(
        "--no-set-logic", dest='sl', action='store_false' )
    parser.set_defaults(sl=True)

    args = parser.parse_args()

    script = def_script(args)
    script.serialize(sys.stdout, daggify=True)

# eof
