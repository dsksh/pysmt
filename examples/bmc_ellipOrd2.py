import sys
import argparse

from pysmt.environment import get_env
from pysmt.shortcuts import Symbol, Not, And, Or, Implies
from pysmt.shortcuts import Equals, LE
from pysmt.shortcuts import Int, Real, Plus, Minus, Times, Div
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import REAL, INT, BOOL, FPType
import pysmt.logics as logics
import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import SmtLibScript

def def_script(args):
    mgr = get_env().formula_manager

    script = SmtLibScript()

    script.add(name=smtcmd.SET_LOGIC, args=[logics.QF_LIRA])

    s28_0 = Symbol("s28_i", REAL) 
    s29_0 = Symbol("s29_i", REAL) 
    script.add(name=smtcmd.DECLARE_FUN, args=[s28_0])
    script.add(name=smtcmd.DECLARE_FUN, args=[s29_0])
    init = mgr.And( s28_0.Equals(Real(0.)), s29_0.Equals(Real(0.)) )
    script.add(name=smtcmd.ASSERT, args=[init])
    
    for j in range(args.num_steps[0]):
        i = Symbol("i%d" % j, REAL)
        l = Symbol("l%d" % j, REAL)
        o = Symbol("o%d" % j, BOOL)
        s28_1 = Symbol("s28_%d" % j, REAL)
        s29_1 = Symbol("s29_%d" % j, REAL)

        script.add(name=smtcmd.DECLARE_FUN, args=[i])
        script.add(name=smtcmd.DECLARE_FUN, args=[l])
        script.add(name=smtcmd.DECLARE_FUN, args=[o])
        script.add(name=smtcmd.DECLARE_FUN, args=[s28_1])
        script.add(name=smtcmd.DECLARE_FUN, args=[s29_1])

        ci = And( mgr.LE(Real(-1.0), i), mgr.LE(i, Real(1.0)) )
        script.add(name=smtcmd.ASSERT, args=[ci])

        c1 = l.Equals( mgr.Minus( mgr.Minus(
            mgr.Times(Real(0.058167), i), mgr.Times(Real(1.4891), s28_0) ),
            mgr.Times(Real(0.88367), s29_0) ) )
        c2 = o.Iff( mgr.GT( mgr.Minus(l, s29_0), Real(args.thres)) )
        c3 = s28_1.Equals( l )
        c4 = s29_1.Equals( s28_0 )

        script.add(name=smtcmd.ASSERT, args=[c1])
        script.add(name=smtcmd.ASSERT, args=[c2])
        script.add(name=smtcmd.ASSERT, args=[c3])
        script.add(name=smtcmd.ASSERT, args=[c4])

        s28_0 = s28_1
        s29_0 = s29_1

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
        "--thres", nargs='?', type=float, default=3 )
    parser.add_argument("num_steps", type=int, nargs=1)
    args = parser.parse_args()

    script = def_script(args)
    script.serialize(sys.stdout, daggify=True)

# eof
