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

def main(args):
    mgr = get_env().formula_manager

    script = SmtLibScript()

    script.add(name=smtcmd.SET_LOGIC, args=[logics.QF_LIRA])

    s0 = Symbol("si", REAL) 
    script.add(name=smtcmd.DECLARE_FUN, args=[s0])
    s28_0 = Symbol("s28_i", REAL) 
    s29_0 = Symbol("s29_i", REAL) 
    script.add(name=smtcmd.DECLARE_FUN, args=[s28_0])
    script.add(name=smtcmd.DECLARE_FUN, args=[s29_0])
    init = mgr.And( s0.Equals(0.), s28_0.Equals(0.), s29_0.Equals(0.) )
    script.add(name=smtcmd.ASSERT, args=[init])
    
    for j in range(args.num_steps[0]):
        s1 = Symbol("s1_%d" % j, REAL)
        script.add(name=smtcmd.DECLARE_FUN, args=[s1])
        i1 = Symbol("i1_%d" % j, REAL)
        script.add(name=smtcmd.DECLARE_FUN, args=[i1])
        ci1 = And( LE(Real(-1), i1), LE(i1, Real(1)) )
        script.add(name=smtcmd.ASSERT, args=[ci1])
        o1 = Symbol("o1_%d" % j, BOOL)
        script.add(name=smtcmd.DECLARE_FUN, args=[o1])
        l1 = Symbol("l1_%d" % j, REAL)
        script.add(name=smtcmd.DECLARE_FUN, args=[l1])

        c1 = l1.Equals( mgr.Plus(i1, Times(Real(0.9), s0) ) )
        c2 = o1.Iff( mgr.GT(l1, Real(args.thres1)) )
        c3 = s1.Equals(l1)

        script.add(name=smtcmd.ASSERT, args=[c1])
        script.add(name=smtcmd.ASSERT, args=[c2])
        script.add(name=smtcmd.ASSERT, args=[c3])

        s0 = s1

        #

        i2 = Symbol("i2_%d" % j, REAL)
        l2 = Symbol("l2_%d" % j, REAL)
        o2 = Symbol("o2_%d" % j, BOOL)
        s28_1 = Symbol("s28_%d" % j, REAL)
        s29_1 = Symbol("s29_%d" % j, REAL)

        script.add(name=smtcmd.DECLARE_FUN, args=[i2])
        script.add(name=smtcmd.DECLARE_FUN, args=[l2])
        script.add(name=smtcmd.DECLARE_FUN, args=[o2])
        script.add(name=smtcmd.DECLARE_FUN, args=[s28_1])
        script.add(name=smtcmd.DECLARE_FUN, args=[s29_1])

        ci2 = And( mgr.LE(Real(-1.0), i2), mgr.LE(i2, Real(1.0)) )
        script.add(name=smtcmd.ASSERT, args=[ci2])

        c4 = l2.Equals( mgr.Minus( mgr.Minus(
            mgr.Times(Real(0.058167), i2), mgr.Times(Real(1.4891), s28_0) ),
            mgr.Times(Real(0.88367), s29_0) ) )
        c5 = o2.Iff( mgr.GT( mgr.Minus(l2, s29_0), Real(args.thres2)) )
        c6 = s28_1.Equals( l2 )
        c7 = s29_1.Equals( s28_0 )

        script.add(name=smtcmd.ASSERT, args=[c4])
        script.add(name=smtcmd.ASSERT, args=[c5])
        script.add(name=smtcmd.ASSERT, args=[c6])
        script.add(name=smtcmd.ASSERT, args=[c7])

        s28_0 = s28_1
        s29_0 = s29_1

    script.add(name=smtcmd.ASSERT, args=[And(o1, o2)])

    script.add(name=smtcmd.CHECK_SAT, args=[])

    script.serialize(sys.stdout, daggify=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        usage="%(prog)s [OPTION] [# of steps]...",
        description="Generate an SMT-LIB formula for BMC."
    )
    parser.add_argument(
        "-v", "--version", action="version",
        version = f"{parser.prog} version 0.0.1" )
    parser.add_argument(
        "--thres1", nargs='?', type=float, default=3 )
    parser.add_argument(
        "--thres2", nargs='?', type=float, default=0.3 )
    parser.add_argument("num_steps", type=int, nargs=1)
    args = parser.parse_args()

    main(args)

# eof
