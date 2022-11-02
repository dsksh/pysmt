import sys
import argparse

from pysmt.environment import get_env
from pysmt.shortcuts import Symbol, Not, And, Or, Implies
from pysmt.shortcuts import Equals, LE
from pysmt.shortcuts import Int, Real, Plus, Minus, Times, Div
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import REAL, INT, BOOL, FPType, RM
import pysmt.logics as logics
import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import SmtLibScript

def main(args):
    mgr = get_env().formula_manager

    script = SmtLibScript()

    if args.sl:
        script.add(name=smtcmd.SET_LOGIC, args=[logics.QF_FP])

    s28_0 = Symbol("s28_i", FPType(11,53)) 
    s29_0 = Symbol("s29_i", FPType(11,53)) 
    script.add(name=smtcmd.DECLARE_FUN, args=[s28_0])
    script.add(name=smtcmd.DECLARE_FUN, args=[s29_0])
    init = mgr.And( s28_0.Equals(mgr.FPPositiveZero(11,53)),
                    s29_0.Equals(mgr.FPPositiveZero(11,53)) )
    script.add(name=smtcmd.ASSERT, args=[init])
    
    for j in range(args.num_steps[0]):
        i = Symbol("i%d" % j, FPType(11,53))
        l = Symbol("l%d" % j, FPType(11,53))
        o = Symbol("o%d" % j, BOOL)
        s28_1 = Symbol("s28_%d" % j, FPType(11,53))
        s29_1 = Symbol("s29_%d" % j, FPType(11,53))

        script.add(name=smtcmd.DECLARE_FUN, args=[i])
        rel = mgr.Not(mgr.FPIsNaN(i))
        script.add(name=smtcmd.ASSERT, args=[rel])

        script.add(name=smtcmd.DECLARE_FUN, args=[l])
        script.add(name=smtcmd.DECLARE_FUN, args=[o])
        script.add(name=smtcmd.DECLARE_FUN, args=[s28_1])
        script.add(name=smtcmd.DECLARE_FUN, args=[s29_1])

        rm1 = Symbol("rm1_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm1])
        rm2 = Symbol("rm2_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm2])

        ci = And( mgr.FPLEQ(mgr.FPToFp(11,53, rm1, Real(-1.0)), i), 
                  mgr.FPLEQ(i, mgr.FPToFp(11,53, rm2, Real(1.0))) )
        script.add(name=smtcmd.ASSERT, args=[ci])

        rm3 = Symbol("rm3_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm3])
        rm4 = Symbol("rm4_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm4])
        rm5 = Symbol("rm5_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm5])
        rm6 = Symbol("rm6_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm6])
        rm7 = Symbol("rm7_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm7])
        rm8 = Symbol("rm8_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm8])
        rm9 = Symbol("rm9_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm9])
        rm10 = Symbol("rm10_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm10])

        c1 = l.Equals( mgr.FPSub( rm3, mgr.FPSub( rm4,
            mgr.FPMul(rm5, mgr.FPToFp(11,53, rm6, Real(0.058167)), i),
            mgr.FPMul(rm7, mgr.FPToFp(11,53, rm8, Real(1.4891)), s28_0) ),
            mgr.FPMul(rm9, mgr.FPToFp(11,53, rm10, Real(0.88367)), s29_0) ) )

        rm11 = Symbol("rm11_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm11])
        rm12 = Symbol("rm12_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm12])

        c2 = o.Iff( mgr.FPGT( mgr.FPSub(rm11, l, s29_0), 
                              mgr.FPToFp(11,53, rm12, Real(args.thres)) ) )
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
        "--thres", nargs='?', type=float, default=3 )
    parser.add_argument("num_steps", type=int, nargs=1)

    parser.add_argument(
        "--set-logic", dest='sl', action='store_true' )
    parser.add_argument(
        "--no-set-logic", dest='sl', action='store_false' )
    parser.set_defaults(sl=True)

    args = parser.parse_args()

    main(args)

# eof
