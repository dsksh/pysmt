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

    s0 = Symbol("si", FPType(11,53))
    script.add(name=smtcmd.DECLARE_FUN, args=[s0])
    s28_0 = Symbol("s28_i", FPType(11,53)) 
    s29_0 = Symbol("s29_i", FPType(11,53)) 
    script.add(name=smtcmd.DECLARE_FUN, args=[s28_0])
    script.add(name=smtcmd.DECLARE_FUN, args=[s29_0])
    init = mgr.And( s0.Equals(mgr.FPPositiveZero(11,53)), 
                    s28_0.Equals(mgr.FPPositiveZero(11,53)), 
                    s29_0.Equals(mgr.FPPositiveZero(11,53)) )
    script.add(name=smtcmd.ASSERT, args=[init])
    
    for j in range(args.num_steps[0]):
        s1 = Symbol("s1_%d" % j, FPType(11,53))
        script.add(name=smtcmd.DECLARE_FUN, args=[s1])
        i1 = Symbol("i1_%d" % j, FPType(11,53))
        script.add(name=smtcmd.DECLARE_FUN, args=[i1])
        rel = mgr.Not(mgr.FPIsNaN(i1))
        script.add(name=smtcmd.ASSERT, args=[rel])

        ci1 = And( mgr.FPLEQ(mgr.FP(mgr.BV(1,1), mgr.BV("#b01111111111",11), mgr.BV(0,52)), i1), 
                   mgr.FPLEQ(i1, mgr.FP(mgr.BV(0,1), mgr.BV("#b01111111111",11), mgr.BV(0,52))) )
        script.add(name=smtcmd.ASSERT, args=[ci1])

        o1 = Symbol("o1_%d" % j, BOOL)
        script.add(name=smtcmd.DECLARE_FUN, args=[o1])
        l1 = Symbol("l1_%d" % j, FPType(11,53))
        script.add(name=smtcmd.DECLARE_FUN, args=[l1])

        rm1 = Symbol("rm1_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm1])
        rm2 = Symbol("rm2_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm2])
        rm3 = Symbol("rm3_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm3])
        rm4 = Symbol("rm4_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm4])

        c1 = l1.Equals( mgr.FPAdd( rm1, i1, 
            mgr.FPMul(rm2, mgr.FPToFp(11,53, rm3, Real(0.9)), s0) ) )
        c2 = o1.Iff( mgr.FPGT(l1, mgr.FPToFp(11,53, rm4, Real(args.thres1))) )
        c3 = s1.Equals(l1)

        script.add(name=smtcmd.ASSERT, args=[c1])
        script.add(name=smtcmd.ASSERT, args=[c2])
        script.add(name=smtcmd.ASSERT, args=[c3])

        s0 = s1

        #

        i2 = Symbol("i2_%d" % j, FPType(11,53))
        l2 = Symbol("l2_%d" % j, FPType(11,53))
        o2 = Symbol("o2_%d" % j, BOOL)
        s28_1 = Symbol("s28_%d" % j, FPType(11,53))
        s29_1 = Symbol("s29_%d" % j, FPType(11,53))

        script.add(name=smtcmd.DECLARE_FUN, args=[i2])
        rel = mgr.Not(mgr.FPIsNaN(i2))
        script.add(name=smtcmd.ASSERT, args=[rel])

        script.add(name=smtcmd.DECLARE_FUN, args=[l2])
        script.add(name=smtcmd.DECLARE_FUN, args=[o2])
        script.add(name=smtcmd.DECLARE_FUN, args=[s28_1])
        script.add(name=smtcmd.DECLARE_FUN, args=[s29_1])

        ci2 = And( mgr.FPLEQ(mgr.FP(mgr.BV(1,1), mgr.BV("#b01111111111",11), mgr.BV(0,52)), i2), 
                  mgr.FPLEQ(i2, mgr.FP(mgr.BV(0,1), mgr.BV("#b01111111111",11), mgr.BV(0,52))) )
        script.add(name=smtcmd.ASSERT, args=[ci2])

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
        rm11 = Symbol("rm11_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm11])
        rm12 = Symbol("rm12_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm12])
        rm13 = Symbol("rm13_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm13])
        rm14 = Symbol("rm14_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm14])

        c4 = l2.Equals( mgr.FPSub( rm5, mgr.FPSub( rm6,
            mgr.FPMul(rm7, mgr.FPToFp(11,53, rm8, Real(0.058167)), i2),
            mgr.FPMul(rm9, mgr.FPToFp(11,53, rm10, Real(1.4891)), s28_0) ),
            mgr.FPMul(rm11, mgr.FPToFp(11,53, rm12, Real(0.88367)), s29_0) ) )
        c5 = o2.Iff( mgr.FPGT( mgr.FPSub(rm13, l2, s29_0), 
                               mgr.FPToFp(11,53, rm14, Real(args.thres2)) ) )
        c6 = s28_1.Equals( l2 )
        c7 = s29_1.Equals( s28_0 )

        script.add(name=smtcmd.ASSERT, args=[c4])
        script.add(name=smtcmd.ASSERT, args=[c5])
        script.add(name=smtcmd.ASSERT, args=[c6])
        script.add(name=smtcmd.ASSERT, args=[c7])

        s28_0 = s28_1
        s29_0 = s29_1

    if args.sat:
        script.add(name=smtcmd.ASSERT, args=[And(o1, o2)])
    else:
        script.add(name=smtcmd.ASSERT, args=[Or(o1, o2)])

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

    parser.add_argument(
        "--set-logic", dest='sl', action='store_true' )
    parser.add_argument(
        "--no-set-logic", dest='sl', action='store_false' )
    parser.set_defaults(sl=True)

    parser.add_argument(
        "-sat", dest='sat', action='store_true' )
    parser.add_argument(
        "-unsat", dest='sat', action='store_false' )
    parser.set_defaults(sat=True)

    args = parser.parse_args()

    main(args)

# eof
