import sys
import argparse
from math import cos, sin, pi

from pysmt.environment import get_env
from pysmt.shortcuts import Symbol, Not, And, Or, Implies
from pysmt.shortcuts import Equals, LE
from pysmt.shortcuts import Int, Real, Plus, Minus, Times, Div
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import REAL, INT, BOOL, FPType, RM
import pysmt.logics as logics
import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import SmtLibScript
from bmc_utils import get_arg_parser, def_alias, decl_const, serialize

def def_script(args):
    mgr = get_env().formula_manager

    script = SmtLibScript()

    if args.sl:
        script.add(name=smtcmd.SET_LOGIC, args=[logics.QF_FP])

    #p1 = Real(0.1)
    #p2 = Real(0.9949874371)
    p1 = Real(0.5)
    p2 = Real(0.86602540303)

    rm1i = Symbol("rm1_i", RM) 
    script.add(name=smtcmd.DECLARE_FUN, args=[rm1i])
    rm2i = Symbol("rm2_i", RM) 
    script.add(name=smtcmd.DECLARE_FUN, args=[rm2i])
    rm3i = Symbol("rm3_i", RM) 
    script.add(name=smtcmd.DECLARE_FUN, args=[rm3i])
    s1_0 = Symbol("si1", FPType(11,53)) 
    script.add(name=smtcmd.DECLARE_FUN, args=[s1_0])
    s2_0 = Symbol("si2", FPType(11,53)) 
    script.add(name=smtcmd.DECLARE_FUN, args=[s2_0])

    init = s1_0.Equals(mgr.FPToFp(11,53, rm1i, Real(cos(0))))
    script.add(name=smtcmd.ASSERT, args=[init])
    init = s2_0.Equals(mgr.FPToFp(11,53, rm2i, Real(sin(0))))
    script.add(name=smtcmd.ASSERT, args=[init])

    #init = mgr.FPEQ( mgr.FPAdd(rm1i, mgr.FPMul(rm2i, s1_0, s1_0), 
    #                                 mgr.FPMul(rm3i, s2_0, s2_0) ),
    #                 mgr.FP(mgr.BV(0,1), mgr.BV("#b01111111111",11), mgr.BV(0,52)) )
    #script.add(name=smtcmd.ASSERT, args=[init])

    for j in range(args.num_steps[0]):
        rm1 = Symbol("rm1_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm1])
        rm2 = Symbol("rm2_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm2])
        rm3 = Symbol("rm3_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm3])
        rm4 = Symbol("rm4_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm4])
        rm5 = Symbol("rm5_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm5])
        l1 = mgr.FPAdd(rm1, mgr.FPMul(rm2, mgr.FPToFp(11,53, rm3, p2), s1_0), 
                            mgr.FPMul(rm4, mgr.FPNeg(mgr.FPToFp(11,53, rm5, p1)), s2_0) )
        s1_1 = Symbol("si1_%d" % j, FPType(11,53)) 
        script.add(name=smtcmd.DECLARE_FUN, args=[s1_1])
        c1 = s1_1.Equals(l1)
        script.add(name=smtcmd.ASSERT, args=[c1])

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
        l2 = mgr.FPAdd(rm6, mgr.FPMul(rm7, mgr.FPToFp(11,53, rm8, p2), s2_0),
                            mgr.FPMul(rm9, mgr.FPToFp(11,53, rm10, p1), s1_0) )
        s2_1 = Symbol("si2_%d" % j, FPType(11,53)) 
        script.add(name=smtcmd.DECLARE_FUN, args=[s2_1])
        c2 = s2_1.Equals(l2)
        script.add(name=smtcmd.ASSERT, args=[c2])

        o = Symbol("o%d" % j, BOOL)
        script.add(name=smtcmd.DECLARE_FUN, args=[o])

        rm11 = Symbol("rm11_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm11])
        co = o.Iff( mgr.FPGT(s1_1, mgr.FPToFp(11,53, rm11, Real(args.thres))) )
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
        "--thres", nargs='?', type=float, default=3 )
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
