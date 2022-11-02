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

def def_script(args):
    mgr = get_env().formula_manager

    script = SmtLibScript()

    if args.sl:
        script.add(name=smtcmd.SET_LOGIC, args=[logics.QF_FP])

    s0 = Symbol("si", FPType(11,53)) 
    script.add(name=smtcmd.DECLARE_FUN, args=[s0])

    init = s0.Equals(mgr.FPPositiveZero(11,53))
    script.add(name=smtcmd.ASSERT, args=[init])
    
    for j in range(args.num_steps[0]):
        s1 = Symbol("s%d" % j, FPType(11,53))
        script.add(name=smtcmd.DECLARE_FUN, args=[s1])

        i = Symbol("i%d" % j, FPType(11,53))
        script.add(name=smtcmd.DECLARE_FUN, args=[i])
        rel = mgr.Not(mgr.FPIsNaN(i))
        script.add(name=smtcmd.ASSERT, args=[rel])

        ci = And( mgr.FPLEQ(mgr.FP(mgr.BV(1,1), mgr.BV("#b01111111111",11), mgr.BV(0,52)), i), 
                  mgr.FPLEQ(i, mgr.FP(mgr.BV(0,1), mgr.BV("#b01111111111",11), mgr.BV(0,52))) )
        #ci = And( mgr.FPLEQ(mgr.FPToFp(11,53, mgr.FPRNE(), Real(-1.0)), i), 
        #          mgr.FPLEQ(i, mgr.FPToFp(11,53, mgr.FPRNE(), Real(1.0))) )
        script.add(name=smtcmd.ASSERT, args=[ci])
        o = Symbol("o%d" % j, BOOL)
        script.add(name=smtcmd.DECLARE_FUN, args=[o])
        l = Symbol("l%d" % j, FPType(11,53))
        script.add(name=smtcmd.DECLARE_FUN, args=[l])

        #c1 = l.Equals( mgr.FPAdd( mgr.FPRNE(), i, 
        #    mgr.FPMul(mgr.FPRNE(), mgr.FPToFp(11,53, mgr.FPRNE(), Real(0.9)), s0) ) )
        #c2 = o.Iff( mgr.FPGT(l, mgr.FPToFp(11,53, mgr.FPRNE(), Real(args.thres))) )
        
        rm1 = Symbol("rm1_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm1])
        rm2 = Symbol("rm2_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm2])
        rm3 = Symbol("rm3_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm3])
        rm4 = Symbol("rm4_%d" % j, RM) 
        script.add(name=smtcmd.DECLARE_FUN, args=[rm4])
        c1 = l.Equals( mgr.FPAdd( rm1, i, 
            mgr.FPMul(rm2, mgr.FPToFp(11,53, rm3, Real(0.9)), s0) ) )
        c2 = o.Iff( mgr.FPGT(l, mgr.FPToFp(11,53, rm4, Real(args.thres))) )

        c3 = s1.Equals(l)

        script.add(name=smtcmd.ASSERT, args=[c1])
        script.add(name=smtcmd.ASSERT, args=[c2])
        script.add(name=smtcmd.ASSERT, args=[c3])

        s0 = s1

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
