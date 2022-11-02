import sys
import argparse

from pysmt.shortcuts import Symbol, Not, And, Or, Implies
from pysmt.shortcuts import Equals, LE, GT
from pysmt.shortcuts import Real, Plus, Minus, Times, Div
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import REAL, INT, BOOL
import pysmt.logics as logics
import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import SmtLibScript

def def_script(args):
    script = SmtLibScript()

    script.add(name=smtcmd.SET_LOGIC, args=[logics.QF_LIRA])

    s0 = Symbol("si", REAL) 
    script.add(name=smtcmd.DECLARE_FUN, args=[s0])
    init = s0.Equals(0.)
    script.add(name=smtcmd.ASSERT, args=[init])
    
    for j in range(args.num_steps[0]):
        s1 = Symbol("s%d" % j, REAL)
        script.add(name=smtcmd.DECLARE_FUN, args=[s1])
        i = Symbol("i%d" % j, REAL)
        script.add(name=smtcmd.DECLARE_FUN, args=[i])
        ci = And( LE(Real(-1), i), LE(i, Real(1)) )
        script.add(name=smtcmd.ASSERT, args=[ci])
        o = Symbol("o%d" % j, BOOL)
        script.add(name=smtcmd.DECLARE_FUN, args=[o])
        l = Symbol("l%d" % j, REAL)
        script.add(name=smtcmd.DECLARE_FUN, args=[l])

        c1 = l.Equals( Plus(i, Times(Real(0.9), s0) ) )
        c2 = o.Iff( GT(l, Real(args.thres)) )
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
    args = parser.parse_args()

    script = def_script(args)

    #for p in ps:
    #    sl_script = smtlibscript_from_formula(p)
    #    sl_script.serialize(sys.stdout, daggify=False)
    script.serialize(sys.stdout, daggify=False)

# eof
