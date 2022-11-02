import sys
import argparse

from pysmt.environment import get_env
from pysmt.shortcuts import Symbol, Not, And, Or, Implies
from pysmt.shortcuts import Equals, LE
from pysmt.shortcuts import Int, Real, Plus, Minus, Times, Div
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import REAL, INT, BOOL, RINT, FunctionType
import pysmt.logics as logics
import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.script import SmtLibScript
from bmc_utils import get_arg_parser, def_alias, decl_const, serialize

def def_script(args):
    mgr = get_env().formula_manager

    script = SmtLibScript()

    script.add(name=smtcmd.SET_LOGIC, args=[logics.QF_LRIA])

    s0 = def_alias(args, mgr, script, "si", mgr.RIZero(mgr.Int(-1)))
    s28_0 = def_alias(args, mgr, script, "s28_i", mgr.RIZero(Int(-1)))
    s29_0 = def_alias(args, mgr, script, "s29_i", mgr.RIZero(Int(-1)))

    for j in range(args.num_steps[0]):
        i1 = decl_const(args, mgr, script, "i1_%d" % j)

        ci1 = And( mgr.GE(Real(1.), mgr.RIUpper(i1)), mgr.GE(mgr.RILower(i1), mgr.Real(-1.)) )
        script.add(name=smtcmd.ASSERT, args=[ci1])

        lv1 = mgr.RIAdd( i1, mgr.RIMul(mgr.RealToRi(Int(-1), Real(0.9)), s0))
        l1 = def_alias(args, mgr, script, "l1_%d" % j, lv1)

        s1 = def_alias(args, mgr, script, "s1_%d" % j, l1)

        o1 = Symbol("o1_%d" % j, BOOL)
        script.add(name=smtcmd.DECLARE_FUN, args=[o1])

        co1 = o1.Iff( mgr.RIGT(l1, mgr.RealToRi(Int(-1), Real(args.thres))) )
        script.add(name=smtcmd.ASSERT, args=[co1])

        s0 = s1

        #

        i2 = decl_const(args, mgr, script, "i2_%d" % j)

        ci2 = And( mgr.GE(Real(1.), mgr.RIUpper(i2)), mgr.GE(mgr.RILower(i2), Real(-1.)) )
        script.add(name=smtcmd.ASSERT, args=[ci2])

        lv2 = mgr.RISub( mgr.RISub(
                 mgr.RIMul(mgr.RealToRi(Int(-1), Real(0.058167)), i2),
                 mgr.RIMul(mgr.RealToRi(Int(-1), Real(1.4891)), s28_0) ),
                 mgr.RIMul(mgr.RealToRi(Int(-1), Real(0.88367)), s29_0) )
        l2 = def_alias(args, mgr, script, "l2_%d" % j, lv2)

        s28_1 = def_alias(args, mgr, script, "s28_%d" % j, l2)
        s29_1 = def_alias(args, mgr, script, "s29_%d" % j, s28_0)

        o2 = Symbol("o2_%d" % j, BOOL)
        script.add(name=smtcmd.DECLARE_FUN, args=[o2])

        co2 = o2.Iff( mgr.RIGT( mgr.RISub(l2, s29_0), 
                 mgr.RealToRi(Int(-1), Real(args.thres2)) ) )
        script.add(name=smtcmd.ASSERT, args=[co2])

        s28_0 = s28_1
        s29_0 = s29_1

    if args.sat:
        script.add(name=smtcmd.ASSERT, args=[And(o1, o2)])
    else:
        script.add(name=smtcmd.ASSERT, args=[Or(o1, o2)])
    script.add(name=smtcmd.CHECK_SAT, args=[])
    return script

if __name__ == "__main__":
    parser = get_arg_parser(3)
    parser.add_argument(
        "--thres2", nargs='?', type=float, default=0.3 )

    parser.add_argument(
        "-sat", dest='sat', action='store_true' )
    parser.add_argument(
        "-unsat", dest='sat', action='store_false' )
    parser.set_defaults(sat=True)

    args = parser.parse_args()

    script = def_script(args)
    serialize(args, script)

# eof
