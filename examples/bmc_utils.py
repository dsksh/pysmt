import sys
import argparse

from pysmt.shortcuts import Symbol, Not, And, Or, Implies
from pysmt.shortcuts import Equals, LE
from pysmt.shortcuts import Int, Real, Plus, Minus, Times, Div
from pysmt.typing import REAL, INT, BOOL, RINT, FunctionType
import pysmt.smtlib.commands as smtcmd

def get_arg_parser(thres):
    parser = argparse.ArgumentParser(
        usage="%(prog)s [OPTION] [# of steps]...",
        description="Generate an SMT-LIB formula for BMC."
    )
    parser.add_argument(
        "-v", "--version", action="version",
        version = f"{parser.prog} version 0.0.1" )
    parser.add_argument(
        "--thres", "--thres1", nargs='?', type=float, default=thres )
    parser.add_argument("num_steps", type=int, nargs=1)

    parser.add_argument(
        '-dp', "--dplus", action='store_true' )
    parser.add_argument(
        '-dm', '-dn', "--dminus", dest='dplus', action='store_false' )
    parser.set_defaults(dplus=True)

    parser.add_argument(
        "--eb", nargs='?', type=int, default=11 )
    parser.add_argument(
        "--sb", nargs='?', type=int, default=53 )

    parser.add_argument(
        "-prpr", action='store_true' )
    parser.set_defaults(prpr=False)

    parser.add_argument(
        "--decompose", action='store_true' )
    parser.add_argument(
        "--no-decompose", dest='decompose', action='store_false' )
    parser.set_defaults(decompose=False)

    parser.add_argument(
        "--daggify", action='store_true' )
    parser.add_argument(
        "--no-daggify", dest='daggify', action='store_false' )
    parser.set_defaults(daggify=True)

    return parser

def def_alias(args, mgr, script, name, val):
    symb = mgr.Symbol(name, RINT) 
    symb.ri_set_alias(True)
    script.add(name=smtcmd.DECLARE_FUN, args=[symb])

    #if args.dplus:
    #    #ca = mgr.RIEQP(symb, val)
    #    #ca = mgr.And( mgr.RILower(symb).Equals(val), mgr.RIUpper(symb).Equals(val) )
    #    cal = mgr.RILower(symb).Equals( mgr.RILower(val) )
    #    cau = mgr.RIUpper(symb).Equals( mgr.RIUpper(val) )
    #    can = mgr.RIIsNaI(symb).Iff( mgr.RIIsNaI(val) )
    #    ca = mgr.And(cal, cau, can)
    #else:
    #    ca = mgr.RIEQN(symb, val)
    ca = mgr.RIIS(symb, val)
    script.add(name=smtcmd.ASSERT, args=[ca])

    #if args.dplus:
    #    rel = mgr.Not(mgr.RIIsNaI(symb))
    #    script.add(name=smtcmd.ASSERT, args=[rel])

    return symb

def decl_const(args, mgr, script, name):
    symb = mgr.Symbol(name, RINT) 
    script.add(name=smtcmd.DECLARE_FUN, args=[symb])

    ## -max_value <= l/u
    #rel = mgr.LE( 
    #        mgr.Times( mgr.Real(-1),
    #                   mgr.Symbol('ri.max_value', REAL) ),
    #        mgr.RILower(symb) )
    #script.add(name=smtcmd.ASSERT, args=[rel])
    #rel = mgr.LE( 
    #        mgr.Times( mgr.Real(-1),
    #                   mgr.Symbol('ri.max_value', REAL) ),
    #        mgr.RIUpper(symb) )
    #script.add(name=smtcmd.ASSERT, args=[rel])

    ## l/u <= max_value
    #rel = mgr.LE( mgr.RILower(symb), 
    #              mgr.Symbol('ri.max_value', REAL) )
    #script.add(name=smtcmd.ASSERT, args=[rel])
    #rel = mgr.LE( mgr.RIUpper(symb), 
    #              mgr.Symbol('ri.max_value', REAL) )
    #script.add(name=smtcmd.ASSERT, args=[rel])

    #rel = mgr.Not(mgr.RIIsPinf(symb))
    #script.add(name=smtcmd.ASSERT, args=[rel])

    #if args.dplus:
    rel = mgr.Not(mgr.RIIsNaI(symb))
    script.add(name=smtcmd.ASSERT, args=[rel])

    return symb

#def decl_const_p(args, mgr, script, name):
#    symb = decl_const(args, mgr, script, name)
#
#    if args.dplus:
#        # l = r_dn(u)
#        rel = mgr.Equals(mgr.RILower(symb), mgr.Function(
#                    mgr.Symbol('ri.r_dn', FunctionType(REAL, [REAL])), 
#                    [mgr.RIUpper(symb)] ))
#        script.add(name=smtcmd.ASSERT, args=[rel])
#    else:
#        # l = u
#        rel = mgr.Equals(mgr.RILower(symb), mgr.RIUpper(symb))
#        script.add(name=smtcmd.ASSERT, args=[rel])
#
#    return symb

def serialize(args, script, out=sys.stdout):
    print(";; p, %d, %d" % (args.eb, args.sb))
    if not args.prpr:
        precs = []
    else:
        precs = [(args.eb, args.sb)]

    script.serialize(out, daggify=args.daggify, decompose=args.decompose, dplus=args.dplus, precs=precs, pr_pr=args.prpr)

# eof
