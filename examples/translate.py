import os
import sys
import argparse

from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter, quote
from pysmt.operators import FP_RNE, FP_RNA, FP_RTP, FP_RTN, FP_RTZ
from pysmt.translators.r_fp import RFpTranslator
from pysmt.translators.r_rint import RRintTranslator

#script = parser.get_script(cStringIO(DEMO_SMTLIB))

def main(args):
    smt2_file = args.smt2_file[0]
    assert os.path.exists(smt2_file)

    parser = SmtLibParser()
    script0 = parser.get_script_fname(smt2_file)

    if args.theory != None and args.theory == "FP":
        if args.rm == "RNE":
            rm = FP_RNE
        elif args.rm == "RNA":
            rm = FP_RNA
        elif args.rm == "RTP":
            rm = FP_RTP
        elif args.rm == "RTN":
            rm = FP_RTN
        elif args.rm == "RTZ":
            rm = FP_RTZ

        translator = RFpTranslator(eb=args.eb, sb=args.sb, rm=rm, rmn=args.rmn, doSetLogic=args.sl, doSkipToFp=args.stfp)
    else:
        # The argument precision should be the actual one (cannot be 0).
        translator = RRintTranslator(dplus=args.dplus, eb=args.eb, sb=args.sb, decompose=args.decompose)

    script = translator.process(script0)

    if args.rmn < 0:
        translator.reset_rm()
        script = translator.process(script0)

    print(";; p, %d, %d" % (args.eb, args.sb))
    if not args.prpr:
        precs = []
    else:
        precs = [(args.eb, args.sb)]

    print(";;")
    print(";; translated from %s" % smt2_file)

    script.serialize(sys.stdout, daggify=args.daggify, decompose=args.decompose, dplus=args.dplus, precs=precs, pr_pr=args.prpr)

#

if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        usage="%(prog)s [OPTION] [SMT2_FILE]...",
        description="Translate Real exprs into other exprs and print the content."
    )
    parser.add_argument(
        "-v", "--version", action="version",
        version = f"{parser.prog} version 0.0.1" )

    parser.add_argument(
        "-t", "--theory", nargs='?', choices=["FP", "RInt"] )

    #parser.add_argument(
    #    "--eq", action='store_true' )
    #parser.add_argument(
    #    "--no-eq", dest='eq', action='store_false' )
    #parser.set_defaults(eq=True)

    # These precision values can be 0 when solving incrementally.
    parser.add_argument(
        "-eb", "--eb", nargs='?', type=int, default=11 )
    parser.add_argument(
        "-sb", "--sb", nargs='?', type=int, default=53 )
    parser.add_argument(
        "-rm", "--rm", nargs='?', choices=["RNE","RNA","RTP","RTN","RTZ"],
        default="RNE" )
    parser.add_argument(
        "-rmn", "--rmn", nargs='?', type=int, default=0 )

    parser.add_argument(
        '-dp', "--dplus", "--dpos", action='store_true' )
    parser.add_argument(
        '-dm', '-dn', "--dminus", "--dneg", dest='dplus', action='store_false' )
    parser.set_defaults(dplus=True)

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

    parser.add_argument(
        "--set-logic", dest='sl', action='store_true' )
    parser.add_argument(
        "--no-set-logic", dest='sl', action='store_false' )
    parser.set_defaults(sl=True)

    parser.add_argument(
        "--skip-tfp", dest='stfp', action='store_true' )
    parser.set_defaults(stfp=False)

    parser.add_argument("smt2_file", nargs=1)

    args = parser.parse_args()
    main(args)
    
# eof
