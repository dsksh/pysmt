import os
import sys
import argparse

from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter, quote
from pysmt.operators import FP_RNE, FP_RNA, FP_RTP, FP_RTN, FP_RTZ
from pysmt.translators.r_fp import RFpTranslator
from pysmt.translators.fp_rint import FpRintTranslator

#script = parser.get_script(cStringIO(DEMO_SMTLIB))

def main(args):
    smt2_file = args.smt2_file[0]
    assert os.path.exists(smt2_file)

    parser = SmtLibParser()
    script = parser.get_script_fname(smt2_file)

    try:
        translator = FpRintTranslator(dplus=args.dplus, decompose=args.decompose)
        ps, script = translator.process(script)
    except Exception as ex:
        print(";; p, 0, 0")
        print(';; error: %s' % ex)
        return
    
    for i in range(len(ps)):
        print(";; p%d, %d, %d" % (i, ps[i][0], ps[i][1]))
    
    print(";;")
    print(";; translated from %s" % smt2_file)
    
    script.serialize(sys.stdout, daggify=args.daggify, decompose=args.decompose, dplus=args.dplus, precs=ps, pr_pr=args.prpr)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        usage="%(prog)s [OPTION] [SMT2_FILE]...",
        description="Translate Real exprs into other exprs and print the content."
    )
    parser.add_argument(
        "-v", "--version", action="version",
        version = f"{parser.prog} version 0.0.1" )

    parser.add_argument(
        "-dp", "--dplus", "--dpos", action='store_true' )
    parser.add_argument(
        "-dm", "-dn", "--dminus", "--dneg", dest='dplus', action='store_false' )
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

    parser.add_argument("smt2_file", nargs=1)

    args = parser.parse_args()
    main(args)
    
# eof
