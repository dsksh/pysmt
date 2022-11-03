#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#

import warnings
from collections import namedtuple
from io import StringIO

import pysmt.smtlib.commands as smtcmd
from pysmt.exceptions import (UnknownSmtLibCommandError, NoLogicAvailableError,
                              UndefinedLogicError, PysmtValueError)
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter, quote
from pysmt.smtlib.printer_decompose import SmtDecomposePrinter
from pysmt.oracles import get_logic
from pysmt.logics import get_closer_smtlib_logic, Logic, SMTLIB2_LOGICS, QF_LRIA
from pysmt.environment import get_env
from pysmt.smtlib.script_rint import *
from pysmt.smtlib.script_rint_decompose import *
import pysmt.smtlib.script_rint_mp as mp
import pysmt.smtlib.script_rint_mp_decompose as mp_d
from pysmt.typing import BOOL, REAL

def check_sat_filter(log):
    """
    Returns the result of the check-sat command from a log.

    Raises errors in case a unique check-sat command cannot be located.
    """
    filtered = [(x,y) for x,y in log if x == smtcmd.CHECK_SAT]
    assert len(filtered) == 1
    return filtered[0][1]


class SmtLibCommand(namedtuple('SmtLibCommand', ['name', 'args'])):
    def serialize(self, outstream=None, printer=None, daggify=True, 
                  decompose=False, dplus=True, precs=[], pr_pr=True):
        """Serializes the SmtLibCommand into outstream using the given printer.

        Exactly one of outstream or printer must be specified. When
        specifying the printer, the associated outstream will be used.
        If printer is not specified, daggify controls the printer to
        be created. If true a daggified formula is produced, otherwise
        a tree printing is done.

        """
        multi_prec = len(precs) >= 2

        if (outstream is None) and (printer is not None):
            outstream = printer.stream
        elif (outstream is not None) and (printer is None):
            if decompose:
                printer = SmtDecomposePrinter(outstream, dplus=dplus, multi_prec=multi_prec)
            elif daggify:
                printer = SmtDagPrinter(outstream, multi_prec=multi_prec)
            else:
                printer = SmtPrinter(outstream, multi_prec=multi_prec)
        else:
            assert (outstream is not None and printer is not None) or \
                   (outstream is None and printer is None), \
                   "Exactly one of outstream and printer must be set."

        if self.name == smtcmd.SET_LOGIC:
            if self.args[0] == QF_LRIA:
                if pr_pr:
                    if not multi_prec:
                        outstream.write(rint_param_decls)
                        #if len(precs) > 0:
                        assert_rint_param_values(outstream, precs[0][0], precs[0][1])
                    else:
                        outstream.write(mp.rint_param_decls)
                        mp.assert_rint_param_values(outstream, precs)
                else:
                    outstream.write("\n;; The definitions of ri constants should be done by the user.\n") 

                if not multi_prec:
                    if not decompose:
                        define_rint_rnd_funs(outstream, precs, pr_pr)
                        outstream.write(rint_prologue)
                        if dplus:
                            outstream.write(rint_prologue_p)
                        else:
                            outstream.write(rint_prologue_m)
                    else:
                        outstream.write(rint_d_prologue)
                        if dplus:
                            outstream.write(rint_d_prologue_p)
                        else:
                            outstream.write(rint_d_prologue_m)
                else:
                    if not decompose:
                        mp.define_rint_rnd_funs(outstream, precs, pr_pr)
                        outstream.write(mp.rint_prologue)
                        if dplus:
                            outstream.write(mp.rint_prologue_p)
                        else:
                            outstream.write(mp.rint_prologue_m)
                    else:
                        outstream.write(mp_d.rint_prologue)
                        if dplus:
                            outstream.write(mp_d.rint_d_prologue_p)
                        else:
                            outstream.write(mp_d.rint_d_prologue_m)
            else:
                outstream.write("(%s %s)" % (self.name, self.args[0]))

        elif self.name == smtcmd.SET_OPTION:
            outstream.write("(%s %s %s)" % (self.name,self.args[0],self.args[1]))

        elif self.name == smtcmd.SET_INFO:
            if self.args[0] == ':status':
                pfx = ';'
            else:
                pfx = ''
            outstream.write("%s(%s %s %s)" % (pfx, self.name, self.args[0],
                                              quote(self.args[1])))

        elif self.name == smtcmd.ASSERT:
            if not decompose:
                outstream.write("(%s " % self.name)
                printer.printer(self.args[0])
                outstream.write(")")
            else:
                r = printer.printer(self.args[0])
                outstream.write("(%s %s)" % (self.name, r))

        elif self.name == smtcmd.GET_VALUE:
            if not decompose:
                outstream.write("(%s (" % self.name)
                printer.printer(self.args[0])
                for a in self.args[1:]:
                    outstream.write(" ")
                    printer.printer(a)
                outstream.write("))")
            else:
                r = []
                for a in self.args:
                    r.append( printer.printer(a) )

                outstream.write("(%s (%s" % (self.name, r[0]))
                for k in r[1:]:
                    outstream.write(" %s" % k)
                outstream.write("))")

        elif self.name in [smtcmd.CHECK_SAT, smtcmd.EXIT,
                           smtcmd.RESET_ASSERTIONS, smtcmd.GET_UNSAT_CORE,
                           smtcmd.GET_ASSIGNMENT, smtcmd.GET_MODEL]:
            outstream.write("(%s)" % self.name)

        elif self.name in [smtcmd.DECLARE_FUN, smtcmd.DECLARE_CONST]:
            symbol = self.args[0]
            type_str = symbol.symbol_type().as_smtlib(self.name == smtcmd.DECLARE_FUN)

            if decompose and symbol.symbol_type().is_ri_type():
                #type_str = "Real"
                type_str = REAL.as_smtlib(self.name == smtcmd.DECLARE_FUN)

            if decompose and symbol.symbol_type().is_function_type():
                raise NotImplementedError("encoding function type is not supported!")

            if symbol.symbol_type().is_ri_type():
                if decompose:
                    if dplus:
                        outstream.write("(%s %s %s)\n" % (self.name,
                                                        quote(symbol.symbol_name() + '.l'),
                                                        type_str))
                        outstream.write("(%s %s %s)\n" % (self.name,
                                                        quote(symbol.symbol_name() + '.u'),
                                                        type_str))
                        if not symbol.ri_is_alias():
                            if not multi_prec:
                                outstream.write("\n(assert (<= %s (ri.r_dn %s)))\n" % (
                                                                quote(symbol.symbol_name() + '.l'),
                                                                quote(symbol.symbol_name() + '.u') ))
                            else:
                                outstream.write("\n(assert (<= %s (ri.r_dn %d %s)))\n" % (
                                                                quote(symbol.symbol_name() + '.l'),
                                                                symbol.get_type().precision,
                                                                quote(symbol.symbol_name() + '.u') ))
        
                        outstream.write("(%s %s %s)" 
                                % ( self.name, quote(symbol.symbol_name() + '.p_nan'), 
                                    BOOL.as_smtlib(self.name == smtcmd.DECLARE_FUN) ) )

                    else: # dminus
                        outstream.write("(%s %s %s)" % (self.name,
                                                        quote(symbol.symbol_name()),
                                                        type_str))
    
                        outstream.write("\n(%s %s %s)" 
                                % ( self.name, quote(symbol.symbol_name() + '.p_nan'), 
                                    BOOL.as_smtlib(self.name == smtcmd.DECLARE_FUN) ) )
    
                else: # not decompose
                    outstream.write("(%s %s %s)" % (self.name,
                                                    quote(symbol.symbol_name()),
                                                    type_str))
    
                    if dplus:
                        # l <= u
                        #rel = self.mgr.LE(self.mgr.RILower(symb), self.mgr.RIUpper(symb))
                        #constr.append( SmtLibCommand(smtcmd.ASSERT, [rel]) )
                        outstream.write("\n(assert (<= (ri.l %s) (ri.u %s)))" % (
                            quote(symbol.symbol_name()),
                            quote(symbol.symbol_name()) ))

                        if not symbol.ri_is_alias():
                            if not multi_prec:
                                outstream.write("\n(assert (<= (ri.l %s) (ri.r_dn (ri.u %s))))" % (
                                                                quote(symbol.symbol_name()),
                                                                quote(symbol.symbol_name()) ))
                            else:
                                outstream.write("\n(assert (<= (ri.l %s) (ri.r_dn %d (ri.u %s))))" % (
                                                                quote(symbol.symbol_name()),
                                                                symbol.get_type().precision,
                                                                quote(symbol.symbol_name()) ))

                    else: # dminus
                        if not symbol.ri_is_alias():
                            # l = u
                            outstream.write("\n(assert (= (ri.l %s) (ri.u %s)))" % (
                                quote(symbol.symbol_name()),
                                quote(symbol.symbol_name()) ))
    
                #outstream.write("\n")

            else: # not RInt
                outstream.write("(%s %s %s)" % ( self.name,
                                                 quote(symbol.symbol_name()),
                                                 type_str ))

        elif self.name == smtcmd.DEFINE_FUN:
            name = self.args[0]

            # TODO
            # Seems like function defs are inlined for most cases...
            # So, okay to skip?
            if decompose:
                outstream.write(";; %s of %s skipped..." % (self.name, name))
                return

            params_list = self.args[1]
            params = " ".join(["(%s %s)" % (v, v.symbol_type().as_smtlib(funstyle=False)) for v in params_list])
            rtype = self.args[2]
            expr = self.args[3]
            outstream.write("(%s %s (%s) %s " % (self.name,
                                                name,
                                                params,
                                                rtype.as_smtlib(funstyle=False)))
            printer.printer(expr)
            outstream.write(")")

        elif self.name in [smtcmd.PUSH, smtcmd.POP]:
            outstream.write("(%s %d)" % (self.name, self.args[0]))

        elif self.name == smtcmd.DEFINE_SORT:
            name = self.args[0]
            params_list = self.args[1]
            params = " ".join(x.as_smtlib(funstyle=False) for x in params_list)
            rtype = self.args[2]
            outstream.write("(%s %s (%s) %s)" % (self.name,
                                                 name,
                                                 params,
                                                 rtype.as_smtlib(funstyle=False)))
        elif self.name == smtcmd.DECLARE_SORT:
            type_decl = self.args[0]
            outstream.write("(%s %s %d)" % (self.name,
                                            type_decl.name,
                                            type_decl.arity))

        elif self.name in smtcmd.ALL_COMMANDS:
            raise NotImplementedError("'%s' is a valid SMT-LIB command "\
                                      "but it is currently not supported. "\
                                      "Please open a bug-report." % self.name)
        else:
            raise UnknownSmtLibCommandError(self.name)

    def serialize_to_string(self, daggify=True, decompose=False):
        buf = StringIO()
        self.serialize(buf, daggify=daggify, decompose=decompose)
        return buf.getvalue()


class SmtLibScript(object):

    def __init__(self):
        self.annotations = None
        self.commands = []
        self.precisions = {}

    def add(self, name, args):
        """Adds a new SmtLibCommand with the given name and arguments."""
        self.add_command(SmtLibCommand(name=name,
                                       args=args))

    def add_command(self, command):
        self.commands.append(command)

    def add_precision(self, k, eb, sb):
        self.precisions[k] = (eb, sb)

    def get_precision(self, k):
        return self.precisions[k]

    def evaluate(self, solver):
        log = []
        for cmd in self.commands:
            r = evaluate_command(cmd, solver)
            log.append((cmd.name, r))
        return log

    def contains_command(self, command_name):
        return any(x.name == command_name for x in self.commands)

    def count_command_occurrences(self, command_name):
        return sum(1 for cmd in self.commands if cmd.name == command_name)

    def filter_by_command_name(self, command_name_set):
        return (cmd for cmd in self.commands if cmd.name in command_name_set)

    def get_strict_formula(self, mgr=None):
        if self.contains_command(smtcmd.PUSH) or \
           self.contains_command(smtcmd.POP):
            raise PysmtValueError("Was not expecting push-pop commands")
        if self.count_command_occurrences(smtcmd.CHECK_SAT) != 1:
            raise PysmtValueError("Was expecting exactly one check-sat command")
        _And = mgr.And if mgr else get_env().formula_manager.And

        assertions = [cmd.args[0]
                      for cmd in self.filter_by_command_name([smtcmd.ASSERT])]
        return _And(assertions)

    def get_declared_symbols(self):
        return {cmd.args[0] for cmd in self.filter_by_command_name([smtcmd.DECLARE_CONST,
                                                                    smtcmd.DECLARE_FUN])}
    def get_define_fun_parameter_symbols(self):
        res = set()
        for cmd in self.filter_by_command_name([smtcmd.DEFINE_FUN]):
            for s in cmd.args[1]:
                res.add(s)
        return res

    def get_last_formula(self, mgr=None):
        """Returns the last formula of the execution of the Script.

        This coincides with the conjunction of the assertions that are
        left on the assertion stack at the end of the SMTLibScript.
        """
        stack = []
        backtrack = []
        _And = mgr.And if mgr else get_env().formula_manager.And

        for cmd in self.commands:
            if cmd.name == smtcmd.ASSERT:
                stack.append(cmd.args[0])
            if cmd.name == smtcmd.RESET_ASSERTIONS:
                stack = []
                backtrack = []
            elif cmd.name == smtcmd.PUSH:
                for _ in range(cmd.args[0]):
                    backtrack.append(len(stack))
            elif cmd.name == smtcmd.POP:
                for _ in range(cmd.args[0]):
                    l = backtrack.pop()
                    stack = stack[:l]

        return _And(stack)

    def to_file(self, fname, daggify=True, decompose=False, dplus=True):
        with open(fname, "w") as outstream:
            self.serialize(outstream, daggify=daggify, decompose=decompose, dplus=dplus)

    def serialize(self, outstream, daggify=True, decompose=False, dplus=True, precs=[], pr_pr=True):
        """Serializes the SmtLibScript expanding commands"""
        multi_prec = len(precs) >= 2
        if decompose:
            printer = SmtDecomposePrinter(outstream, dplus=dplus, multi_prec=multi_prec)
        elif daggify:
            printer = SmtDagPrinter(outstream, annotations=self.annotations, multi_prec=multi_prec)
        else:
            printer = SmtPrinter(outstream, annotations=self.annotations, multi_prec=multi_prec)

        for cmd in self.commands:
            cmd.serialize(printer=printer, daggify=daggify, decompose=decompose, dplus=dplus, precs=precs, pr_pr=pr_pr)
            outstream.write("\n")

    def __len__(self):
        return len(self.commands)

    def __iter__(self):
        return iter(self.commands)

    def __str__(self):
        return "\n".join((str(cmd) for cmd in self.commands))


def smtlibscript_from_formula(formula, logic=None):
    script = SmtLibScript()

    if logic is None:
        # Get the simplest SmtLib logic that contains the formula
        f_logic = get_logic(formula)

        smt_logic = None
        try:
            smt_logic = get_closer_smtlib_logic(f_logic)
        except NoLogicAvailableError:
            warnings.warn("The logic %s is not reducible to any SMTLib2 " \
                          "standard logic. Proceeding with non-standard " \
                          "logic '%s'" % (f_logic, f_logic),
                          stacklevel=3)
            smt_logic = f_logic
    elif not (isinstance(logic, Logic) or isinstance(logic, str)):
        raise UndefinedLogicError(str(logic))
    else:
        if logic not in SMTLIB2_LOGICS:
            warnings.warn("The logic %s is not reducible to any SMTLib2 " \
                          "standard logic. Proceeding with non-standard " \
                          "logic '%s'" % (logic, logic),
                          stacklevel=3)
        smt_logic = logic

    script.add(name=smtcmd.SET_LOGIC,
               args=[smt_logic])

    # Declare all types
    types = get_env().typeso.get_types(formula, custom_only=True)
    for type_ in types:
        script.add(name=smtcmd.DECLARE_SORT, args=[type_.decl])

    deps = formula.get_free_variables()
    # Declare all variables
    for symbol in deps:
        assert symbol.is_symbol()
        script.add(name=smtcmd.DECLARE_FUN, args=[symbol])

    # Assert formula
    script.add_command(SmtLibCommand(name=smtcmd.ASSERT,
                                     args=[formula]))
    # check-sat
    script.add_command(SmtLibCommand(name=smtcmd.CHECK_SAT,
                                     args=[]))
    return script


def evaluate_command(cmd, solver):
    if cmd.name == smtcmd.SET_INFO:
        return solver.set_info(cmd.args[0], cmd.args[1])

    if cmd.name == smtcmd.SET_OPTION:
        opt = cmd.args[0]
        if opt[0] == ':':
            opt = opt[1:]
        return solver.set_option(opt, cmd.args[1])

    elif cmd.name == smtcmd.ASSERT:
        return solver.assert_(cmd.args[0])

    elif cmd.name == smtcmd.CHECK_SAT:
        return solver.check_sat()

    elif cmd.name == smtcmd.RESET_ASSERTIONS:
        return solver.reset_assertions()

    elif cmd.name == smtcmd.GET_VALUE:
        return solver.get_values(cmd.args)

    elif cmd.name == smtcmd.PUSH:
        return solver.push(cmd.args[0])

    elif cmd.name == smtcmd.POP:
        return solver.pop(cmd.args[0])

    elif cmd.name == smtcmd.EXIT:
        return solver.exit()

    elif cmd.name == smtcmd.SET_LOGIC:
        name = cmd.args[0]
        return solver.set_logic(name)

    elif cmd.name == smtcmd.DECLARE_FUN:
        return solver.declare_fun(cmd.args[0])

    elif cmd.name == smtcmd.DECLARE_CONST:
        return solver.declare_const(cmd.args[0])

    elif cmd.name == smtcmd.DEFINE_FUN:
        (var, formals, typename, body) = cmd.args
        return solver.define_fun(var, formals, typename, body)

    elif cmd.name == smtcmd.ECHO:
        return None

    elif cmd.name == smtcmd.CHECK_SAT_ASSUMING:
        return solver.check_sat(cmd.args)

    elif cmd.name == smtcmd.GET_UNSAT_CORE:
        return solver.get_unsat_core()

    elif cmd.name == smtcmd.GET_MODEL:
        return solver.get_model()

    elif cmd.name == smtcmd.DECLARE_SORT:
        name = cmd.args[0].name
        arity = cmd.args[0].arity
        return solver.declare_sort(name, arity)

    elif cmd.name in smtcmd.ALL_COMMANDS:
        raise NotImplementedError("'%s' is a valid SMT-LIB command "\
                                  "but it is currently not supported. "\
                                  "Please open a bug-report." % cmd.name)
    else:
        raise UnknownSmtLibCommandError(cmd.name)
