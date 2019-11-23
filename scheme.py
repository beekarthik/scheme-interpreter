from __future__ import print_function  # Python 2 compatibility

from scheme_builtins import *
from scheme_reader import *
from ucb import main, trace

##############
# Eval/Apply #
##############

def scheme_eval(expr, env, _=None): # Optional third argument is ignored
    """Evaluate Scheme expression EXPR in environment ENV.

    >>> expr = read_line('(+ 2 2)')
    >>> expr
    Pair('+', Pair(2, Pair(2, nil)))
    >>> scheme_eval(expr, create_global_frame())
    4
    """
    if scheme_symbolp(expr):
        return env.lookup(expr)
    elif self_evaluating(expr):
        return expr

    if not scheme_listp(expr):
        raise SchemeError('malformed list: {0}'.format(repl_str(expr)))
    first, rest = expr.first, expr.rest
    if scheme_symbolp(first) and first in SPECIAL_FORMS:
        return SPECIAL_FORMS[first](rest, env)
    else:
        operator = scheme_eval(first, env)
        if isinstance(operator, MacroProcedure):
            return scheme_eval(operator.apply_macro(rest, env), env)
        check_procedure(operator)
        return scheme_apply(operator, rest.map(lambda x: scheme_eval(x,env)), env)

def self_evaluating(expr):
    return (scheme_atomp(expr) and not scheme_symbolp(expr)) or expr is None

def scheme_apply(procedure, args, env):
    """Apply Scheme PROCEDURE to argument values ARGS (a Scheme list) in
    environment ENV."""
    check_procedure(procedure)
    if isinstance(procedure, BuiltinProcedure):
        return procedure.apply(args, env)
    else:
        new_env = procedure.make_call_frame(args, env)
        return eval_all(procedure.body, new_env)

def eval_all(expressions, env):
    if expressions == nil:
        return
    if expressions.rest == nil:
        return scheme_eval(expressions.first, env, True)
    else:
        scheme_eval(expressions.first, env)
        return eval_all(expressions.rest, env)

################
# Environments #
################

class Frame(object):
    def __init__(self, parent):
        """An empty frame with parent frame PARENT (which may be None)."""
        self.bindings = {}
        self.parent = parent

    def __repr__(self):
        if self.parent is None:
            return '<Global Frame>'
        s = sorted(['{0}: {1}'.format(k, v) for k, v in self.bindings.items()])
        return '<{{{0}}} -> {1}>'.format(', '.join(s), repr(self.parent))

    def define(self, symbol, value):
        self.bindings[symbol] = value

    def lookup(self, symbol):
        if symbol in self.bindings:
            return self.bindings[symbol]
        elif self.parent is not None:
            return self.parent.lookup(symbol)
        raise SchemeError('unknown identifier: {0}'.format(symbol))


    def make_child_frame(self, formals, vals):
        child = Frame(self)

        while formals or vals:
            if formals == nil or vals == nil:
                raise SchemeError("unequal number of formals and values")
            child.define(formals.first, vals.first)
            formals = formals.rest
            vals = vals.rest

        return child

##############
# Procedures #
##############

class Procedure(object):
    """The supertype of all Scheme procedures."""

def scheme_procedurep(x):
    return isinstance(x, Procedure)

class BuiltinProcedure(Procedure):
    def __init__(self, fn, use_env=False, name='builtin'):
        self.name = name
        self.fn = fn
        self.use_env = use_env

    def __str__(self):
        return '#[{0}]'.format(self.name)

    def apply(self, args, env):
        if not scheme_listp(args):
            raise SchemeError('arguments are not in a list: {0}'.format(args))
        python_args = []
        while args is not nil:
            python_args.append(args.first)
            args = args.rest
        if self.use_env:
            python_args.append(env)
        try:
            return self.fn(*python_args)
        except TypeError:
            raise SchemeError('Wrong number of args passed into {0}'.format(self.fn.__name__))

class LambdaProcedure(Procedure):
    def __init__(self, formals, body, env):
        self.formals = formals
        self.body = body
        self.env = env

    def make_call_frame(self, args, env):
        return self.env.make_child_frame(self.formals, args)

    def __str__(self):
        return str(Pair('lambda', Pair(self.formals, self.body)))

    def __repr__(self):
        return 'LambdaProcedure({0}, {1}, {2})'.format(
            repr(self.formals), repr(self.body), repr(self.env))

class MacroProcedure(LambdaProcedure):
    def apply_macro(self, operands, env):
        """Apply this macro to the operand expressions."""
        return complete_apply(self, operands, env)

def add_builtins(frame, funcs_and_names):
    for name, fn, proc_name in funcs_and_names:
        frame.define(name, BuiltinProcedure(fn, name=proc_name))

#################
# Special Forms #
#################


def do_define_form(expressions, env):
    """Evaluate a define form."""
    check_form(expressions, 2)
    target = expressions.first
    if scheme_symbolp(target):
        check_form(expressions, 2, 2)
        env.define(target, scheme_eval(expressions.rest.first, env))
        return target
    elif isinstance(target, Pair) and scheme_symbolp(target.first):
        env.define(target.first, do_lambda_form(Pair(target.rest, expressions.rest), env))
        return target.first
    else:
        bad_target = target.first if isinstance(target, Pair) else target
        raise SchemeError('non-symbol: {0}'.format(bad_target))

def do_quote_form(expressions, env):
    check_form(expressions, 1, 1)
    return expressions.first

def do_begin_form(expressions, env):
    check_form(expressions, 1)
    return eval_all(expressions, env)

def do_lambda_form(expressions, env):
    check_form(expressions, 2)
    formals = expressions.first
    check_formals(formals)
    return LambdaProcedure(formals, expressions.rest, env)

def do_if_form(expressions, env):
    check_form(expressions, 2, 3)
    if scheme_truep(scheme_eval(expressions.first, env)):
        return scheme_eval(expressions.rest.first, env, True)
    elif len(expressions) == 3:
        return scheme_eval(expressions.rest.rest.first, env, True)

def do_and_form(expressions, env):
    if expressions == nil:
        return True
    if expressions.rest == nil:
        return scheme_eval(expressions.first, env, True)

    eval_first_arg = scheme_eval(expressions.first, env)

    if scheme_truep(eval_first_arg) and expressions.rest == nil:
        return eval_first_arg
    elif scheme_falsep(eval_first_arg):
        return eval_first_arg
    else:
        return do_and_form(expressions.rest, env)

def do_or_form(expressions, env):
    if expressions == nil:
        return False

    if expressions.rest == nil:
        return scheme_eval(expressions.first, env, True)

    eval_first_arg = scheme_eval(expressions.first, env)

    if scheme_falsep(eval_first_arg) and expressions.rest == nil:
        return eval_first_arg
    elif scheme_truep(eval_first_arg):
        return eval_first_arg
    else:
        return do_or_form(expressions.rest, env)

def do_cond_form(expressions, env):
    """Evaluate a cond form."""
    while expressions is not nil:
        clause = expressions.first
        check_form(clause, 1)
        if clause.first == 'else':
            test = True
            if expressions.rest != nil:
                raise SchemeError('else must be last')
        else:
            test = scheme_eval(clause.first, env)
        if scheme_truep(test):
            if clause.rest is nil:
                return test
            else:
                return eval_all(clause.rest, env)
        expressions = expressions.rest

def do_let_form(expressions, env):
    check_form(expressions, 2)
    let_env = make_let_frame(expressions.first, env)
    return eval_all(expressions.rest, let_env)

def make_let_frame(bindings, env):
    if not scheme_listp(bindings):
        raise SchemeError('bad bindings list in let form')
    def formal_and_vals(bindings):
        if bindings is nil:
            return nil, nil
        else:
            check_form(bindings.first, 1, 2)
            formals, vals = formal_and_vals(bindings.rest)
            return Pair(bindings.first.first, formals), Pair(scheme_eval(bindings.first.rest.first, env), vals)

    formals, vals = formal_and_vals(bindings)
    check_formals(formals)

    return env.make_child_frame(formals, vals)

def do_define_macro(expressions, env):
    """Evaluate a define-macro form."""
    check_form(expressions, 2)
    if isinstance(expressions.first, Pair) and scheme_symbolp(expressions.first.first):
        new_macro = MacroProcedure(expressions.first.rest, expressions.rest, env)
        env.define(expressions.first.first, new_macro)
        return expressions.first.first
    else:
        raise SchemeError('invalid macro name')


def do_quasiquote_form(expressions, env):
    def quasiquote_item(val, env, level):
        if not scheme_pairp(val):
            return val
        if val.first == 'unquote':
            level -= 1
            if level == 0:
                expressions = val.rest
                check_form(expressions, 1, 1)
                return scheme_eval(expressions.first, env)
        elif val.first == 'quasiquote':
            level += 1

        return val.map(lambda elem: quasiquote_item(elem, env, level))

    check_form(expressions, 1, 1)
    return quasiquote_item(expressions.first, env, 1)

def do_unquote(expressions, env):
    raise SchemeError('unquote outside of quasiquote')


SPECIAL_FORMS = {
    'and': do_and_form,
    'begin': do_begin_form,
    'cond': do_cond_form,
    'define': do_define_form,
    'if': do_if_form,
    'lambda': do_lambda_form,
    'let': do_let_form,
    'or': do_or_form,
    'quote': do_quote_form,
    'define-macro': do_define_macro,
    'quasiquote': do_quasiquote_form,
    'unquote': do_unquote,
}

def check_form(expr, min, max=float('inf')):
    if not scheme_listp(expr):
        raise SchemeError('badly formed expression: ' + repl_str(expr))
    length = len(expr)
    if length < min:
        raise SchemeError('too few operands in form')
    elif length > max:
        raise SchemeError('too many operands in form')

def check_formals(formals):
    symbols = set()
    def check_and_add(symbol, is_last):
        if not scheme_symbolp(symbol):
            raise SchemeError('non-symbol: {0}'.format(symbol))
        if symbol in symbols:
            raise SchemeError('duplicate symbol: {0}'.format(symbol))
        symbols.add(symbol)

    while isinstance(formals, Pair):
        check_and_add(formals.first, formals.rest is nil)
        formals = formals.rest


def check_procedure(procedure):
    if not scheme_procedurep(procedure):
        raise SchemeError('{0} is not callable: {1}'.format(
            type(procedure).__name__.lower(), repl_str(procedure)))


#################
# Dynamic Scope #
#################

class MuProcedure(Procedure):
    def __init__(self, formals, body):
        """A procedure with formal parameter list FORMALS (a Scheme list) and
        Scheme list BODY as its definition."""
        self.formals = formals
        self.body = body

    def make_call_frame(self, args, parent_env):
        return parent_env.make_child_frame(self.formals, args)

    def __str__(self):
        return str(Pair('mu', Pair(self.formals, self.body)))

    def __repr__(self):
        return 'MuProcedure({0}, {1})'.format(
            repr(self.formals), repr(self.body))

def do_mu_form(expressions, env):
    check_form(expressions, 2)
    formals = expressions.first
    check_formals(formals)
    return MuProcedure(formals, expressions.rest)

SPECIAL_FORMS['mu'] = do_mu_form

###########
# Streams #
###########

class Promise(object):
    """A promise."""
    def __init__(self, expression, env):
        self.expression = expression
        self.env = env

    def evaluate(self):
        if self.expression is not None:
            value = scheme_eval(self.expression, self.env)
            if not (value is nil or isinstance(value, Pair)):
                raise SchemeError("result of forcing a promise should be a pair or nil, but was %s" % value)
            self.value = value
            self.expression = None
        return self.value

    def __str__(self):
        return '#[promise ({0}forced)]'.format(
                'not ' if self.expression is not None else '')

def do_delay_form(expressions, env):
    check_form(expressions, 1, 1)
    return Promise(expressions.first, env)

def do_cons_stream_form(expressions, env):
    check_form(expressions, 2, 2)
    return Pair(scheme_eval(expressions.first, env),
                do_delay_form(expressions.rest, env))

SPECIAL_FORMS['cons-stream'] = do_cons_stream_form
SPECIAL_FORMS['delay'] = do_delay_form

##################
# Tail Recursion #
##################

class Thunk(object):
    def __init__(self, expr, env):
        self.expr = expr
        self.env = env

def complete_apply(procedure, args, env):
    val = scheme_apply(procedure, args, env)
    if isinstance(val, Thunk):
        return scheme_eval(val.expr, val.env)
    else:
        return val

def optimize_tail_calls(original_scheme_eval):
    def optimized_eval(expr, env, tail=False):
        if tail and not scheme_symbolp(expr) and not self_evaluating(expr):
            return Thunk(expr, env)
        result = Thunk(expr, env)
        while isinstance(result, Thunk):
            result = original_scheme_eval(result.expr, result.env)

        return result
    return optimized_eval

scheme_eval = optimize_tail_calls(scheme_eval)

####################
# Extra Procedures #
####################

def scheme_map(fn, s, env):
    check_type(fn, scheme_procedurep, 0, 'map')
    check_type(s, scheme_listp, 1, 'map')
    return s.map(lambda x: complete_apply(fn, Pair(x, nil), env))

def scheme_filter(fn, s, env):
    check_type(fn, scheme_procedurep, 0, 'filter')
    check_type(s, scheme_listp, 1, 'filter')
    head, current = nil, nil
    while s is not nil:
        item, s = s.first, s.rest
        if complete_apply(fn, Pair(item, nil), env):
            if head is nil:
                head = Pair(item, nil)
                current = head
            else:
                current.rest = Pair(item, nil)
                current = current.rest
    return head

def scheme_reduce(fn, s, env):
    check_type(fn, scheme_procedurep, 0, 'reduce')
    check_type(s, lambda x: x is not nil, 1, 'reduce')
    check_type(s, scheme_listp, 1, 'reduce')
    value, s = s.first, s.rest
    while s is not nil:
        value = complete_apply(fn, scheme_list(value, s.first), env)
        s = s.rest
    return value

################
# Input/Output #
################

def read_eval_print_loop(next_line, env, interactive=False, quiet=False,
                         startup=False, load_files=(), report_errors=False):
    """Read and evaluate input until an end of file or keyboard interrupt."""
    if startup:
        for filename in load_files:
            scheme_load(filename, True, env)
    while True:
        try:
            src = next_line()
            while src.more_on_line:
                expression = scheme_read(src)
                result = scheme_eval(expression, env)
                if not quiet and result is not None:
                    print(repl_str(result))
        except (SchemeError, SyntaxError, ValueError, RuntimeError) as err:
            if report_errors:
                if isinstance(err, SyntaxError):
                    err = SchemeError(err)
                    raise err
            if (isinstance(err, RuntimeError) and
                'maximum recursion depth exceeded' not in getattr(err, 'args')[0]):
                raise
            elif isinstance(err, RuntimeError):
                print('Error: maximum recursion depth exceeded')
            else:
                print('Error:', err)
        except KeyboardInterrupt:  # <Control>-C
            if not startup:
                raise
            print()
            print('KeyboardInterrupt')
            if not interactive:
                return
        except EOFError:  # <Control>-D, etc.
            print()
            return

def scheme_load(*args):
    """Load a Scheme source file. ARGS should be of the form (SYM, ENV) or
    (SYM, QUIET, ENV). The file named SYM is loaded into environment ENV,
    with verbosity determined by QUIET (default true)."""
    if not (2 <= len(args) <= 3):
        expressions = args[:-1]
        raise SchemeError('"load" given incorrect number of arguments: '
                          '{0}'.format(len(expressions)))
    sym = args[0]
    quiet = args[1] if len(args) > 2 else True
    env = args[-1]
    if (scheme_stringp(sym)):
        sym = eval(sym)
    check_type(sym, scheme_symbolp, 0, 'load')
    with scheme_open(sym) as infile:
        lines = infile.readlines()
    args = (lines, None) if quiet else (lines,)
    def next_line():
        return buffer_lines(*args)

    read_eval_print_loop(next_line, env, quiet=quiet, report_errors=True)

def scheme_load_all(directory, env):
    assert scheme_stringp(directory)
    directory = eval(directory)
    import os
    for x in sorted(os.listdir(".")):
        if not x.endswith(".scm"):
            continue
        scheme_load(x, env)

def scheme_open(filename):
    try:
        return open(filename)
    except IOError as exc:
        if filename.endswith('.scm'):
            raise SchemeError(str(exc))
    try:
        return open(filename + '.scm')
    except IOError as exc:
        raise SchemeError(str(exc))

def create_global_frame():
    env = Frame(None)
    env.define('eval',
               BuiltinProcedure(scheme_eval, True, 'eval'))
    env.define('apply',
               BuiltinProcedure(complete_apply, True, 'apply'))
    env.define('load',
               BuiltinProcedure(scheme_load, True, 'load'))
    env.define('load-all',
               BuiltinProcedure(scheme_load_all, True, 'load-all'))
    env.define('procedure?',
               BuiltinProcedure(scheme_procedurep, False, 'procedure?'))
    env.define('map',
               BuiltinProcedure(scheme_map, True, 'map'))
    env.define('filter',
               BuiltinProcedure(scheme_filter, True, 'filter'))
    env.define('reduce',
               BuiltinProcedure(scheme_reduce, True, 'reduce'))
    env.define('undefined', None)
    add_builtins(env, BUILTINS)
    return env

@main
def run(*argv):
    import argparse
    parser = argparse.ArgumentParser(description='CS 61A Scheme Interpreter')
    parser.add_argument('-load', '-i', action='store_true',
                       help='run file interactively')
    parser.add_argument('file', nargs='?',
                        type=argparse.FileType('r'), default=None,
                        help='Scheme file to run')
    args = parser.parse_args()


    next_line = buffer_input
    interactive = True
    load_files = []

    if args.file is not None:
        if args.load:
            load_files.append(getattr(args.file, 'name'))
        else:
            lines = args.file.readlines()
            def next_line():
                return buffer_lines(lines)
            interactive = False

    read_eval_print_loop(next_line, create_global_frame(), startup=True,
                         interactive=interactive, load_files=load_files)
    tscheme_exitonclick()
