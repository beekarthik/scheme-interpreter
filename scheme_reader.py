from __future__ import print_function  # Python 2 compatibility

import numbers

from ucb import main, trace, interact
from scheme_tokens import tokenize_lines, DELIMITERS
from buffer import Buffer, InputReader, LineReader
import scheme

# Pairs and Scheme lists

class Pair(object):
    def __init__(self, first, rest):
        from scheme_builtins import scheme_valid_cdrp, SchemeError
        if not (rest is nil or isinstance(rest, Pair) or type(rest).__name__ == 'Promise'):
            print(rest, type(rest).__name__)
            raise SchemeError("cdr can only be a pair, nil, or a promise but was {}".format(rest))
        self.first = first
        self.rest = rest

    def __repr__(self):
        return 'Pair({0}, {1})'.format(repr(self.first), repr(self.rest))

    def __str__(self):
        s = '(' + repl_str(self.first)
        rest = self.rest
        while isinstance(rest, Pair):
            s += ' ' + repl_str(rest.first)
            rest = rest.rest
        if rest is not nil:
            s += ' . ' + repl_str(rest)
        return s + ')'

    def __len__(self):
        n, rest = 1, self.rest
        while isinstance(rest, Pair):
            n += 1
            rest = rest.rest
        if rest is not nil:
            raise TypeError('length attempted on improper list')
        return n

    def __eq__(self, p):
        if not isinstance(p, Pair):
            return False
        return self.first == p.first and self.rest == p.rest

    def map(self, fn):
        mapped = fn(self.first)
        if self.rest is nil or isinstance(self.rest, Pair):
            return Pair(mapped, self.rest.map(fn))
        else:
            raise TypeError('ill-formed list (cdr is a promise)')

    def flatmap(self, fn):
        from scheme_builtins import scheme_append
        mapped = fn(self.first)
        if self.rest is nil or isinstance(self.rest, Pair):
            return scheme_append(mapped, self.rest.flatmap(fn))
        else:
            raise TypeError('ill-formed list (cdr is a promise)')


class nil(object):
    def __repr__(self):
        return 'nil'

    def __str__(self):
        return '()'

    def __len__(self):
        return 0

    def map(self, fn):
        return self

    def flatmap(self, fn):
        return self

nil = nil()

quotes = {"'":  'quote',
          '`':  'quasiquote',
          ',':  'unquote'}

def scheme_read(src):
    if src.current() is None:
        raise EOFError
    val = src.pop_first()
    if val == 'nil':
        return nil
    elif val == '(':
        return read_tail(src)
    elif val in quotes:
        return Pair(quotes[val], Pair(scheme_read(src), nil))
    elif val not in DELIMITERS:
        return val
    else:
        raise SyntaxError('unexpected token: {0}'.format(val))

def read_tail(src):
    try:
        if src.current() is None:
            raise SyntaxError('unexpected end of file')
        elif src.current() == ')':
            src.pop_first()
            return nil
        else:
            return Pair(scheme_read(src), read_tail(src))
    except EOFError:
        raise SyntaxError('unexpected end of file')


def buffer_input(prompt='scm> '):
    return Buffer(tokenize_lines(InputReader(prompt)))

def buffer_lines(lines, prompt='scm> ', show_prompt=False):
    if show_prompt:
        input_lines = lines
    else:
        input_lines = LineReader(lines, prompt)
    return Buffer(tokenize_lines(input_lines))

def read_line(line):
    return scheme_read(Buffer(tokenize_lines([line])))

def repl_str(val):
    if val is True:
        return "#t"
    if val is False:
        return "#f"
    if val is None:
        return "undefined"
    if isinstance(val, numbers.Number) and not isinstance(val, numbers.Integral):
        return repr(val)
    return str(val)

def read_print_loop():
    while True:
        try:
            src = buffer_input('read> ')
            while src.more_on_line:
                expression = scheme_read(src)
                if expression == 'exit':
                    print()
                    return
                print('str :', expression)
                print('repr:', repr(expression))
        except (SyntaxError, ValueError) as err:
            print(type(err).__name__ + ':', err)
        except (KeyboardInterrupt, EOFError):  # <Control>-D, etc.
            print()
            return

@main
def main(*args):
    if len(args) and '--repl' in args:
        read_print_loop()
