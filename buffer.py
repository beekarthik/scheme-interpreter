from __future__ import print_function  # Python 2 compatibility

import math
import sys

if sys.version_info[0] < 3:  # Python 2 compatibility
    def input(prompt):
        sys.stderr.write(prompt)
        sys.stderr.flush()
        line = sys.stdin.readline()
        if not line: raise EOFError()
        return line.rstrip('\r\n')

class Buffer(object):
    def __init__(self, source):
        self.index = 0
        self.lines = []
        self.source = source
        self.current_line = ()
        self.current()

    def pop_first(self):
        current = self.current()
        self.index += 1
        return current

    def current(self):
        while not self.more_on_line:
            self.index = 0
            try:
                self.current_line = next(self.source)
                self.lines.append(self.current_line)
            except StopIteration:
                self.current_line = ()
                return None
        return self.current_line[self.index]

    @property
    def more_on_line(self):
        return self.index < len(self.current_line)

    def __str__(self):
        n = len(self.lines)
        msg = '{0:>' + str(math.floor(math.log10(n))+1) + "}: "

        s = ''
        for i in range(max(0, n-4), n-1):
            s += msg.format(i+1) + ' '.join(map(str, self.lines[i])) + '\n'
        s += msg.format(n)
        s += ' '.join(map(str, self.current_line[:self.index]))
        s += ' >> '
        s += ' '.join(map(str, self.current_line[self.index:]))
        return s.strip()

try:
    import readline
except:
    pass

class InputReader(object):
    def __init__(self, prompt):
        self.prompt = prompt

    def __iter__(self):
        while True:
            yield input(self.prompt)
            self.prompt = ' ' * len(self.prompt)

class LineReader(object):
    def __init__(self, lines, prompt, comment=";"):
        self.lines = lines
        self.prompt = prompt
        self.comment = comment

    def __iter__(self):
        while self.lines:
            line = self.lines.pop(0).strip('\n')
            if (self.prompt is not None and line != "" and
                not line.lstrip().startswith(self.comment)):
                print(self.prompt + line)
                self.prompt = ' ' * len(self.prompt)
            yield line
        raise EOFError
