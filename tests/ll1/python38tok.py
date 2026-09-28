"""Token classes of a Python source, one per line, for tests/ll1/Python.lean.

Usage: python3 python38tok.py python38.ebnf program.py

The tokenizer of the running Python gives the tokens. The quoted terminals of
the grammar and the operators stand for themselves, `async` and `await` become
ASYNC and AWAIT as in the tokenizer of 3.8, and an f-string, split in parts by
the tokenizer since 3.12, is one STRING. Comments, blank lines and the
encoding are dropped.
"""
import re
import sys
import tokenize

grammar = re.sub(r'\(\*.*?\*\)', '', open(sys.argv[1]).read(), flags=re.S)
literals = set(re.findall(r'"([^"]*)"|\'([^\']*)\'', grammar))
literals = {a or b for a, b in literals}
out = []
depth = 0
with open(sys.argv[2], 'rb') as f:
    for tok in tokenize.tokenize(f.readline):
        name = tokenize.tok_name[tok.type]
        if name in ('FSTRING_START', 'TSTRING_START'):
            if depth == 0:
                out.append('STRING')
            depth += 1
            continue
        if name in ('FSTRING_END', 'TSTRING_END'):
            depth -= 1
            continue
        if depth > 0 or name in ('ENCODING', 'NL', 'COMMENT'):
            continue
        if name == 'NAME':
            if tok.string in ('async', 'await'):
                out.append(tok.string.upper())
            elif tok.string in literals:
                out.append(tok.string)
            else:
                out.append('NAME')
        elif name == 'OP':
            out.append(tok.string)
        else:
            out.append(name)
print('\n'.join(out))
