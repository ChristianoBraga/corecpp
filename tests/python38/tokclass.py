"""Token classes of a Python source for the LL(1) test of the grammar of Python 3.8.

The tokenizer of the running Python gives the tokens. Keywords of the grammar
and operators stand for themselves, `async` and `await` become ASYNC and
AWAIT as in the tokenizer of 3.8, and an f-string, split in parts by the
tokenizer since 3.12, is one STRING.
"""
import sys, tokenize, re
grammar_terms = set()
with open(sys.argv[1]) as g:
    for t in tokenize.generate_tokens(g.readline):
        if t.type == tokenize.STRING:
            grammar_terms.add(t.string[1:-1])
out = []
depth = 0
with open(sys.argv[2], 'rb') as f:
    for tok in tokenize.tokenize(f.readline):
        name = tokenize.tok_name[tok.type]
        if name in ('FSTRING_START', 'TSTRING_START'):
            if depth == 0: out.append('STRING')
            depth += 1; continue
        if name in ('FSTRING_END', 'TSTRING_END'):
            depth -= 1; continue
        if depth > 0: continue
        if name in ('ENCODING', 'NL', 'COMMENT'): continue
        if name == 'NAME':
            if tok.string in ('async', 'await'): out.append(tok.string.upper())
            elif tok.string in grammar_terms: out.append(tok.string)
            else: out.append('NAME')
        elif name == 'OP': out.append(tok.string)
        else: out.append(name)
print('\n'.join(out))
