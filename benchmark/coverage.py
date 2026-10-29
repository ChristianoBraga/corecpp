"""Coverage of the constructions of Core C++ by the benchmark corpus.

Usage: python3 -I benchmark/coverage.py [benchmark/corpus]

Counts, for every construction, the programs that use it, and exits with 1
when a construction has no program. A construction of the abstract syntax,
CoreCpp/Syntax.lean, is found in the output of `corecpp ast`. A construction
the abstract syntax records as a flag or a name is found by a pattern on the
same output. Two forms are left out, `Ty.nullT` and `Expr.locOf`, which no
program writes.
"""
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

CONSTRUCTORS = {
    "Ty": "int bool void cls ptr lib fn",
    "UnOp": "not neg",
    "BinOp": "add sub mul div mod eq ne lt le gt ge and or",
    "Expr": "intLit boolLit nullptr var unop binop cond call newObj newLib this "
            "methodCall field arrow deref index lambda callFn",
    "Cmd": "block ite while for ret decl declRef declAuto assign exprStmt delete",
    "Decl": "cls fn tmpl libTmpl libFn",
    "Vis": "pub priv",
}

OPERATORS = ["+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "[]"]

FLAGS = {
    "return without a value": r"CoreCpp\.Cmd\.ret none",
    "base class": r"base := some",
    "constructor": r"ctor := some",
    "destructor": r"dtor := some",
    "virtual destructor": r"dtor := some \{[^}]*isVirtual := true",
    "destructor not virtual": r"dtor := some \{[^}]*isVirtual := false",
    "virtual method": r"isVirtual := true,\s*isOverride := false",
    "override": r"isOverride := true",
    "method returning a reference": r"retRef := true",
    "parameter by reference": r"byRef := true",
    "namespace": r'name := "\w+::\w+"',
    "nested namespace": r'name := "\w+::\w+::\w+"',
    "method call with .": r'\)\s+false\s+"[^"]+"\s+\[',
    "method call with ->": r'\)\s+true\s+"[^"]+"\s+\[',
    "std::vector": r'Ty\.lib "std::vector"',
    "std::function": r'Ty\.lib "std::function"',
    "assert": r'Decl\.libFn "assert"',
    "if without else": r"CoreCpp\.Cmd\.ite[\s\S]*?\]\s*\[\]",
}
for op in OPERATORS:
    FLAGS[f"operator{op}"] = r'name := "operator' + re.escape(op) + '"'


def features(ast):
    found = set()
    for kind, names in CONSTRUCTORS.items():
        for n in names.split():
            if re.search(rf"CoreCpp\.{kind}\.{n}\b", ast):
                found.add(f"{kind}.{n}")
    for name, pat in FLAGS.items():
        if re.search(pat, ast):
            found.add(name)
    return found


def main():
    corpus = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ROOT / "benchmark" / "corpus")
    files = sorted(corpus.glob("*.cpp"))
    counts = {f"{k}.{n}": 0 for k, ns in CONSTRUCTORS.items() for n in ns.split()}
    counts.update({k: 0 for k in FLAGS})
    for f in files:
        out = subprocess.run([str(ROOT / "bin" / "corecpp"), "ast", str(f)],
                             capture_output=True, text=True)
        if out.returncode != 0:
            print(f"{f.name}: corecpp does not parse it", file=sys.stderr)
            continue
        for c in features(out.stdout):
            counts[c] += 1
    width = max(map(len, counts))
    for c, n in counts.items():
        print(f"{c:<{width}}  {n:4d}{'  MISSING' if n == 0 else ''}")
    missing = [c for c, n in counts.items() if n == 0]
    print(f"{len(files)} programs, {len(counts) - len(missing)} of {len(counts)} constructions covered")
    sys.exit(1 if missing else 0)


if __name__ == "__main__":
    main()
