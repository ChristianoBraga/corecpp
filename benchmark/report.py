"""Report on the benchmark corpus, by class of construction.

Usage: python3 -I benchmark/report.py > benchmark/REPORT.md

Run from the root of the repository after `lake build benchfuel`. Reads the
corpus, runs `corecpp ast` for the constructions and `benchfuel` for the fuel,
the time and the result. Compares the result with the exit code of g++ that
the header of each program records. Runs the programs over the limit of
`benchfuel` once under `corecpp run`, for the agreement only. Classifies the
programs of `ub/` and `notcore/` with g++, `corecpp run` and `corecpp check`. Writes the
results to `benchmark/fuel.tsv` and `benchmark/slow.tsv`, and the option
`--reuse` reads them back instead of running the programs again.
"""
import concurrent.futures
import os
import pathlib
import statistics
import subprocess
import sys
import tempfile
import time as clock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import coverage  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
CORPUS = ROOT / "benchmark" / "corpus"
LIMIT = 30
WORKERS = 1
SLOW_LIMIT = None
SLOW_WORKERS = 6
EXTRA = ["ub", "notcore"]

CLASSES = [
    ("Types", [f"Ty.{n}" for n in coverage.CONSTRUCTORS["Ty"].split()]),
    ("Unary operators", [f"UnOp.{n}" for n in coverage.CONSTRUCTORS["UnOp"].split()]),
    ("Binary operators", [f"BinOp.{n}" for n in coverage.CONSTRUCTORS["BinOp"].split()]),
    ("Expressions", [f"Expr.{n}" for n in coverage.CONSTRUCTORS["Expr"].split()]
     + ["method call with .", "method call with ->"]),
    ("Commands", [f"Cmd.{n}" for n in coverage.CONSTRUCTORS["Cmd"].split()]
     + ["if without else", "return without a value"]),
    ("Declarations", [f"Decl.{n}" for n in coverage.CONSTRUCTORS["Decl"].split()]
     + ["namespace", "nested namespace", "parameter by reference"]),
    ("Classes", ["Vis.pub", "Vis.priv", "base class", "constructor", "destructor",
                 "virtual destructor", "destructor not virtual", "virtual method",
                 "override", "method returning a reference"]),
    ("Operator overloading", [f"operator{op}" for op in coverage.OPERATORS]),
    ("Library", ["std::vector", "std::function", "assert"]),
]


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT).stdout


def benchfuel(f):
    """The line of `benchfuel` for one program, or None past LIMIT seconds."""
    t0 = clock.monotonic()
    try:
        line = subprocess.run([str(ROOT / ".lake" / "build" / "bin" / "benchfuel"), str(f)],
                              capture_output=True, text=True, cwd=ROOT, timeout=LIMIT).stdout.strip() or None
    except subprocess.TimeoutExpired:
        line = None
    wall = clock.monotonic() - t0
    print(f"{f.stem} {wall:.1f} s {'done' if line else 'over the limit'}", file=sys.stderr, flush=True)
    if line and float(line.split("\t")[3]) > 1000 * wall:
        sys.exit(f"{f.stem}: evaluator time {line.split(chr(9))[3]} ms exceeds the wall time {wall:.1f} s")
    return line


def slow(f):
    """The exit code of `corecpp run` on one program and its wall time in seconds,
    with no time limit."""
    t0 = clock.monotonic()
    try:
        code = subprocess.run([str(ROOT / ".lake" / "build" / "bin" / "corecpp"), "run", str(f)],
                              capture_output=True, cwd=ROOT, timeout=SLOW_LIMIT).returncode
    except subprocess.TimeoutExpired:
        code = None
    wall = clock.monotonic() - t0
    print(f"{f.stem} {wall:.1f} s run {code}", file=sys.stderr, flush=True)
    return f"{f.stem}\t{code}\t{wall:.1f}"


UNDEFINED = ("division by zero", "int overflow", "dereference of nullptr", "outside a vector",
             "outside the store", "ended without return", "without a virtual destructor", "already freed")


def undefined(message):
    """Whether an error message of `corecpp` names undefined behaviour of C++17."""
    return any(k in message for k in UNDEFINED)


def handwritten(f):
    """The exit codes of g++ and corecpp on a program written by hand, and the error message of corecpp."""
    exe = pathlib.Path(tempfile.mkdtemp()) / f.stem
    if subprocess.run(["g++", "-std=c++17", "-o", str(exe), str(f)], capture_output=True).returncode == 0:
        g = subprocess.run([str(exe)], capture_output=True, timeout=LIMIT).returncode
        g = g % 256 if g >= 0 else 128 - g
    else:
        g = "reject"
    r = subprocess.run([str(ROOT / ".lake" / "build" / "bin" / "corecpp"), "run", str(f)],
                       capture_output=True, text=True, cwd=ROOT, timeout=LIMIT)
    m = (r.stdout + r.stderr).strip().splitlines()
    msg = m[-1] if m else ""
    msg = msg.split("error (", 1)[1].rstrip(")") if "error (" in msg else msg.split(": ", 1)[-1]
    checked = subprocess.run([str(ROOT / ".lake" / "build" / "bin" / "corecpp"), "check", str(f)],
                             capture_output=True, cwd=ROOT).returncode == 0
    return g, r.returncode, msg, checked


def cached(path, fn, files):
    """The lines of `fn` on `files`, read from `path` under --reuse, else computed and written to `path`."""
    if "--reuse" in sys.argv and path.exists():
        return path.read_text().splitlines()
    with concurrent.futures.ThreadPoolExecutor(WORKERS if fn is benchfuel else SLOW_WORKERS) as pool:
        lines = [line for line in pool.map(fn, files) if line]
    path.write_text("".join(f"{line}\n" for line in lines))
    return lines


def main():
    files = sorted(CORPUS.glob("*.cpp"))
    names = [f.stem for f in files]
    feats = {f.stem: coverage.features(run([str(ROOT / "bin" / "corecpp"), "ast", str(f)]))
             for f in files}
    fuel, time, result = {}, {}, {}
    for line in cached(ROOT / "benchmark" / "fuel.tsv", benchfuel, files):
        n, fu, res, t = line.split("\t")
        fuel[n] = int(fu) if fu.isdigit() else None
        result[n], time[n] = res, float(t)
    over = [n for n in names if n not in time]
    slow_code, slow_wall = {}, {}
    for line in cached(ROOT / "benchmark" / "slow.tsv", slow, [f for f in files if f.stem in over]):
        n, c, w = line.split("\t")
        slow_code[n] = int(c) if c.lstrip("-").isdigit() else None
        slow_wall[n] = float(w)
    gxx = {f.stem: int(f.read_text().split("Exit code ")[1].split()[0]) for f in files}
    core = {n: (int(r) % 256 if r.lstrip("-").isdigit() else 134) for n, r in result.items()}
    core |= {n: c for n, c in slow_code.items() if c is not None}
    message = {n: r[len("error ("):-1] for n, r in result.items() if r.startswith("error (")}
    seeds = [int(f.read_text().split("seed ")[1].split(".")[0]) for f in files]

    out = []
    p = out.append
    p("# Benchmark report")
    p("")
    p(f"The corpus holds {len(files)} programs, drawn by `gen.py` from the seeds 1 to {max(seeds)}. "
      f"The build discarded {max(seeds) - len(files)} seeds.")
    p("")
    p("## Agreement with g++")
    p("")
    p("The agreement covers the corpus and two directories of programs written by hand, "
      "`ub/` with undefined behaviour and `notcore/` with valid C++17 programs outside Core C++. "
      "A program fails because it is not Core C++ when `corecpp check` rejects it with a syntax or type error. "
      "A program fails due to undefined behaviour when `corecpp` gives an error result of undefined behaviour, exit code 134. "
      "The errors `outOfFuel`, `noTarget`, `negativeSize` and a failed `assert` do not count, "
      "since C++17 defines the behaviour of the last three and the first one is a limit of the evaluator "
      "(`Error` in `CoreCpp/Semantics.lean`). "
      "No exit code of g++ is compared for these two outcomes. "
      "Otherwise a program agrees when `g++ -std=c++17` and `corecpp` give the same exit code. "
      "The build keeps only corpus programs free of sanitizer reports, and `gen.py` draws only Core C++ programs, "
      "so no corpus program fails by construction.")
    p("")
    notcore = set()
    extra = {f.stem: f for d in EXTRA for f in sorted((ROOT / "benchmark" / d).glob("*.cpp"))}
    for n, f in extra.items():
        gxx[n], core[n], message[n], checked = handwritten(f)
        if not checked:
            notcore.add(n)
    outcome = {}
    for n in list(names) + list(extra):
        if n not in core:
            continue
        outcome[n] = ("Fails because the program is not Core C++" if n in notcore
                      else "Fails due to undefined behaviour" if core[n] == 134 and undefined(message.get(n, ""))
                      else "Agree" if core[n] == gxx[n] else "Fails otherwise")
    p("| Outcome | Corpus | `ub/` | `notcore/` |")
    p("| --- | --- | --- | --- |")
    for o in ["Agree", "Fails due to undefined behaviour", "Fails because the program is not Core C++"] \
            + (["Fails otherwise"] if "Fails otherwise" in outcome.values() else []):
        p(f"| {o} | {sum(outcome.get(n) == o for n in names)} | "
          + " | ".join(str(sum(outcome[n] == o for n in extra if extra[n].parent.name == d)) for d in EXTRA) + " |")
    p("")
    p("| Program | Outcome | g++ | corecpp | Message of corecpp |")
    p("| --- | --- | --- | --- | --- |")
    for n, f in extra.items():
        p(f"| `{f.parent.name}/{f.name}` | {outcome[n]} | {gxx[n]} | {core[n]} | {message[n]} |")
    p("")
    fs = [fuel[n] for n in names if fuel.get(n) is not None]
    ts = [time[n] for n in names if n in time]
    p("## Fuel and time")
    p("")
    p("The fuel of a program is the least fuel under which the evaluator gives a result, "
      "the depth of its derivation. The time is the wall clock time of the evaluator at the default fuel of 10⁶, "
      "parsing and type checking excluded, measured by `benchfuel` on one machine. "
      f"`benchfuel` runs one program at a time, each with a limit of {LIMIT} s. "
      f"{len(over)} programs exceed the limit{', ' + ', '.join(over) if over else ''}, and the table excludes them. A later section reports their agreement.")
    p("")
    p("| Measure | Minimum | Median | 90th percentile | Maximum |")
    p("| --- | --- | --- | --- | --- |")
    q = lambda xs, k: sorted(xs)[min(len(xs) - 1, int(k * len(xs)))]
    p(f"| Fuel | {min(fs)} | {statistics.median(fs):g} | {q(fs, 0.9)} | {max(fs)} |")
    p(f"| Time (ms) | {min(ts):.1f} | {statistics.median(ts):.1f} | {q(ts, 0.9):.1f} | {max(ts):.1f} |")
    p("")
    p(f"The total time of the evaluator on the corpus is {sum(ts) / 1000:.1f} s.")
    p("")
    if over:
        p(f"## Programs over {LIMIT} s")
        p("")
        p(f"Each program over the limit of `benchfuel` runs once under `corecpp run` at the default fuel, "
          f"with no time limit and no search for the least fuel. "
          f"The time is the wall clock time of the process, parsing and type checking included, "
          f"with up to {SLOW_WORKERS} programs at a time.")
        p("")
        p("| Program | g++ | corecpp | Time (s) |")
        p("| --- | --- | --- | --- |")
        for n in over:
            c = slow_code.get(n)
            p(f"| {n} | {gxx[n]} | {c} | {slow_wall[n]:.1f} |")
        p("")
    p("## Coverage by class of construction")
    p("")
    p("Each table counts the programs that use a construction, with the median fuel and the median time of those programs. "
      "`coverage.py` defines how each construction is found.")
    covered = total = 0
    for cls, items in CLASSES:
        p("")
        p(f"### {cls}")
        p("")
        p("| Construction | Programs | Median fuel | Median time (ms) |")
        p("| --- | --- | --- | --- |")
        for c in items:
            users = [n for n in names if c in feats[n]]
            total += 1
            covered += bool(users)
            fs_ = [fuel[n] for n in users if fuel.get(n) is not None]
            mf = statistics.median(fs_) if fs_ else "none"
            ts = [time[n] for n in users if n in time]
            mt = f"{statistics.median(ts):.1f}" if ts else "none"
            p(f"| `{c}` | {len(users)} | {mf if isinstance(mf, str) else f'{mf:g}'} | {mt} |")
    p("")
    p(f"The corpus covers {covered} of {total} constructions.")
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
