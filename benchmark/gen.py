"""Random generator of Core C++ programs for the benchmark.

Every generated program is meant to be well typed, to terminate and to stay
clear of undefined behaviour, so that g++ and corecpp agree on its exit code.

Usage: python3 benchmark/gen.py SEED > program.cpp

The program has the same text for the same seed. Every int value stays below
1000 in magnitude. An atom is a literal, a variable, a call or a read of an
object, a vector or a closure, each bounded so. A product of two atoms and a
sum of two products stay below 2 * 10^6, and every stored value is reduced
modulo 1000. A divisor has the form (a % 7 + 8), which lies in [2, 14]. An
index has the form ((a % n + n) % n), which lies in [0, n). Loops run at most
ten times and recursion descends at most eight levels.

Calls with side effects, the mutators of objects and the functions with
reference parameters, occur only as statements, so no expression depends on
the order in which C++17 evaluates its operands. A program deletes only the
objects it created and never uses an object after its deletion.
"""
import random
import sys


class Scope:
    FIELDS = ["ints", "fixed", "bools", "objs", "orefs", "counters", "nums",
              "vecs", "bvecs", "fns", "fns2", "preds", "frefs", "boxes",
              "lists", "trackers"]

    def __init__(self, parent=None):
        self.parent = parent
        for f in self.FIELDS:
            setattr(self, f, [])

    def all(self, field):
        s, out = self, []
        while s:
            out += getattr(s, field)
            s = s.parent
        return out


class Gen:
    def __init__(self, seed):
        self.r = random.Random(seed)
        self.n = 0
        self.funcs = []       # (name, recursive) pure int functions
        self.preds = []       # bool functions of one int
        self.voids = []       # void functions (int& a, int b)
        self.hier = None      # (base, [(class, arity)])
        self.counter = None   # qualified name of the counter class
        self.box = None       # qualified name of the class template Box
        self.ovl = False
        self.swap = False
        self.num = False
        self.node = False
        self.guard = False
        self.mk = None
        self.peek = None
        self.bump = None
        self.apply = None
        self.mul = None
        self.headers = set()

    def fresh(self, base):
        self.n += 1
        return f"{base}{self.n}"

    def chance(self, p):
        return self.r.random() < p

    # Expressions of type int

    def atom(self, sc, d, fns):
        r = self.r
        opts = ["lit"] * 2
        if sc.all("ints") or sc.all("fixed"):
            opts += ["var"] * 5
        if d > 0:
            opts += ["neg", "cond"]
            if fns:
                opts += ["call"] * 2
            if self.ovl:
                opts += ["ovl"]
            for f, k in [("objs", "obj"), ("orefs", "oref"), ("counters", "counter"),
                         ("nums", "num"), ("vecs", "vec"), ("fns", "fn"), ("fns2", "fn2"),
                         ("frefs", "fref"), ("boxes", "box"), ("lists", "list"),
                         ("trackers", "tracker"), ("bools", "bvar")]:
                if sc.all(f):
                    opts.append(k)
            if self.apply and sc.all("fns"):
                opts.append("apply")
            if self.peek and self.based(sc):
                opts.append("peek")
        k = r.choice(opts)
        a = lambda: self.atom(sc, d - 1, fns)
        b = lambda: self.bounded(sc, d - 1, fns)
        if k == "lit":
            return str(r.randint(0, 20))
        if k == "var":
            return r.choice(sc.all("ints") + sc.all("fixed"))
        if k == "neg":
            return f"-({a()})"
        if k == "cond":
            return f"({self.cond(sc, d - 1, fns)} ? {a()} : {a()})"
        if k == "bvar":
            return f"({r.choice(sc.all('bools'))} ? {a()} : {a()})"
        if k == "call":
            name, rec = r.choice(fns)
            if rec:
                return f"{name}({a()} % 8, {b()})"
            return f"{name}({b()}, {b()})"
        if k == "ovl":
            if self.chance(0.5):
                return f"ovl({b()})"
            return f"ovl({self.cond(sc, d - 1, fns)})"
        if k == "obj":
            o, cls = r.choice(sc.all("objs"))
            m = r.choice(["get()", "kind()", "twice()", "bonus()", "score"])
            if m == "score":
                m = f"score({b()})"
            if self.chance(0.2):
                return f"(*{o}).{m}"
            return f"{o}->{m}"
        if k == "oref":
            o = r.choice(sc.all("orefs"))
            return f"{o}.{r.choice(['get()', 'kind()', 'bonus()', 'score(' + b() + ')'])}"
        if k == "peek":
            o = r.choice(self.based(sc))
            return f"{self.peek}(*{o}, {b()})"
        if k == "counter":
            return f"{r.choice(sc.all('counters'))}->get()"
        if k == "num":
            nm = r.choice(sc.all("nums"))
            if self.chance(0.5):
                return f"(*{nm})[{a()}]"
            return f"{nm}->get()"
        if k == "vec":
            v, n = r.choice(sc.all("vecs"))
            return f"(*{v})[({a()} % {n} + {n}) % {n}]"
        if k == "fn":
            return f"(*{r.choice(sc.all('fns'))})({b()})"
        if k == "fn2":
            return f"(*{r.choice(sc.all('fns2'))})({b()}, {b()})"
        if k == "fref":
            return f"{r.choice(sc.all('frefs'))}({b()})"
        if k == "apply":
            return f"{self.apply}({r.choice(sc.all('fns'))}, {b()})"
        if k == "box":
            bx, t = r.choice(sc.all("boxes"))
            m = r.choice(["get()", "ref()"])
            if t == "int":
                return f"{bx}->{m}"
            return f"({bx}->{m} ? {a()} : {a()})"
        if k == "list":
            h = r.choice(sc.all("lists"))
            return f"({h} == nullptr ? 0 : {h}->val)"
        return f"{r.choice(sc.all('trackers'))}->count"

    def based(self, sc):
        """The pointers whose static type is the base, which a parameter of
        type base& binds, since a reference argument has exactly the type of
        the parameter, node param_ref of the blueprint."""
        return [o for o, st in sc.all("objs") if st == self.hier[0]]

    def prod(self, sc, d, fns):
        a = self.atom(sc, d, fns)
        k = self.r.choice(["", "", "*", "/", "%"])
        if not k:
            return a
        b = self.atom(sc, d, fns)
        if k == "*":
            return f"{a} * {b}"
        return f"{a} {k} ({b} % 7 + 8)"

    def expr(self, sc, d, fns):
        e = self.prod(sc, d, fns)
        if self.chance(0.6):
            e += f" {self.r.choice('+-')} {self.prod(sc, d, fns)}"
        return e

    def bounded(self, sc, d, fns):
        if self.chance(0.3):
            return self.atom(sc, d, fns)
        return f"({self.expr(sc, d, fns)}) % 1000"

    # Expressions of type bool

    def cond(self, sc, d, fns):
        r = self.r
        opts = ["cmp"] * 4 + ["lit"]
        if d > 0:
            opts += ["and", "or", "not"]
            if self.preds:
                opts.append("pred")
            for f, k in [("bools", "bvar"), ("preds", "lpred"), ("nums", "numcmp"),
                         ("bvecs", "bvec"), ("lists", "null")]:
                if sc.all(f):
                    opts.append(k)
            if len(sc.all("objs")) >= 2:
                opts.append("ptreq")
            if any(t == "bool" for _, t in sc.all("boxes")):
                opts.append("bbox")
        k = r.choice(opts)
        c = lambda: self.cond(sc, d - 1, fns)
        if k == "cmp" or d <= 0 and k not in ["lit"]:
            op = r.choice(["<", "<=", ">", ">=", "==", "!="])
            return f"{self.prod(sc, d, fns)} {op} {self.prod(sc, d, fns)}"
        if k == "lit":
            return r.choice(["true", "false"])
        if k == "not":
            return f"!({c()})"
        if k in ["and", "or"]:
            return f"({c()}) {'&&' if k == 'and' else '||'} ({c()})"
        if k == "pred":
            return f"{r.choice(self.preds)}({self.bounded(sc, d - 1, fns)})"
        if k == "bvar":
            return r.choice(sc.all("bools"))
        if k == "lpred":
            return f"(*{r.choice(sc.all('preds'))})({self.bounded(sc, d - 1, fns)})"
        if k == "numcmp":
            a, b = r.choice(sc.all("nums")), r.choice(sc.all("nums"))
            return f"*{a} {r.choice(['<', '<=', '>', '>=', '==', '!='])} *{b}"
        if k == "bvec":
            v, n = r.choice(sc.all("bvecs"))
            return f"(*{v})[({self.atom(sc, d - 1, fns)} % {n} + {n}) % {n}]"
        if k == "null":
            return f"{r.choice(sc.all('lists'))} {r.choice(['==', '!='])} nullptr"
        if k == "ptreq":
            (a, _), (b, _) = r.sample(sc.all("objs"), 2)
            return f"{a} {r.choice(['==', '!='])} {b}"
        bx = r.choice([b for b, t in sc.all("boxes") if t == "bool"])
        return f"{bx}->get()"

    # Statements

    def block(self, sc, ind, budget, loops, fns, main=False):
        out = []
        for _ in range(budget):
            out += self.stmt(sc, ind, loops, fns, main)
        return out

    def stmt(self, sc, ind, loops, fns, main):
        r = self.r
        p = "  " * ind
        opts = ["decl"] * 3 + ["assign"] * 2 + ["if", "bool", "block"]
        if sc.all("bools"):
            opts.append("bassign")
        if loops > 0:
            opts += ["for", "while", "forx"]
        if self.voids and sc.all("ints"):
            opts.append("void")
        if self.swap and len(sc.all("ints")) >= 2:
            opts.append("swap")
        if main:
            opts += ["ref", "vec", "bvec", "lambda", "lambda2", "pred", "assert"]
            if self.hier:
                opts += ["new"] * 2
            if sc.all("objs"):
                opts += ["mut", "oref", "alias"]
                if self.bump and self.based(sc):
                    opts.append("bump")
            if sc.all("orefs"):
                opts.append("orefmut")
            if self.counter:
                opts += ["counter"]
            if sc.all("counters"):
                opts.append("cadd")
            if self.num:
                opts.append("num")
            if len(sc.all("nums")) >= 1:
                opts += ["numop", "numw"]
            if sc.all("vecs"):
                opts += ["vwrite"]
            if sc.all("bvecs"):
                opts += ["bvwrite"]
            if sc.all("fns"):
                opts.append("fref")
            if self.mul:
                opts.append("mul")
            if self.box:
                opts.append("box")
            if sc.all("boxes"):
                opts += ["bset", "bref"]
            if self.node:
                opts.append("list")
            if sc.all("lists"):
                opts.append("lsum")
        k = r.choice(opts)
        if k in ["assign", "ref", "assert", "void"] and not sc.all("ints"):
            k = "decl"
        B = lambda d=2: self.bounded(sc, d, fns)
        C = lambda d=2: self.cond(sc, d, fns)
        if k == "decl":
            x = self.fresh("x")
            e = B()
            sc.ints.append(x)
            return [f"{p}{r.choice(['int', 'int', 'auto'])} {x} = {e};"]
        if k == "assign":
            return [f"{p}{r.choice(sc.all('ints'))} = {B()};"]
        if k == "bool":
            c = self.fresh("c")
            e = C()
            sc.bools.append(c)
            return [f"{p}bool {c} = {e};"]
        if k == "bassign":
            return [f"{p}{r.choice(sc.all('bools'))} = {C()};"]
        if k == "if":
            out = [f"{p}if ({C()}) {{"]
            out += self.block(Scope(sc), ind + 1, r.randint(1, 3), loops, fns, main)
            if self.chance(0.5):
                out += [f"{p}}} else {{"]
                out += self.block(Scope(sc), ind + 1, r.randint(1, 3), loops, fns, main)
            return out + [f"{p}}}"]
        if k == "block":
            return [f"{p}{{"] + self.block(Scope(sc), ind + 1, r.randint(1, 3), loops, fns, main) + [f"{p}}}"]
        if k in ["for", "forx", "while"]:
            i = self.fresh("i")
            n = r.randint(1, 10)
            inner = Scope(sc)
            inner.fixed.append(i)
            if k == "for":
                out = [f"{p}for (int {i} = 0; {i} < {n}; {i} = {i} + 1) {{"]
            elif k == "forx":
                out = [f"{p}int {i} = 0;", f"{p}for ({i} = 0; {i} < {n}; {i} = {i} + 1) {{"]
            else:
                out = [f"{p}int {i} = 0;", f"{p}while ({i} < {n}) {{"]
            out += self.block(inner, ind + 1, r.randint(1, 3), loops - 1, fns, main)
            if k == "while":
                out += [f"{p}  {i} = {i} + 1;"]
            return out + [f"{p}}}"]
        if k == "void":
            return [f"{p}{r.choice(self.voids)}({r.choice(sc.all('ints'))}, {B()});"]
        if k == "swap":
            a, b = r.sample(sc.all("ints"), 2)
            return [f"{p}swap({a}, {b});"]
        if k == "ref":
            x = r.choice(sc.all("ints"))
            y = self.fresh("r")
            out = [f"{p}int& {y} = {x};", f"{p}{y} = {B()};"]
            sc.fixed.append(y)
            return out
        if k == "assert":
            self.headers.add("cassert")
            x = r.choice(sc.all("ints") + sc.all("fixed"))
            return [f"{p}assert({x} < 1000 && {x} > -1000);"]
        if k == "new":
            base, classes = self.hier
            cls, arity = r.choice(classes)
            args = ", ".join(B(1) for _ in range(arity))
            o = self.fresh("o")
            st = base if self.chance(0.6) else cls
            sc.objs.append((o, st))
            return [f"{p}{st}* {o} = new {cls}({args});"]
        if k == "mut":
            o, _ = r.choice(sc.all("objs"))
            if self.chance(0.3):
                return [f"{p}(*{o}).add({B()});"]
            return [f"{p}{o}->add({B()});"]
        if k == "bump":
            o = r.choice(self.based(sc))
            return [f"{p}{self.bump}(*{o}, {B()});"]
        if k == "oref":
            o, st = r.choice(sc.all("objs"))
            y = self.fresh("q")
            sc.orefs.append(y)
            return [f"{p}{st}& {y} = *{o};"]
        if k == "orefmut":
            return [f"{p}{r.choice(sc.all('orefs'))}.add({B()});"]
        if k == "alias":
            o, st = r.choice(sc.all("objs"))
            y = self.fresh("p")
            line = f"{p}{st}* {y} = {o};"
            sc.objs.append((y, st))
            self.aliases.add(y)
            return [line]
        if k == "counter":
            c = self.fresh("k")
            e = B(1)
            sc.counters.append(c)
            if self.mk and self.chance(0.5):
                return [f"{p}{self.counter}* {c} = {self.mk}({e});"]
            return [f"{p}{self.counter}* {c} = new {self.counter}({e});"]
        if k == "cadd":
            return [f"{p}{r.choice(sc.all('counters'))}->add({B()});"]
        if k == "num":
            nm = self.fresh("n")
            e = B(1)
            sc.nums.append(nm)
            return [f"{p}Num* {nm} = new Num({e});"]
        if k == "numop":
            a, b = r.choice(sc.all("nums")), r.choice(sc.all("nums"))
            nm = self.fresh("n")
            sc.nums.append(nm)
            return [f"{p}Num* {nm} = *{a} {r.choice('+-*/%')} *{b};"]
        if k == "numw":
            return [f"{p}(*{r.choice(sc.all('nums'))})[{self.atom(sc, 1, fns)}] = {B()};"]
        if k == "vec":
            self.headers.add("vector")
            v, i = self.fresh("v"), self.fresh("i")
            n = r.randint(1, 10)
            out = [f"{p}std::vector<int>* {v} = new std::vector<int>({n});"]
            sc.vecs.append((v, n))
            inner = Scope(sc)
            inner.fixed.append(i)
            return out + [f"{p}for (int {i} = 0; {i} < {n}; {i} = {i} + 1) {{",
                          f"{p}  (*{v})[{i}] = {self.bounded(inner, 1, fns)};",
                          f"{p}}}"]
        if k == "bvec":
            self.headers.add("vector")
            v = self.fresh("v")
            n = r.randint(1, 10)
            out = [f"{p}std::vector<bool>* {v} = new std::vector<bool>({n});"]
            sc.bvecs.append((v, n))
            return out
        if k == "vwrite":
            v, n = r.choice(sc.all("vecs"))
            return [f"{p}(*{v})[({self.atom(sc, 1, fns)} % {n} + {n}) % {n}] = {B()};"]
        if k == "bvwrite":
            v, n = r.choice(sc.all("bvecs"))
            return [f"{p}(*{v})[({self.atom(sc, 1, fns)} % {n} + {n}) % {n}] = {C()};"]
        if k in ["lambda", "lambda2", "pred"]:
            self.headers.add("functional")
            f = self.fresh("f")
            body = Scope()
            ps = ["y"] if k != "lambda2" else ["y", "z"]
            body.fixed += ps
            caps = sc.all("ints") + sc.all("fixed")
            if caps:
                body.fixed += r.sample(caps, min(len(caps), r.randint(0, 2)))
            stmts = ""
            if self.chance(0.4):
                t = self.fresh("t")
                stmts = f"int {t} = {self.bounded(body, 1, [])}; "
                body.ints.append(t)
            if k == "pred":
                ret, e = "bool", self.cond(body, 1, [])
                ty = "bool(int)"
                sc.preds.append(f)
            else:
                ret, e = "int", self.bounded(body, 1, [])
                ty = "int(int)" if k == "lambda" else "int(int, int)"
                (sc.fns if k == "lambda" else sc.fns2).append(f)
            params = ", ".join(f"int {q}" for q in ps)
            return [f"{p}std::function<{ty}>* {f} = new std::function<{ty}>([=]({params}) -> {ret} {{ {stmts}return {e}; }});"]
        if k == "fref":
            f = r.choice(sc.all("fns"))
            y = self.fresh("g")
            sc.frefs.append(y)
            return [f"{p}std::function<int(int)>& {y} = *{f};"]
        if k == "mul":
            self.headers.add("functional")
            f = self.fresh("f")
            e = B(1)
            sc.fns.append(f)
            return [f"{p}std::function<int(int)>* {f} = {self.mul}({e});"]
        if k == "box":
            bx = self.fresh("b")
            if self.chance(0.6):
                line = f"{p}{self.box}<int>* {bx} = new {self.box}<int>({B(1)});"
                sc.boxes.append((bx, "int"))
            else:
                line = f"{p}{self.box}<bool>* {bx} = new {self.box}<bool>({C(1)});"
                sc.boxes.append((bx, "bool"))
            return [line]
        if k in ["bset", "bref"]:
            bx, t = r.choice(sc.all("boxes"))
            v = B() if t == "int" else C()
            if k == "bset":
                return [f"{p}{bx}->set({v});"]
            return [f"{p}{bx}->ref() = {v};"]
        if k == "list":
            h, i, t = self.fresh("h"), self.fresh("i"), self.fresh("t")
            n = r.randint(0, 8)
            inner = Scope(sc)
            inner.fixed.append(i)
            out = [f"{p}Node* {h} = nullptr;",
                   f"{p}for (int {i} = 0; {i} < {n}; {i} = {i} + 1) {{",
                   f"{p}  Node* {t} = new Node();",
                   f"{p}  {t}->val = {self.bounded(inner, 1, fns)};",
                   f"{p}  {t}->next = {h};",
                   f"{p}  {h} = {t};",
                   f"{p}}}"]
            sc.lists.append(h)
            return out
        if k == "lsum":
            h = r.choice(sc.all("lists"))
            s, q = self.fresh("x"), self.fresh("p")
            out = [f"{p}int {s} = 0;",
                   f"{p}Node* {q} = {h};",
                   f"{p}while ({q} != nullptr) {{",
                   f"{p}  {s} = ({s} + {'(*' + q + ').val' if self.chance(0.5) else q + '->val'}) % 1000;",
                   f"{p}  {q} = {q}->next;",
                   f"{p}}}"]
            sc.ints.append(s)
            return out
        return []

    # Declarations

    def function(self, rec):
        r = self.r
        name = self.fresh("f")
        fns = [f for f in self.funcs if not (rec and f[1])]
        sc = Scope()
        if rec:
            sc.fixed += ["n", "a"]
            out = [f"int {name}(int n, int a) {{",
                   f"  if (n <= 0) {{",
                   f"    return {self.bounded(sc, 1, fns)};",
                   f"  }}"]
            out += self.block(sc, 1, r.randint(1, 3), 1, fns)
            out += [f"  return ({name}(n - 1, {self.bounded(sc, 1, fns)}) + {self.atom(sc, 1, fns)}) % 1000;", "}"]
        else:
            sc.fixed += ["a", "b"]
            out = [f"int {name}(int a, int b) {{"]
            out += self.block(sc, 1, r.randint(1, 4), 2, fns)
            if self.chance(0.3):
                i = self.fresh("i")
                inner = Scope(sc)
                inner.fixed.append(i)
                out += [f"  for (int {i} = 0; {i} < {r.randint(1, 10)}; {i} = {i} + 1) {{",
                        f"    if ({self.cond(inner, 1, fns)}) {{",
                        f"      return {self.bounded(inner, 1, fns)};",
                        "    }",
                        "  }"]
            out += [f"  return {self.bounded(sc, 2, fns)};", "}"]
        self.funcs.append((name, rec))
        return out

    def pred(self):
        name = self.fresh("pred")
        sc = Scope()
        sc.fixed.append("a")
        out = [f"bool {name}(int a) {{", f"  return {self.cond(sc, 2, self.funcs)};", "}"]
        self.preds.append(name)
        return out

    def void(self):
        name = self.fresh("set")
        sc = Scope()
        sc.fixed.append("b")
        sc.fixed.append("a")
        out = [f"void {name}(int& a, int b) {{",
               f"  if ({self.cond(sc, 1, self.funcs)}) {{",
               "    return;",
               "  }",
               f"  a = {self.bounded(sc, 1, self.funcs)};",
               "}"]
        self.voids.append(name)
        return out

    def hierarchy(self):
        r = self.r
        base = self.fresh("Base")
        out = [f"class {base} {{",
               "private:",
               "  int v;",
               "  int secret() { return v % 10; }",
               "public:",
               "  int get() { return v; }",
               "  void setv(int x) { v = x; }",
               "  void add(int d) { v = (v + d) % 1000; }",
               "  int kind() { return 1; }",
               "  int twice() { return (this->secret() * 2 + this->v) % 1000; }",
               "  virtual int score(int x) { return (v + x) % 1000; }",
               f"  virtual int bonus() {{ return {r.randint(0, 9)}; }}",
               f"  virtual ~{base}() {{ }}",
               "};"]
        classes = [(base, 0)]
        parent = base
        if self.chance(0.5):
            mid = self.fresh("Mid")
            out += [f"class {mid} : public {base} {{",
                    "public:",
                    f"  int score(int x) override {{ return (get() * 2 + x) % 1000; }}",
                    f"  int bonus() override {{ return {r.randint(10, 19)}; }}",
                    "};"]
            classes.append((mid, 0))
            parent = mid
        for _ in range(r.randint(1, 2)):
            der = self.fresh("Derived")
            k = r.randint(1, 9)
            op = r.choice(["+", "-", "*"])
            out += [f"class {der} : public {parent} {{",
                    "private:",
                    "  int w;",
                    "public:",
                    f"  {der}(int x, int y) {{",
                    "    this->w = y;",
                    "    setv(x);",
                    "  }",
                    f"  int score(int x) override {{ return (get() {op} w * {k} + x) % 1000; }}",
                    "};"]
            classes.append((der, 2))
        self.hier = (base, classes)
        if self.chance(0.6):
            self.peek = self.fresh("peek")
            out += [f"int {self.peek}({base}& o, int x) {{",
                    "  return (o.score(x) + o.get()) % 1000;",
                    "}"]
        if self.chance(0.6):
            self.bump = self.fresh("bump")
            out += [f"void {self.bump}({base}& o, int d) {{",
                    "  o.add(d);",
                    "}"]
        return out

    def counter_decl(self):
        r = self.r
        cls = self.fresh("Counter")
        body = [f"class {cls} {{",
                "private:",
                "  int v;",
                "public:",
                f"  {cls}(int x) {{ this->v = x; }}",
                "  int get() { return v; }",
                "  void add(int d) { v = (v + d) % 1000; }",
                "};"]
        ns = r.choice([[], ["Util"], ["Outer", "Inner"]])
        for name in reversed(ns):
            body = [f"namespace {name} {{"] + ["  " + l for l in body] + ["}"]
        self.counter = "::".join(ns + [cls])
        out = body
        if self.chance(0.5):
            self.mk = self.fresh("make")
            out += [f"{self.counter}* {self.mk}(int x) {{", f"  return new {self.counter}(x);", "}"]
        return out

    def box_decl(self):
        body = ["template<typename T>",
                "class Box {",
                "private:",
                "  T item;",
                "public:",
                "  Box(T x) { this->item = x; }",
                "  T get() { return item; }",
                "  void set(T x) { item = x; }",
                "  T& ref() { return item; }",
                "};"]
        if self.chance(0.2):
            self.box = "Store::Box"
            return ["namespace Store {"] + ["  " + l for l in body] + ["}"]
        self.box = "Box"
        return body

    def num_decl(self):
        self.num = True
        ops = []
        for op in "+-*":
            ops.append(f"  Num* operator{op}(Num& o) {{ return new Num((v {op} o.v) % 1000); }}")
        for op in "/%":
            ops.append(f"  Num* operator{op}(Num& o) {{ return new Num(v {op} (o.get() % 7 + 8)); }}")
        for op in ["==", "!=", "<", "<=", ">", ">="]:
            ops.append(f"  bool operator{op}(Num& o) {{ return v {op} o.get(); }}")
        return ["class Num {",
                "private:",
                "  int v;",
                "public:",
                "  Num(int x) { this->v = x; }",
                "  int get() { return v; }"] + ops + [
                "  int& operator[](int i) { return v; }",
                "};"]

    def program(self):
        r = self.r
        self.aliases = set()
        decls = []
        if self.chance(0.5):
            decls.append(self.counter_decl())
        if self.chance(0.6):
            decls.append(self.hierarchy())
        if self.chance(0.4):
            self.headers.add("vector")
            decls.append(self.box_decl())
        if self.chance(0.4):
            decls.append(self.num_decl())
        if self.chance(0.4):
            self.node = True
            decls.append(["class Node {", "public:", "  int val;", "  Node* next;", "};"])
        if self.chance(0.3):
            self.guard = True
            decls.append(["class Tracker {", "public:", "  int count;", "};",
                          "class Guard {",
                          "private:",
                          "  Tracker* t;",
                          "  int k;",
                          "public:",
                          "  Guard(Tracker* t0, int k0) {",
                          "    this->t = t0;",
                          "    this->k = k0;",
                          "  }",
                          "  ~Guard() { t->count = (t->count + k) % 1000; }",
                          "};"])
        if self.chance(0.4):
            self.swap = True
            decls.append(["void swap(int& a, int& b) {", "  int t = a;", "  a = b;", "  b = t;", "}"])
        if self.chance(0.3):
            self.ovl = True
            decls.append(["int ovl(int x) {", f"  return (x * {r.randint(2, 9)}) % 1000;", "}",
                          "int ovl(bool x) {", f"  return x ? {r.randint(0, 20)} : {r.randint(0, 20)};", "}"])
        if self.chance(0.3):
            self.headers.add("functional")
            self.apply = self.fresh("apply")
            decls.append([f"int {self.apply}(std::function<int(int)>* f, int x) {{",
                          "  return (*f)(x);", "}"])
        if self.chance(0.3):
            self.headers.add("functional")
            self.mul = self.fresh("mul")
            decls.append([f"std::function<int(int)>* {self.mul}(int k) {{",
                          "  return new std::function<int(int)>([=](int x) -> int { return (k * x) % 1000; });",
                          "}"])
        for _ in range(r.randint(0, 4)):
            decls.append(self.function(self.chance(0.4)))
        if self.chance(0.4):
            decls.append(self.pred())
        if self.chance(0.3):
            decls.append(self.void())
        sc = Scope()
        body = []
        if self.guard:
            body += ["  Tracker* tracker = new Tracker();"]
            sc.trackers.append("tracker")
        body += self.block(sc, 1, r.randint(4, 12), 2, list(self.funcs), main=True)
        if self.guard:
            g = self.fresh("guard")
            body += [f"  Guard* {g} = new Guard(tracker, {self.bounded(sc, 1, list(self.funcs))});",
                     f"  delete {g};"]
        res = self.fresh("result")
        body.append(f"  int {res} = {self.bounded(sc, 2, list(self.funcs))};")
        for o, _ in sc.objs:
            if o not in self.aliases:
                body.append(f"  delete {o};")
        for f in ["counters", "nums", "fns", "fns2", "preds", "trackers"]:
            for x in sc.all(f):
                body.append(f"  delete {x};")
        for v, _ in sc.vecs + sc.bvecs + sc.boxes:
            body.append(f"  delete {v};")
        for h in sc.lists:
            t = self.fresh("t")
            body += [f"  while ({h} != nullptr) {{",
                     f"    Node* {t} = {h}->next;",
                     f"    delete {h};",
                     f"    {h} = {t};",
                     "  }"]
        body.append(f"  return {res};")
        head = [f"#include <{h}>" for h in sorted(self.headers)]
        lines = head + [""]
        for d in decls:
            lines += d + [""]
        lines += ["int main() {"] + body + ["}"]
        return "\n".join(lines) + "\n"


if __name__ == "__main__":
    sys.stdout.write(Gen(int(sys.argv[1])).program())
