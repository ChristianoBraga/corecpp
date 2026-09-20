import CoreCpp

open CoreCpp

/-! ## Lexer and parser -/

#eval lex "int x = 10; // comment\nx = x + 1;"

#eval parseExpr "1 + 2 * 3"
#eval parseExpr "a < b && !(c == d) ? x : y"
#eval parseExpr "f(1, g(2), -3)"
#eval parseExpr "1 +"

#eval parseStatement "if (x % 2 == 0) { x = x / 2; } else { x = x - 1; }"
#eval parseStatement "for (int i = 2; i <= n; i = i + 1) { acc = acc * i; }"
#eval parseStatement "int x;"

#eval parseProgram "int factorial(int n) {
  int acc = 1;
  for (int i = 2; i <= n; i = i + 1) {
    acc = acc * i;
  }
  return acc;
}

int main() {
  int x = 5;
  while (x > 0) {
    if (x % 2 == 0) { x = x / 2; } else { x = x - 1; }
  }
  auto y = factorial(4);
  return y;
}"

/-! ## Evaluator -/

def prog (s : String) : Except String (Except Error Val) :=
  (parseProgram s).map run

#eval prog "int factorial(int n) {
  int acc = 1;
  for (int i = 2; i <= n; i = i + 1) { acc = acc * i; }
  return acc;
}
int main() { return factorial(5); }"

-- scope, the inner block variable does not shadow the outer one after the block
#eval prog "int main() {
  int x = 1;
  { int x = 10; x = x + 1; }
  return x;
}"

-- return inside while interrupts the loop
#eval prog "int main() {
  int i = 0;
  while (true) { i = i + 1; if (i == 7) { return i; } }
}"

-- int overflow is an error
#eval prog "int main() { int x = 2147483647; return x + 1; }"

-- division by zero is an error
#eval prog "int main() { int z = 0; return 10 / z; }"

-- division truncates toward zero, as in C++
#eval prog "int main() { return -7 / 2 * 10 + -7 % 2; }"

-- short circuit avoids the division
#eval prog "int main() { int z = 0; bool b = z != 0 && 10 / z > 1; return b ? 1 : 0; }"

-- void function without return
#eval prog "void nothing() { int x = 1; } int main() { nothing(); return 3; }"

-- assignment evaluates the right operand before the left
#eval prog "int main() { int x = 1; x = x + 41; return x; }"

-- type checking
#eval (parseProgram "int main() { bool b = true; int x = b + 1; return x; }").map check
#eval (parseProgram "int f(int n) { return n; } int main() { return f(true); }").map check
#eval (parseProgram "int main() { int x = 1; return x; }").map check

-- derivation trace of a small program
#eval do
  let p ← parseProgram "int main() { int x = 1; x = x + 41; return x; }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## UD II, classes with fields, pointers, nullptr and vectors -/

-- a linked list summed through pointers
#eval prog "class No { public: int valor; No* prox; };
int soma(No* p) { return p == nullptr ? 0 : p->valor + soma(p->prox); }
int main() {
  No* lista = new No();
  lista->valor = 1;
  lista->prox = new No();
  lista->prox->valor = 2;
  return soma(lista);
}"

-- a vector created with new, indexed through the pointer
#eval prog "int main() {
  std::vector<int>* v = new std::vector<int>(3);
  (*v)[0] = 1; (*v)[1] = 2; (*v)[2] = 3;
  int s = 0;
  for (int i = 0; i < 3; i = i + 1) { s = s + (*v)[i]; }
  return s;
}"

-- two pointers to the same object, one write seen through both
#eval prog "class P { public: int x; };
int main() { P* a = new P(); P* b = a; b->x = 7; return a->x + (a == b ? 10 : 0); }"

-- new gives every field its default value
#eval prog "class R { public: int n; bool ok; R* prox; };
int main() { R* r = new R(); return r->n + (r->ok ? 10 : 1) + (r->prox == nullptr ? 100 : 0); }"

-- dereferencing nullptr is an error
#eval prog "class No { public: int valor; No* prox; };
int main() { No* p = nullptr; return p->valor; }"

-- an index outside the vector is an error
#eval prog "int main() { std::vector<int>* v = new std::vector<int>(2); return (*v)[2]; }"

-- a negative size is an error
#eval prog "int main() { std::vector<int>* v = new std::vector<int>(0 - 1); return 0; }"

-- objects never live in variables, only behind pointers
#eval (parseProgram "class P { public: int x; }; int main() { P a = new P(); return 0; }").map check
-- an unknown field
#eval (parseProgram "class P { public: int x; }; int main() { P* a = new P(); return a->y; }").map check
-- nullptr has no type of its own for a variable
#eval (parseProgram "int main() { auto p = nullptr; return 0; }").map check
-- a field of class type would be an object by value
#eval (parseProgram "class Q { public: int y; }; class P { public: Q q; }; int main() { return 0; }").map check
-- pointers admit equality and nothing else
#eval (parseProgram "class P { public: int x; }; int main() { P* a = new P(); return a + 1; }").map check

-- the trace of a field update
#eval do
  let p ← parseProgram "class P { public: int x; }; int main() { P* a = new P(); a->x = 3; return a->x; }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## UD III, local references and evaluation order -/

-- a reference is a second name for the same location
#eval prog "int main() { int x = 1; int& y = x; y = y + 41; return x; }"

-- the reference leaves with its block, the variable stays
#eval prog "int main() { int x = 1; { int& y = x; y = 5; } return x + 1; }"

-- references to a field and to a vector element
#eval prog "class P { public: int a; int b; };
int main() {
  P* p = new P(); int& a = p->a; a = 7;
  std::vector<int>* v = new std::vector<int>(3); int& e = (*v)[1]; e = 9;
  return p->a * 10 + (*v)[1];
}"

-- a reference to a pointer variable
#eval prog "class P { public: int a; };
int main() { P* p = nullptr; P*& q = p; q = new P(); q->a = 3; return p->a; }"

-- a reference made inside a block to a field of an object that escapes the block
#eval prog "class P { public: int a; };
int main() { P* keep = nullptr; { P* p = new P(); int& r = p->a; r = 4; keep = p; } return keep->a; }"

-- calls with effects inside an expression, left operand first
#eval prog "class Cont { public: int n; };
int prox(Cont* c) { c->n = c->n + 1; return c->n; }
int main() { Cont* c = new Cont(); return prox(c) + 10 * prox(c); }"

-- the initialiser of a reference must denote a location
#eval (parseProgram "int main() { int& r = 5; return r; }").map check
-- the referent has the declared type
#eval (parseProgram "int main() { int x = 1; bool& b = x; return 0; }").map check

-- the trace of an aliasing write
#eval do
  let p ← parseProgram "int main() { int x = 1; int& y = x; y = 2; return x; }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## UD IV, reference parameters, lambdas and std::function -/

-- swap by reference, the parameters alias the arguments
#eval prog "void troca(int& a, int& b) { int t = a; a = b; b = t; }
int main() { int x = 1; int y = 2; troca(x, y); return x * 10 + y; }"

-- a reference parameter bound to a field and to a vector element
#eval prog "class P { public: int a; };
void inc(int& r) { r = r + 1; }
int main() { P* p = new P(); inc(p->a); inc(p->a);
  std::vector<int>* v = new std::vector<int>(2); inc((*v)[1]);
  return p->a * 10 + (*v)[1]; }"

-- a lambda returned by a function and applied through a std::function parameter
#eval prog "std::function<int(int)> multiplicador(int k) {
  return [=](int x) -> int { return k * x; };
}
int aplica(std::function<int(int)> f, int v) { return f(v); }
int main() { return aplica(multiplicador(3), 14); }"

-- a counter through a captured pointer, the object outlives its block
#eval prog "class Caixa { public: int valor; };
std::function<int()> contador() {
  Caixa* c = new Caixa();
  c->valor = 0;
  return [=]() -> int { c->valor = c->valor + 1; return c->valor; };
}
int main() { std::function<int()> k = contador(); int primeiro = k(); return k() + k() + primeiro; }"

-- the capture is a copy taken at the lambda, later writes to n are not seen
#eval prog "int main() { int n = 5;
  std::function<int(int)> soma = [=](int x) -> int { return x + n; };
  n = 100; return soma(1); }"

-- a lambda passed directly as an argument
#eval prog "int duasVezes(std::function<int(int)> f, int x) { return f(f(x)); }
int main() { return duasVezes([=](int x) -> int { return x * x; }, 3); }"

-- a function value copied into another variable and called through it
#eval prog "int main() { std::function<int(int, int)> g = [=](int a, int b) -> int { return a - b; };
  std::function<int(int, int)> h = g; return h(10, 3); }"

-- a captured variable is read only inside the lambda
#eval (parseProgram "int main() { int n = 1; std::function<int()> f = [=]() -> int { n = 2; return n; }; return f(); }").map check
-- and cannot be aliased by a reference either
#eval (parseProgram "int main() { int n = 1; std::function<int()> f = [=]() -> int { int& r = n; r = 3; return n; }; return f(); }").map check
-- a lambda is not an auto initialiser, by the grammar
#eval parseProgram "int main() { auto f = [=](int x) -> int { return x; }; return f(1); }"
-- a lambda is not an operand, by the grammar
#eval parseProgram "int main() { return 1 + [=]() -> int { return 1; }; }"
-- the argument of a reference parameter denotes a location
#eval (parseProgram "void inc(int& r) { r = r + 1; } int main() { inc(5); return 0; }").map check
-- only function values are called
#eval (parseProgram "int main() { int x = 1; return x(2); }").map check
-- the lambda has exactly the parameter types of the std::function
#eval (parseProgram "int main() { std::function<int(int)> f = [=](bool b) -> int { return 1; }; return f(1); }").map check
-- no field of function type in this subset
#eval (parseProgram "class C { public: std::function<int()> f; }; int main() { return 0; }").map check

-- the trace of a call through a closure
#eval do
  let p ← parseProgram "int main() { int n = 2; std::function<int(int)> f = [=](int x) -> int { return x + n; }; return f(40); }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## UD V, classes, methods, inheritance, delete and namespaces -/

-- a class with a private field, a constructor and methods, this and the unqualified field
#eval prog "class Contador {
private:
  int valor;
public:
  Contador(int inicial) { this->valor = inicial; }
  void incrementa() { valor = valor + 1; }
  int atual() { return valor; }
};
int main() { Contador* c = new Contador(40); c->incrementa(); c->incrementa(); return c->atual(); }"

-- an abstract data type, a stack over a vector
#eval prog "class Pilha {
private:
  std::vector<int>* itens;
  int topo;
public:
  Pilha(int n) { this->itens = new std::vector<int>(n); this->topo = 0; }
  void empilha(int x) { (*itens)[topo] = x; topo = topo + 1; }
  int desempilha() { topo = topo - 1; return (*itens)[topo]; }
};
int main() { Pilha* p = new Pilha(8); p->empilha(1); p->empilha(41); return p->desempilha() + p->desempilha(); }"

-- inheritance, virtual dispatch, subsumption, a namespace and delete with a virtual destructor
#eval prog "namespace Geometria {
  class Forma { public: virtual int area() { return 0; } virtual ~Forma() { } };
  class Quadrado : public Forma {
  private: int lado;
  public: Quadrado(int l) { this->lado = l; } int area() override { return lado * lado; }
  };
}
int main() { Geometria::Forma* f = new Geometria::Quadrado(4); int a = f->area(); delete f; return a; }"

-- a non virtual method through a base pointer is the method of the base
#eval prog "class B { public: int f() { return 1; } virtual int g() { return 10; } };
class D : public B { public: int g() override { return 20; } };
int main() { B* b = new D(); return b->f() + b->g(); }"

-- destructors run from the tag up to the root
#eval prog "class Log { public: int n; };
class B { public: Log* log; virtual ~B() { log->n = log->n + 1; } };
class D : public B { public: ~D() { log->n = log->n + 10; } };
int main() { Log* g = new Log(); D* d = new D(); d->log = g; B* b = d; delete b; return g->n; }"

-- delete nullptr does nothing, delete of a vector frees its elements
#eval prog "class C { public: int x; };
int main() { C* p = nullptr; delete p; std::vector<int>* v = new std::vector<int>(3); delete v; return 5; }"

-- a method returning this
#eval prog "class A { public: int k; A* self() { return this; } };
int main() { A* a = new A(); a->k = 3; return a->self()->self()->k; }"

-- double delete is error
#eval prog "class C { public: int x; }; int main() { C* p = new C(); delete p; delete p; return 0; }"

-- delete through a base pointer without a virtual destructor is error
#eval prog "class B { public: int x; ~B() { } }; class D : public B { public: int y; };
int main() { B* b = new D(); delete b; return 0; }"

-- access after delete is error
#eval prog "class C { public: int x; }; int main() { C* p = new C(); delete p; return p->x; }"

-- a private member is not visible outside the class
#eval (parseProgram "class C { private: int x; public: C() { x = 1; } }; int main() { C* p = new C(); return p->x; }").map check
-- a non virtual method is not redefined
#eval (parseProgram "class B { public: int f() { return 1; } }; class D : public B { public: int f() { return 2; } }; int main() { return 0; }").map check
-- override needs a virtual method in a base
#eval (parseProgram "class B { public: int f() { return 1; } }; class D : public B { public: int g() override { return 2; } }; int main() { return 0; }").map check
-- a base with a parameterised constructor cannot be derived from, there is no initialiser list
#eval (parseProgram "class B { public: int x; B(int v) { x = v; } }; class D : public B { public: int y; }; int main() { return 0; }").map check
-- this outside a class
#eval (parseProgram "int main() { return this->x; }").map check
-- a Base* is not a Derivada*
#eval (parseProgram "class B { public: int x; }; class D : public B { public: int y; }; int main() { B* b = new D(); D* d = b; return 0; }").map check
-- the constructor is named after the class, by the grammar
#eval parseProgram "class C { public: D() { } }; int main() { return 0; }"

-- the trace of a constructor and a method call
#eval do
  let p ← parseProgram "class C { private: int v; public: C(int x) { v = x; } int dobro() { return v * 2; } };
int main() { C* c = new C(21); return c->dobro(); }"
  let (r, log) := runWith true p
  return (r, renderTrace log)
