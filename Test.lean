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
