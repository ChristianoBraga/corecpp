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
#eval prog "class Node { public: int value; Node* next; };
int sum(Node* p) { return p == nullptr ? 0 : p->value + sum(p->next); }
int main() {
  Node* list = new Node();
  list->value = 1;
  list->next = new Node();
  list->next->value = 2;
  return sum(list);
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
#eval prog "class R { public: int n; bool ok; R* next; };
int main() { R* r = new R(); return r->n + (r->ok ? 10 : 1) + (r->next == nullptr ? 100 : 0); }"

-- dereferencing nullptr is an error
#eval prog "class Node { public: int value; Node* next; };
int main() { Node* p = nullptr; return p->value; }"

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
#eval prog "class Cell { public: int n; };
int next(Cell* c) { c->n = c->n + 1; return c->n; }
int main() { Cell* c = new Cell(); return next(c) + 10 * next(c); }"

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
#eval prog "void swap(int& a, int& b) { int t = a; a = b; b = t; }
int main() { int x = 1; int y = 2; swap(x, y); return x * 10 + y; }"

-- a reference parameter bound to a field and to a vector element
#eval prog "class P { public: int a; };
void inc(int& r) { r = r + 1; }
int main() { P* p = new P(); inc(p->a); inc(p->a);
  std::vector<int>* v = new std::vector<int>(2); inc((*v)[1]);
  return p->a * 10 + (*v)[1]; }"

-- a lambda returned by a function and applied through a std::function parameter
#eval prog "std::function<int(int)> multiplier(int k) {
  return [=](int x) -> int { return k * x; };
}
int apply(std::function<int(int)> f, int v) { return f(v); }
int main() { return apply(multiplier(3), 14); }"

-- a counter through a captured pointer, the object outlives its block
#eval prog "class Box { public: int value; };
std::function<int()> counter() {
  Box* c = new Box();
  c->value = 0;
  return [=]() -> int { c->value = c->value + 1; return c->value; };
}
int main() { std::function<int()> k = counter(); int first = k(); return k() + k() + first; }"

-- the capture is a copy taken at the lambda, later writes to n are not seen
#eval prog "int main() { int n = 5;
  std::function<int(int)> sum = [=](int x) -> int { return x + n; };
  n = 100; return sum(1); }"

-- a lambda passed directly as an argument
#eval prog "int applyTwice(std::function<int(int)> f, int x) { return f(f(x)); }
int main() { return applyTwice([=](int x) -> int { return x * x; }, 3); }"

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
#eval prog "class Counter {
private:
  int value;
public:
  Counter(int initial) { this->value = initial; }
  void increment() { value = value + 1; }
  int current() { return value; }
};
int main() { Counter* c = new Counter(40); c->increment(); c->increment(); return c->current(); }"

-- an abstract data type, a stack over a vector
#eval prog "class Stack {
private:
  std::vector<int>* items;
  int top;
public:
  Stack(int n) { this->items = new std::vector<int>(n); this->top = 0; }
  void push(int x) { (*items)[top] = x; top = top + 1; }
  int pop() { top = top - 1; return (*items)[top]; }
};
int main() { Stack* p = new Stack(8); p->push(1); p->push(41); return p->pop() + p->pop(); }"

-- inheritance, virtual dispatch, subsumption, a namespace and delete with a virtual destructor
#eval prog "namespace Geometry {
  class Shape { public: virtual int area() { return 0; } virtual ~Shape() { } };
  class Square : public Shape {
  private: int side;
  public: Square(int l) { this->side = l; } int area() override { return side * side; }
  };
}
int main() { Geometry::Shape* f = new Geometry::Square(4); int a = f->area(); delete f; return a; }"

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
-- a Base* is not a Derived*
#eval (parseProgram "class B { public: int x; }; class D : public B { public: int y; }; int main() { B* b = new D(); D* d = b; return 0; }").map check
-- the constructor is named after the class, by the grammar
#eval parseProgram "class C { public: D() { } }; int main() { return 0; }"

-- the trace of a constructor and a method call
#eval do
  let p ← parseProgram "class C { private: int v; public: C(int x) { v = x; } int twice() { return v * 2; } };
int main() { C* c = new C(21); return c->twice(); }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## UD VI, overloading, operators, templates and inference -/

-- overloading by the type of the argument
#eval prog "int twice(int n) { return 2 * n; }
bool twice(bool b) { return b; }
int main() { return twice(21) + (twice(false) ? 1 : 0); }"

-- overloading by the number of arguments
#eval prog "int sum(int a) { return a; }
int sum(int a, int b) { return a + b; }
int main() { return sum(1) + sum(2, 39); }"

-- a method is overloaded like a function
#eval prog "class C { public: int v; int sum(int a) { return v + a; } int sum(int a, int b) { return v + a + b; } };
int main() { C* c = new C(); c->v = 1; return c->sum(2) + c->sum(3, 34); }"

-- an exact match wins over a candidate reached by subsumption
#eval prog "class A { public: int a; }; class B : public A { public: int b; };
int f(A* x) { return 1; }
int f(B* x) { return 2; }
int main() { B* z = new B(); return f(z); }"

-- an infix operator on an object is the call of its member
#eval prog "class Point { public: int x; Point* operator+(Point& o) { Point* r = new Point(); r->x = x + o.x; return r; } };
int main() { Point* a = new Point(); a->x = 21; Point* c = *a + *a; return c->x; }"

-- an overloaded comparison gives a bool
#eval prog "class Pair { public: int k; bool operator<(Pair& o) { return k < o.k; } };
int main() { Pair* a = new Pair(); a->k = 1; Pair* b = new Pair(); b->k = 2; return (*a < *b) ? 42 : 0; }"

-- operator[] returning a reference denotes a location
#eval prog "class V { private: std::vector<int>* d; public: V(int n) { this->d = new std::vector<int>(n); }
int& operator[](int i) { return (*d)[i]; } };
int main() { V* v = new V(2); (*v)[0] = 40; (*v)[1] = (*v)[0] + 2; return (*v)[1]; }"

-- a class template instantiated at two types
#eval prog "template<typename T> class Box { private: T v; public: Box(T x) { this->v = x; } T get() { return v; } };
int main() { Box<int>* a = new Box<int>(40); Box<bool>* b = new Box<bool>(true);
return a->get() + (b->get() ? 2 : 0); }"

-- the instantiation of a template that uses the parameter in a vector
#eval prog "template<typename T> class Stack { private: std::vector<T>* items; int top;
public: Stack(int n) { this->items = new std::vector<T>(n); this->top = 0; }
void push(T x) { (*items)[top] = x; top = top + 1; }
T pop() { top = top - 1; return (*items)[top]; } };
int main() { Stack<int>* p = new Stack<int>(4); p->push(20); p->push(22);
return p->pop() + p->pop(); }"

-- auto copies the type of a pointer to an instantiation
#eval prog "template<typename T> class Box { private: T v; public: Box(T x) { this->v = x; } T get() { return v; } };
int main() { auto c = new Box<int>(42); auto n = c->get(); return n; }"

-- a member takes an object by reference, never by value
#eval (parseProgram "class P { public: int x; int sum(P o) { return x + o.x; } }; int main() { return 0; }").map check

-- two overloads that differ only in a std::function parameter are rejected
#eval (parseProgram "int g(std::function<int(int)> h) { return h(1); }
int g(std::function<bool(bool)> h) { return 0; }
int main() { return 0; }").map check

-- two candidates and no exact match is an ambiguous call
#eval (parseProgram "class A { public: int a; }; class B : public A { public: int b; }; class C : public B { public: int c; };
int f(A* x) { return 1; }
int f(B* x) { return 2; }
int main() { C* z = new C(); return f(z); }").map check

-- an operator[] that returns a value does not denote a location
#eval (parseProgram "class C { public: int v; int operator[](int i) { return v; } };
int main() { C* c = new C(); (*c)[0] = 1; return 0; }").map check

-- a member that returns a reference returns a location
#eval (parseProgram "class C { private: int v; public: int& at() { return 1; } };
int main() { return 0; }").map check

-- an instantiation of a name that is not a template
#eval (parseProgram "int main() { Stack<int>* p = new Stack<int>(2); return 0; }").map check

-- the grammar admits one type parameter
#eval parseProgram "template<typename T> class C { public: T v; }; int main() { C<int, bool>* p = nullptr; return 0; }"

-- the trace of an overloaded call and of an operator member
#eval do
  let p ← parseProgram "class Point { public: int x; Point* operator+(Point& o) { Point* r = new Point(); r->x = x + o.x; return r; } };
int twice(int n) { return 2 * n; }
bool twice(bool b) { return b; }
int main() { Point* a = new Point(); a->x = twice(3); Point* c = *a + *a; return c->x; }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## UD VII, the fragments of the paradigms -/

def impProg : String :=
  "int gcd(int a, int b) {
    while (b != 0) { int t = b; b = a % b; a = t; }
    return a;
  }
  int main() { int x = gcd(48, 18); int& y = x; y = y + 1; return y; }"

def ooProg : String :=
  "class Account {
   public:
     int balance;
     virtual int rate() { return 2; }
     void deposit(int v) { balance = balance + v; }
     virtual ~Account() { }
   };
   int main() { Account* c = new Account(); c->deposit(5); int s = c->balance; delete c; return s; }"

def funProg : String :=
  "std::function<int(int)> scale(int k) { return [=](int x) -> int { return k * x; }; }
   int main() { std::function<int(int)> t = scale(3); return t(4); }"

-- the imperative program lies in the three fragments that admit it
#eval (parseProgram impProg).map (fragment .imperative)
#eval (parseProgram impProg).map (fragment .oo)
#eval (parseProgram impProg).map (fragment .functional)

-- classes leave the imperative and the functional fragments
#eval (parseProgram ooProg).map (fragment .oo)
#eval (parseProgram ooProg).map (fragment .imperative)
#eval (parseProgram ooProg).map (fragment .functional)

-- lambdas and function values leave the imperative and the object oriented ones
#eval (parseProgram funProg).map (fragment .functional)
#eval (parseProgram funProg).map (fragment .oo)

-- a program with both a class and a lambda lies in no fragment
#eval (parseProgram "class C { public: int v; };
std::function<int(int)> f() { return [=](int x) -> int { return x; }; }
int main() { C* c = new C(); return f()(c->v); }").map fun p =>
  (fragment .imperative p, fragment .oo p, fragment .functional p)

/-! ## UD VII, the logic language -/

open Logic

def appendProg : String :=
  "append([], L, L).
   append([H|T], L, [H|R]) :- append(T, L, R).
   ?- append([1, 2], [3, 4], R)."

def factProg : String :=
  "factorial(0, 1).
   factorial(N, F) :- N > 0, M is N - 1, factorial(M, G), F is N * G.
   ?- factorial(5, F)."

-- unification, with the occurs check
#eval unify [] (.var "X") (.fn "f" [.num 1])
#eval unify [] (.fn "f" [.var "X", .num 2]) (.fn "f" [.num 1, .var "Y"])
#eval unify [] (.var "X") (.fn "f" [.var "X"])
#eval unify [] (.fn "f" [.num 1]) (.fn "g" [.num 1])

-- the parser of the logic language
#eval Logic.parse "p(a, B). q(X) :- p(X, X). ?- q(Z)."
#eval Logic.parse "p(a)"

-- concatenation answers three questions with the same clauses
#eval (Logic.parse appendProg).map fun (cs, qs) => qs.map fun q => Logic.query cs q
#eval match Logic.parse "append([], L, L).
  append([H|T], L, [H|R]) :- append(T, L, R).
  ?- append(X, Y, [1, 2])." with
  | .ok (cs, qs) => IO.println ("\n".intercalate (qs.map fun q => Logic.answersToString q (Logic.query cs q)))
  | .error e => IO.println e

-- arithmetic through the built in is
#eval match Logic.parse factProg with
  | .ok (cs, qs) => IO.println ("\n".intercalate (qs.map fun q => Logic.answersToString q (Logic.query cs q)))
  | .error e => IO.println e

-- a query with no answer, and a left recursive program that the depth bound stops
#eval (Logic.parse "p(1). ?- p(2).").map fun (cs, qs) => qs.map fun q => Logic.query cs q
#eval (Logic.parse "q(X) :- q(X). ?- q(1).").map fun (cs, qs) =>
  qs.map fun q => (Logic.query cs q (depth := 50)).length
