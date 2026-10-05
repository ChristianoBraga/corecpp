import CoreCpp

open CoreCpp

/-- A program with the declarations of the headers `<vector>` and `<functional>`
when it uses the standard library, as `#include` gives them. -/
def parseStd (s : String) : Except String Program :=
  let std := "namespace std { template <typename T> class vector; template <typename F> class function; }"
  parseUnit ((if (s.splitOn "std::").length > 1 then [(std, true)] else []) ++ [(s, false)])

/-! ## Lexer and parser -/

#eval lex "int x = 10; // comment\nx = x + 1;"

#eval parseExpr "1 + 2 * 3"
#eval parseExpr "a < b && !(c == d) ? x : y"
#eval parseExpr "f(1, g(2), -3)"
#eval parseExpr "1 +"

#eval parseStatement "if (x % 2 == 0) { x = x / 2; } else { x = x - 1; }"
#eval parseStatement "for (int i = 2; i <= n; i = i + 1) { acc = acc * i; }"
#eval parseStatement "int x;"

#eval parseStd "int factorial(int n) {
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
  (parseStd s).map run

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
-- a conditional over locations of one type denotes a location, objects included,
-- and the last two, of different types and with a branch that is no location, are type errors
#eval prog "class Shape { public: virtual int area() { return 1; } }; class Square : public Shape { public: int side; Square() { side = 3; } int area() override { return side * side; } }; int main() { Square* s = new Square(); Shape* b = new Shape(); bool c = true; return (c ? *s : *b).area() * 10 + (!c ? *s : *b).area(); }"
#eval (parseStd "class Shape { public: virtual int area() { return 1; } }; class Square : public Shape { public: int side; Square() { side = 3; } int perimeter() { return 4 * side; } }; int main() { Square* s = new Square(); Shape* b = new Shape(); bool c = true; return (c ? *s : *b).perimeter(); }").map check
#eval prog "class Node { public: int value; Node(int v) { value = v; } }; int main() { Node* p = new Node(3); Node* q = new Node(4); bool c = false; return (c ? *p : *q).value; }"
#eval prog "class Node { public: int value; Node(int v) { value = v; } }; int main() { Node* p = new Node(3); Node* q = new Node(4); bool c = true; Node& r = c ? *p : *q; r.value = 9; return p->value; }"
#eval prog "int main() { int x = 1; int y = 2; bool c = false; (c ? x : y) = 7; return x * 10 + y; }"
#eval (parseStd "class A { public: int value; }; class B { public: int value; }; int main() { A* p = new A(); B* q = new B(); bool c = true; return (c ? *p : *q).value; }").map check
#eval (parseStd "int main() { int x = 1; bool c = true; (c ? x : 2) = 7; return x; }").map check

-- a pointer and nullptr join at the pointer type in either order
#eval (parseStd "class Node { public: int value; }; int main() { Node* p = new Node(); p->value = 7; bool c = true; auto q = c ? p : nullptr; Node* r = c ? nullptr : p; return q->value; }").map check
#eval prog "class Node { public: int value; }; int main() { Node* p = new Node(); p->value = 7; bool c = true; return (c ? p : nullptr)->value; }"

-- the quotient and the remainder of -2^31 by -1, both undefined in C++17
#eval prog "int main() { int a = -2147483647 - 1; int b = -1; return a / b; }"
#eval prog "int main() { int a = -2147483647 - 1; int b = -1; return a % b; }"

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
#eval (parseStd "int main() { bool b = true; int x = b + 1; return x; }").map check
#eval (parseStd "int f(int n) { return n; } int main() { return f(true); }").map check
#eval (parseStd "int main() { int x = 1; return x; }").map check

-- derivation trace of a small program
#eval do
  let p ← parseStd "int main() { int x = 1; x = x + 41; return x; }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## Classes with fields, pointers, nullptr and vectors -/

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
#eval (parseStd "class P { public: int x; }; int main() { P a = new P(); return 0; }").map check
-- an unknown field
#eval (parseStd "class P { public: int x; }; int main() { P* a = new P(); return a->y; }").map check
-- nullptr has no type of its own for a variable
#eval (parseStd "int main() { auto p = nullptr; return 0; }").map check
-- a field of class type would be an object by value
#eval (parseStd "class Q { public: int y; }; class P { public: Q q; }; int main() { return 0; }").map check
-- pointers admit equality and nothing else
#eval (parseStd "class P { public: int x; }; int main() { P* a = new P(); return a + 1; }").map check

-- the trace of a field update
#eval do
  let p ← parseStd "class P { public: int x; }; int main() { P* a = new P(); a->x = 3; return a->x; }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## Local references and evaluation order -/

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

-- a field never has type void
#eval (parseStd "class Box { public: void hole; }; int main() { Box* b = new Box(); return 0; }").map check

-- a local reference to an object binds its location, as a reference parameter does
#eval prog "class Counter { public: int value; Counter() { value = 1; } };
int main() { Counter* p = new Counter(); Counter& c = *p; c.value = 5; return p->value; }"
#eval prog "class Counter { public: int value; Counter() { value = 1; } };
int main() { std::vector<Counter*>* v = new std::vector<Counter*>(1); (*v)[0] = new Counter(); Counter& c = *(*v)[0]; return c.value; }"

-- a reference to a base binds an object of a derived class, and dispatches on it
#eval prog "class Shape { public: virtual int area() { return 1; } }; class Square : public Shape { public: int side; Square() { side = 3; } int area() override { return side * side; } }; int main() { Square* s = new Square(); Shape& r = *s; return r.area(); }"
#eval (parseStd "class Shape { public: int id; }; class Square : public Shape { public: int side; }; int main() { Shape* b = new Shape(); Square& r = *b; return 0; }").map check

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
#eval (parseStd "int main() { int& r = 5; return r; }").map check
-- the referent has the declared type
#eval (parseStd "int main() { int x = 1; bool& b = x; return 0; }").map check

-- the trace of an aliasing write
#eval do
  let p ← parseStd "int main() { int x = 1; int& y = x; y = 2; return x; }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## Reference parameters, lambdas and std::function -/

-- swap by reference, the parameters alias the arguments
#eval prog "void swap(int& a, int& b) { int t = a; a = b; b = t; }
int main() { int x = 1; int y = 2; swap(x, y); return x * 10 + y; }"

-- a reference parameter bound to a field and to a vector element
#eval prog "class P { public: int a; };
void inc(int& r) { r = r + 1; }
int main() { P* p = new P(); inc(p->a); inc(p->a);
  std::vector<int>* v = new std::vector<int>(2); inc((*v)[1]);
  return p->a * 10 + (*v)[1]; }"

-- a std::function returned by a function and called through its pointer
#eval prog "std::function<int(int)>* multiplier(int k) {
  return new std::function<int(int)>([=](int x) -> int { return k * x; });
}
int apply(std::function<int(int)>* f, int v) { return (*f)(v); }
int main() { return apply(multiplier(3), 14); }"

-- a counter through a captured pointer, the object outlives its block
#eval prog "class Box { public: int value; };
std::function<int()>* counter() {
  Box* c = new Box();
  c->value = 0;
  return new std::function<int()>([=]() -> int { c->value = c->value + 1; return c->value; });
}
int main() { std::function<int()>* k = counter(); int first = (*k)(); return (*k)() + (*k)() + first; }"

-- the capture is a copy taken at the lambda, later writes to n are not seen
#eval prog "int main() { int n = 5;
  std::function<int(int)>* sum = new std::function<int(int)>([=](int x) -> int { return x + n; });
  n = 100; return (*sum)(1); }"

-- a lambda as the argument of new std::function, the object passed by pointer
#eval prog "int applyTwice(std::function<int(int)>* f, int x) { return (*f)((*f)(x)); }
int main() { return applyTwice(new std::function<int(int)>([=](int x) -> int { return x * x; }), 3); }"

-- a second pointer to the same function object calls the same closure, then delete
#eval prog "int main() { std::function<int(int, int)>* g = new std::function<int(int, int)>([=](int a, int b) -> int { return a - b; });
  std::function<int(int, int)>* h = g; int r = (*h)(10, 3); delete g; return r; }"

-- the function with no target, new std::function<F>(), is error when called
#eval prog "int main() { std::function<int(int)>* f = new std::function<int(int)>(); return (*f)(1); }"

-- a field holds a pointer to a function object, called through the pointer
#eval prog "class Button { public: std::function<int()>* handler; };
int main() { Button* b = new Button(); b->handler = new std::function<int()>([=]() -> int { return 4; });
  return (*b->handler)(); }"

-- a reference to a function object is called as a variable
#eval prog "int main() { std::function<int(int)>* p = new std::function<int(int)>([=](int x) -> int { return x + 1; });
  std::function<int(int)>& f = *p; return f(41); }"

-- a captured variable is read only inside the lambda
#eval (parseStd "int main() { int n = 1; std::function<int()>* f = new std::function<int()>([=]() -> int { n = 2; return n; }); return (*f)(); }").map check
-- and cannot be aliased by a reference either
#eval (parseStd "int main() { int n = 1; std::function<int()>* f = new std::function<int()>([=]() -> int { int& r = n; r = 3; return n; }); return (*f)(); }").map check
-- a lambda is not an auto initialiser, by the grammar
#eval parseStd "int main() { auto f = [=](int x) -> int { return x; }; return f(1); }"
-- a lambda is not an operand, by the grammar
#eval parseStd "int main() { return 1 + [=]() -> int { return 1; }; }"
-- the argument of a reference parameter denotes a location
#eval (parseStd "void inc(int& r) { r = r + 1; } int main() { inc(5); return 0; }").map check
-- only function values are called
#eval (parseStd "int main() { int x = 1; return x(2); }").map check
-- the lambda has exactly the function type of the std::function
#eval (parseStd "int main() { std::function<int(int)>* f = new std::function<int(int)>([=](bool b) -> int { return 1; }); return (*f)(1); }").map check
-- a std::function is an object, never held by value, in a field or in a variable
#eval (parseStd "class C { public: std::function<int()> f; }; int main() { return 0; }").map check
#eval (parseStd "int main() { std::function<int()>* p = new std::function<int()>(); std::function<int()> f = *p; return 0; }").map check
-- a lambda occurs only as an argument of new, by the grammar
#eval parseStd "int applyTwice(std::function<int(int)>* f, int x) { return (*f)((*f)(x)); }
int main() { return applyTwice([=](int x) -> int { return x * x; }, 3); }"
#eval parseStd "int main() { std::function<int()> f = [=]() -> int { return 1; }; return 0; }"
#eval parseStd "int main() { return [=]() -> int { return 1; }; }"
-- and only of new std::function, by the type checker
#eval (parseStd "class C { public: int n; C(int m) { n = m; } }; int main() { C* c = new C([=]() -> int { return 1; }); return 0; }").map check

-- the trace of a call through a function object
#eval do
  let p ← parseStd "int main() { int n = 2; std::function<int(int)>* f = new std::function<int(int)>([=](int x) -> int { return x + n; }); return (*f)(40); }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## Methods, inheritance, delete and namespaces -/

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
#eval (parseStd "class C { private: int x; public: C() { x = 1; } }; int main() { C* p = new C(); return p->x; }").map check
-- a non virtual method is not redefined
#eval (parseStd "class B { public: int f() { return 1; } }; class D : public B { public: int f() { return 2; } }; int main() { return 0; }").map check
-- override needs a virtual method in a base
#eval (parseStd "class B { public: int f() { return 1; } }; class D : public B { public: int g() override { return 2; } }; int main() { return 0; }").map check
-- a base with a parameterised constructor cannot be derived from, there is no initialiser list
#eval (parseStd "class B { public: int x; B(int v) { x = v; } }; class D : public B { public: int y; }; int main() { return 0; }").map check
-- this outside a class
#eval (parseStd "int main() { return this->x; }").map check
-- a Base* is not a Derived*
#eval (parseStd "class B { public: int x; }; class D : public B { public: int y; }; int main() { B* b = new D(); D* d = b; return 0; }").map check
-- the constructor is named after the class, by the grammar
#eval parseStd "class C { public: D() { } }; int main() { return 0; }"

-- the trace of a constructor and a method call
#eval do
  let p ← parseStd "class C { private: int v; public: C(int x) { v = x; } int twice() { return v * 2; } };
int main() { C* c = new C(21); return c->twice(); }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## Overloading, operators, templates and inference -/

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
#eval (parseStd "class P { public: int x; int sum(P o) { return x + o.x; } }; int main() { return 0; }").map check

-- two overloads that differ in the pointer type of a std::function parameter are distinct
#eval (parseStd "int g(std::function<int(int)>* h) { return (*h)(1); }
int g(std::function<bool(bool)>* h) { return 0; }
int main() { return 0; }").map check

-- two candidates and no exact match is an ambiguous call
#eval (parseStd "class A { public: int a; }; class B : public A { public: int b; }; class C : public B { public: int c; };
int f(A* x) { return 1; }
int f(B* x) { return 2; }
int main() { C* z = new C(); return f(z); }").map check

-- an operator[] that returns a value does not denote a location
#eval (parseStd "class C { public: int v; int operator[](int i) { return v; } };
int main() { C* c = new C(); (*c)[0] = 1; return 0; }").map check

-- a member that returns a reference returns a location
#eval (parseStd "class C { private: int v; public: int& at() { return 1; } };
int main() { return 0; }").map check

-- an instantiation of a name that is not a template
#eval (parseStd "int main() { Stack<int>* p = new Stack<int>(2); return 0; }").map check

-- the grammar admits one type parameter
#eval parseStd "template<typename T> class C { public: T v; }; int main() { C<int, bool>* p = nullptr; return 0; }"

-- the trace of an overloaded call and of an operator member
#eval do
  let p ← parseStd "class Point { public: int x; Point* operator+(Point& o) { Point* r = new Point(); r->x = x + o.x; return r; } };
int twice(int n) { return 2 * n; }
bool twice(bool b) { return b; }
int main() { Point* a = new Point(); a->x = twice(3); Point* c = *a + *a; return c->x; }"
  let (r, log) := runWith true p
  return (r, renderTrace log)

/-! ## Lexical agreement with C++ -/

-- Each program is rejected, since C++ would read it otherwise.
#eval lex "bool and = true;"
#eval lex "return 010;"
#eval lex "return 2147483648;"
#eval parseStd "int main() { return 5--2; }"
-- The largest literal and a unary minus after a binary one remain.
#eval lex "return 2147483647;"
#eval parseStd "int main() { return 5 - -2; }"

/-! ## LL(1) table and predictive parser -/

#eval Grammar.grammar.conflicts
#eval Grammar.derive "int main() { return a.f(1)(2); }"
#eval Grammar.derive "int main() { return 1 +; }"
#eval show IO Unit from do
  let files ← System.FilePath.readDir "examples"
  let mut agree := 0
  for f in files do
    if f.path.extension != some "cpp" then continue
    let src ← IO.FS.readFile f.path
    let ll := match Grammar.derive src with | .ok _ => true | .error _ => false
    if (parseProgram src).isOk == ll then agree := agree + 1
    else IO.println s!"{f.fileName} disagrees"
  IO.println s!"{agree} examples, both parsers agree"

/-! ## Declarations that only a header holds -/

-- namespace std in a program, which C++ leaves undefined, is a syntax error
#eval parseProgram "namespace std { template <typename T> class vector; } int main() { return 0; }"
-- so is a function without a body
#eval parseProgram "void assert(bool condition); int main() { assert(true); return 0; }"
-- the same declarations from a header are accepted
#eval (parseUnit [("void assert(bool condition);", true), ("int main() { assert(1 == 1); return 0; }", false)]).map run
-- a class template without a body outside a header is a syntax error too
#eval parseProgram "template <typename T> class box; int main() { return 0; }"

/-! ## Members -/

-- a field is never virtual
#eval parseProgram "class Point { public: virtual int x; }; int main() { return 0; }"
-- the destructor is public, like the constructor
#eval parseProgram "class Node { private: ~Node() { } }; int main() { return 0; }"
#eval (parseProgram "class Node { public: ~Node() { } }; int main() { Node* n = new Node(); delete n; return 0; }").map run

/-! ## A qualified name across two lines -/

-- the `::` opens the next line and still marks `std` as a namespace identifier
#eval (parseUnit [("namespace std { template <typename T> class vector; }", true),
                  ("int main() { std", false),
                  ("::vector<int>* v = new std::vector<int>(3); delete v; return 0; }", false)]).map run
