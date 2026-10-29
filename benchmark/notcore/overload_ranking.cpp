// Core C++ benchmark, not a Core C++ program. A call that overload resolution in C++ settles by ranking conversion sequences.
class A {
public:
  int a;
};

class B : public A {
public:
  int b;
};

class C : public B {
public:
  int c;
};

int f(A* x) { return 1; }
int f(B* x) { return 2; }

int main() {
  C* c = new C();
  int r = f(c);
  delete c;
  return r;
}
