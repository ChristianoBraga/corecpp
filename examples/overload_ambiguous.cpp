// Core C++ example, overloading. Accepted by g++ and rejected by Core C++, the
// direction the subset allows. C++ ranks the conversion sequences and picks
// f(B*), the more derived one. Core C++ does not rank them, so a call that
// two overloads accept without an exact match is ambiguous. g++ returns 2.
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
  C* z = new C();
  int r = f(z);
  delete z;
  return r;
}
