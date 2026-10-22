// Core C++ example, lambdas. A lambda is the argument of new std::function,
#include <functional>
// and the object is passed by pointer and applied twice. Exit code 81.
int applyTwice(std::function<int(int)>* f, int x) {
  return (*f)((*f)(x));
}

int main() {
  return applyTwice(new std::function<int(int)>([=](int x) -> int { return x * x; }), 3);
}
