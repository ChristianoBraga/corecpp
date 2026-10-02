// Core C++ example, the std::function with no target. new std::function<F>()
#include <functional>
// is the default construction of C++, a function with no target, and a call
// of it is error, as the bad_function_call of C++ ends the program. Exit code 134.
int main() {
  std::function<int(int)>* f = new std::function<int(int)>();
  return (*f)(1);
}
