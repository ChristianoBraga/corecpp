// Core C++ example, function objects. A std::function is an object, reached by
#include <functional>
// pointer, and a second pointer to it calls the same closure. Exit code 7.
int main() {
  std::function<int(int, int)>* g = new std::function<int(int, int)>([=](int a, int b) -> int { return a - b; });
  std::function<int(int, int)>* h = g;
  int r = (*h)(10, 3);
  delete g;
  return r;
}
