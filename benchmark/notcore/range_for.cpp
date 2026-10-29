// Core C++ benchmark, not a Core C++ program. A range-based for statement.
#include <vector>

int main() {
  std::vector<int>* v = new std::vector<int>(3);
  (*v)[0] = 1;
  (*v)[1] = 2;
  (*v)[2] = 3;
  int s = 0;
  for (int x : *v) {
    s = s + x;
  }
  delete v;
  return s;
}
