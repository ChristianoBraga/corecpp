// Core C++ benchmark, undefined behaviour. An index outside a vector, where a[n] is *(a.begin() + n) (N4659 §26.2.3, Table 88) and a past-the-end iterator is not dereferenceable (N4659 §27.2.1 ¶7).
#include <vector>

int main() {
  std::vector<int>* v = new std::vector<int>(4);
  int s = 0;
  for (int i = 0; i <= 4; i = i + 1) {
    s = s + (*v)[i];
  }
  delete v;
  return s;
}
