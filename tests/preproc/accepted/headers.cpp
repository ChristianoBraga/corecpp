// Headers under conditions, included twice, and a vector.
#include <vector>
#ifdef CCPP_FUN
#include <functional>
#endif
#include <vector>
int main() {
  std::vector<int>* v = new std::vector<int>(2);
  (*v)[0] = 4;
  (*v)[1] = 5;
  int s = (*v)[0] + (*v)[1];
#ifdef CCPP_FUN
  std::function<int(int)>* twice = new std::function<int(int)>([=](int x) -> int { return 2 * x; });
  s = (*twice)(s);
#endif
  return s;
}
