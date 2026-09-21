// Core C++ example, closures. The capture [=] copies n when the lambda is
// evaluated, so the later assignment to n is not seen by sum. Exit code 6.
int main() {
  int n = 5;
  std::function<int(int)> sum = [=](int x) -> int { return x + n; };
  n = 100;
  return sum(1);
}
