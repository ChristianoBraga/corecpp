// Core C++ example, UD IV. The capture [=] copies n when the lambda is
// evaluated, so the later assignment to n is not seen by soma. Exit code 6.
int main() {
  int n = 5;
  std::function<int(int)> soma = [=](int x) -> int { return x + n; };
  n = 100;
  return soma(1);
}
