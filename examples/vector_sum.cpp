// Core C++ example, UD II. A vector is an object created with new, reached
// through a pointer, and (*v)[i] denotes the location of its element i. The
// elements start at 0. Exit code 6.
int main() {
  std::vector<int>* v = new std::vector<int>(3);
  (*v)[0] = 1;
  (*v)[1] = 2;
  (*v)[2] = 3;
  int s = 0;
  for (int i = 0; i < 3; i = i + 1) {
    s = s + (*v)[i];
  }
  return s;
}
