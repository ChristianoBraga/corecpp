// Core C++ example, UD II. An index outside the vector is error in Core C++.
// In C++ operator[] is undefined behaviour there, and the program may return
// any value. Exit code 134 in Core C++.
int main() {
  std::vector<int>* v = new std::vector<int>(2);
  (*v)[0] = 1;
  (*v)[1] = 2;
  return (*v)[2];
}
