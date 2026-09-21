// Core C++ example, pointers. Dereferencing nullptr is error in Core C++. In C++
// it is undefined behaviour, and on most machines the process is killed by
// SIGSEGV. Exit code 134 in Core C++.
class Node {
public:
  int value;
  Node* next;
};

int main() {
  Node* p = nullptr;
  return p->value;
}
