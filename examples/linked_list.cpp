// Core C++ example, recursive types. A class with fields only, a pointer to it as the
// recursive type, nullptr as the end of the list, and a recursive sum through
// the pointers. Every object is created with new and reached through a
// pointer. Exit code 6.
class Node {
public:
  int value;
  Node* next;
};

int sum(Node* p) {
  return p == nullptr ? 0 : p->value + sum(p->next);
}

int main() {
  Node* list = new Node();
  list->value = 1;
  list->next = new Node();
  list->next->value = 2;
  list->next->next = new Node();
  list->next->next->value = 3;
  return sum(list);
}
