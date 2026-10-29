// Core C++ benchmark, undefined behaviour. An indirection through nullptr (N4659 §11.3.2 ¶5, note).
class Node {
public:
  int val;
  Node* next;
};

int main() {
  Node* a = new Node();
  a->val = 1;
  a->next = nullptr;
  int s = a->val + a->next->val;
  delete a;
  return s;
}
