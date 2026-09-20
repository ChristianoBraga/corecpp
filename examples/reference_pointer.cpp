// Core C++ example, UD III. A reference to a pointer variable. Assigning
// through q changes p, and the object created through q is reached through p.
// Exit code 3.
class P {
public:
  int a;
};

int main() {
  P* p = nullptr;
  P*& q = p;
  q = new P();
  q->a = 3;
  return p->a;
}
