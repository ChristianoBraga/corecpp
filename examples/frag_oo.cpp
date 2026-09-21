// Core C++ example, UD VII. The object oriented fragment. Classes, a virtual
// method redefined with override, dispatch by the class tag, state reached
// only through this and through pointers, and delete with a virtual
// destructor. No lambda and no function value. Exit code 2.
class Conta {
public:
  int saldo;
  virtual int taxa() { return 2; }
  void deposita(int v) { saldo = saldo + v; }
  int saca(int v) { saldo = saldo - v - taxa(); return saldo; }
  virtual ~Conta() { }
};

class Poupanca : public Conta {
public:
  int taxa() override { return 0; }
};

int main() {
  Conta* c = new Conta();
  c->deposita(100);
  int a = c->saca(10);
  Conta* p = new Poupanca();
  p->deposita(100);
  int b = p->saca(10);
  delete c;
  delete p;
  return b - a;
}
