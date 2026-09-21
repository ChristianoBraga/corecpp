// Core C++ example, the object oriented fragment. The object oriented fragment. Classes, a virtual
// method redefined with override, dispatch by the class tag, state reached
// only through this and through pointers, and delete with a virtual
// destructor. Node lambda and no function value. Exit code 2.
class Account {
public:
  int balance;
  virtual int rate() { return 2; }
  void deposit(int v) { balance = balance + v; }
  int withdraw(int v) { balance = balance - v - rate(); return balance; }
  virtual ~Account() { }
};

class Savings : public Account {
public:
  int rate() override { return 0; }
};

int main() {
  Account* c = new Account();
  c->deposit(100);
  int a = c->withdraw(10);
  Account* p = new Savings();
  p->deposit(100);
  int b = p->withdraw(10);
  delete c;
  delete p;
  return b - a;
}
