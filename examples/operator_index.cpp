// Core C++ example, UD VI. operator[] returns int&, so v[i] denotes a
// location and stands on the left of an assignment. Indexing an object is
// the call of a member, and the reference return is what makes the
// assignment legitimate. Returns 30.
class Vect {
private:
  std::vector<int>* data;
public:
  Vect(int n) { this->data = new std::vector<int>(n); }
  int& operator[](int i) { return (*data)[i]; }
  ~Vect() { delete data; }
};

int main() {
  Vect* v = new Vect(3);
  (*v)[0] = 10;
  (*v)[1] = 20;
  int s = (*v)[0] + (*v)[1];
  delete v;
  return s;
}
