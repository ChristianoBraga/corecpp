// Core C++ example, UD VI. operator[] returns int&, so v[i] denotes a
// location and stands on the left of an assignment. Indexing an object is
// the call of a member, and the reference return is what makes the
// assignment legitimate. Returns 30.
class Vetor {
private:
  std::vector<int>* dados;
public:
  Vetor(int n) { this->dados = new std::vector<int>(n); }
  int& operator[](int i) { return (*dados)[i]; }
  ~Vetor() { delete dados; }
};

int main() {
  Vetor* v = new Vetor(3);
  (*v)[0] = 10;
  (*v)[1] = 20;
  int s = (*v)[0] + (*v)[1];
  delete v;
  return s;
}
