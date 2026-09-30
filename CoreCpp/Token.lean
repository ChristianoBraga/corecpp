/-!
# Core C++ tokens

Five token classes, as in section 3 of the language design. Reserved words,
type identifiers (initial uppercase), variable identifiers (initial lowercase),
integer literals, operators and punctuation.
-/

namespace CoreCpp

inductive Token where
  | kw     (s : String)   -- reserved word
  | typeId (s : String)   -- type identifier, initial uppercase
  | varId  (s : String)   -- variable identifier, initial lowercase
  | intLit (n : Nat)      -- decimal integer literal
  | sym    (s : String)   -- operator or punctuation
  | eof
  deriving Repr, BEq, DecidableEq, Inhabited

def Token.toString : Token → String
  | .kw s     => s
  | .typeId s => s
  | .varId s  => s
  | .intLit n => Nat.repr n
  | .sym s    => s
  | .eof      => "<end of input>"

instance : ToString Token := ⟨Token.toString⟩

/-- Reserved words of the subset handled by this parser. -/
def keywords : List String :=
  ["int", "bool", "void", "if", "else", "while", "for", "return",
   "true", "false", "auto", "delete", "new", "nullptr", "this",
   "class", "public", "private", "virtual", "override", "namespace",
   "template", "typename", "operator", "std"]

/-- The keywords of C++17 (N4659 §5.11 [lex.key], Table 5) and the alternative
representations (Table 6). A Core C++ program uses none of them outside
`keywords`, so every Core C++ program stays a C++ program. -/
def cppReserved : List String :=
  ["alignas", "alignof", "asm", "auto", "bool", "break", "case", "catch", "char",
   "char16_t", "char32_t", "class", "const", "constexpr", "const_cast", "continue",
   "decltype", "default", "delete", "do", "double", "dynamic_cast", "else", "enum",
   "explicit", "export", "extern", "false", "float", "for", "friend", "goto", "if",
   "inline", "int", "long", "mutable", "namespace", "new", "noexcept", "nullptr",
   "operator", "private", "protected", "public", "register", "reinterpret_cast",
   "return", "short", "signed", "sizeof", "static", "static_assert", "static_cast",
   "struct", "switch", "template", "this", "thread_local", "throw", "true", "try",
   "typedef", "typeid", "typename", "union", "unsigned", "using", "virtual", "void",
   "volatile", "wchar_t", "while",
   "and", "and_eq", "bitand", "bitor", "compl", "not", "not_eq", "or", "or_eq",
   "xor", "xor_eq"]

/-- Symbols of three, two and one characters, longest first. The tokens `--`
and `++` belong to no production. The lexer reads them so that `5--2` fails as
it does in C++, where the longest match gives `--`. -/
def symbols3 : List String := ["[=]"]
def symbols2 : List String := ["==", "!=", "<=", ">=", "&&", "||", "->", "::", "--", "++"]
def symbols1 : List String :=
  ["+", "-", "*", "/", "%", "<", ">", "!", "?", ":", "=", "(", ")", "{", "}",
   "[", "]", ",", ";", ".", "&", "~"]

end CoreCpp
