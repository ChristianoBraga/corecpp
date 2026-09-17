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
   "template", "typename", "operator"]

/-- Symbols of three, two and one characters, longest first. -/
def symbols3 : List String := ["[=]"]
def symbols2 : List String := ["==", "!=", "<=", ">=", "&&", "||", "->", "::"]
def symbols1 : List String :=
  ["+", "-", "*", "/", "%", "<", ">", "!", "?", ":", "=", "(", ")", "{", "}",
   "[", "]", ",", ";", ".", "&", "~"]

end CoreCpp
