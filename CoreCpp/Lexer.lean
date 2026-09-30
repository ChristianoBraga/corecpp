import CoreCpp.Token

/-!
# Core C++ lexer

A function from `String` to `Array Token`, written as a finite automaton over
the list of characters with the longest match rule. The uppercase and
lowercase convention is realised here, in `identifier`. The lexer rejects what
C++ would read otherwise, so that every Core C++ program is a C++ program with
the same meaning. It rejects a keyword or alternative representation of C++
outside the subset, an integer literal with a leading `0`, which C++ reads in
octal, and an integer literal above 2147483647, to which C++ gives a type
wider than `int`.
-/

namespace CoreCpp

namespace Lexer

/-- Takes the longest prefix of characters satisfying `p`. -/
def takeWhile (p : Char → Bool) : List Char → String × List Char
  | [] => ("", [])
  | c :: cs =>
    if p c then
      let (s, rest) := takeWhile p cs
      (String.singleton c ++ s, rest)
    else ("", c :: cs)

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentChar  (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Classifies an identifier by its initial, or as a reserved word. -/
def identifier (s : String) : Token :=
  if keywords.contains s then .kw s
  else if s.front.isUpper then .typeId s
  else .varId s

/-- Tries to match one of the symbols at the start of the input. -/
def matchSymbol (syms : List String) (cs : List Char) : Option (String × List Char) :=
  syms.findSome? fun s =>
    let n := s.length
    if cs.take n == s.toList then some (s, cs.drop n) else none

/-- Discards a line comment. -/
def skipLine : List Char → List Char
  | [] => []
  | '\n' :: cs => cs
  | _ :: cs => skipLine cs

partial def run (cs : List Char) (acc : Array Token) : Except String (Array Token) :=
  match cs with
  | [] => .ok (acc.push .eof)
  | c :: rest =>
    if c.isWhitespace then run rest acc
    else if c == '/' && rest.head? == some '/' then run (skipLine rest) acc
    else if c.isDigit then
      let (digits, rest') := takeWhile Char.isDigit cs
      if digits.length > 1 && digits.front == '0' then
        .error s!"integer literal {digits} starts with 0, which C++ reads in octal"
      else if digits.toNat! > 2147483647 then
        .error s!"integer literal {digits} exceeds 2147483647, the largest int"
      else run rest' (acc.push (.intLit digits.toNat!))
    else if isIdentStart c then
      let (name, rest') := takeWhile isIdentChar cs
      if cppReserved.contains name && !keywords.contains name then
        .error s!"'{name}' is a reserved word of C++ outside the subset"
      else run rest' (acc.push (identifier name))
    else
      match matchSymbol symbols3 cs with
      | some (s, rest') => run rest' (acc.push (.sym s))
      | none =>
        match matchSymbol symbols2 cs with
        | some (s, rest') => run rest' (acc.push (.sym s))
        | none =>
          match matchSymbol symbols1 cs with
          | some (s, rest') => run rest' (acc.push (.sym s))
          | none => .error s!"unexpected character '{c}'"

end Lexer

/-- The lexer. -/
def lex (input : String) : Except String (Array Token) :=
  Lexer.run input.toList #[]

end CoreCpp
