import CoreCpp.Token

/-!
# Core C++ lexer

A function from `String` to `Array Token`, written as a finite automaton over
the list of characters with the longest match rule, followed by one pass over
the token array that marks the namespace identifiers. The uppercase and
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

/-- Classifies an identifier as a reserved word, or else by its initial. An
uppercase initial gives a type identifier, and a lowercase initial or `_` a
variable identifier. -/
def identifier (s : String) : Token :=
  if keywords.contains s then .kw s
  else if s.front.isUpper then .typeId s
  else .varId s

/-- Tries to match one of the symbols at the start of the input. -/
def matchSymbol (syms : List String) (cs : List Char) : Option (String × List Char) :=
  syms.findSome? fun s =>
    let n := s.length
    if cs.take n == s.toList then some (s, cs.drop n) else none

/-- Discards a line comment, up to the next newline or the end of the input. -/
def skipLine : List Char → List Char
  | [] => []
  | '\n' :: cs => cs
  | _ :: cs => skipLine cs

/-- The automaton. It discards white space and line comments, reads the longest
run of digits as an integer literal and the longest run of identifier
characters as an identifier, tries the symbols of three, two and one
characters in that order, and ends the array with `eof`. -/
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

/-- Marks as a namespace identifier every identifier whose next token is `::`.
The pass runs over the token array, so it sees neither the white space nor the
comments the automaton has already dropped, and it marks `std :: vector` as it
marks `std::vector`. `parseUnit` runs it once on the tokens of all the lines,
so a `::` at the start of a line marks the identifier that ends the line
before. -/
def qualifiers (ts : Array Token) : Array Token :=
  ts.mapIdx fun i t =>
    match t, ts[i + 1]? with
    | .typeId n, some (.sym "::") | .varId n, some (.sym "::") => .nsId n
    | _, _ => t

end Lexer

/-- The lexer, the automaton `Lexer.run` followed by the pass
`Lexer.qualifiers`. -/
def lex (input : String) : Except String (Array Token) :=
  (Lexer.run input.toList #[]).map Lexer.qualifiers

end CoreCpp
