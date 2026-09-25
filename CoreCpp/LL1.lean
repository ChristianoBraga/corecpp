import Std.Data.HashMap

/-!
# LL(1) grammars and the table driven predictive parser

A generic construction over a type of terminals `T`. A grammar in EBNF is
translated to BNF, the nullable nonterminals and the sets FIRST and FOLLOW are
computed as least fixed points, the predictive parsing table is built from
them, and the grammar is LL(1) when no entry of the table holds two
productions. The parser is the nonrecursive predictive parser, a stack of
grammar symbols driven by the table, whose output is the leftmost derivation
of the input. The construction follows Aho, Lam, Sethi and Ullman, Compilers,
Principles, Techniques, and Tools, second edition, section 4.4.
-/

namespace CoreCpp.LL1

/-- A grammar symbol, a terminal or a nonterminal named by a string. -/
inductive Sym (T : Type) where
  | t (a : T)
  | n (A : String)
  deriving Repr, BEq, DecidableEq

/-- A production `A → α`. -/
structure Production (T : Type) where
  lhs : String
  rhs : List (Sym T)
  deriving Repr, BEq, DecidableEq

/-- A grammar in BNF, a start symbol and a list of productions. The index of a
production in the list names it in the table and in derivations. -/
structure Grammar (T : Type) where
  start : String
  prods : List (Production T)
  deriving Repr

/-- A lookahead, a terminal or the end marker `$`, written `none`. -/
abbrev Look (T : Type) := Option T

/-! ## EBNF and its translation to BNF -/

/-- A right side in EBNF. Sequence, alternative, repetition `X*` and option
`X?` over terminals and nonterminals. -/
inductive Ebnf (T : Type) where
  | t (a : T)
  | n (A : String)
  | seq (es : List (Ebnf T))
  | alt (es : List (Ebnf T))
  | star (e : Ebnf T)
  | opt (e : Ebnf T)
  deriving Repr, Inhabited

/-- A rule `A ::= e` of an EBNF grammar. -/
structure Rule (T : Type) where
  lhs : String
  rhs : Ebnf T

/-- The state of the translation, the productions produced so far and a
counter for the auxiliary nonterminals. -/
structure TrState (T : Type) where
  prods : Array (Production T) := #[]
  next : Nat := 0

abbrev Tr (T : Type) := StateM (TrState T)

/-- A fresh auxiliary nonterminal, named after the rule that needs it. -/
def fresh (owner : String) : Tr T String := do
  let s ← get
  set { s with next := s.next + 1 }
  return s!"{owner}.{s.next}"

def emit (A : String) (rhs : List (Sym T)) : Tr T Unit :=
  modify fun s => { s with prods := s.prods.push ⟨A, rhs⟩ }

mutual

/-- The symbols of `e` in a sequence. A sequence is spliced, and an
alternative, a repetition and an option become an auxiliary nonterminal.
The repetition `X*` becomes `R → X R | ε` and the option `X?` becomes
`O → X | ε`, both right recursive, so the translation adds no left recursion. -/
def symbols (owner : String) : Ebnf T → Tr T (List (Sym T))
  | .t a => return [.t a]
  | .n A => return [.n A]
  | .seq es => symbolsSeq owner es
  | .alt es => do
    let X ← fresh owner
    alternatives owner X es
    return [.n X]
  | .star e => do
    let X ← fresh owner
    let body ← symbols owner e
    emit X (body ++ [.n X])
    emit X []
    return [.n X]
  | .opt e => do
    let X ← fresh owner
    let body ← symbols owner e
    emit X body
    emit X []
    return [.n X]

def symbolsSeq (owner : String) : List (Ebnf T) → Tr T (List (Sym T))
  | [] => return []
  | e :: es => return (← symbols owner e) ++ (← symbolsSeq owner es)

/-- One production `X → α` per alternative. -/
def alternatives (owner X : String) : List (Ebnf T) → Tr T Unit
  | [] => return
  | e :: es => do
    emit X (← symbols owner e)
    alternatives owner X es

end

/-- The BNF grammar of a list of EBNF rules. A top level alternative gives one
production per alternative, without an auxiliary nonterminal. -/
def translate (start : String) (rules : List (Rule T)) : Grammar T :=
  let go : Tr T Unit := rules.forM fun r =>
    match r.rhs with
    | .alt es => alternatives r.lhs r.lhs es
    | e => do emit r.lhs (← symbols r.lhs e)
  let (_, s) := go.run {}
  ⟨start, s.prods.toList⟩

/-! ## Translation through a DFA per rule

The second translation reads each rule as a regular expression over grammar
symbols, as the parser generator `pgen` of CPython does. The expression goes
to an NFA by the construction of Thompson, the NFA to a DFA by the subset
construction, and the DFA to a right linear grammar with one nonterminal per
state. A state `q` with an arc labelled `X` to `q'` gives `q → X q'`, and a
final state gives `q → ε`. Two arcs of a state never carry the same symbol, so
the grammar has no common prefix inside a rule. -/

/-- An NFA over grammar symbols, arcs labelled by a symbol or by ε. -/
structure Nfa (T : Type) where
  arcs : Array (Nat × Option (Sym T) × Nat) := #[]
  size : Nat := 0

abbrev NfaM (T : Type) := StateM (Nfa T)

def Nfa.new : NfaM T Nat := modifyGet fun a => (a.size, { a with size := a.size + 1 })

def Nfa.arc (p : Nat) (l : Option (Sym T)) (q : Nat) : NfaM T Unit :=
  modify fun a => { a with arcs := a.arcs.push (p, l, q) }

mutual

/-- The arcs from `p` to `q` of the language of `e`. -/
def thompson : Ebnf T → Nat → Nat → NfaM T Unit
  | .t a, p, q => Nfa.arc p (some (.t a)) q
  | .n A, p, q => Nfa.arc p (some (.n A)) q
  | .seq es, p, q => thompsonSeq es p q
  | .alt es, p, q => thompsonAlt es p q
  | .star e, p, q => do
    let m ← Nfa.new
    Nfa.arc p none m
    thompson e m m
    Nfa.arc m none q
  | .opt e, p, q => do
    Nfa.arc p none q
    thompson e p q

def thompsonSeq : List (Ebnf T) → Nat → Nat → NfaM T Unit
  | [], p, q => Nfa.arc p none q
  | [e], p, q => thompson e p q
  | e :: es, p, q => do
    let m ← Nfa.new
    thompson e p m
    thompsonSeq es m q

def thompsonAlt : List (Ebnf T) → Nat → Nat → NfaM T Unit
  | [], _, _ => return
  | e :: es, p, q => do
    thompson e p q
    thompsonAlt es p q

end

variable [DecidableEq T] in
/-- The ε closure of a set of states, sorted and without repetition. -/
def Nfa.closure (a : Nfa T) (ss : List Nat) : List Nat :=
  let step (xs : List Nat) : List Nat :=
    a.arcs.foldl (fun acc (p, l, q) =>
      if l.isNone && acc.contains p && !acc.contains q then acc ++ [q] else acc) xs
  let rec go : Nat → List Nat → List Nat
    | 0, xs => xs
    | k + 1, xs => let ys := step xs; if ys.length == xs.length then xs else go k ys
  (go (a.size + 1) ss.eraseDups).mergeSort

variable [DecidableEq T] in
/-- The subset construction. The result lists the sets of NFA states of the
DFA, the first one initial, and the arcs between their indices. -/
def Nfa.toDfa (a : Nfa T) (start : Nat) :
    Array (List Nat) × List (Nat × Sym T × Nat) :=
  let rec go : Nat → List Nat → Array (List Nat) → List (Nat × Sym T × Nat) →
      Array (List Nat) × List (Nat × Sym T × Nat)
    | 0, _, seen, tr => (seen, tr)
    | _ + 1, [], seen, tr => (seen, tr)
    | k + 1, i :: todo, seen, tr =>
      let S := seen[i]!
      let labels := (a.arcs.toList.filterMap fun (p, l, _) =>
        if S.contains p then l else none).eraseDups
      let (seen, todo, tr) := labels.foldl (fun (seen, todo, tr) l =>
        let target := a.closure (a.arcs.toList.filterMap fun (p, l', q) =>
          if S.contains p && l' == some l then some q else none)
        match seen.findIdx? (· == target) with
        | some j => (seen, todo, tr ++ [(i, l, j)])
        | none => (seen.push target, todo ++ [seen.size], tr ++ [(i, l, seen.size)])) (seen, todo, tr)
      go k todo seen tr
  go (2 ^ (min a.size 20) + 1) [0] #[a.closure [start]] []

variable [DecidableEq T] in
/-- The right linear grammar of the DFA of one rule. The initial state keeps
the name of the rule, and state `i` is named `A#i`. -/
def ruleDfa (r : Rule T) : List (Production T) :=
  let (a, (s, f)) := (do
      let s ← Nfa.new
      let f ← Nfa.new
      thompson r.rhs s f
      return (s, f) : NfaM T (Nat × Nat)).run {} |>.swap
  let (states, arcs) := a.toDfa s
  let name (i : Nat) := if i == 0 then r.lhs else s!"{r.lhs}#{i}"
  let finals := (List.range states.size).filter fun i => states[i]!.contains f
  arcs.map (fun (i, l, j) => ⟨name i, [l, .n (name j)]⟩) ++
    finals.map fun i => ⟨name i, []⟩

variable [DecidableEq T] in
/-- The grammar of a list of EBNF rules through their DFAs. -/
def translateDfa (start : String) (rules : List (Rule T)) : Grammar T :=
  ⟨start, rules.flatMap ruleDfa⟩

/-! ## Nullable, FIRST and FOLLOW -/

variable {T : Type} [DecidableEq T]

/-- A finite map from nonterminals to finite sets, as association lists. -/
abbrev SetMap (V : Type) := List (String × List V)

def SetMap.get [BEq V] (m : SetMap V) (A : String) : List V := (m.lookup A).getD []

/-- Add the elements of `vs` to the set of `A`. -/
def SetMap.addAll [BEq V] (m : SetMap V) (A : String) (vs : List V) : SetMap V :=
  let old := m.get A
  let new := vs.foldl (fun acc v => acc.insert v) old
  if new.length == old.length then m
  else (A, new) :: m.filter (·.1 != A)

/-- Iterate `f` from `x` until the value stops changing, at most `fuel` times.
Every step iterated here only adds elements, and a step that changes the
value adds at least one pair of a nonterminal and a lookahead, so the fuel of
`Grammar.fuel` suffices to reach the least fixed point. -/
def iterate [BEq α] (f : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => let y := f x; if y == x then x else iterate f k y

def Grammar.nonterminals (g : Grammar T) : List String :=
  g.prods.foldl (fun acc p => acc.insert p.lhs) []

def Grammar.terminals (g : Grammar T) : List T :=
  g.prods.foldl (fun acc p => p.rhs.foldl (fun acc s =>
    match s with | .t a => acc.insert a | .n _ => acc) acc) []

/-- A bound on the number of steps of each fixed point, one more than the
number of pairs of a nonterminal and a lookahead. -/
def Grammar.fuel (g : Grammar T) : Nat :=
  g.nonterminals.length * (g.terminals.length + 1) + 1

/-- The nullable nonterminals, those with `A ⇒* ε`. -/
def Grammar.nullable (g : Grammar T) : List String :=
  let step (ns : List String) : List String :=
    g.prods.foldl (fun acc p =>
      if p.rhs.all (fun | .t _ => false | .n B => ns.contains B) then acc.insert p.lhs
      else acc) ns
  iterate step g.fuel []

/-- FIRST of a sequence of symbols, with whether the sequence is nullable. -/
def firstSeq (first : SetMap T) (nullable : List String) : List (Sym T) → List T × Bool
  | [] => ([], true)
  | .t a :: _ => ([a], false)
  | .n B :: rest =>
    if nullable.contains B then
      let (s, e) := firstSeq first nullable rest
      ((first.get B).foldl (fun acc a => acc.insert a) s, e)
    else (first.get B, false)

/-- FIRST of every nonterminal. -/
def Grammar.first (g : Grammar T) : SetMap T :=
  let nu := g.nullable
  let step (m : SetMap T) : SetMap T :=
    g.prods.foldl (fun m p => m.addAll p.lhs (firstSeq m nu p.rhs).1) m
  iterate (fun m => step m) g.fuel []

/-- The contribution of one production `A → α` to FOLLOW. For every
occurrence `A → β B γ`, FIRST(γ) goes into FOLLOW(B), and FOLLOW(A) too when
γ is nullable. -/
def followProd (first : SetMap T) (nullable : List String) (A : String) :
    List (Sym T) → SetMap (Look T) → SetMap (Look T)
  | [], m => m
  | .t _ :: rest, m => followProd first nullable A rest m
  | .n B :: rest, m =>
    let (s, e) := firstSeq first nullable rest
    let m := m.addAll B (s.map some)
    let m := if e then m.addAll B (m.get A) else m
    followProd first nullable A rest m

/-- FOLLOW of every nonterminal, with `$` in FOLLOW of the start symbol. -/
def Grammar.follow (g : Grammar T) : SetMap (Look T) :=
  let nu := g.nullable
  let fs := g.first
  let step (m : SetMap (Look T)) : SetMap (Look T) :=
    g.prods.foldl (fun m p => followProd fs nu p.lhs p.rhs m) m
  iterate step g.fuel [(g.start, [none])]

/-! ## The predictive parsing table -/

/-- The lookaheads that select a production `A → α`, FIRST(α), and FOLLOW(A)
when α is nullable. -/
def predict (fs : SetMap T) (nu : List String)
    (fo : SetMap (Look T)) (p : Production T) : List (Look T) :=
  let (s, e) := firstSeq fs nu p.rhs
  s.map some ++ (if e then fo.get p.lhs else [])

/-- The table, a map from a nonterminal and a lookahead to the indices of the
productions the pair selects. -/
abbrev Table (T : Type) := List ((String × Look T) × List Nat)

def Grammar.table (g : Grammar T) : Table T :=
  let nu := g.nullable
  let fs := g.first
  let fo := g.follow
  let add (tb : Table T) (key : String × Look T) (i : Nat) : Table T :=
    match tb.lookup key with
    | some is => if is.contains i then tb else (key, is ++ [i]) :: tb.filter (·.1 != key)
    | none => (key, [i]) :: tb
  (g.prods.zipIdx).foldl (fun tb (p, i) =>
    (predict fs nu fo p).foldl (fun tb a => add tb (p.lhs, a) i) tb) []

/-- The entries of the table with more than one production. -/
def Grammar.conflicts (g : Grammar T) : Table T :=
  g.table.filter (·.2.length ≥ 2)

/-- The grammar is LL(1) when its table has no conflict, that is, when for
every nonterminal `A` and any two of its productions `A → α` and `A → β`,
FIRST(α FOLLOW(A)) and FIRST(β FOLLOW(A)) are disjoint. -/
def Grammar.isLL1 (g : Grammar T) : Bool := g.conflicts.isEmpty

/-! ## The parser -/

/-- A derivation tree. A leaf holds an input token, a node a nonterminal, the
index of the production applied and the subtrees of its right side. -/
inductive Tree (α : Type) where
  | leaf (a : α)
  | node (A : String) (prod : Nat) (kids : List (Tree α))
  deriving Repr

/-- The nonrecursive predictive parser. The stack starts with the start symbol.
A terminal on top must match the next token and both go. A nonterminal `A` on
top is replaced by the right side of the production at `A` and the lookahead,
whose index is output. The input is accepted when stack and input end
together, and the output is the leftmost derivation. -/
def Grammar.parse [Hashable T] (g : Grammar T) (tb : Table T) (cls : α → T) (input : List α) :
    Except String (List Nat) :=
  let prods := g.prods.toArray
  let tb : Std.HashMap (String × Look T) (List Nat) := Std.HashMap.ofList tb
  let rec loop : Nat → List (Sym T) → List α → List Nat → Except String (List Nat)
    | 0, _, _, _ => .error "parser fuel exhausted"
    | _ + 1, [], [], out => .ok out.reverse
    | _ + 1, [], _ :: _, _ => .error "input continues after the program"
    | k + 1, .t b :: st, a :: rest, out =>
      if cls a == b then loop k st rest out
      else .error s!"unexpected token at {input.length - rest.length - 1}"
    | _ + 1, .t _ :: _, [], _ => .error "unexpected end of input"
    | k + 1, .n A :: st, inp, out =>
      match tb[(A, inp.head?.map cls)]? with
      | some (i :: _) =>
        match prods[i]? with
        | some p => loop k (p.rhs ++ st) inp (i :: out)
        | none => .error "table names a missing production"
      | _ => .error s!"no production of {A} at token {input.length - inp.length}"
  let rhsMax := g.prods.foldl (fun n p => max n p.rhs.length) 0
  loop ((input.length + 1) * (g.prods.length + 1) * (rhsMax + 2)) [.n g.start] input []

mutual

/-- The subtree of a symbol, from the remaining input and the remaining
derivation, read in preorder. -/
def buildTree (prods : Array (Production T)) :
    Nat → Sym T → List α → List Nat → Option (Tree α × List α × List Nat)
  | 0, _, _, _ => none
  | _ + 1, .t _, a :: inp, d => some (.leaf a, inp, d)
  | _ + 1, .t _, [], _ => none
  | k + 1, .n A, inp, i :: d => do
    let p ← prods[i]?
    let (kids, inp, d) ← buildTrees prods k p.rhs inp d
    return (.node A i kids, inp, d)
  | _ + 1, .n _, _, [] => none

def buildTrees (prods : Array (Production T)) :
    Nat → List (Sym T) → List α → List Nat → Option (List (Tree α) × List α × List Nat)
  | 0, _, _, _ => none
  | _ + 1, [], inp, d => some ([], inp, d)
  | k + 1, s :: ss, inp, d => do
    let (t, inp, d) ← buildTree prods k s inp d
    let (ts, inp, d) ← buildTrees prods k ss inp d
    return (t :: ts, inp, d)

end

/-- The derivation tree of a leftmost derivation. -/
def Grammar.tree (g : Grammar T) (input : List α) (deriv : List Nat) : Option (Tree α) :=
  match buildTree g.prods.toArray (2 * (input.length + deriv.length) + 2) (.n g.start) input deriv with
  | some (t, [], []) => some t
  | _ => none

end CoreCpp.LL1
