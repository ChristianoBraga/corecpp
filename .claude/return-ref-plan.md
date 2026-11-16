# Plan. One expression judgment, an lvalue yields its location

Agreed on 2026-11-16. It replaces the rewrite of `return e` into
`return locOf e` and the earlier plan of a return mode in the command
judgment, which the user rejected.

## Problem

In `examples/operator_index.cpp` the assignment `(*v)[0] = 10` writes
through the call `Vect::operator[](0)`, declared `int&`, whose body is
`return (*data)[i]`. The rule Return evaluates its operand with ⇒, so the
location ℓᵢ of the element never leaves the body. Today `Typing.annotate`
rewrites the operand into `locOf e` (`refRets`, `CoreCpp/Typing.lean`), a
form no valid C++17 program can write.

## Principles

1. The source program stays as the programmer writes it, valid C++17, with
   no rewrite.
2. A static decision stays static. The dynamic judgment carries no return
   mode.
3. ρ maps an identifier to its location and σ maps a location to its value.
   Locations are values. For `Box* p = new Box()`, ρ(p) = ℓ_p and
   σ(ℓ_p) = `loc ℓ₁`. A pointer variable is an object with storage of its
   own. A pointer type is an object type (N4659 [basic.types], §6.9
   paragraph 8), and an object created by a definition occupies a region of
   storage (N4659 [intro.object], §4.5 paragraph 1).

## Text of the standard

A glvalue is an expression whose evaluation determines the identity of an
object (N4659 [basic.lval], §6.10 paragraph 1.1). A glvalue in a context
where a prvalue is expected is converted to a prvalue (§6.10 paragraph 3, a
note). The lvalue‑to‑rvalue conversion converts a glvalue of a non‑function,
non‑array type to a prvalue (N4659 [conv.lval], §7.1 paragraph 1). The
`return` statement initialises the glvalue result or prvalue result object
of the call by copy‑initialisation from the operand (N4659 [stmt.return],
§9.6.3 paragraph 2). That initialisation is sequenced before the destruction
of the local variables of the enclosing block (§9.6.3 paragraph 3). A
discarded‑value expression receives the lvalue‑to‑rvalue conversion only
when it is a glvalue of volatile‑qualified type (N4659 [expr], §8
paragraph 12).

The design follows the distinction of L‑values and R‑values in Strachey,
*Fundamental Concepts in Programming Languages*, 1967, reprinted in
Higher‑Order and Symbolic Computation 13 (2000), pp. 11–49.

## Design

### The judgment

One judgment ρ, σ ⊢ e ⇒ r, σ′ with a result r of a new type.

```
r ::= val v      a prvalue, the value v
    | lval ℓ     a glvalue, the object at ℓ
```

The relation `LEval` and the judgment ⇒ₗ disappear. The tag keeps the
location of an object apart from a pointer value. `p` yields `lval ℓ_p`,
while `new Box()` yields `val (loc ℓ₁)`.

### The conversion

rd(σ, val v) = v, and rd(σ, lval ℓ) = σ(ℓ) when ℓ ∈ dom σ. A missing ℓ has
no derivation and is the runtime `error`. The rules write rd as a premise
where C++17 applies the lvalue‑to‑rvalue conversion.

| Context | Requires |
| --- | --- |
| operand of `!`, `-`, arithmetic, comparison, `&&`, `\|\|` | rd |
| condition of `?:`, `if`, `while`, `for` | rd |
| right side of `=`, initialiser of `τ x` and `auto x` | rd |
| by value argument, captured variable of a lambda | rd |
| operand of `*`, `->`, `delete`, index of `[]` | rd |
| left side of `=`, initialiser of `τ& x`, reference argument | `lval ℓ` |
| receiver of `e.m(…)` and `e.f` | `lval ℓ` |
| `e;` | nothing, the result is discarded |
| operand of `return` | nothing, the call converts |

### The rules that yield a location

```
ρ(x) = ℓ                     ρ, σ ⊢ e ⇒ r, σ′    rd(σ′, r) = loc ℓ
────────────────── (Var)     ───────────────────────────────── (Deref)
ρ, σ ⊢ x ⇒ lval ℓ, σ         ρ, σ ⊢ *e ⇒ lval ℓ, σ′

ρ, σ ⊢ e ⇒ lval ℓ, σ′    σ′(ℓ) = obj C [… f ↦ ℓ_f …]
──────────────────────────────────────────────────── (Field)
ρ, σ ⊢ e.f ⇒ lval ℓ_f, σ′
```

VarField, Arrow and Index follow the same pattern. Index reads its base with
rd and takes ℓᵢ from the relation `index` of the vector module. Cond passes
on the result of the chosen branch unchanged, so `c ? *s : *b` yields a
location when both branches do (N4659 [expr.cond], §8.16 paragraph 5). `this` yields
`val (loc ℓ)`, a prvalue.

### Return and calls

```
ρ, σ ⊢ e ⇒ r, σ′
──────────────────────────────── (Return)
ρ, σ ⊢ return e ⇒ ret r, ρ, σ′
```

`Ctrl.ret` carries a result r in place of a value. The call adapts r by the
declared return type, which the declaration of the function holds.

| Callee | Result of the call |
| --- | --- |
| declared `τ`, a function, method or lambda | `val (rd(σ₂, r))`, read before the locals leave σ |
| method declared `τ&` | r, which must be `lval ℓ` |
| declared `void`, ending without `return` | `val void` |

The read happens in σ₂, before the free of the locals, the order of N4659
§9.6.3 paragraph 3. The rules MethodCall, MethodCallRef and MethodLoc merge
into one rule.

### Static semantics

Unchanged. The judgments Γ ⊢ e : τ and Γ ⊢ₗ e : τ and the rule T‑RetRef
still decide statically which expressions denote locations. The rule
T‑LocOf goes with `locOf`.

## What disappears

`Expr.locOf`, `refRets`, the rules LocOf and T‑LocOf, the relation `LEval`,
the function `Eval.lval`, the rule Read and its premise `Expr.isPlace`, and
the separate rules LocCond‑T and LocCond‑F.

## Steps

1. `CoreCpp/Semantics.lean`. Add the type of results `Res` with `val` and
   `lval`, the conversion `rd`, and `Ctrl.ret` over `Res`.
2. `CoreCpp/Syntax.lean`, `Pretty.lean`, `Templates.lean`. Remove
   `Expr.locOf`.
3. `CoreCpp/Typing.lean`, `Semantics/Static.lean`. Remove `refRets`, the
   `locOf` cases and T‑LocOf.
4. `CoreCpp/Semantics/Dynamic.lean`. Merge `Eval` and `LEval` into one
   relation over `Res`, with rd in the premises of the table above. Adapt
   `Args`, `Bind`, `Member`, `CallMethod`, `Apply`, `Returns` and the command
   rules.
5. `CoreCpp/Semantics/Library.lean`. Check the relations `index`, `call` and
   `new` of the modules for the new results.
6. `CoreCpp/Eval.lean`. Merge `expr` and `lval` into one function over `Res`,
   add `rd`, and adapt the trace to print `lval ℓ` and `val v`.
7. Proofs. `Determinism.lean`, `FuelMono.lean`, `InterpSound.lean`,
   `InterpComplete.lean` and `Progress.lean` lose the mutual case of `LEval`
   and the rule Read.
8. Blueprint. The chapters `Domains`, `Expressions`, `Commands`,
   `Abstraction`, `Encapsulation`, `TypeSystems` and `Library` state ⇒ₗ
   today. They move to the single judgment. `Grammar` loses `locOf`.
9. `benchmark/coverage.py`. Remove `Expr.locOf` from the forms it leaves
   out.
10. Tests. A reference return through a loop and a conditional, a function
    with a `return` of an lvalue and a `return` of a prvalue, and a `trace`
    test of `operator_index.cpp`.

## Verification

`lake build`, `lake env lean tests/Test.lean`, `lake env lean
tests/Grammar.lean`, `bin/compare`, and `lake exe vbp build` inside `docs/`.
The 38 examples that agree with `g++` today must still agree.

## Open choices

1. The names of the results. `val` and `lval`, or the C++17 names prvalue
   and glvalue.
2. Whether Γ ⊢ₗ e : τ stays a second static judgment or becomes a value
   category in Γ ⊢ e : τ.

## Incidental finding

The rule MethodLoc in the node `op_refret` of
`docs/CoreCppBlueprint/Chapters/TypeSystems.lean` has a garbled premise,
"returns τ\the premises of MethodCall, with m returning τ& and". Step 8
replaces that rule.
