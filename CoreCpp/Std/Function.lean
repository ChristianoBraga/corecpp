import CoreCpp.Std.Intrinsic

/-!
# `std::function`, the intrinsic of `<functional>`

    namespace std { template <typename F> class function; }

The template argument is a function type `τ(τ₁, …, τₖ)`. A lambda of that
type converts to `std::function<τ(τ₁, …, τₖ)>`, and the value of the
conversion is the closure of the lambda. `nullptr` converts too, and its
value `null` is the function with no target, the state of a default
constructed `std::function` in C++ (N4659 §23.14.13.2.1, paragraphs 1 and 2).
That state is the default a field of the type gets, and the call of it is
`error`, as the `bad_function_call` of C++ (§23.14.13.2.4, paragraph 2). A
value of the type is never an object, and a vector has no elements of it.

The only comparisons are with `nullptr`, `==` and `!=` in either order, as
C++ defines them (§23.14.13.2.6). Two values of the type do not compare.
-/

namespace CoreCpp.Std

def function : Intrinsic where
  name := "std::function"
  arity := 1
  convertible := true
  instOk
    | [.fn ..] => .ok ()
    | [t] => .error s!"the argument of std::function is a function type, not {t}"
    | ts => .error s!"std::function has one template argument, not {ts.length}"
  /-  ───────────────────────────────────────────────────────────────── (TF-Call)
      Γ ⊢_function operator() : τ₁ × … × τₖ → τ    at std::function<τ(τ₁, …, τₖ)>

      ─────────────────────────────────────────── (TF-Eq, ⋈ ∈ {==, !=})
      Γ ⊢_function operator⋈ : nullptr_t → bool                                 -/
  sig
    | .member "operator()", [.fn r ps] => .ok { params := ps, ret := r }
    | .member "operator==", [.fn ..] | .member "operator!=", [.fn ..] =>
      .ok { params := [.nullT], ret := .bool }
    | u, _ => .error s!"std::function has no {u.toString}"
  /-  ───────────────────────────────────────── (TF-Conv)    ───────────────────────────────────────── (TF-Null)
      Γ ⊢_function F ↪ std::function<F>                      Γ ⊢_function nullptr_t ↪ std::function<F>   -/
  convFrom
    | [f@(.fn ..)], t => t == f || t == .nullT
    | _, _ => false
  /-  ─────────────────────────────────── (F-Default)
      default std::function<F> = null                                            -/
  default
    | [.fn ..] => some .null
    | _ => none
  eval apply use _ args σ :=
    match use, args with
    /-  apply(v, v̄) ⇒ v′, σ′
        ─────────────────────────────────────── (F-Call)
        σ ⊢_function operator()(v, v̄) ⇒ v′, σ′

        The premise is the application of a closure, the judgement of the
        language that runs the body of the lambda.                                -/
    | .member "operator()", f :: vs => do
      let (v, σ') ← apply f vs σ
      return ("F-Call", .val v, σ')
    /-  ───────────────────────────────────────────────────── (F-Eq)
        σ ⊢_function operator==(v, null) ⇒ bool (v = null), σ

        ───────────────────────────────────────────────────── (F-Ne)
        σ ⊢_function operator!=(v, null) ⇒ bool (v ≠ null), σ

        A value of the type is null or a closure, so the comparison asks
        whether the function has a target.                                        -/
    | .member "operator==", [f, .null] => return ("F-Eq", .val (.bool (f == .null)), σ)
    | .member "operator!=", [f, .null] => return ("F-Ne", .val (.bool (f != .null)), σ)
    | u, _ => throw (.typeError s!"std::function has no {u.toString} on these arguments")

end CoreCpp.Std
