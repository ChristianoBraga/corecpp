import CoreCpp.Std.Intrinsic

/-!
# `std::function`, the intrinsic of `<functional>`

    namespace std { template <typename F> class function; }

The template argument is a function type `τ(τ₁, …, τₖ)`. A lambda of that
type converts to `std::function<τ(τ₁, …, τₖ)>`, and the value of the
conversion is the closure of the lambda. A value of the type is never an
object, and it has no default, so no field and no element has the type.
-/

namespace CoreCpp.Std

def function : Intrinsic where
  name := "std::function"
  arity := 1
  hasDefault := false
  convertible := true
  instOk
    | [.fn ..] => .ok ()
    | [t] => .error s!"the argument of std::function is a function type, not {t}"
    | ts => .error s!"std::function has one template argument, not {ts.length}"
  /-  ───────────────────────────────────────────────────────────────── (TF-Call)
      Γ ⊢_function operator() : τ₁ × … × τₖ → τ    at std::function<τ(τ₁, …, τₖ)>   -/
  sig
    | .member "operator()", [.fn r ps] => .ok { params := ps, ret := r }
    | u, _ => .error s!"std::function has no {u.toString}"
  /-  ───────────────────────────────────────── (TF-Conv)
      Γ ⊢_function F ↪ std::function<F>                                          -/
  convFrom
    | [f@(.fn ..)], t => t == f
    | _, _ => false
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
    | u, _ => throw (.typeError s!"std::function has no {u.toString} on these arguments")

end CoreCpp.Std
