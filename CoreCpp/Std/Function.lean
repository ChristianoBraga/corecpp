import CoreCpp.Std.Module

/-!
# `std::function`, the functions of `<functional>`

    namespace std { template <typename F> class function; }

A `std::function<F>` is an object, created with `new std::function<F>(λ)` or
`new std::function<F>()`, reached by pointer and called as `(*f)(ē)`, the rule
CallFn of the language. Its value is `lib std::function [ℓ_t]` with the
target at ℓ_t, a closure, or `null` for the function with no target, which
default construction gives (N4659 §23.14.13.2.1 ¶1). A call of it is then
`error`, as `bad_function_call` ends a program that does not catch it. The
relations are `CoreCpp.Semantics.Function`.
-/

namespace CoreCpp.Std.Function

/-- TF-New, TF-Empty and TF-Delete. The argument of `new` has the function
type F itself, the type of a lambda. -/
def statics : StaticFns where
  wf
    | [.fn ..] => .ok ()
    | [t] => .error s!"the argument of std::function is a function type, not {t}"
    | ts => .error s!"std::function has one template argument, not {ts.length}"
  new
    | [f@(.fn ..)] => [([f], .ptr (.lib "std::function" [f])), ([], .ptr (.lib "std::function" [f]))]
    | _ => []
  delete
    | [.fn ..] => true
    | _ => false

/-- F-New, F-Empty and F-Delete. -/
def fns : Fns where
  new
    | [_], [w@(.closure ..)], σ => do
      let (lt, σ₁) := σ.alloc w
      let (l, σ₂) := σ₁.alloc (.lib "std::function" [lt])
      return ("F-New", .loc l, σ₂)
    | [_], [], σ => do
      let (lt, σ₁) := σ.alloc .null
      let (l, σ₂) := σ₁.alloc (.lib "std::function" [lt])
      return ("F-Empty", .loc l, σ₂)
    | _, _, _ => throw (.typeError "std::function has no new on these arguments")
  delete
    | .lib _ ls, σ => return ("F-Delete", σ.free ls)
    | _, _ => throw (.typeError "std::function has no delete on this value")

end CoreCpp.Std.Function
