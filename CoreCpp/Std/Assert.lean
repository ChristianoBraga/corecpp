import CoreCpp.Std.Intrinsic

/-!
# `assert`, the intrinsic of `<cassert>`

    void assert(bool condition);

In C++ `assert` is a macro. With `NDEBUG` undefined, a failed assertion calls
`abort`, and Core C++ gives `error`, which ends with the same exit status.
-/

namespace CoreCpp.Std

def assert : Intrinsic where
  name := "assert"
  arity := 1
  /-  ───────────────────────────── (TA-Call)
      Γ ⊢_assert call : bool → void                                              -/
  sig
    | .call, _ => .ok { params := [.bool], ret := .void }
    | u, _ => .error s!"assert has no {u.toString}"
  eval _ use _ args σ :=
    match use, args with
    /-  ──────────────────────────────── (A-True)
        σ ⊢_assert call(true) ⇒ void, σ

        ──────────────────────────────── (A-False)
        σ ⊢_assert call(false) ⇒ error                                            -/
    | .call, [.bool true] => return ("A-True", .val .void, σ)
    | .call, [.bool false] => throw (.library "assertion failed")
    | u, _ => throw (.typeError s!"assert has no {u.toString} on these arguments")

end CoreCpp.Std
