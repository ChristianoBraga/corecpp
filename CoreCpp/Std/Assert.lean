import CoreCpp.Std.Module

/-!
# `assert`, the functions of `<cassert>`

    void assert(bool condition);

In C++ `assert` is a macro. With `NDEBUG` undefined, a failed assertion calls
`abort`, and Core C++ gives `error`, which ends with the same exit status.
The relations are `CoreCpp.Semantics.Assert`.
-/

namespace CoreCpp.Std.Assert

/-- TA-Call. -/
def statics : StaticFns where
  call := some ([.bool], .void)

/-- A-True. A failed assertion is `error`. -/
def fns : Fns where
  call
    | [.bool true], σ => return ("A-True", .void, σ)
    | [.bool false], _ => throw (.library "assertion failed")
    | _, _ => throw (.typeError "assert has no call on these arguments")

end CoreCpp.Std.Assert
