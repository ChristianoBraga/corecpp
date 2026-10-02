import CoreCpp.Std.Module

/-!
# `std::vector`, the functions of `<vector>`

    namespace std { template <typename T> class vector; }

A vector is an object, created with `new` and reached by pointer, whose
value is `lib std::vector ℓ̄`, one location per element. The relations are
`CoreCpp.Semantics.Vector`.
-/

namespace CoreCpp.Std.Vector

/-- The element type of a vector has values and a default, so it is neither
an object type, nor a type of the library, nor `void`, `nullptr_t` or a
function type. -/
def elementOk : Ty → Except String Unit
  | .cls c => .error s!"an element of std::vector is an object of class {c}, which is never copied"
  | t@(.lib ..) => .error s!"an element of std::vector has the type {t} of the library"
  | t@(.fn ..) => .error s!"an element of std::vector has the function type {t}"
  | .void => .error "an element of std::vector has type void"
  | .nullT => .error "an element of std::vector has type nullptr_t"
  | _ => .ok ()

/-- TV-New, TV-Index and TV-Delete. -/
def statics : StaticFns where
  wf
    | [t] => elementOk t
    | ts => .error s!"std::vector has one template argument, not {ts.length}"
  new
    | [t] => [([.int], .ptr (.lib "std::vector" [t]))]
    | _ => []
  index
    | [t] => some (.int, t)
    | _ => none
  delete
    | [_] => true
    | _ => false

/-- V-New, V-Index and V-Delete. A negative size and an index out of bounds
are `error`. -/
def fns : Fns where
  new
    | [t], [.int k], σ => do
      if k < 0 then throw (.negativeSize k)
      let (ls, σ₁) := σ.allocMany (List.replicate k.toNat t.default)
      let (l, σ₂) := σ₁.alloc (.lib "std::vector" ls)
      return ("V-New", .loc l, σ₂)
    | _, _, _ => throw (.typeError "std::vector has no new on these arguments")
  index
    | .lib _ ls, .int i, σ =>
      match ls[i.toNat]? with
      | some l => if i < 0 then throw (.outOfBounds i ls.length) else return ("V-Index", l, σ)
      | none => throw (.outOfBounds i ls.length)
    | _, _, _ => throw (.typeError "std::vector has no indexing on these arguments")
  delete
    | .lib _ ls, σ => return ("V-Delete", σ.free ls)
    | _, _ => throw (.typeError "std::vector has no delete on this value")

end CoreCpp.Std.Vector
