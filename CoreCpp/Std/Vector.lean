import CoreCpp.Std.Intrinsic

/-!
# `std::vector`, the intrinsic of `<vector>`

    namespace std { template <typename T> class vector; }

A vector is an object, created with `new` and reached by pointer, whose
value is `lib std::vector ℓ̄`, one location per element.
-/

namespace CoreCpp.Std

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

def vector : Intrinsic where
  name := "std::vector"
  arity := 1
  isObject := true
  instOk
    | [t] => elementOk t
    | ts => .error s!"std::vector has one template argument, not {ts.length}"
  /-  ──────────────────────────────────────────── (TV-New)
      Γ ⊢_vector new : int → std::vector<τ>*

      ──────────────────────────────────────────── (TV-Index)
      Γ ⊢_vector operator[] : int → τ, a location                                  -/
  sig
    | .new, [t] => .ok { params := [.int], ret := .ptr (.lib "std::vector" [t]) }
    | .member "operator[]", [t] => .ok { params := [.int], ret := t, retLoc := true }
    | .delete, _ => .ok { params := [], ret := .void }
    | u, _ => .error s!"std::vector has no {u.toString}"
  eval _ use targs args σ :=
    match use, targs, args with
    /-  k ≥ 0    (ℓᵢ, σᵢ) = alloc σᵢ₋₁ (default τ) for 1 ≤ i ≤ k    (ℓ, σ′) = alloc σₖ (lib std::vector [ℓ₁ … ℓₖ])
        ─────────────────────────────────────────────────────────────────────────────── (V-New)
        σ₀ ⊢_vector new⟨τ⟩(k) ⇒ loc ℓ, σ′

        With k < 0 the result is error, a negative size.                             -/
    | .new, [t], [.int k] => do
      if k < 0 then throw (.negativeSize k)
      let some d := t.default | throw (.typeError s!"an element of type {t} has no default")
      let (ls, σ₁) := σ.allocMany (List.replicate k.toNat d)
      let (l, σ₂) := σ₁.alloc (.lib "std::vector" ls)
      return ("V-New", .val (.loc l), σ₂)
    /-  0 ≤ i < n
        ──────────────────────────────────────────────── (V-Index)
        σ ⊢_vector operator[](lib [ℓ₀ … ℓₙ₋₁], i) ⇒ ℓᵢ, σ

        With i < 0 or i ≥ n the result is error, out of bounds.                   -/
    | .member "operator[]", _, [.lib _ ls, .int i] =>
      match ls[i.toNat]? with
      | some l => if i < 0 then throw (.outOfBounds i ls.length) else return ("V-Index", .loc l, σ)
      | none => throw (.outOfBounds i ls.length)
    /-  ──────────────────────────────────────────────── (V-Delete)
        σ ⊢_vector delete(lib [ℓ₀ … ℓₙ₋₁]) ⇒ σ ∖ {ℓ₀, …, ℓₙ₋₁}

        The language frees the location of the vector itself.                       -/
    | .delete, _, [.lib _ ls] => return ("V-Delete", .val .void, σ.free ls)
    | u, _, _ => throw (.typeError s!"std::vector has no {u.toString} on these arguments")

end CoreCpp.Std
