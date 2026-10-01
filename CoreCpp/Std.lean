import CoreCpp.Std.Intrinsic
import CoreCpp.Std.Vector
import CoreCpp.Std.Function
import CoreCpp.Std.Assert

/-!
# The library of Core C++

The intrinsics that the headers of Core C++ declare. The language finds an
intrinsic by the name its header declares, and it knows no intrinsic
otherwise.
-/

namespace CoreCpp.Std

/-- The intrinsics, one per declaration of a header. -/
def library : List Intrinsic := [vector, function, assert]

def lookup (name : String) : Option Intrinsic := library.find? (·.name == name)

/-- The static judgements of the intrinsic named `name`. -/
def statics (name : String) : Option Statics := (lookup name).map (·.toStatics)

/-- Object types, the class types and the types of the library whose values
live in the store. -/
def isObject : Ty → Bool
  | .cls _ => true
  | .lib n _ => (statics n).any (·.isObject)
  | _ => false

/-- Types with a default value, the types a field or an element may have. -/
def hasDefault : Ty → Bool
  | .lib n _ => (statics n).any (·.hasDefault)
  | .fn .. => false
  | _ => true

/-- Types to which another type converts, which tell no two overloads apart. -/
def convertible : Ty → Bool
  | .lib n _ => (statics n).any (·.convertible)
  | _ => false

end CoreCpp.Std
