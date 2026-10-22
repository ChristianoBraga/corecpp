import CoreCpp.Std.Module
import CoreCpp.Std.Vector
import CoreCpp.Std.Function
import CoreCpp.Std.Assert

/-!
# The library of Core C++

The functions of the modules that the headers of Core C++ declare. The
language finds a module by the name its header declares, and it knows no
module otherwise.
-/

namespace CoreCpp.Std

/-- The static functions of the module of a declared name. -/
def staticFnsOf : String → Option StaticFns
  | "std::vector" => some Vector.statics
  | "std::function" => some Function.statics
  | "assert" => some Assert.statics
  | _ => none

/-- The dynamic functions of the module of a declared name. -/
def fnsOf : String → Option Fns
  | "std::vector" => some Vector.fns
  | "std::function" => some Function.fns
  | "assert" => some Assert.fns
  | _ => none

/-- Object types, the class types and the types of the library created with
`new`, whose values live in the store and are reached by pointer or by
reference. -/
def isObject : Ty → Bool
  | .cls _ => true
  | .lib n ts => (staticFnsOf n).any fun S => !(S.new ts).isEmpty
  | _ => false

end CoreCpp.Std
