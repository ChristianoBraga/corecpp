import Lake
open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.32.0"
require corecpp from ".."

package CoreCppBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib CoreCppBlueprint where
