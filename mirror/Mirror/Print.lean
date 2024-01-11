import Lean
import Mirror.Translate

namespace Lean.ToDafny

/--
Add a new Lean command to print all Dafny exported declarations
-/
elab "#print_dafny_exports" : command => do
  let { decls, .. } := extension.getState (← getEnv)
  for decl in decls.reverse do
    IO.println decl

end Lean.ToDafny
