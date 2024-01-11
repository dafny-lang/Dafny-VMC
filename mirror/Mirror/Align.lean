import Lean
import Mirror.Extension

namespace Lean.ToDafny

/--
Declare syntax for the `align_dafny` attribute
-/
syntax (name := align_dafny) "align_dafny" str : attr

initialize
  registerBuiltinAttribute {
    ref   := by exact decl_name%
    name  := `align_dafny
    descr := "instruct Lean to map a Lean declaration to an existing Dafny declaration."
    applicationTime := AttributeApplicationTime.afterTypeChecking
    add   := fun declName stx _attrKind => do
     let some declNameD := stx[1].isStrLit?
       | throwError "invalid attribute parameter"
     -- We just populate the mapping
     modifyEnv fun env => extension.addEntry env (.addDecl declName declNameD)
    erase := fun _ => do
      throwError "this attribute cannot be removed"
  }

end Lean.ToDafny
