import Lean
import Mirror.Dafny

namespace Lean.ToDafny

structure State where
  /--
  Mapping from Lean declaration name to Dafny declaration name.
  In the future, we may want to extend it with additional information
  (e.g., whether it is an infix operator or not, precedence, etc)
  -/
  map : SMap Name String := {}
  /--
  Dafny exported declarations as an array of strings.
  -/
  decls : List String := []
  deriving Inhabited

/--
Apply `switch` to the `map` field.
We use `switch` after we finalize the `import` process to instruct the value
that it will not be used "linearly" anymore. This is just an optimization.
-/
def State.switch (s : State) : State :=
  { s with map := s.map.switch }

inductive Entry where
  | addDecl (declNameLean : Name) (declNameDafny : String)
  | toExport (dafnyDecl : String)
  deriving Inhabited

def addEntry (s : State) (e : Entry) : State :=
  match e with
  | .addDecl key val => { s with map := s.map.insert key val }
  | .toExport decl => { s with decls := decl :: s.decls }

/--
Declare an environment extension to store the mapping from Lean declaration names to
Dafny declaration names.
Remark: the `initialize` commands are executed when the module is imported.
-/
initialize extension : SimplePersistentEnvExtension Entry State ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := addEntry
    addImportedFn := fun es => (mkStateFromImportedEntries addEntry {} es).switch
  }

end Lean.ToDafny
