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

partial def toDafnyTerm (e : Expr) : MetaM Term := do
  match e with
  | .lit (.natVal n)     => return .num n
  -- ignore meta data
  | .mdata _ e           => toDafnyTerm e
  | .const ``Nat.zero .. => return .num 0
  | .app .. => e.withApp fun f args => do
    match f with
    | .const declName .. =>
      let { map, .. } := extension.getState (← getEnv)
      if let some declNameD := map.find? declName then
        let argsD ← args.mapM toDafnyTerm
        return .app declNameD argsD.toList
      -- TODO: use an auxliary mapping to map builtin constants
      else if declName == ``HAdd.hAdd && args.size == 6 then
        return .add (← toDafnyTerm args[4]!) (← toDafnyTerm args[5]!)
      else if declName == ``Nat.succ && args.size == 1 then
        return .add (← toDafnyTerm args[0]!) (.num 1)
      else if declName == ``OfNat.ofNat && args.size == 3 then
        toDafnyTerm args[1]!
      else
        throwError "toDafnyTerm: not supported constant application {e}"
    | _ => throwError "toDafnyTerm: not supported application {e}"
  | _ => throwError "toDafnyTerm: not supported {e}"

partial def toDafnyForm (e : Expr) : MetaM Formula := do
  match e with
  | .app .. => e.withApp fun f args => do
    match f with
    | .const declName .. =>
      if declName == ``Eq && args.size == 3 then
        return .eq (← toDafnyTerm args[1]!) (← toDafnyTerm args[2]!)
      else if declName == ``Ne && args.size == 3 then
        return .ne (← toDafnyTerm args[1]!) (← toDafnyTerm args[2]!)
      else if declName == ``And && args.size == 2 then
        return .and (← toDafnyForm args[0]!) (← toDafnyForm args[1]!)
      else
        throwError "toDafnyForm: not supported constant application {e}"
    | _ => throwError "toDafnyForm: not supported application {e}"
  | .lam .. => throwError "toDafnyForm: not supported lambda abstraction {e}"
  | .bvar .. => throwError "toDafnyForm: not supported bound variable {e}"
  | .fvar .. => throwError "toDafnyForm: not supported free variable {e}"
  | .mvar .. => throwError "toDafnyForm: not supported meta variable {e}"
  | .sort .. => throwError "toDafnyForm: not supported sort {e}"
  | .const .. => throwError "toDafnyForm: not supported constants {e}"
  | .forallE _ _ body _ =>
    return .forall (← toDafnyForm body)
  | .letE .. => throwError "toDafnyForm: not supported let expressions {e}"
  | .lit .. => throwError "toDafnyForm: not supported literals {e}"
  | .mdata .. => throwError "toDafnyForm: not supported metadata {e}"
  | .proj .. => throwError "toDafnyForm: not supported projection {e}"

end Lean.ToDafny
