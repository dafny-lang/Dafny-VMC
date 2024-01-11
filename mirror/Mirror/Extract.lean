import Lean

namespace Lean.ToDafny

/--
State for the new environment extension that will be declared later.
-/
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

/--
Declare syntax for the `export_dafny` attribute
-/
syntax (name := export_dafny) "export_dafny" str : attr

/--
Declare syntax for the `align_dafny` attribute
-/
syntax (name := align_dafny) "align_dafny" str : attr

/--
Dafny terms
-/
inductive Term where
  | num (val : Nat)
  | add (lhs rhs : Term)
  | app (f : String) (args : List Term)
  -- TODO: extend

/--
A Dafny formula
-/
inductive Formula where
  | eq (lhs rhs : Term)
  | ne (lhs rhs : Term)
  | and (lhs rhs : Formula)
  | forall (body: Formula)
  -- TODO: extend

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

def join (s : List String) : String :=
  match s with
  | [] => ""
  | [a] => a
  | a::as => a ++ ", " ++ join as

partial def Term.print (e : Term) : String :=
  match e with
  | .num val => toString val
  | .add lhs rhs => s!"{lhs.print} + {rhs.print}"
  | .app f args => s!"{f}({join (args.map (·.print))})"

def Formula.print (f : Formula) : String :=
  match f with
  | .and lhs rhs => s!"{lhs.print} && {rhs.print}"
  | .eq lhs rhs => s!"{lhs.print} == {rhs.print}"
  | .ne lhs rhs => s!"{lhs.print} != {rhs.print}"
  | .forall body => s!"{body.print}"

def saveAxiom (declName : String) (form : Formula) : CoreM Unit :=
  modifyEnv fun env => extension.addEntry env (.toExport s!"axiom {declName} : {form.print}")

open Meta in
initialize
  registerBuiltinAttribute {
    -- `ref` is used to implement jump-to-definition.
    -- The tactic `by exact decl_name%` retrieves the automatically generated name for
    -- this `initialize` declaration.
    ref   := by exact decl_name%
    name  := `export_dafny
    descr := "instruct Lean to convert the given declaration to Dafny"
    -- The `add` function will be executed after the kernel has accepted
    -- the Lean declaration.
    applicationTime := AttributeApplicationTime.afterTypeChecking
    add   := fun declName stx _attrKind =>
      let go : MetaM Unit := do
        let info ← getConstInfo declName
        let some declNameD := stx[1].isStrLit?
          | throwError "invalid attribute parameter"
        if (← isProp info.type) then
          saveAxiom declNameD (← toDafnyForm info.type)
        -- else if (ConstantInfo.isInductive info) then
        --   let v := ConstantInfo.inductiveVal! info
        --   if v.ctors.length == 1 then
        --     let ctorName := v.ctors[0]!
        --     let quux ← getConstInfo ctorName
        --     match quux with
        --       | ConstantInfo.ctorInfo v =>
        --          throwError "fffff {v.name}
        --                            {v.numFields}
        --                            {v.numParams}
        --                            {v.type}

        --                            "
        --       | _          =>  panic! "Expected a `ConstantInfo.ctorInfo`."
        --   else throwError "inductive not supported yet
        --         {v.name}
        --         {v.levelParams}
        --         {v.type}
        --         {v.numParams}
        --         {v.numIndices}
        --         {v.all}
        --         {v.ctors}
        --         {v.isRec}
        --     "
        --else if (← isType info.type) then
        --  throwError "types not supported yet for translation {info.name}"
        else
          match info with
            | ConstantInfo.defnInfo v =>
              if (← Lean.Meta.isInstance v.name) then
                let l := Meta.instanceExtension.getState (← getEnv) |>.instanceNames
                throwError "Instance: ({v.name}) ({v.value}) ({v.type})
                   {l.toList}"
              else throwError "Missing decl: defn"
            | ConstantInfo.axiomInfo _ => throwError "Missing decl: axiom"
            | ConstantInfo.thmInfo _ => throwError "Missing decl: thm"
            | ConstantInfo.opaqueInfo _ => throwError "Missing decl: opaque"
            | ConstantInfo.quotInfo _ => throwError "Missing decl: quot"
            | ConstantInfo.inductInfo v =>
              if (Lean.isClass (← getEnv) v.name) then
                let l := (classExtension.getState (← getEnv)).outParamMap
                throwError "Class: {v.name} {v.ctors}
                       {l.toList} {l.toList.length}"
              else throwError "Missing decl: induct"
            | ConstantInfo.ctorInfo _ => throwError "Missing decl: ctor"
            | ConstantInfo.recInfo _ => throwError "Missing decl: rec"
          -- We may add support for exporting constants too.
        modifyEnv fun env => extension.addEntry env (.addDecl declName declNameD)
      -- Remark: The `add` method is in the `AttrM`, we use `run` to execute an `MetaM` action.
      -- We need `MetaM` to be able use methods such as `isProp` and `inferType`.
      discard <| go.run {} {}
    erase := fun _ => do
      throwError "this attribute cannot be removed"
  }

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

/--
Add a new Lean command to print all Dafny exported declarations
-/
elab "#print_dafny_exports" : command => do
  let { decls, .. } := extension.getState (← getEnv)
  for decl in decls.reverse do
    IO.println decl

end Lean.ToDafny
