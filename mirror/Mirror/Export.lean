import Lean
import Mirror.Translate

namespace Lean.ToDafny

syntax (name := export_dafny) "export_dafny" str : attr

def saveAxiom (declName : String) (form : Formula) : CoreM Unit :=
  modifyEnv fun env => extension.addEntry env (.toExport s!"axiom {declName} : {form.print}")

open Meta

  -- Example fetching explicit Dafny name
  -- let some declNameD := stx[1].isStrLit?
  --   | throwError "invalid attribute parameter"
def processDecl (declName: Name): MetaM Unit :=
  do
  let info ← getConstInfo declName
  match info with
    | ConstantInfo.defnInfo v =>
      if (← Lean.Meta.isInstance v.name) then
        let l := Meta.instanceExtension.getState (← getEnv) |>.instanceNames
        throwError "Instance: ({v.name}) ({v.value}) ({v.type})
            {l.toList}"
      else throwError "defn {info.name} {info.type}"
    | ConstantInfo.axiomInfo _ => throwError "Missing decl: axiom"
    | ConstantInfo.thmInfo _ =>
      -- saveAxiom declName.toString (← toDafnyForm info.type)
      saveDeclaration (← toDafnyDeclIn declName)
    | ConstantInfo.opaqueInfo _ => throwError "Missing decl: opaque"
    | ConstantInfo.quotInfo _ => throwError "Missing decl: quot"
    | ConstantInfo.inductInfo v => -- Could be structure, class, inductive
      if (Lean.isClass (← getEnv) v.name) then
        let l := (classExtension.getState (← getEnv)).outParamMap
        throwError "Class: {v.name} {v.ctors}
                {l.toList} {l.toList.length}"
      else throwError "Missing decl: induct"
    | ConstantInfo.ctorInfo _ => throwError "Missing decl: ctor"
    | ConstantInfo.recInfo _ => throwError "Missing decl: rec"


   --if (← isProp info.type) then
  --  saveAxiom declName.toString (← toDafnyForm info.type)
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
  -- else
    -- match info with


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
      let go : MetaM Unit :=
        do
          processDecl declName
          -- Following is for explicit Dafny name
          --modifyEnv fun env => extension.addEntry env (.addDecl declName declNameD)
          modifyEnv fun env => extension.addEntry env (.addDecl declName declName.toString)
      -- Remark: The `add` method is in the `AttrM`, we use `run` to execute an `MetaM` action.
      -- We need `MetaM` to be able use methods such as `isProp` and `inferType`.
      discard <| go.run {} {}
    erase := fun _ => do
      throwError "this attribute cannot be removed"
  }

end Lean.ToDafny
