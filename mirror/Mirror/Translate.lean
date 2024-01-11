import Lean
import Mirror.Dafny
import Mirror.Extension

namespace Lean.ToDafny

def saveDeclaration (d : Declaration) : CoreM Unit :=
  modifyEnv fun env => extension.addEntry env (.toExport s!"{d.print}")

mutual

partial def toDafnyTerm (e : Expr) : MetaM Term := do
  match e with
  | .bvar _ => throwError "toDafnyTerm: not supported -- bound variable {e}"
  | .fvar _ => throwError "toDafnyTerm: not supported -- free variable {e}"
  | .mvar _ => throwError "toDafnyTerm: not supported -- meta variable {e}"
  | .sort _ => throwError "toDafnyTerm: not supported -- sort {e}"
  | .const ``Nat.zero .. => return .num 0
  | .const name .. =>
    let info ← getConstInfo name
    toDafnyDecl name
    return .name name.toString
  | .app .. => (e.withApp fun f args => do
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
        throwError "toDafnyTerm: not supported -- constant application {e}"
    | _ => throwError "toDafnyTerm: not supported -- application {e}"
    )
  | .lam _ _ _ _ => throwError "toDafnyTerm: not supported -- lambda abstraction {e}"
  | .forallE _ _ _ _ => throwError "toDafnyTerm: not supported -- dependent arrow {e}"
  | .letE _ _ _ _ _ => throwError "toDafnyTerm: not supported -- let expression {e}"
  | .lit (.natVal n) => return .num n
  | .lit _ => throwError "toDafnyTerm: not supported -- literals {e}"
  | .mdata _ e           => toDafnyTerm e
  | .proj _ _ _ => throwError "toDafnyTerm: not supported -- projection {e}"

partial def toDafnyForm (e : Expr) : MetaM Formula := do
  match e with
  | .bvar .. => throwError "toDafnyForm: not supported -- bound variable {e}"
  | .fvar .. => throwError "toDafnyForm: not supported -- free variable {e}"
  | .mvar .. => throwError "toDafnyForm: not supported -- meta variable {e}"
  | .sort .. => throwError "toDafnyForm: not supported -- sort {e}"
  | .const .. => throwError "toDafnyForm: not supported -- constants {e}"
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
        throwError "toDafnyForm: not supported -- constant application {e}"
    | _ => throwError "toDafnyForm: not supported -- application {e}"
  | .lam .. => throwError "toDafnyForm: not supported -- lambda abstraction {e}"
  | .forallE _ _ body _ =>
    return .forall (← toDafnyForm body)
  | .letE .. => throwError "toDafnyForm: not supported -- let expressions {e}"
  | .lit .. => throwError "toDafnyForm: not supported -- literals {e}"
  | .mdata .. => throwError "toDafnyForm: not supported -- metadata {e}"
  | .proj .. => throwError "toDafnyForm: not supported -- projection {e}"

partial def toDafnyDeclIn (declName: Name) : MetaM Declaration := do
  let info ← getConstInfo declName
  match info with
    | ConstantInfo.defnInfo _ => return .constant declName.toString
    | ConstantInfo.axiomInfo _ => throwError "Missing decl: axiom"
    | ConstantInfo.thmInfo _ => return .axiom declName.toString (← toDafnyForm info.type)
    | ConstantInfo.opaqueInfo _ => throwError "Missing decl: opaque"
    | ConstantInfo.quotInfo _ => throwError "Missing decl: quot"
    | ConstantInfo.inductInfo _ => throwError "Missing decl: induct"
    | ConstantInfo.ctorInfo _ => throwError "Missing decl: ctor"
    | ConstantInfo.recInfo _ => throwError "Missing decl: rec"

partial def toDafnyDecl (declName: Name) : MetaM Unit := do
  saveDeclaration (← toDafnyDeclIn declName)

end

end Lean.ToDafny
