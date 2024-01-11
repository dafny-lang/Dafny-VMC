import Lean
import Mirror.Dafny
import Mirror.Extension

namespace Lean.ToDafny

def saveDeclaration (d : Declaration) : CoreM Unit :=
  modifyEnv fun env => extension.addEntry env (.toExport s!"{d.print}")

mutual

partial def toDafnyExpr (env : List String) (e : Expr) : MetaM Expression := do
  match e with
  | .bvar _ => return .name (env[0]!)
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
        let argsD ← args.mapM (toDafnyExpr env)
        return .app declNameD argsD.toList
      -- TODO: use an auxliary mapping to map builtin constants
      else if declName == ``HAdd.hAdd && args.size == 6 then
        return .binop .addition (← toDafnyExpr env args[4]!) (← toDafnyExpr env args[5]!)
      else if declName == ``Nat.succ && args.size == 1 then
        return .binop .addition (← toDafnyExpr env args[0]!) (.num 1)
      else if declName == ``OfNat.ofNat && args.size == 3 then
        toDafnyExpr env args[1]!
      else if declName == ``Eq && args.size == 3 then
        return .binop .equality (← toDafnyExpr env args[1]!) (← toDafnyExpr env args[2]!)
      else if declName == ``Ne && args.size == 3 then
        return .binop .inequality (← toDafnyExpr env args[1]!) (← toDafnyExpr env args[2]!)
      else if declName == ``And && args.size == 2 then
        return .binop .conjunction (← toDafnyExpr env args[0]!) (← toDafnyExpr env args[1]!)
      else
        toDafnyDecl declName
        return .app declName.toString ([← toDafnyExpr env args[0]!])
    | _ => throwError "toDafnyTerm: not supported -- application {e}"
    )
  | .lam .. =>
    throwError "toDafnyTerm: not supported -- lambda abstraction {e}"
  | .forallE _ _ body _ =>
        return .forall (← toDafnyExpr env body)
  | .letE _ _ _ _ _ => throwError "toDafnyTerm: not supported -- let expression {e}"
  | .lit (.natVal n) => return .num n
  | .lit _ => throwError "toDafnyTerm: not supported -- literals {e}"
  | .mdata _ e           => toDafnyExpr env e
  | .proj _ _ _ => throwError "toDafnyTerm: not supported -- projection {e}"

partial def toDafnyTyp (e: Expr) : MetaM Typ := do
  match e with
  | .bvar .. => throwError "toDafnyTyp: not supported -- bound variable {e}"
  | .fvar .. => throwError "toDafnyTyp: not supported -- free variable {e}"
  | .mvar .. => throwError "toDafnyTyp: not supported -- meta variable {e}"
  | .sort .. => throwError "toDafnyTyp: not supported -- sort {e}"
  | .const name .. =>
    if name == ``Nat then return .nat
    else throwError "toDafnyTyp: not supported -- constant {e}"
  | .app .. => throwError "toDafnyTyp: not supported -- application {e}"
  | .lam .. => throwError "toDafnyTyp: not supported -- lambda abstraction {e}"
  | .forallE _ domain range _ =>
    return .arrow (← toDafnyTyp domain) (← toDafnyTyp range)
  | .letE .. => throwError "toDafnyTyp: not supported -- let expressions {e}"
  | .lit .. => throwError "toDafnyTyp: not supported -- literals {e}"
  | .mdata .. => throwError "toDafnyTyp: not supported -- metadata {e}"
  | .proj .. => throwError "toDafnyTyp: not supported -- projection {e}"

partial def toDafnyDeclIn (declName: Name) : MetaM Declaration := do
  let info ← getConstInfo declName
  match info with
    | ConstantInfo.defnInfo _ =>
      let typ ← toDafnyTyp info.type
      match typ with
      | .nat => return .constant declName.toString typ (← toDafnyExpr [] info.value!)
      | .arrow domain range =>
        match info.value! with
        | .lam binderName binderType body _ => return .function declName.toString binderName.toString domain range (← toDafnyExpr [binderName.toString] body)
        | _ => throwError "Error: should be abstraction"
    | ConstantInfo.axiomInfo _ => throwError "Missing decl: axiom"
    | ConstantInfo.thmInfo _ => return .axiom declName.toString (← toDafnyExpr [] info.type)
    | ConstantInfo.opaqueInfo _ => throwError "Missing decl: opaque"
    | ConstantInfo.quotInfo _ => throwError "Missing decl: quot"
    | ConstantInfo.inductInfo _ => throwError "Missing decl: induct"
    | ConstantInfo.ctorInfo _ => throwError "Missing decl: ctor"
    | ConstantInfo.recInfo _ => throwError "Missing decl: rec"

partial def toDafnyDecl (declName: Name) : MetaM Unit := do
  saveDeclaration (← toDafnyDeclIn declName)

end

end Lean.ToDafny
