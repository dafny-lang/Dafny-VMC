
namespace Lean.ToDafny

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

end Lean.ToDafny
