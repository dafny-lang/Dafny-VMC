
namespace Lean.ToDafny

inductive Typ where
  | nat
  | arrow (domain range : Typ)

inductive BinOp where
  | equality
  | inequality
  | equivalence
  | conjunction
  | disjunction
  | implication
  | addition
  | substraction
  | multiplication
  | division

inductive Expression where
  | num (val : Nat)
  | app (f : String) (args : List Expression)
  | name (s: String)
  | binop (op : BinOp) (lhs rhs : Expression)
  | forall (body: Expression)
  | exists (body: Expression)

inductive Declaration where
  | axiom (name: String) (body: Expression)
  | constant (name: String) (t : Typ) (body : Expression)
  | function (name: String) (inparams : String) (inparamstyp : Typ) (outparam : Typ) (body : Expression)
  | predicate (name: String)
  | datatype (name: String)
  | type (name: String)

def join (s : List String) : String :=
  match s with
  | [] => ""
  | [a] => a
  | a::as => a ++ ", " ++ join as

def Typ.print (t : Typ): String :=
  match t with
  | nat => "nat"
  | arrow t1 t2 => s!"{t1.print} -> {t2.print}"

def BinOp.print (o : BinOp) : String :=
  match o with
  | equality => "=="
  | inequality => "!="
  | equivalence => "<==>"
  | conjunction => "&&"
  | disjunction => "||"
  | implication => "==>"
  | addition => "+"
  | substraction => "-"
  | multiplication => "*"
  | division => "/"

partial def Expression.print (e : Expression) : String :=
  match e with
  | .num val => toString val
  | .app f args => s!"{f}({join (args.map (·.print))})"
  | .name n => n
  | .binop op lhs rhs => s!"{lhs.print} {op.print} {rhs.print}"
  | .forall body => s!"{body.print}"
  | .exists body => s!"{body.print}"

def Declaration.print (d : Declaration) : String :=
  match d with
  | .axiom name form => s!"lemma {name}() \n  ensures {form.print}"
  | .constant name typ body => s!"const {name} : {typ.print} := {body.print}"
  | .function name inp intyp outyp body => s!"function {name} ({inp} : {intyp.print}) : {outyp.print} \n {body.print} "
  | .predicate name => s!"predicate {name}"
  | .datatype name => s!"datatype {name}"
  | .type name => s!"type {name}"

end Lean.ToDafny
