include "Correctness.dfy"
include "Implementation.dfy"
include "Interface.dfy"
include "Model.dfy"

module Uniform {

  type T = Interface.Trait
  type If = Implementation.TraitFoundational
  type Ie = Implementation.TraitExtern

}