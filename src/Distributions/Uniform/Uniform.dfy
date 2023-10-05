include "Correctness.dfy"
include "Implementation.dfy"
include "Interface.dfy"
include "Model.dfy"

module Uniform {

  trait T extends Interface.Trait {}
  trait If extends Implementation.TraitFoundational {}
  trait Ie extends Implementation.TraitExtern {}

}