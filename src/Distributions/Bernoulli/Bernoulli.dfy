include "Correctness.dfy"
include "Implementation.dfy"
include "Interface.dfy"
include "Model.dfy"

module Bernoulli {

  trait T extends Interface.Trait {}
  trait I extends Implementation.Trait {}

}