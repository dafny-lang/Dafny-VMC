include "Correctness.dfy"
include "Implementation.dfy"
include "Interface.dfy"
include "Model.dfy"

module Uniform {
  import Interface = UniformInterface
  import Implementation = UniformImplementation
  import Correctness = UniformCorrectness
  import Model = UniformModel
}