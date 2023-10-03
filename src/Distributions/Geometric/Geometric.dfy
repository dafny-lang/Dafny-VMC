include "Correctness.dfy"
include "Implementation.dfy"
include "Interface.dfy"
include "Model.dfy"

module Geometric {
  import Interface = GeometricInterface
  import Implementation = GeometricImplementation
  import Correctness = GeometricCorrectness
  import Model = GeometricModel
}