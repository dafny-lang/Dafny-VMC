/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "../Uniform/Interface.dfy"
include "Model.dfy"

module Interface {
  import Rationals
  import UniformInterface
  import Model

  trait {:termination false} IBernoulli extends UniformInterface.IUniform {

    method Bernoulli(p: Rationals.Rational) returns (c: bool)
      modifies this
      decreases *
      requires 0 <= p.numer <= p.denom
      ensures Model.ProbBernoulli(p.numer, p.denom)(old(s)) == (c, s)

  }
}
