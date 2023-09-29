/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "../Uniform/Interface.dfy"
include "Model.dfy"

module BernoulliInterface {
  import Rationals
  import UniformInterface
  import BernoulliModel

  trait {:termination false} IBernoulli extends UniformInterface.IUniform {

    method Bernoulli(p: Rationals.Rational) returns (c: bool)
      modifies this
      decreases *
      requires 0 <= p.numer <= p.denom
      ensures BernoulliModel.ProbBernoulli(p.numer, p.denom)(old(s)) == (c, s)

  }
}
