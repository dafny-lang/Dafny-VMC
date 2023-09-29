/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "../Uniform/Interface.dfy"
include "Model.dfy"

module BernoulliRationalInterface {
  import Rationals
  import UniformInterface
  import BernoulliRationalModel

  trait {:termination false} IBernoulliRational extends UniformInterface.IUniform {

    method BernoulliRational(p: Rationals.Rational) returns (c: bool)
      modifies this
      decreases *
      requires 0 <= p.numer <= p.denom
      ensures BernoulliRationalModel.ProbBernoulliRational(p.numer, p.denom)(old(s)) == (c, s)

  }
}
