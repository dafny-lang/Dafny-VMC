/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "../Uniform/Uniform.dfy"
include "Model.dfy"

module Interface {
  import Rationals
  import Uniform
  import Model

  trait {:termination false} Trait extends Uniform.Interface.Trait {

    method BernoulliSample(p: Rationals.Rational) returns (c: bool)
      modifies this
      decreases *
      requires 0 <= p.numer <= p.denom
      ensures Model.Sample(p.numer, p.denom)(old(s)) == (c, s)

  }
}
