/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Bernoulli.Interface {
  import Uniform
  import opened Pos

  trait {:termination false} Trait extends Uniform.Interface.Trait {

    method BernoulliSample (num: nat, den: pos)
      returns (o: bool)
      requires num <= den
      modifies this
      decreases *

  }

}