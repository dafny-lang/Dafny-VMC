/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Interface {
  import Bernoulli
  import opened Pos

  trait {:termination false} Trait extends Bernoulli.Interface.Trait {

    method BernoulliExpNegSample (num: nat, den: pos)
      returns (o: bool)
      modifies this
      decreases *

    method BernoulliExpNegSampleUnit (num: nat, den: pos)
      returns (o: bool)
      requires num <= den
      modifies this
      decreases *

  }

}