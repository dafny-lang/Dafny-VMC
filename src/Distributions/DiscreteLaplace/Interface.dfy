/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Interface {
  import Bernoulli
  import BernoulliExpNeg
  import opened Pos

  trait {:termination false} Trait extends Bernoulli.Interface.Trait, BernoulliExpNeg.Interface.Trait {

    method DiscreteLaplaceSample (num: pos, den: pos)
      returns (o: int)
      modifies this
      decreases *

  }

}