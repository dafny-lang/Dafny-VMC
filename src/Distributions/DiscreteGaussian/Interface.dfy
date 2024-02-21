/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteGaussian.Interface {
  import BernoulliExpNeg
  import DiscreteLaplace
  import opened Pos

  trait {:termination false} Trait extends BernoulliExpNeg.Interface.Trait, DiscreteLaplace.Interface.Trait {

    method DiscreteGaussianSample (num: pos, den: pos)
      returns (o: int)
      modifies this
      decreases *

  }

}