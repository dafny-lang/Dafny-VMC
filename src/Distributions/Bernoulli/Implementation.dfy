/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Bernoulli.Implementation {
  import Interface
  import opened Pos

  trait {:termination false} Trait extends Interface.Trait {

    method BernoulliSample (num: nat, den: pos)
      returns (o: bool)
      requires num <= den
      modifies this
      decreases *
    {
      var d := UniformSample(den);
      o := d < num;
    }
  }

}