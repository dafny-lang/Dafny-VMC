/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteGaussian.Implementation {
  import Interface
  import opened Pos

  trait {:termination false} Trait extends Interface.Trait {

    method {:verify false} DiscreteGaussianSampleLoop (num: pos, den: pos, t: pos)
      returns (o: (int,bool))
      modifies this
      decreases *
    {
      var Y := DiscreteLaplaceSample(t, 1);
      var y := (if Y < 0 then -Y else Y);
      var n := (y * t * den - num) * (y * t * den - num);
      var d := 2 * num * (t) * (t) * den;
      var C := BernoulliExpNegSample(n, d);
      o := (Y,C);
    }

    method DiscreteGaussianSample (num: pos, den: pos)
      returns (o: int)
      modifies this
      decreases *
    {
      var ti := num / den;
      var t := ti + 1;
      var num := (num) * (num);
      var den := (den) * (den);
      var x := DiscreteGaussianSampleLoop(num, den, t);
      while ! (x.1)
        decreases *
      {
        x := DiscreteGaussianSampleLoop(num, den, t);
      }
      var r := x;
      o := r.0;
    }
  }

}