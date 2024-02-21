/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Implementation {
  import Interface
  import opened Pos

  trait {:termination false} Trait extends Interface.Trait {

    method DiscreteLaplaceSampleLoopIn1Aux (t: pos)
      returns (o: (nat,bool))
      modifies this
      decreases *
    {
      var U := UniformSample(t);
      var D := BernoulliExpNegSample(U, t);
      o := (U,D);
    }

    method DiscreteLaplaceSampleLoopIn1 (t: pos)
      returns (o: nat)
      modifies this
      decreases *
    {
      var x := DiscreteLaplaceSampleLoopIn1Aux(t);
      while ! (x.1)
        decreases *
      {
        x := DiscreteLaplaceSampleLoopIn1Aux(t);
      }
      var r1 := x;
      o := r1.0;
    }

    method DiscreteLaplaceSampleLoopIn2Aux (num: nat, den: pos, K: (bool,pos))
      returns (o: (bool,pos))
      requires num <= den
      modifies this
      decreases *
    {
      var A := BernoulliExpNegSampleUnit(num, den);
      o := (A,K.1 + 1);
    }

    method DiscreteLaplaceSampleLoopIn2 (num: nat, den: pos)
      returns (o: pos)
      modifies this
      decreases *
    {
      var K := (true,1);
      while K.0
        decreases *
      {
        K := DiscreteLaplaceSampleLoopIn2Aux(1, 1, K);
      }
      var r2 := K;
      o := r2.1;
    }

    method {:verify false} DiscreteLaplaceSampleLoop (num: pos, den: pos)
      returns (o: (bool,nat))
      modifies this
      decreases *
    {
      var U := DiscreteLaplaceSampleLoopIn1(num);
      var v := DiscreteLaplaceSampleLoopIn2(1, 1);
      var V := v - 2;
      var X := U + num * V;
      var Y := X / den;
      var B := BernoulliSample(1, 2);
      o := (B,Y);
    }

    method {:verify false} DiscreteLaplaceSample (num: pos, den: pos)
      returns (o: int)
      modifies this
      decreases *
    {
      var x := DiscreteLaplaceSampleLoop(num, den);
      while ! (! (x.0 == true && x.1 == 0))
        decreases *
      {
        x := DiscreteLaplaceSampleLoop(num, den);
      }
      var r := x;
      var Z := if r.0 == true then - (r.1) else r.1;
      o := Z;
    }

  }

}