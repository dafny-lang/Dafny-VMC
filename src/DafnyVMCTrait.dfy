
module DafnyVMCTrait {

  import UniformPowerOfTwo

  import FisherYates

  import opened Pos

  trait {:termination false} RandomTrait extends  UniformPowerOfTwo.Interface.Trait, FisherYates.Implementation.Trait {

    method {:verify false} UniformSample (n: pos)
      returns (o: nat)
      modifies this
      decreases *
    {
      var x := UniformPowerOfTwoSample(2 * n);
      while ! (x < n)
        decreases *
      {
        x := UniformPowerOfTwoSample(2 * n);
      }
      var r := x;
      o := r;
    }

    method {:verify false} BernoulliSample (num: nat, den: pos)
      returns (o: bool)
      requires num <= den
      modifies this
      decreases *
    {
      var d := UniformSample(den);
      o := d < num;
    }

    method {:verify false} BernoulliExpNegSampleUnitLoop (num: nat, den: pos, state: (bool,pos))
      returns (o: (bool,pos))
      requires num <= den
      modifies this
      decreases *
    {
      var A := BernoulliSample(num, state.1 * den);
      o := (A,state.1 + 1);
    }

    method {:verify false} BernoulliExpNegSampleUnitAux (num: nat, den: pos)
      returns (o: nat)
      requires num <= den
      modifies this
      decreases *
    {
      var state := (true,1);
      while state.0
        decreases *
      {
        state := BernoulliExpNegSampleUnitLoop(num, den, state);
      }
      var r := state;
      o := r.1;
    }

    method {:verify false} BernoulliExpNegSampleUnit (num: nat, den: pos)
      returns (o: bool)
      requires num <= den
      modifies this
      decreases *
    {
      var K := BernoulliExpNegSampleUnitAux(num, den);
      if K % 2 == 0 {
        o := true;
      } else {
        o := false;
      }
    }

    method {:verify false} BernoulliExpNegSampleGenLoop (iter: nat)
      returns (o: bool)
      modifies this
      decreases *
    {
      if iter == 0 {
        o := true;
      } else {
        var B := BernoulliExpNegSampleUnit(1, 1);
        if ! (B == true) {
          o := B;
        } else {
          var R := BernoulliExpNegSampleGenLoop(iter - 1);
          o := R;
        }
      }
    }

    method {:verify false} BernoulliExpNegSample (num: nat, den: pos)
      returns (o: bool)
      modifies this
      decreases *
    {
      if num <= den {
        var X := BernoulliExpNegSampleUnit(num, den);
        o := X;
      } else {
        var gamf := num / den;
        var B := BernoulliExpNegSampleGenLoop(gamf);
        if B == true {
          var num := num - gamf * den;
          var X := BernoulliExpNegSampleUnit(num, den);
          o := X;
        } else {
          o := false;
        }
      }
    }

    method {:verify false} DiscreteLaplaceSampleLoopIn1Aux (t: pos)
      returns (o: (nat,bool))
      modifies this
      decreases *
    {
      var U := UniformSample(t);
      var D := BernoulliExpNegSample(U, t);
      o := (U,D);
    }

    method {:verify false} DiscreteLaplaceSampleLoopIn1 (t: pos)
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

    method {:verify false} DiscreteLaplaceSampleLoopIn2Aux (num: nat, den: pos, K: (bool,pos))
      returns (o: (bool,pos))
      requires num <= den
      modifies this
      decreases *
    {
      var A := BernoulliExpNegSampleUnit(num, den);
      o := (A,K.1 + 1);
    }

    method {:verify false} DiscreteLaplaceSampleLoopIn2 (num: nat, den: pos)
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

    method {:verify false} DiscreteGaussianSample (num: pos, den: pos)
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
