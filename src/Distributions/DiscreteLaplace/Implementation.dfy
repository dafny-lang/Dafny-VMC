/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Implementation {
  import Rationals
  import Interface
  import Monad
  import Model
  import Uniform
  import BernoulliExpNeg
  import Bernoulli
  import Coin
  import Equivalence
  import Loops

  trait {:termination false} Trait extends Interface.Trait {

    // Based on Algorithm 2 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method DiscreteLaplaceSample(scale: Rationals.Rational) returns (z: int)
      modifies this
      requires scale.numer >= 1
      decreases *
      ensures Monad.Result(z, s) == Model.Sample(scale)(old(s))
    {
      var b := true;
      var y := 0;
      while b && y == 0
        decreases *
      {
        var u := UniformSample(scale.numer);
        var d := BernoulliExpNegSample(Rationals.Rational(u, scale.numer));
        if d {
          var v := DiscreteLaplaceSampleHelper();
          var x := u + scale.numer * v;
          y := x / scale.denom;
          b := CoinSample();
        }
      }
      z := if b then -y else y;
      assume {:axiom} Monad.Result(z, s) == Equivalence.SampleTailRecursive(scale)(old(s));
      Equivalence.SampleTailRecursiveEquivalence(scale, old(s));
    }

    method DiscreteLaplaceSampleHelper() returns (v: int) 
      modifies this
      decreases *
      ensures Model.SampleHelper.requires(old(s))
      ensures Model.SampleHelper(old(s)) == Monad.Result(v, s)
    {
      assume {:axiom} Model.SampleHelper.requires(old(s));

      var a := true;
      v := 0;
      ghost var fuel := Loops.LeastFuel(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, (true, 0), old(s));

      ghost var prevFuel := fuel;
      ghost var prevA := a;
      ghost var prevV := v;
      ghost var prevS := s;
    

      a := BernoulliExpNegSample(Rationals.Int(1));
      if a {
        v := v + 1;
      }
      fuel := fuel - 1;

      while a
        decreases *
        invariant Equivalence.SampleTailRecursiveHelperLoop(old(s)) == Equivalence.SampleTailRecursiveHelperLoopCut((a, v), fuel)(s)
        //invariant !a ==> Equivalence.SampleTailRecursiveHelperLoopCut((a, v), fuel)(s) == Monad.Result((a, v), s); 
        //invariant Equivalence.SampleTailRecursiveHelperLoop(old(s)) == Equivalence.SampleTailRecursiveHelperLoopCut((prevA, prevV), prevFuel)(prevS)
        //invariant Equivalence.SampleTailRecursiveHelperLoopCut((prevA, prevV), prevFuel)(prevS) == Equivalence.SampleTailRecursiveHelperLoopCut((a, v), fuel)(s)
      {
        assume {:axiom} fuel > 1;
        prevFuel := fuel;
        prevA := a;
        prevV := v;
        prevS := s;

        a := BernoulliExpNegSample(Rationals.Int(1));
        if a {
          v := v + 1;
        }
        fuel := fuel - 1;
      }

      //assert A1: Equivalence.SampleTailRecursiveHelperLoopCut((a, v), fuel)(s) == Monad.Result((a, v), s);
      //assert A2: Equivalence.SampleTailRecursiveHelperLoop(old(s)) == Equivalence.SampleTailRecursiveHelperLoopCut((prevA, prevV), prevFuel)(prevS);
      //assert A3: Equivalence.SampleTailRecursiveHelperLoopCut((prevA, prevV), prevFuel)(prevS) == Equivalence.SampleTailRecursiveHelperLoopCut((a, v), fuel)(s);
      var f := (x: (bool, int)) => x.1;



      calc {
        Model.SampleHelper(old(s));
        { Equivalence.SampleTailRecursiveHelperEquivalence(old(s)); }
        Equivalence.SampleTailRecursiveHelper(old(s));
        Equivalence.SampleTailRecursiveHelperLoop(old(s)).Map(f);
        //{ reveal A2; }
       // Equivalence.SampleTailRecursiveHelperLoopCut((prevA, prevV), prevFuel)(prevS).Map(f);
       // { reveal A3; }
        Equivalence.SampleTailRecursiveHelperLoopCut((a, v), fuel)(s).Map(f);
        //{ reveal A1; }
        Monad.Result((a, v), s).Map(f);
        Monad.Result(v, s); 
      }
      
    }
  }
}
