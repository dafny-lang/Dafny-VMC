/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Equivalence {
  import Rand
  import Monad
  import Rationals
  import BernoulliExpNeg
  import Uniform
  import Coin
  import Model
  import Loops

  /************
   Definitions
  ************/

  ghost function SampleTailRecursive(scale: Rationals.Rational, b: bool := true, y: int := 0): Monad.Hurd<int>
    requires scale.numer >= 1
  {
    assume {:axiom} false; // assume termination
    (s: Rand.Bitstream) =>
      if !(b && y == 0) then
        Monad.Result(if b then -y else y, s)
      else
        var (u, s) :- Uniform.Model.Sample(scale.numer)(s);
        var (d, s) :- BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer))(s);
        if d then
          var (v, s) :- SampleTailRecursiveHelper(s);
          var x := u + scale.numer * v;
          var y := x / scale.denom;
          var sample := Coin.Model.Sample(s);
          SampleTailRecursive(scale, sample.value, y)(sample.rest)
        else
          SampleTailRecursive(scale, b, y)(s)
  }

  ghost function SampleTailRecursiveHelper(s: Rand.Bitstream): Monad.Result<int>
    requires Loops.WhileCutTerminates(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, (true, 0), s)
  {
    var f := (x: (bool, int)) => x.1;
    SampleTailRecursiveHelperLoop(s).Map(f)
  }

  ghost function SampleTailRecursiveHelperLoop(s: Rand.Bitstream, x: (bool, int) := (true, 0)): Monad.Result<(bool, int)>
    requires Loops.WhileCutTerminates(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, s)
  {
    var fuel := Loops.LeastFuel(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, s);
    SampleTailRecursiveHelperLoopCut(x, fuel)(s)
  }

  ghost function SampleTailRecursiveHelperLoopCut(x: (bool, int) := (true, 0), fuel: nat): Monad.Hurd<(bool, int)>
    decreases fuel
  {
    (s: Rand.Bitstream) => 
      if fuel == 0 || !x.0 then
        Monad.Result(x, s)
      else
        var (a, s') :- BernoulliExpNeg.Model.Sample(Rationals.Int(1))(s);
        SampleTailRecursiveHelperLoopCut((a, if a then x.1 + 1 else x.1), fuel - 1)(s')
        // Monad.Bind(Model.SampleHelperLoopBody(x), (x': (bool, int)) => SampleTailRecursiveHelperLoopCut(x', fuel - 1))
  }

  /*******
   Lemmas
  *******/

  lemma {:axiom} SampleTailRecursiveEquivalence(scale: Rationals.Rational, s: Rand.Bitstream)
    requires scale.numer >= 1
    ensures SampleTailRecursive(scale)(s) == Model.Sample(scale)(s)

  lemma SampleTailRecursiveHelperEquivalence(s: Rand.Bitstream)
    requires Loops.WhileCutTerminates(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, (true, 0), s)
    ensures SampleTailRecursiveHelper(s) == Model.SampleHelper(s)
  {
    var f := (x: (bool, int)) => x.1;

    calc {
      SampleTailRecursiveHelper(s);
      SampleTailRecursiveHelperLoop(s).Map(f);
      if SampleTailRecursiveHelperLoop(s).Diverging? then Monad.Diverging else Monad.Result(f(SampleTailRecursiveHelperLoop(s).value), SampleTailRecursiveHelperLoop(s).rest);
      { SampleTailRecursiveHelperEquivalence2((true, 0), s); }
      if Model.SampleHelperLoop(s).Diverging? then Monad.Diverging else Monad.Result(f(Model.SampleHelperLoop(s).value), Model.SampleHelperLoop(s).rest);
      Model.SampleHelperLoop(s).Map(f);
      Model.SampleHelper(s);
    }
  }

  lemma SampleTailRecursiveHelperEquivalence2(x: (bool, int), s: Rand.Bitstream)
    requires Loops.WhileCutTerminates(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, s)
    ensures SampleTailRecursiveHelperLoop(s, x) == Model.SampleHelperLoop(s, x)
  {
    var fuel := Loops.LeastFuel(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, s);
    calc {
      SampleTailRecursiveHelperLoop(s, x);
      SampleTailRecursiveHelperLoopCut(x, fuel)(s);
      { SampleTailRecursiveHelperEquivalence3(x, s, fuel); }
      Loops.WhileCut(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, fuel)(s);
      { reveal Loops.While(); }
      Loops.While(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody)(x)(s);
      Model.SampleHelperLoop(s, x);
    }
  }

  lemma SampleTailRecursiveHelperEquivalence3(x: (bool, int), s: Rand.Bitstream, fuel: nat)
    decreases fuel
    ensures SampleTailRecursiveHelperLoopCut(x, fuel)(s) == Loops.WhileCut(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, fuel)(s)
  {
    if !x.0 {
      calc {
        SampleTailRecursiveHelperLoopCut(x, fuel)(s);
        Monad.Return(x)(s);
        Loops.WhileCut(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, fuel)(s);
      }
    } else if fuel == 0 {
      calc {
        SampleTailRecursiveHelperLoopCut(x, fuel)(s);
        Monad.Return(x)(s);
        Loops.WhileCut(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, fuel)(s);
      }
    } else {
      var r := Model.SampleHelperLoopBody(x)(s);
      if r.Result? {
        var (x', s') := Model.SampleHelperLoopBody(x)(s).Extract();
        calc {
          SampleTailRecursiveHelperLoopCut(x, fuel)(s);
          Monad.Bind(Model.SampleHelperLoopBody(x), (x': (bool, int)) => SampleTailRecursiveHelperLoopCut(x', fuel - 1))(s);
          SampleTailRecursiveHelperLoopCut(x', fuel - 1)(s');
          { SampleTailRecursiveHelperEquivalence3(x', s', fuel - 1); }
          Loops.WhileCut(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x', fuel - 1)(s');
          Monad.Bind(Model.SampleHelperLoopBody(x), (x': (bool, int)) => Loops.WhileCut(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x', fuel - 1))(s);
          Loops.WhileCut(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, fuel)(s);
        }
      } else {
        calc {
          SampleTailRecursiveHelperLoopCut(x, fuel)(s);
          Monad.Bind(Model.SampleHelperLoopBody(x), (x': (bool, int)) => SampleTailRecursiveHelperLoopCut(x', fuel - 1))(s);
          Monad.Diverging;
          Monad.Bind(Model.SampleHelperLoopBody(x), (x': (bool, int)) => Loops.WhileCut(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x', fuel - 1))(s);
          Loops.WhileCut(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, fuel)(s);
        }
      }
    }
  }
}