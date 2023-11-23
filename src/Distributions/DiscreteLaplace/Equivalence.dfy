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
          var (v, s) :- SampleTailRecursiveHelper()(s);
          var x := u + scale.numer * v;
          var y := x / scale.denom;
          var sample := Coin.Model.Sample(s);
          SampleTailRecursive(scale, sample.value, y)(sample.rest)
        else
          SampleTailRecursive(scale, b, y)(s)
  }

  ghost function SampleTailRecursiveHelper(): Monad.Hurd<int> 
    requires Loops.WhileCutTerminates(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, (true, 0), s)   
  {
    var f := (x: (bool, int)) => x.1;
    Monad.Map(SampleTailRecursiveHelperLoop(), f)
  }

  ghost function SampleTailRecursiveHelperLoop(x: (bool, int) := (true, 0)): Monad.Hurd<(bool, int)> 
    requires Loops.WhileCutTerminates(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, s) 
  {
    var fuel := Loops.LeastFuel(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, s);
    SampleTailRecursiveHelperLoopCut(x, fuel)
  }

  ghost function SampleTailRecursiveHelperLoopCut(x: (bool, int) := (true, 0), fuel): Monad.Hurd<(bool, int)> {
    if fuel == 0 || !x.0 then 
      Monad.Return(x)
    else
      Monad.Bind(Model.SamplerHelperLoopBody(x), (x': (bool, int)) => SampleTailRecursiveHelperLoop(x', fuel - 1))
  }

  /*******
   Lemmas
  *******/

  lemma {:axiom} SampleTailRecursiveEquivalence(scale: Rationals.Rational, s: Rand.Bitstream)
    requires scale.numer >= 1
    ensures SampleTailRecursive(scale)(s) == Model.Sample(scale)(s)

  lemma SampleTailRecursiveHelperEquivalence(s: Rand.Bitstream)
    ensures SampleTailRecursiveHelper()(s) == Model.SampleHelper()(s)
  {
    var f := (x: (bool, int)) => x.1;
    var (x, s') :- SampleTailRecursiveHelperLoop((true, 0))(s);
    var (x', s'') :- Model.SampleHelperLoop((true, 0))(s);
    calc {
      SampleTailRecursiveHelper()(s);
      Monad.Map(SampleTailRecursiveHelperLoop(), f)(s);
      Monad.Bind(SampleTailRecursiveHelperLoop(), (x: bool, int) => Monad.Return(f(x)))(s);
      Monad.Return(f(x'))(s');
      { assert x == x' && s' == s'' by { SampleTailRecursiveHelperCutEquivalence((ture, 0), s) }; }
      Monad.Return(f(x''))(s'');
      Monad.Bind(Model.SampleHelperLoop(), (x: bool, int) => Monad.Return(f(x)));
      Monad.Map(Model.SampleHelperLoop(), f)(s);
      Model.SampleHelper()(s);
    }
  }

  lemma SampleTailRecursiveHelperCutEquivalence(x: (bool, int), s: Rand.Bitstream)
    requires Loops.WhileCutTerminates(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, s) 
    ensures SampleTailRecursiveHelperLoop(x)(s) == Model.SampleHelperLoop(x)(s)
  {
    var fuel := Loops.LeastFuel(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, x, s);
    calc {
      SampleTailRecursiveHelperLoop(x)(s);
      SampleTailRecursiveHelperLoopCut(x, fuel)(s);
      { SampleTailRecursiveHelperCutEquivalence(x, s, fuel); }
      Loops.WhileCut(SampleHelperLoopCondition, SampleHelperLoopBody, x, fuel)(s);
      Loops.While(SampleHelperLoopCondition, SampleHelperLoopBody)(x)(s);
      Model.SampleHelperLoop(x)(s);
    }
  }

  lemma SampleTailRecursiveHelperCutEquivalence(x: (bool, int), s: Rand.Bitstream, fuel: nat)
    ensures SampleTailRecursiveHelperLoopCut(x, fuel)(s) == Loops.WhileCut(SampleHelperLoopCondition, SampleHelperLoopBody, x, fuel)(s)
  {
    if !x.0 {
      calc {
        SampleTailRecursiveHelperLoopCut(x, fuel)(s)
        Monad.Return(x)(s);
        Loops.WhileCut(SampleHelperLoopCondition, SampleHelperLoopBody, x, fuel)(s);
      }
    } else if fuel == 0 {
      calc {
        SampleTailRecursiveHelperLoopCut(x, fuel)(s)
        Monad.Return(x)(s);
        Loops.WhileCut(SampleHelperLoopCondition, SampleHelperLoopBody, x, fuel)(s)
      }
    } else {
      var (x', s') :- Model.SamplerHelperLoopBody(x)(s);
      calc {
        SampleTailRecursiveHelperLoopCut(x, fuel)(s);
        Monad.Bind(Model.SamplerHelperLoopBody(x), (x': (bool, int)) => SampleTailRecursiveHelperLoopCut(x', fuel - 1))(s);
        SampleTailRecursiveHelperLoopCut(x', fuel - 1)(s');
        { SampleTailRecursiveHelperEquivalence(x', s', fuel - 1); }
        Loops.WhileCut(SampleHelperLoopCondition, SampleHelperLoopBody, x', fuel - 1)(s');
        Monad.Bind(Model.SampleHelperLoopBody(x), (x': (bool, int) => Loops.WhileCut(SampleHelperLoopCondition, SampleHelperLoopBody, x', fuel - 1)))(s);
        Monad.Bind(Model.SampleHelperLoopBody(x), (x': (bool, int) => Loops.WhileCut(SampleHelperLoopCondition, SampleHelperLoopBody, x', fuel - 1)))(s);
        Loops.WhileCut(SampleHelperLoopCondition, SampleHelperLoopBody, x, fuel)(s)
    }
  }
}