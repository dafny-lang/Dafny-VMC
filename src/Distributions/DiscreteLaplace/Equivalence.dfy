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

  /*******
   Lemmas
  *******/

  lemma SampleLiftToEnsure(scale: Rationals.Rational, s: Rand.Bitstream, t: Rand.Bitstream, x: (bool, int))
    requires scale.numer >= 1
    requires R1: Monad.Result(x, s) == Model.SampleLoop(scale)(t)
    ensures Monad.Result(if x.0 then -x.1 else x.1, s) == Model.Sample(scale)(t)
  {
    var f := (x: (bool, int)) => if x.0 then -x.1 else x.1;

    calc {
      Monad.Result(if x.0 then -x.1 else x.1, s);
      Monad.Result(f(x), s);
      Monad.Result(x, s).Map(f);
      { reveal R1; }
      Model.SampleLoop(scale)(t).Map(f);
      Monad.Map(Model.SampleLoop(scale), f)(t);
      { reveal Model.Sample(); }
      Model.Sample(scale)(t);
    }
  }

  lemma SampleInnerLoopLiftToEnsures(s: Rand.Bitstream, t: Rand.Bitstream, a: bool, v: int)
    requires R1: Model.SampleInnerLoop()(s) == Model.SampleInnerLoop((a, v))(t)
    requires R2: !a
    ensures Model.SampleInnerLoopFull()(s) == Monad.Result(v, t)
  {
    var f := (x: (bool, int)) => x.1;

    assert A: Model.SampleInnerLoop()(s) == Monad.Result((a, v), t) by {
      calc {
        Model.SampleInnerLoop()(s);
        { reveal R1; }
        Model.SampleInnerLoop((a, v))(t);
        { SampleInnerLoopTailRecursiveEquivalence(t, (a, v)); reveal R2; }
        Monad.Return((a, v))(t);
        Monad.Result((a, v), t);
      }
    }

    calc {
      Model.SampleInnerLoopFull()(s);
      { reveal Model.SampleInnerLoopFull(); }
      Model.SampleInnerLoop()(s).Map(f);
      { reveal A; }
      Monad.Result((a, v), t).Map(f);
      Monad.Result(v, t);
    }
  }

  lemma SampleInnerLoopTailRecursiveEquivalence(s: Rand.Bitstream, x: (bool, int) := (true, 0))
    ensures
      Model.SampleInnerLoop(x)(s) ==
      if x.0 then
        Monad.Bind(
          BernoulliExpNeg.Model.Sample(Rationals.Int(1)),
          (a: bool) => Model.SampleInnerLoop((a, if a then x.1 + 1 else x.1))
        )(s)
      else
        Monad.Return(x)(s)
  {
    calc {
      Model.SampleInnerLoop(x)(s);
    == { reveal Loops.While();
         reveal Model.SampleInnerLoop();
         reveal Model.SampleInnerLoopBody();
         reveal Model.SampleInnerLoopCondition(); }
      Loops.While(Model.SampleInnerLoopCondition, Model.SampleInnerLoopBody)(x)(s);
    == { Model.SampleInnerLoopTerminatesAlmostSurely();
         Loops.WhileUnroll(Model.SampleInnerLoopCondition, Model.SampleInnerLoopBody, x, s);
         reveal Model.SampleInnerLoop();
         reveal Model.SampleInnerLoopBody();
         reveal Model.SampleInnerLoopCondition(); }
      if Model.SampleInnerLoopCondition(x) then
        Monad.Bind(Model.SampleInnerLoopBody(x), (y: (bool, int)) => Model.SampleInnerLoop(y))(s)
      else
        Monad.Return(x)(s);
    == { reveal Model.SampleInnerLoopBody();
         reveal Model.SampleInnerLoopCondition(); }
      if x.0 then
        Monad.Bind(
          Monad.Bind(
            BernoulliExpNeg.Model.Sample(Rationals.Int(1)),
            (a: bool) => Monad.Return((a, if a then x.1 + 1 else x.1))
          ),
          (y: (bool, int)) => Model.SampleInnerLoop(y)
        )(s)
      else
        Monad.Return(x)(s);
    ==
      if x.0 then
        Monad.Bind(
          BernoulliExpNeg.Model.Sample(Rationals.Int(1)),
          (a: bool) =>
            Monad.Bind(
              Monad.Return((a, if a then x.1 + 1 else x.1)),
              (y: (bool, int)) => Model.SampleInnerLoop(y)
            )
        )(s)
      else
        Monad.Return(x)(s);
    ==
      if x.0 then
        Monad.Bind(
          BernoulliExpNeg.Model.Sample(Rationals.Int(1)),
          (a: bool) => Model.SampleInnerLoop((a, if a then x.1 + 1 else x.1))
        )(s)
      else
        Monad.Return(x)(s);
    }
  }
}