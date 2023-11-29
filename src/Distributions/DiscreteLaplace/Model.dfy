/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Model {
  import Monad
  import Rand
  import Rationals
  import Uniform
  import BernoulliExpNeg
  import Coin
  import Loops

  /************
   Definitions
  ************/

  ghost function Sample(scale: Rationals.Rational): Monad.Hurd<int>
    requires scale.numer >= 1
  {
    var f := (x: (bool, int)) => if x.0 then -x.1 else x.1;
    Monad.Map(SampleLoop(scale), f)
  }

  ghost function SampleLoop(scale: Rationals.Rational): Monad.Hurd<(bool, int)>
    requires scale.numer >= 1
  {
    Loops.While(SampleLoopCondition, SampleLoopBody(scale))((true, 0))
  }

  // TODO: add correct version later
  ghost function SampleLoopBody(scale: Rationals.Rational): ((bool, int)) -> Monad.Hurd<(bool, int)>
    requires scale.numer >= 1
  {
    // replace with functional version using SampleHelper
    (x: (bool, int)) => Monad.Return(x)
  }

  ghost function SampleLoopCondition(x: (bool, int)): bool {
    x.0 && (x.1 == 0)
  }

  ghost function SampleInnerLoopFull(): Monad.Hurd<int> {
    var f := (x: (bool, int)) => x.1;
    Monad.Map(SampleInnerLoop(), f)
  }

  ghost function SampleInnerLoop(x: (bool, int) := (true, 0)): (f: Monad.Hurd<(bool, int)>) {
    Loops.While(SampleInnerLoopCondition, SampleInnerLoopBody)(x)
  }

  ghost function SampleInnerLoop2(x: (bool, int)): (f: Monad.Hurd<(bool, int)>)
    ensures f == Loops.While(SampleInnerLoopCondition, SampleInnerLoopBody)(x)
  {
    var f := Loops.While(SampleInnerLoopCondition, SampleInnerLoopBody)(x);
    f
  }

  ghost function SampleInnerLoopBody(x: (bool, int)): Monad.Hurd<(bool, int)> {
    Monad.Bind(
      BernoulliExpNeg.Model.Sample(Rationals.Int(1)), 
      (a: bool) => Monad.Return((a, if a then x.1 + 1 else x.1))
    )
  }

  ghost opaque function SampleInnerLoopCondition(x: (bool, int)): bool {
    x.0
  }

  /*******
   Lemmas
  *******/

  // add later
  lemma {:axiom} SampleInnerLoopTerminatesAlmostSurely()
    ensures Loops.WhileTerminatesAlmostSurely(SampleInnerLoopCondition, SampleInnerLoopBody)

}
