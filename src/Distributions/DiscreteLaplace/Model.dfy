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

  ghost opaque function Sample(scale: Rationals.Rational): Monad.Hurd<int>
    requires scale.numer >= 1
  {
    var f := (x: (bool, int)) => if x.0 then -x.1 else x.1;
    Monad.Map(SampleLoop(scale), f)
  }

  ghost opaque function SampleLoop(scale: Rationals.Rational, x: (bool, int) := (true, 0)): Monad.Hurd<(bool, int)>
    requires scale.numer >= 1
  {
    Loops.While(SampleLoopCondition, SampleLoopBody(scale))(x)
  }

  ghost opaque function SampleLoopBody(scale: Rationals.Rational): ((bool, int)) -> Monad.Hurd<(bool, int)>
    requires scale.numer >= 1
  {
    (bY: (bool, int)) =>
      Monad.Bind(
        Uniform.Model.Sample(scale.numer),
        (u: nat) =>
          Monad.Bind(
            BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer)),
            (d: bool) =>
              if d then
                Monad.Bind(
                  SampleInnerLoopFull(),
                  (v: int) =>
                    Monad.Bind(
                      Coin.Model.Sample,
                      (b: bool) =>
                        var x := u + scale.numer * v;
                        var y := x / scale.denom;
                        Monad.Return((b, y))
                    )
                )
              else
                Monad.Return(bY)
          )
      )
  }

  ghost opaque function SampleLoopCondition(x: (bool, int)): bool {
    x.0 && (x.1 == 0)
  }

  ghost opaque function SampleInnerLoopFull(): Monad.Hurd<int> {
    var f := (x: (bool, int)) => x.1;
    Monad.Map(SampleInnerLoop(), f)
  }

  ghost opaque function SampleInnerLoop(x: (bool, int) := (true, 0)): Monad.Hurd<(bool, int)> {
    Loops.While(SampleInnerLoopCondition, SampleInnerLoopBody)(x)
  }

  ghost opaque function SampleInnerLoopBody(x: (bool, int)): Monad.Hurd<(bool, int)> {
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

  // TODO: add later
  lemma {:axiom} SampleInnerLoopTerminatesAlmostSurely()
    ensures Loops.WhileTerminatesAlmostSurely(SampleInnerLoopCondition, SampleInnerLoopBody)

  // TODO: add later
  lemma {:axiom} SampleLoopTerminatesAlmostSurely(scale: Rationals.Rational)
    requires scale.numer >= 1
    ensures Loops.WhileTerminatesAlmostSurely(SampleLoopCondition, SampleLoopBody(scale))
}
