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

  ghost function SampleLoopBody(scale: Rationals.Rational): ((bool, int)) -> Monad.Hurd<(bool, int)>
    requires scale.numer >= 1
  {
    // replace with functional version using SampleHelper
    (x: (bool, int)) => Monad.Return(x)
  }

  ghost function SampleLoopCondition(x: (bool, int)): bool {
    x.0 && x.1 == 0
  }

  ghost function SampleHelper(s: Rand.Bitstream): Monad.Result<int>
    requires Loops.WhileCutTerminates(SampleHelperLoopCondition, SampleHelperLoopBody, (true, 0), s)
  {
    var f := (x: (bool, int)) => x.1;
    SampleHelperLoop(s).Map(f)
  }

  ghost function SampleHelperLoop(s: Rand.Bitstream, x: (bool, int) := (true, 0)): Monad.Result<(bool, int)>
    requires Loops.WhileCutTerminates(SampleHelperLoopCondition, SampleHelperLoopBody, x, s)
  {
    Loops.While(SampleHelperLoopCondition, SampleHelperLoopBody)(x)(s)
  }

  ghost function SampleHelperLoopBody(x: (bool, int)): Monad.Hurd<(bool, int)> {
    (s: Rand.Bitstream) =>
      var (a, s) :- BernoulliExpNeg.Model.Sample(Rationals.Int(1))(s);
      Monad.Result((a, if a then x.1 + 1 else x.1), s)
  }

  ghost function SampleHelperLoopCondition(x: (bool, int)): bool {
    x.0
  }
}
