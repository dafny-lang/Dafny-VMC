/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/Quantifier.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"

module UniformPowerOfTwoModel {
  import RandomNumberGenerator
  import Quantifier
  import Monad
  import Independence
  import WhileAndUntil

  function UnifStepHelper(m: nat): bool -> Monad.Hurd<nat> {
    (b: bool) => Monad.Return(if b then 2*m + 1 else 2*m)
  }

  function UnifStep(m: nat): Monad.Hurd<nat> {
    Monad.Bind(Monad.Deconstruct, UnifStepHelper(m))
  }

  // Definition 48
  function Sample(n: nat): (h: Monad.Hurd<nat>) {
    if n == 0 then
      Monad.Return(0)
    else
      Monad.Bind(Sample(n/2), UnifStep)
  }

  lemma {:axiom} SampleTerminates(n: nat)
    requires n > 0
    ensures
      var b := Sample(n - 1);
      var c := (x: nat) => x < n;
      && Independence.IsIndepFn(b)
      && Quantifier.ExistsStar(WhileAndUntil.Helper2(b, c))
      && WhileAndUntil.ProbUntilTerminates(b, c)

  function SampleAlternative(n: nat, k: nat := 1, u: nat := 0): Monad.Hurd<nat>
    requires k >= 1
    decreases 2*n - k
  {
    (s: RandomNumberGenerator.RNG) =>
      if k > n then
        (u, s)
      else
        SampleAlternative(n, 2*k, if Monad.Head(s) then 2*u + 1 else 2*u)(Monad.Tail(s))
  }

  // incomplete
  lemma SampleCorrespondence(n: nat, s: RandomNumberGenerator.RNG)
    ensures SampleAlternative(n)(s) == Sample(n)(s)
  {
    var f := (m: nat) =>
        var g := (b: bool) =>
                   Monad.Return(if b then 2*m + 1 else 2*m);
        Monad.Bind(Monad.Deconstruct, g);
    if n == 0 {
    } else if n == 1 {
      assert n / 2 == 0;
      assert (0, s) == Sample(n/2)(s);
      calc {
        Sample(n)(s);
        Monad.Bind(Sample(n/2), f)(s);
        f(0)(s);
        Monad.Bind(Monad.Deconstruct, (b: bool) => Monad.Return(if b then 1 else 0))(s);
        Monad.Return(if Monad.Head(s) then 1 else 0)(Monad.Tail(s));
        (if Monad.Head(s) then 1 else 0, Monad.Tail(s));
        SampleAlternative(1, 2, if Monad.Head(s) then 1 else 0)(Monad.Tail(s));
        SampleAlternative(1, 1, 0)(s);
        SampleAlternative(n)(s);
      }
    } else {
      assume {:axiom} false;
    }
  }
}
