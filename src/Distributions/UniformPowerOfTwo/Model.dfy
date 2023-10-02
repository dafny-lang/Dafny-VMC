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
  function ProbUnif(n: nat): (h: Monad.Hurd<nat>) {
    if n == 0 then
      Monad.Return(0)
    else
      Monad.Bind(ProbUnif(n/2), UnifStep)
  }

  lemma {:axiom} ProbUnifTerminates(n: nat)
    requires n > 0
    ensures
      var b := ProbUnif(n - 1);
      var c := (x: nat) => x < n;
      && Independence.IsIndepFn(b)
      && Quantifier.ExistsStar(WhileAndUntil.Helper2(b, c))
      && WhileAndUntil.ProbUntilTerminates(b, c)

  function ProbUnifAlternative(n: nat, s: RandomNumberGenerator.RNG, k: nat := 1, u: nat := 0): (t: (nat, RandomNumberGenerator.RNG))
    requires k >= 1
    decreases 2*n - k
  {
    if k > n then
      (u, s)
    else
      ProbUnifAlternative(n, Monad.Tail(s), 2*k, if Monad.Head(s) then 2*u + 1 else 2*u)
  }

  function UnifAlternativeModel(n: nat, k: nat := 1, u: nat := 0): Monad.Hurd<nat>
    requires k >= 1
  {
    (s: RandomNumberGenerator.RNG) => ProbUnifAlternative(n, s, k, u)
  }

  function UnifModel(n: nat): (f: Monad.Hurd<nat>)
    ensures forall s :: f(s) == UnifAlternativeModel(n)(s)
  {
    var f := ProbUnif(n);
    assert forall s :: f(s) == UnifAlternativeModel(n)(s) by {
      forall s ensures f(s) == UnifAlternativeModel(n)(s) {
        ProbUnifCorrespondence(n, s);
      }
    }
    f
  }

  // incomplete
  lemma ProbUnifCorrespondence(n: nat, s: RandomNumberGenerator.RNG)
    ensures ProbUnifAlternative(n, s) == ProbUnif(n)(s)
  {
    var f := (m: nat) =>
        var g := (b: bool) =>
                   Monad.Return(if b then 2*m + 1 else 2*m);
        Monad.Bind(Monad.Deconstruct, g);
    if n == 0 {
    } else if n == 1 {
      assert n / 2 == 0;
      assert (0, s) == ProbUnif(n/2)(s);
      calc {
        ProbUnif(n)(s);
        Monad.Bind(ProbUnif(n/2), f)(s);
        f(0)(s);
        Monad.Bind(Monad.Deconstruct, (b: bool) => Monad.Return(if b then 1 else 0))(s);
        Monad.Return(if Monad.Head(s) then 1 else 0)(Monad.Tail(s));
        (if Monad.Head(s) then 1 else 0, Monad.Tail(s));
        ProbUnifAlternative(1, Monad.Tail(s), 2, if Monad.Head(s) then 1 else 0);
        ProbUnifAlternative(1, s, 1, 0);
        ProbUnifAlternative(n, s);
      }
    } else {
      assume {:axiom} false;
    }
  }
}
