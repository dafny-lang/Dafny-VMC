/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/Quantifier.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"

module UnifModel {
  import opened RandomNumberGenerator
  import opened Quantifier
  import opened Monad
  import opened Independence
  import opened WhileAndUntil

  // Definition 48
  function ProbUnif(n: nat): (h: Hurd<nat>) {
    if n == 0 then
      Return(0)
    else
      var f := (m: nat) =>
                  var g := (b: bool) =>
                            Return(if b then 2*m + 1 else 2*m);
                  Bind(Deconstruct, g);
      Bind(ProbUnif(n/2), f)
  }

  lemma {:axiom} ProbUnifTerminates(n: nat)
    requires n > 0
    ensures
      var b := ProbUnif(n - 1);
      var c := (x: nat) => x < n;
      && IsIndepFn(b)
      && ExistsStar(Helper2(b, c))
      && ProbUntilTerminates(b, c)

  function ProbUnifAlternative(n: nat, s: RNG, k: nat := 1, u: nat := 0): (t: (nat, RNG))
    requires k >= 1
    decreases 2*n - k
  {
    if k > n then
      (u, s)
    else
      ProbUnifAlternative(n, Tail(s), 2*k, if Head(s) then 2*u + 1 else 2*u)
  }

  function UnifAlternativeModel(n: nat, k: nat := 1, u: nat := 0): Hurd<nat>
    requires k >= 1
  {
    (s: RNG) => ProbUnifAlternative(n, s, k, u)
  }

  function UnifModel(n: nat): (f: Hurd<nat>)
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

  lemma ProbUnifCorrespondence(n: nat, s: RNG)
    ensures ProbUnifAlternative(n, s) == ProbUnif(n)(s)
  {
    var f := (m: nat) =>
        var g := (b: bool) =>
                   Return(if b then 2*m + 1 else 2*m);
        Bind(Deconstruct, g);
    if n == 0 {
    } else if n == 1 {
      assert n / 2 == 0;
      assert (0, s) == ProbUnif(n/2)(s);
      calc {
        ProbUnif(n)(s);
        Bind(ProbUnif(n/2), f)(s);
        f(0)(s);
        Bind(Deconstruct, (b: bool) => Return(if b then 1 else 0))(s);
        Return(if Head(s) then 1 else 0)(Tail(s));
        (if Head(s) then 1 else 0, Tail(s));
        ProbUnifAlternative(1, Tail(s), 2, if Head(s) then 1 else 0);
        ProbUnifAlternative(1, s, 1, 0);
        ProbUnifAlternative(n, s);
      }
    } else {
      assume {:axiom} false;
    }
  }
}
