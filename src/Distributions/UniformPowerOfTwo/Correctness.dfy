/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Helper.dfy"
include "../../Math/MeasureTheory.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Quantifier.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"
include "Model.dfy"

module UniformPowerOfTwoCorrectness {
  import Helper
  import Monad
  import Independence
  import RandomNumberGenerator
  import Quantifier
  import WhileAndUntil
  import MeasureTheory
  import UniformPowerOfTwoModel

  /************
   Definitions
  ************/

  // Definition 50
  // An approximately uniform sampler: may have too much mass on 0.
  function ProbUniformCut(t: nat, n: nat): Monad.Hurd<nat>
    requires n > 0
  {
    if t == 0 then
      Monad.Return(0)
    else
      var f := (m: nat) =>
                 if n <= m then
                   ProbUniformCut(t-1, n)
                 else
                   Monad.Return(m);
      Monad.Bind(UniformPowerOfTwoModel.ProbUnif(n-1), f)
  }

  function ProbUniformAlternative(n: nat, s: RandomNumberGenerator.RNG): (t: (nat, RandomNumberGenerator.RNG))
    requires n > 0
  {
    assume {:axiom} false; // Assume termination
    var (u, s) := UniformPowerOfTwoModel.ProbUnif(n-1)(s);
    if u < n then
      (u, s)
    else
      ProbUniformAlternative(n, s)
  }

  function ProbUnifExistence(n: nat, s: RandomNumberGenerator.RNG, j: nat): (i: nat)
    ensures UniformPowerOfTwoModel.ProbUnif(n)(s).1(j) == s(i)
  {
    if n == 0 then
      j
    else
      var i := ProbUnifExistence(n / 2, s, j + 1);
      calc {
        UniformPowerOfTwoModel.ProbUnif(n)(s).1(j);
      ==
        Monad.Tail(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1)(j);
      ==
        UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1(j + 1);
      ==
        s(i);
      }
      i
  }

  function ProbUnifDeconstruct(n: nat, m: nat, s: RandomNumberGenerator.RNG): (i: nat)
    ensures s(i) == Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0
  {
    var i := ProbUnifExistence(n / 2, s, 0);
    assert UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1(0) == s(i);
    assert Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0 == UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1(0);
    i
  }

  ghost predicate UnifIsCorrect(n: nat, k: nat, m: nat)
    requires (n == 0 && k == 0) || (k != 0 && Helper.Power(2, k - 1) <= n < Helper.Power(2, k))
  {
    RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m) == if m < Helper.Power(2, k) then 1.0 / (Helper.Power(2, k) as real) else 0.0
  }

  function ProbUnif1(n: nat): RandomNumberGenerator.RNG -> RandomNumberGenerator.RNG {
    (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n)(s).1
  }

  /*******
   Lemmas
  *******/

  // Equation (4.8)
  lemma UnifCorrectness(n: nat, k: nat)
    requires (n == 0 && k == 0) || (k != 0 && Helper.Power(2, k - 1) <= n < Helper.Power(2, k))
    ensures forall m: nat :: UnifIsCorrect(n, k, m)
  {
    forall m: nat ensures UnifIsCorrect(n, k, m) {
      if (n == 0 && k == 0) {
        UnifCorrectnessCaseNZeroKZero(m);
      } else {
        assert (k != 0 && Helper.Power(2, k - 1) <= n < Helper.Power(2, k));
        assert n > 0;
        assert n > 1 ==> n / 2 > 0;
        if k - 2 < 0 {
          assert 0 < k < 2;
          assert k == 1;
          assert Helper.Power(2, k) == 2;
          assert 0 < n < 2;
          assert n == 1;
          assert n / 2 == 0;
          if m % 2 == 0 {
            UnifCorrectnessCaseKOneMEven(n, m);
          } else {
            assert m % 2 == 1;
            UnifCorrectnessCaseKOneMOdd(n, m);
          }
        } else {
          assert Helper.Power(2, k - 1) / 2 <= n / 2 < Helper.Power(2, k) / 2;
          assert Helper.Power(2, k - 2) <= n / 2 < Helper.Power(2, k - 1);
          var u := m / 2;
          if m % 2 == 0 {
            UnifCorrectnessCaseKGreaterOneMEven(n, k, m);
          } else {
            UnifCorrectnessCaseKGreaterOneMOdd(n, k, m);
          }
        }
      }
    }
  }

  lemma UnifCorrectnessCaseNZeroKZero(m: nat)
    ensures UnifIsCorrect(0, 0, m)
  {
    assert Helper.Power(2, 0) == 1;
    if m == 0 {
      assert (iset s | UniformPowerOfTwoModel.ProbUnif(0)(s).0 == m) == (iset s {:trigger true} | true);
      RandomNumberGenerator.RNGHasMeasure();
    } else {
      assert (iset s | UniformPowerOfTwoModel.ProbUnif(0)(s).0 == m) == iset{};
      RandomNumberGenerator.RNGHasMeasure();
    }
  }

  lemma UnifCorrectnessCaseKOneMEven(n: nat, m: nat)
    requires 1 <= n < 2
    requires m % 2 == 0
    ensures UnifIsCorrect(n, 1, m)
  {
    calc {
      RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
    == { ProbUnifCaseSplit(n, m); }
      RandomNumberGenerator.mu(iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == m) / 2.0;
    == { assert (iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == m) == (iset s {:trigger 0 == m} | 0 == m); }
      RandomNumberGenerator.mu(iset s {:trigger 0 == m} | 0 == m) / 2.0;
    }
    if m < Helper.Power(2, 1) {
      assert m == 0;
      calc {
        RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
      ==
        RandomNumberGenerator.mu(iset s {:trigger 0 == m} | 0 == m) / 2.0;
      == { assert (iset s: RandomNumberGenerator.RNG {:trigger 0 == m} | 0 == m) == (iset s {:trigger true} | true); }
        RandomNumberGenerator.mu(iset s {:trigger true} | true) / 2.0;
      == { RandomNumberGenerator.RNGHasMeasure(); }
        1.0 / 2.0;
      ==
        1.0 / (2 as real);
      == { assert Helper.Power(2, 1) == 2; }
        1.0 / (Helper.Power(2, 1) as real);
      }
    } else {
      assert m != 0;
      calc {
        RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
      ==
        RandomNumberGenerator.mu(iset s {:trigger 0 == m} | 0 == m) / 2.0;
      == { assert (iset s: RandomNumberGenerator.RNG {:trigger 0 == m} | 0 == m) == iset{}; }
        RandomNumberGenerator.mu(iset {}) / 2.0;
      == { RandomNumberGenerator.RNGHasMeasure(); }
        0.0 / 2.0;
      ==
        0.0;
      }
    }
  }

  lemma UnifCorrectnessCaseKOneMOdd(n: nat, m: nat)
    requires 1 <= n < 2
    requires m % 2 == 1
    ensures UnifIsCorrect(n, 1, m)
  {
    calc {
      RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
    == { ProbUnifCaseSplit(n, m); }
      RandomNumberGenerator.mu(iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 + 1 == m) / 2.0;
    == { assert (iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 + 1 == m) == (iset s {:trigger 1 == m} | 1 == m); }
      RandomNumberGenerator.mu(iset s {:trigger 1 == m} | 1 == m) / 2.0;
    }
    if m < Helper.Power(2, 1) {
      assert m == 1;
      calc {
        RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
      ==
        RandomNumberGenerator.mu(iset s {:trigger 1 == m} | 1 == m) / 2.0;
      == { assert (iset s: RandomNumberGenerator.RNG {:trigger 1 == m} | 1 == m) == (iset s {:trigger true} | true); }
        RandomNumberGenerator.mu(iset s {:trigger true} | true) / 2.0;
      == { RandomNumberGenerator.RNGHasMeasure(); Helper.DivisionSubstituteAlternativeReal(2.0, RandomNumberGenerator.mu(iset s {:trigger true} | true), 1.0); }
        1.0 / 2.0;
      ==
        1.0 / (Helper.Power(2, 1) as real);
      }
    } else {
      assert m != 1;
      calc {
        RandomNumberGenerator.mu(iset s: RandomNumberGenerator.RNG | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
      ==
        RandomNumberGenerator.mu(iset s: RandomNumberGenerator.RNG {:trigger 1 == m} | 1 == m) / 2.0;
      == { assert (iset s: RandomNumberGenerator.RNG {:trigger 1 == m} | 1 == m) == iset{}; }
        RandomNumberGenerator.mu(iset {}) / 2.0;
      == { RandomNumberGenerator.RNGHasMeasure(); }
        0.0 / 2.0;
      ==
        0.0;
      }
    }
  }

  lemma UnifCorrectnessCaseKGreaterOneMEven(n: nat, k: nat, m: nat)
    requires k >= 2
    requires Helper.Power(2, k - 1) <= n < Helper.Power(2, k)
    requires m % 2 == 0
    ensures UnifIsCorrect(n, k, m)
  {
    var u := m / 2;
    assert m == 2 * u;
    calc {
      RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
    == { ProbUnifCaseSplit(n, m); }
      RandomNumberGenerator.mu(iset s | 2 * UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == m) / 2.0;
    == { assert (iset s | 2 * UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == m) == (iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == u); }
      RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == u) / 2.0;
    }
    if m < Helper.Power(2, k) {
      assert RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == u) == 1.0 / (Helper.Power(2, k - 1) as real) by {
        assert u < Helper.Power(2, k - 1);
        UnifCorrectness(n / 2, k - 1);
        assert UnifIsCorrect(n / 2, k - 1, u);
      }
      calc {
        RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
      ==
        RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == u) / 2.0;
      ==
        (1.0 / Helper.Power(2, k - 1) as real) / 2.0;
      == { PowerOfTwoLemma(k - 1); }
        1.0 / (Helper.Power(2, k) as real);
      }
      assert UnifIsCorrect(n / 2, k - 1, u);
    } else {
      assert u >= Helper.Power(2, k - 1);
      UnifCorrectness(n / 2, k - 1);
      assert UnifIsCorrect(n / 2, k - 1, u);
      assert RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m) == 0.0;
      assert UnifIsCorrect(n / 2, k - 1, u);
    }
  }

  lemma UnifCorrectnessCaseKGreaterOneMOdd(n: nat, k: nat, m: nat)
    requires k >= 2
    requires Helper.Power(2, k - 1) <= n < Helper.Power(2, k)
    requires m % 2 == 1
    ensures UnifIsCorrect(n, k, m)
  {
    var u := m / 2;
    assert m == 2 * u + 1;
    calc {
      RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
    == { ProbUnifCaseSplit(n, m); }
      RandomNumberGenerator.mu(iset s | 2 * UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 + 1 == m) / 2.0;
    == { assert (iset s | 2 * UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 + 1 == m) == (iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == u); }
      RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == u) / 2.0;
    }
    if m < Helper.Power(2, k) {
      assert RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == u) == 1.0 / (Helper.Power(2, k - 1) as real) by {
        assert u < Helper.Power(2, k - 1);
        UnifCorrectness(n / 2, k - 1);
        assert UnifIsCorrect(n / 2, k - 1, u);
      }
      calc {
        RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
      ==
        RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == u) / 2.0;
      ==
        (1.0 / Helper.Power(2, k - 1) as real) / 2.0;
      == { PowerOfTwoLemma(k - 1); }
        1.0 / (Helper.Power(2, k) as real);
      }
      assert UnifIsCorrect(n, k, m);
    } else {
      assert u >= Helper.Power(2, k - 1);
      UnifCorrectness(n / 2, k - 1);
      assert UnifIsCorrect(n / 2, k - 1, u);
      assert RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m) == 0.0;
      assert UnifIsCorrect(n, k, m);
    }
  }

  lemma PowerOfTwoLemma(k: nat)
    ensures (1.0 / Helper.Power(2, k) as real) / 2.0 == 1.0 / (Helper.Power(2, k + 1) as real)
  {
    calc {
      (1.0 / Helper.Power(2, k) as real) / 2.0;
    == { Helper.DivDivToDivMul(1.0, Helper.Power(2, k) as real, 2.0); }
      1.0 / (Helper.Power(2, k) as real * 2.0);
    == { Helper.NatMulNatToReal(Helper.Power(2, k), 2); }
      1.0 / (Helper.Power(2, k) * 2) as real;
    ==
      1.0 / (Helper.Power(2, k + 1) as real);
    }
  }

  // Equation (4.7)
  lemma {:axiom} ProbUnifIsIndepFn(n: nat)
    ensures Independence.IsIndepFn(UniformPowerOfTwoModel.ProbUnif(n))

  // See PROB_UNIFORM_TERMINATES
  lemma {:axiom} ProbUnifForAllStar(n: nat)
    requires n != 0
    ensures
      var p := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 < n;
      Quantifier.ForAllStar(p)

  lemma ProbUnifIsMeasurePreserving(n: nat)
    ensures MeasureTheory.IsMeasurePreserving(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, RandomNumberGenerator.event_space, RandomNumberGenerator.mu, ProbUnif1(n))
  {
    var f := ProbUnif1(n);
    assert MeasureTheory.IsMeasurable(RandomNumberGenerator.event_space, RandomNumberGenerator.event_space, f) by {
      ProbUnifIsIndepFn(n);
      assert Independence.IsIndepFn(UniformPowerOfTwoModel.ProbUnif(n));
    }
    var g := ProbUnif1(n / 2);
    if n == 0 {
      forall e | e in RandomNumberGenerator.event_space ensures RandomNumberGenerator.mu(MeasureTheory.PreImage(f, e)) == RandomNumberGenerator.mu(e) {
        forall s: RandomNumberGenerator.RNG ensures f(s) == s {
          assert f(s) == s;
        }
        MeasureTheory.PreImageIdentity(f, e);
      }
      assert MeasureTheory.IsMeasurePreserving(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, RandomNumberGenerator.event_space, RandomNumberGenerator.mu, f);
    } else {
      forall e | e in RandomNumberGenerator.event_space ensures RandomNumberGenerator.mu(MeasureTheory.PreImage(f, e)) == RandomNumberGenerator.mu(e) {
        var e' := (iset s | Monad.Tail(s) in e);
        assert e' in RandomNumberGenerator.event_space by {
          assert e' == MeasureTheory.PreImage(Monad.Tail, e);
          Monad.TailIsMeasurePreserving();
          assert MeasureTheory.IsMeasurable(RandomNumberGenerator.event_space, RandomNumberGenerator.event_space, Monad.Tail);
        }
        assert MeasureTheory.PreImage(f, e) == MeasureTheory.PreImage(g, e') by {
          assert forall s :: f(s) in e <==> g(s) in e' by {
            forall s ensures f(s) in e <==> g(s) in e' {
              calc {
                f(s) in e;
              <==> { assert f(s) == UniformPowerOfTwoModel.ProbUnif(n)(s).1; }
                UniformPowerOfTwoModel.ProbUnif(n)(s).1 in e;
              <==> { ProbUnifTailDecompose(n, s); }
                Monad.Tail(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1) in e;
              <==>
                UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1 in e';
              <==> { assert UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1 == g(s); }
                g(s) in e';
              }
            }
          }
          MeasureTheory.PreImagesEqual(f, e, g, e');
        }
        assert RandomNumberGenerator.mu(MeasureTheory.PreImage(f, e)) == RandomNumberGenerator.mu(e) by {
          calc {
            RandomNumberGenerator.mu(MeasureTheory.PreImage(f, e));
          ==
            RandomNumberGenerator.mu(MeasureTheory.PreImage(g, e'));
          == { ProbUnifIsMeasurePreserving(n / 2); assert MeasureTheory.IsMeasurePreserving(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, RandomNumberGenerator.event_space, RandomNumberGenerator.mu, g); assert e' in RandomNumberGenerator.event_space; }
            RandomNumberGenerator.mu(e');
          == { assert e' == MeasureTheory.PreImage(Monad.Tail, e); }
            RandomNumberGenerator.mu(MeasureTheory.PreImage(Monad.Tail, e));
          == { Monad.TailIsMeasurePreserving(); }
            RandomNumberGenerator.mu(e);
          }
        }
      }
      assert MeasureTheory.IsMeasurePreserving(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, RandomNumberGenerator.event_space, RandomNumberGenerator.mu, f);
    }
  }

  lemma ProbUnifTailDecompose(n: nat, s: RandomNumberGenerator.RNG)
    requires n != 0
    ensures UniformPowerOfTwoModel.ProbUnif(n)(s).1 == Monad.Tail(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1)
  {
    var (a, s') := UniformPowerOfTwoModel.ProbUnif(n / 2)(s);
    var (b, s'') := Monad.Deconstruct(s');
    calc {
      UniformPowerOfTwoModel.ProbUnif(n)(s).1;
    ==
      Monad.Bind(UniformPowerOfTwoModel.ProbUnif(n / 2), UniformPowerOfTwoModel.UnifStep)(s).1;
    ==
      UniformPowerOfTwoModel.UnifStep(a)(s').1;
    ==
      Monad.Bind(Monad.Deconstruct, (b: bool) => Monad.Return(if b then 2*a + 1 else 2*a))(s').1;
    ==
      Monad.Return(if b then 2*a + 1 else 2*a)(s'').1;
    ==
      s'';
    ==
      Monad.Tail(s');
    ==
      Monad.Tail(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1);
    }
  }

  lemma ProbUnifCorrectnessIff(n: nat, s: RandomNumberGenerator.RNG, m: nat)
    requires n > 0
    ensures
      var a := UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0;
      var b := Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0;
      UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m
      <==>
      (b && 2*a + 1 == m) || (!b && 2*a == m)
  {
    var (a, s') := UniformPowerOfTwoModel.ProbUnif(n / 2)(s);
    var (b, s'') := Monad.Deconstruct(s');
    calc {
      UniformPowerOfTwoModel.ProbUnif(n)(s).0;
    ==
      Monad.Bind(UniformPowerOfTwoModel.ProbUnif(n / 2), UniformPowerOfTwoModel.UnifStep)(s).0;
    ==
      UniformPowerOfTwoModel.UnifStep(a)(s').0;
    ==
      Monad.Bind(Monad.Deconstruct, b => Monad.Return(if b then 2*a + 1 else 2*a))(s').0;
    ==
      Monad.Return(if b then 2*a + 1 else 2*a)(s'').0;
    ==
      if b then 2*a + 1 else 2*a;
    }
  }

  lemma ProbUnifCorrectnessEvenCaseIff(n: nat, s: RandomNumberGenerator.RNG, m: nat)
    requires m % 2 == 0
    requires n > 0
    ensures
      var a := UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0;
      var b := Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0;
      UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m <==> (!b && 2*a == m)
  {
    var a: nat := UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0;
    var b := Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0;
    if UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m {
      if (b && 2*a + 1 == m) {
        assert m % 2 == 1 by {
          Helper.DivModAddMultiple(2, 1, a);
        }
        assert m % 2 == 0;
        assert false;
      }
      assert !(b && 2*a + 1 == m) ==> (!b && 2*a == m) by {
        ProbUnifCorrectnessIff(n, s, m);
        assert (b && 2*a + 1 == m) || (!b && 2*a == m);
      }
    }
    if (!b && 2*a == m) {
      assert (b && 2*a + 1 == m) || (!b && 2*a == m);
      assert UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m by { ProbUnifCorrectnessIff(n, s, m); }
    }
  }

  lemma ProbUnifOddCaseIff(n: nat, s: RandomNumberGenerator.RNG, m: nat)
    requires m % 2 == 1
    requires n > 0
    ensures
      var a := UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0;
      var b := Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0;
      UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m <==> (b && 2*a + 1 == m)
  {
    var a := UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0;
    var b := Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0;
    if UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m {
      if (!b && 2*a == m) {
        assert m % 2 == 0 by { assert m / 2 == a; }
        assert m % 2 == 1;
      }
      assert !(!b && 2*a == m) ==> (b && 2*a + 1 == m) by {
        ProbUnifCorrectnessIff(n, s, m);
        assert (b && 2*a + 1 == m) || (!b && 2*a == m);
      }
    }
    if (b && 2*a + 1 == m) {
      assert (b && 2*a + 1 == m) || (!b && 2*a == m);
      assert UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m by { ProbUnifCorrectnessIff(n, s, m); }
    }
  }

  lemma ProbUnifEvenCaseSetEquality(n: nat, m: nat)
    requires m % 2 == 0
    requires n > 0
    ensures
      var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0;
      var a_of := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0;
      (iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m) == (iset s | !b_of(s) && 2*a_of(s) == m)
  {
    var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0;
    var a_of := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0;
    forall s ensures UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m <==> (!b_of(s) && 2*a_of(s) == m) {
      ProbUnifCorrectnessEvenCaseIff(n, s, m);
    }
  }

  lemma ProbUnifOddCaseSetEquality(n: nat, m: nat)
    requires m % 2 == 1
    requires n > 0
    ensures
      var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0;
      var a_of := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0;
      (iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m) == (iset s | b_of(s) && 2*a_of(s) + 1 == m)
  {
    var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0;
    var a_of := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0;
    forall s ensures UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m <==> (b_of(s) && 2*a_of(s) + 1 == m) {
      ProbUnifOddCaseIff(n, s, m);
    }
  }

  lemma ProbUnifEvenCase(n: nat, m: nat)
    requires m % 2 == 0
    requires n > 0
    ensures RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m) == RandomNumberGenerator.mu(iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == m) / 2.0
  {
    var a_of := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0;
    var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0;
    var A: iset<nat> := (iset x | 2*x == m);
    var E: iset<RandomNumberGenerator.RNG> := (iset s | Monad.Deconstruct(s).0 == false);
    var f := ProbUnif1(n / 2);

    var e1 := (iset s | ProbUnif1(n / 2)(s) in E);
    var e2 := (iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 in A);

    assert Eq1: (iset s | !b_of(s)) == e1 by {
      forall s ensures !b_of(s) <==> UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1 in E {
      }
    }

    assert Eq2: (iset s | 2*a_of(s) == m) == e2 by {
      forall s ensures 2*a_of(s) == m <==> UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 in A {
      }
    }

    assert Eq3: (iset s | 2*a_of(s) == m) == (iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == m) by {
      forall s ensures 2*a_of(s) == m <==> 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == m {
      }
    }

    assert Eq4: e1 == MeasureTheory.PreImage(ProbUnif1(n / 2), E) by {
      forall s ensures UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1 in E <==> f(s) in E {
      }
    }

    assert EMeasure: E in RandomNumberGenerator.event_space && RandomNumberGenerator.mu(E) == 0.5 by {
      assert E == (iset s | Monad.Head(s) == false);
      Monad.HeadIsMeasurable(false);
    }

    assert Indep: RandomNumberGenerator.mu(e1 * e2) == RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2) by {
      assert e1 == (iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1 in E) by {
        forall s ensures s in e1 <==> UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1 in E {
        }
      }
      assert MeasureTheory.AreIndepEvents(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, e1, e2) by {
        assert Independence.IsIndepFunction(UniformPowerOfTwoModel.ProbUnif(n / 2)) by {
          assert Independence.IsIndepFn(UniformPowerOfTwoModel.ProbUnif(n / 2)) by {
            ProbUnifIsIndepFn(n / 2);
          }
        }
        assert E in RandomNumberGenerator.event_space by { reveal EMeasure; }
        assert Independence.IsIndepFunctionCondition(UniformPowerOfTwoModel.ProbUnif(n / 2), A, E);
      }
      Independence.AreIndepEventsConjunctElimination(e1, e2);
    }

    assert Prob: 0.5 == RandomNumberGenerator.mu(e1) by {
      calc {
        0.5;
      == { reveal EMeasure; }
        RandomNumberGenerator.mu(E);
      == { reveal EMeasure; ProbUnifIsMeasurePreserving(n / 2); }
        RandomNumberGenerator.mu(MeasureTheory.PreImage(ProbUnif1(n / 2), E));
      == { reveal Eq4; }
        RandomNumberGenerator.mu(e1);
      }
    }

    assert Inter: (iset s | !b_of(s) && 2*a_of(s) == m) == (iset s | !b_of(s)) * (iset s | 2*a_of(s) == m) by {
      forall s ensures !b_of(s) && 2*a_of(s) == m <==> !b_of(s) && 2*a_of(s) == m {
      }
    }

    assert MulSub: RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2) == 0.5 * RandomNumberGenerator.mu(e2) by {
      reveal EMeasure;
      assert RandomNumberGenerator.mu(e1) == 0.5 by { reveal Prob; }
      assert RandomNumberGenerator.mu(e1) == 0.5 ==> RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2) == 0.5 * RandomNumberGenerator.mu(e2);
    }

    calc {
      RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
    == { ProbUnifEvenCaseSetEquality(n, m); }
      RandomNumberGenerator.mu(iset s | !b_of(s) && 2*a_of(s) == m);
    == {  reveal Inter; }
      RandomNumberGenerator.mu((iset s | !b_of(s)) * (iset s | 2*a_of(s) == m));
    == { reveal Eq1; reveal Eq2; }
      RandomNumberGenerator.mu(e1 * e2);
    == { reveal Indep; }
      RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2);
    == { reveal MulSub; }
      0.5 * RandomNumberGenerator.mu(e2);
    == { Helper.DivisionByTwo(RandomNumberGenerator.mu(e2)); }
      RandomNumberGenerator.mu(e2) / 2.0;
    == { reveal Eq2; }
      RandomNumberGenerator.mu(iset s | 2*a_of(s) == m) / 2.0;
    == { reveal Eq3; }
      RandomNumberGenerator.mu(iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == m) / 2.0;
    }
  }

  lemma ProbUnifOddCase(n: nat, m: nat)
    requires m % 2 == 1
    requires n > 0
    ensures RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m) == RandomNumberGenerator.mu(iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 + 1 == m) / 2.0
  {
    var a_of := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0;
    var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1).0;
    var A: iset<nat> := (iset x | 2*x + 1 == m);
    var E: iset<RandomNumberGenerator.RNG> := (iset s | Monad.Deconstruct(s).0 == true);
    var f := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1;

    var e1 := (iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1 in E);
    var e2 := (iset s | UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 in A);

    assert Eq1: (iset s | b_of(s)) == e1 by {
      forall s ensures b_of(s) <==> UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1 in E {
      }
    }

    assert Eq2: (iset s | 2*a_of(s) + 1 == m) == e2 by {
      forall s ensures 2*a_of(s) + 1 == m <==> UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 in A {
      }
    }

    assert Eq3: (iset s | 2*a_of(s) + 1 == m) == (iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 + 1 == m) by {
      forall s ensures 2*a_of(s) + 1 == m <==> 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 + 1 == m {
      }
    }

    assert Eq4: e1 == MeasureTheory.PreImage(f, E) by {
      forall s ensures UniformPowerOfTwoModel.ProbUnif(n / 2)(s).1 in E <==> f(s) in E {
      }
    }

    assert E in RandomNumberGenerator.event_space && RandomNumberGenerator.mu(E) == 0.5 by {
      assert E == (iset s | Monad.Head(s) == true);
      Monad.HeadIsMeasurable(true);
    }

    assert Indep: RandomNumberGenerator.mu(e1 * e2) == RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2) by {
      assert MeasureTheory.AreIndepEvents(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, e1, e2) by {
        assert Independence.IsIndepFunction(UniformPowerOfTwoModel.ProbUnif(n / 2)) by {
          assert Independence.IsIndepFn(UniformPowerOfTwoModel.ProbUnif(n / 2)) by {
            ProbUnifIsIndepFn(n / 2);
          }
        }
        assert E in RandomNumberGenerator.event_space;
        assert Independence.IsIndepFunctionCondition(UniformPowerOfTwoModel.ProbUnif(n / 2), A, E);
      }
      Independence.AreIndepEventsConjunctElimination(e1, e2);
    }

    assert Prob: 0.5 == RandomNumberGenerator.mu(e1) by {
      calc {
        0.5;
      ==
        RandomNumberGenerator.mu(E);
      == { ProbUnifIsMeasurePreserving(n / 2); }
        RandomNumberGenerator.mu(MeasureTheory.PreImage(f, E));
      == { reveal Eq4; }
        RandomNumberGenerator.mu(e1);
      }
    }

    assert Prob2: RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2) == 0.5 * RandomNumberGenerator.mu(e2) by {
      reveal Prob;
    }

    calc {
      RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m);
    == { ProbUnifOddCaseSetEquality(n, m); }
      RandomNumberGenerator.mu(iset s | b_of(s) && 2*a_of(s) + 1 == m);
    == { assert (iset s | b_of(s) && 2*a_of(s) + 1 == m) == (iset s | b_of(s)) * (iset s | 2*a_of(s) + 1 == m); }
      RandomNumberGenerator.mu((iset s | b_of(s)) * (iset s | 2*a_of(s) + 1 == m));
    == { reveal Eq1; reveal Eq2; }
      RandomNumberGenerator.mu(e1 * e2);
    == { reveal Indep; }
      RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2);
    == { reveal Prob2; }
      0.5 * RandomNumberGenerator.mu(e2);
    ==
      RandomNumberGenerator.mu(e2) / 2.0;
    == { reveal Eq2; }
      RandomNumberGenerator.mu(iset s | 2*a_of(s) + 1 == m) / 2.0;
    == { reveal Eq3; }
      RandomNumberGenerator.mu(iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 + 1 == m) / 2.0;
    }
  }

  lemma ProbUnifCaseSplit(n: nat, m: nat)
    requires n > 0
    ensures RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n)(s).0 == m) == if m % 2 == 0 then RandomNumberGenerator.mu(iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 == m) / 2.0 else RandomNumberGenerator.mu(iset s | 2*UniformPowerOfTwoModel.ProbUnif(n / 2)(s).0 + 1 == m) / 2.0
  {
    if m % 2 == 0 {
      ProbUnifEvenCase(n, m);
    } else {
      ProbUnifOddCase(n, m);
    }
  }

}
