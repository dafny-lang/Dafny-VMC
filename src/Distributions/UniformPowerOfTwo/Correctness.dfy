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
  import opened Helper
  import opened Monad
  import opened Independence
  import opened RandomNumberGenerator
  import opened Quantifier
  import opened WhileAndUntil
  import opened MeasureTheory
  import opened UniformPowerOfTwoModel

  /************
   Definitions
  ************/

  // Definition 50
  function ProbUniformCut(t: nat, n: nat): Hurd<nat>
    requires n > 0
  {
    if t == 0 then
      Return(0)
    else
      var f := (m: nat) =>
                 if n <= m then
                   ProbUniformCut(t-1, n)
                 else
                   Return(m);
      Bind(ProbUnif(n-1), f)
  }

  function ProbUniformAlternative(n: nat, s: RNG): (t: (nat, RNG))
    requires n > 0
  {
    assume {:axiom} false; // Assume termination
    var (u, s) := ProbUnif(n-1)(s);
    if u < n then
      (u, s)
    else
      ProbUniformAlternative(n, s)
  }

  function ProbUnifExistence(n: nat, s: RNG, j: nat): (i: nat)
    ensures ProbUnif(n)(s).1(j) == s(i)
  {
    if n == 0 then
      j
    else
      var i := ProbUnifExistence(n / 2, s, j + 1);
      calc {
        ProbUnif(n)(s).1(j);
      ==
        Tail(ProbUnif(n / 2)(s).1)(j);
      ==
        ProbUnif(n / 2)(s).1(j + 1);
      ==
        s(i);
      }
      i
  }

  function ProbUnifDeconstruct(n: nat, m: nat, s: RNG): (i: nat)
    ensures s(i) == Deconstruct(ProbUnif(n / 2)(s).1).0
  {
    var i := ProbUnifExistence(n / 2, s, 0);
    assert ProbUnif(n / 2)(s).1(0) == s(i);
    assert Deconstruct(ProbUnif(n / 2)(s).1).0 == ProbUnif(n / 2)(s).1(0);
    i
  }

  /*******
   Lemmas
  *******/

  ghost predicate UnifIsCorrect(n: nat, k: nat, m: nat)
    requires (n == 0 && k == 0) || (k != 0 && Power(2, k - 1) <= n < Power(2, k))
  {
    mu(iset s | ProbUnif(n)(s).0 == m) == if m < Power(2, k) then 1.0 / (Power(2, k) as real) else 0.0
  }

  // Equation (4.8)
  lemma {:vcs_split_on_every_assert} UnifCorrectness(n: nat, k: nat)
    requires (n == 0 && k == 0) || (k != 0 && Power(2, k - 1) <= n < Power(2, k))
    ensures forall m: nat :: UnifIsCorrect(n, k, m)
  {
    forall m: nat ensures UnifIsCorrect(n, k, m) {
      if (n == 0 && k == 0) {
        assert Power(2, k) == 1;
        if m == 0 {
          assert (iset s | ProbUnif(n)(s).0 == m) == (iset s {:trigger true} | true);
          RNGHasMeasure();
        } else {
          assert (iset s | ProbUnif(n)(s).0 == m) == iset{};
          RNGHasMeasure();
        }
      } else {
        assert (k != 0 && Power(2, k - 1) <= n < Power(2, k));
        assert n > 0;
        assert n > 1 ==> n / 2 > 0;
        if k - 2 < 0 {
          assert 0 < k < 2;
          assert k == 1;
          assert Power(2, k) == 2;
          assert 0 < n < 2;
          assert n == 1;
          assert n / 2 == 0;
          if m % 2 == 0 {
            calc {
              mu(iset s | ProbUnif(n)(s).0 == m);
            == { ProbUnifCaseSplit(n, m); }
              mu(iset s | 2*ProbUnif(n / 2)(s).0 == m) / 2.0;
            == { assert (iset s | 2*ProbUnif(n / 2)(s).0 == m) == (iset s {:trigger 0 == m} | 0 == m); }
              mu(iset s {:trigger 0 == m} | 0 == m) / 2.0;
            }
            if m < Power(2, k) {
              assert m == 0;
              calc {
                mu(iset s | ProbUnif(n)(s).0 == m);
              ==
                mu(iset s {:trigger 0 == m} | 0 == m) / 2.0;
              == { assert (iset s: RNG {:trigger 0 == m} | 0 == m) == (iset s {:trigger true} | true); }
                mu(iset s {:trigger true} | true) / 2.0;
              == { RNGHasMeasure(); }
                1.0 / 2.0;
              == { assert 2.0 == 2 as real; DivisionSubstitute(1.0, 2.0, 2 as real); }
                1.0 / (2 as real);
              == { assert k == 1; assert Power(2, k) == 2; assert Power(2, k) as real == 2 as real; DivisionSubstitute(1.0, 2 as real, Power(2, k) as real); }
                1.0 / (Power(2, k) as real);
              }
            } else {
              assert m != 0;
              calc {
                mu(iset s | ProbUnif(n)(s).0 == m);
              ==
                mu(iset s {:trigger 0 == m} | 0 == m) / 2.0;
              == { assert (iset s: RNG {:trigger 0 == m} | 0 == m) == iset{}; }
                mu(iset {}) / 2.0;
              == { RNGHasMeasure(); }
                0.0 / 2.0;
              ==
                0.0;
              }
            }
          } else {
            assert m % 2 == 1;
            calc {
              mu(iset s | ProbUnif(n)(s).0 == m);
            == { ProbUnifCaseSplit(n, m); }
              mu(iset s | 2*ProbUnif(n / 2)(s).0 + 1 == m) / 2.0;
            == { assert (iset s | 2*ProbUnif(n / 2)(s).0 + 1 == m) == (iset s {:trigger 1 == m} | 1 == m); }
              mu(iset s {:trigger 1 == m} | 1 == m) / 2.0;
            }
            if m < Power(2, k) {
              assert m == 1;
              calc {
                mu(iset s | ProbUnif(n)(s).0 == m);
              ==
                mu(iset s {:trigger 1 == m} | 1 == m) / 2.0;
              == { assert (iset s: RNG {:trigger 1 == m} | 1 == m) == (iset s {:trigger true} | true); }
                mu(iset s {:trigger true} | true) / 2.0;
              == { RNGHasMeasure(); DivisionSubstituteAlternativeReal(2.0, mu(iset s {:trigger true} | true), 1.0); }
                1.0 / 2.0;
              == { assert k == 1; assert 2.0 == 2 as real == Power(2, k) as real; DivisionSubstitute(1.0, 2.0, Power(2, k) as real); }
                1.0 / (Power(2, k) as real);
              }
            } else {
              assert m != 1;
              calc {
                mu(iset s: RNG | ProbUnif(n)(s).0 == m);
              ==
                mu(iset s: RNG {:trigger 1 == m} | 1 == m) / 2.0;
              == { assert (iset s: RNG {:trigger 1 == m} | 1 == m) == iset{}; }
                mu(iset {}) / 2.0;
              == { RNGHasMeasure(); }
                0.0 / 2.0;
              ==
                0.0;
              }
            }
          }
        } else {
          assert Power(2, k - 1) / 2 <= n / 2 < Power(2, k) / 2;
          assert Power(2, k - 2) <= n / 2 < Power(2, k - 1);

          var u := m / 2;
          if m % 2 == 0 {
            assert m == 2 * u;
            calc {
              mu(iset s | ProbUnif(n)(s).0 == m);
            == { ProbUnifCaseSplit(n, m); }
              mu(iset s | 2 * ProbUnif(n / 2)(s).0 == m) / 2.0;
            == { assert (iset s | 2 * ProbUnif(n / 2)(s).0 == m) == (iset s | ProbUnif(n / 2)(s).0 == u); }
              mu(iset s | ProbUnif(n / 2)(s).0 == u) / 2.0;
            }
            if m < Power(2, k) {
              assert mu(iset s | ProbUnif(n / 2)(s).0 == u) == 1.0 / (Power(2, k - 1) as real) by {
                assert u < Power(2, k - 1);
                UnifCorrectness(n / 2, k - 1);
                assert UnifIsCorrect(n / 2, k - 1, u);
              }
              calc {
                mu(iset s | ProbUnif(n)(s).0 == m);
              ==
                mu(iset s | ProbUnif(n / 2)(s).0 == u) / 2.0;
              ==
                (1.0 / Power(2, k - 1) as real) / 2.0;
              ==
                1.0 / (Power(2, k - 1) as real * 2.0);
              ==
                1.0 / (Power(2, k - 1) * 2) as real;
              ==
                1.0 / (Power(2, k) as real);
              }
            } else {
              assert u >= Power(2, k - 1);
              UnifCorrectness(n / 2, k - 1);
              assert UnifIsCorrect(n / 2, k - 1, u);
              assert mu(iset s | ProbUnif(n)(s).0 == m) == 0.0;
            }
          } else {
            assert m == 2 * u + 1;
            calc {
              mu(iset s | ProbUnif(n)(s).0 == m);
            == { ProbUnifCaseSplit(n, m); }
              mu(iset s | 2 * ProbUnif(n / 2)(s).0 + 1 == m) / 2.0;
            == { assert (iset s | 2 * ProbUnif(n / 2)(s).0 + 1 == m) == (iset s | ProbUnif(n / 2)(s).0 == u); }
              mu(iset s | ProbUnif(n / 2)(s).0 == u) / 2.0;
            }
            if m < Power(2, k) {
              assert mu(iset s | ProbUnif(n / 2)(s).0 == u) == 1.0 / (Power(2, k - 1) as real) by {
                assert u < Power(2, k - 1);
                UnifCorrectness(n / 2, k - 1);
                assert UnifIsCorrect(n / 2, k - 1, u);
              }
              calc {
                mu(iset s | ProbUnif(n)(s).0 == m);
              ==
                mu(iset s | ProbUnif(n / 2)(s).0 == u) / 2.0;
              ==
                (1.0 / Power(2, k - 1) as real) / 2.0;
              ==
                1.0 / (Power(2, k - 1) as real * 2.0);
              ==
                1.0 / (Power(2, k - 1) * 2) as real;
              ==
                1.0 / (Power(2, k) as real);
              }
            } else {
              assert u >= Power(2, k - 1);
              UnifCorrectness(n / 2, k - 1);
              assert UnifIsCorrect(n / 2, k - 1, u);
              assert mu(iset s | ProbUnif(n)(s).0 == m) == 0.0;
            }
          }
        }
      }
    }
  }

  // Equation (4.7)
  lemma {:axiom} ProbUnifIsIndepFn(n: nat)
    ensures IsIndepFn(ProbUnif(n))

  // See PROB_UNIFORM_TERMINATES
  lemma {:axiom} ProbUnifForAllStar(n: nat)
    requires n != 0
    ensures
      var p := (s: RNG) => ProbUnif(n-1)(s).0 < n;
      ForAllStar(p)

  lemma {:vcs_split_on_every_assert} ProbUnifIsMeasurePreserving(n: nat)
    ensures
      var f := (s: RNG) => ProbUnif(n)(s).1;
      IsMeasurePreserving(event_space, mu, event_space, mu, f)
  {
    var f := (s: RNG) => ProbUnif(n)(s).1;
    assert IsMeasurable(event_space, event_space, f) by {
      ProbUnifIsIndepFn(n);
      assert IsIndepFn(ProbUnif(n));
    }
    var g := (s: RNG) => ProbUnif(n / 2)(s).1;
    if n == 0 {
      forall e | e in event_space ensures mu(PreImage(f, e)) == mu(e) {
        calc {
          mu(PreImage(f, e));
        == { assert PreImage(f, e) == (iset s | f(s) in e); }
          mu(iset s | f(s) in e);
        == { assert (iset s | f(s) in e) == (iset s | ProbUnif(n)(s).1 in e); }
          mu(iset s | ProbUnif(n)(s).1 in e);
        == { assert (iset s | ProbUnif(n)(s).1 in e) == (iset s | s in e); }
          mu(iset s | s in e);
        == { assert (iset s | s in e) == e; }
          mu(e);
        }
      }
    } else {
      forall e | e in event_space ensures mu(PreImage(f, e)) == mu(e) {
        var e' := (iset s | Tail(s) in e);
        assert e' in event_space by {
          assert e' == PreImage(Tail, e);
          TailIsMeasurePreserving();
          assert IsMeasurable(event_space, event_space, Tail);
        }
        assert A: forall s :: ProbUnif(n)(s).1 in e <==> Tail(ProbUnif(n / 2)(s).1) in e by {
          forall s ensures ProbUnif(n)(s).1 in e <==> Tail(ProbUnif(n / 2)(s).1) in e {
            ProbUnifTailDecompose(n, s);
          }
        }
        assert B: forall s :: Tail(ProbUnif(n / 2)(s).1) in e <==> ProbUnif(n / 2)(s).1 in e' by {
          forall s ensures Tail(ProbUnif(n / 2)(s).1) in e <==> ProbUnif(n / 2)(s).1 in e' {
            assert Tail(ProbUnif(n / 2)(s).1) in e <==> ProbUnif(n / 2)(s).1 in e';
          }
        }
        assert C: forall s :: f(s) in e <==> ProbUnif(n)(s).1 in e by {
          forall s ensures f(s) in e <==> ProbUnif(n)(s).1 in e {
            assert f(s) == ProbUnif(n)(s).1;
          }
        }
        calc {
          mu(PreImage(f, e));
        == { assert PreImage(f, e) == (iset s | f(s) in e); }
          mu(iset s | f(s) in e);
        == { assert (iset s | f(s) in e) == (iset s | ProbUnif(n)(s).1 in e) by { reveal C; } }
          mu(iset s | ProbUnif(n)(s).1 in e);
        == { assert (iset s | ProbUnif(n)(s).1 in e) == (iset s | Tail(ProbUnif(n / 2)(s).1) in e) by { reveal A; } }
          mu(iset s | Tail(ProbUnif(n / 2)(s).1) in e);
        == { assert (iset s | Tail(ProbUnif(n / 2)(s).1) in e) == (iset s | ProbUnif(n / 2)(s).1 in e') by { reveal B; } }
          mu(iset s | ProbUnif(n / 2)(s).1 in e');
        == { assert (iset s | ProbUnif(n / 2)(s).1 in e') == (iset s | g(s) in e'); }
          mu(iset s | g(s) in e');
        == { assert (iset s | g(s) in e') == PreImage(g, e'); }
          mu(PreImage(g, e'));
        == { ProbUnifIsMeasurePreserving(n / 2); assert IsMeasurePreserving(event_space, mu, event_space, mu, g); assert e' in event_space; }
          mu(e');
        == { assert e' == PreImage(Tail, e); }
          mu(PreImage(Tail, e));
        == { TailIsMeasurePreserving(); }
          mu(e);
        }
      }
    }
  }

  lemma ProbUnifTailDecompose(n: nat, s: RNG)
    requires n != 0
    ensures ProbUnif(n)(s).1 == Tail(ProbUnif(n / 2)(s).1)
  {
    var f := (m: nat) =>
        var g := (b: bool) =>
                   Return(if b then 2*m + 1 else 2*m);
        Bind(Deconstruct, g);
    var (a, s') := ProbUnif(n / 2)(s);
    var (b, s'') := Deconstruct(s');
    calc {
      ProbUnif(n)(s).1;
    ==
      Bind(ProbUnif(n / 2), f)(s).1;
    ==
      f(a)(s').1;
    ==
      Bind(Deconstruct, (b: bool) => Return(if b then 2*a + 1 else 2*a))(s').1;
    ==
      Return(if b then 2*a + 1 else 2*a)(s'').1;
    ==
      s'';
    ==
      Tail(s');
    ==
      Tail(ProbUnif(n / 2)(s).1);
    }
  }

  lemma ProbUnifCorrectnessIff(n: nat, s: RNG, m: nat)
    requires n > 0
    ensures
      var a := ProbUnif(n / 2)(s).0;
      var b := Deconstruct(ProbUnif(n / 2)(s).1).0;
      ProbUnif(n)(s).0 == m
      <==>
      (b && 2*a + 1 == m) || (!b && 2*a == m)
  {
    var f := (m: nat) =>
        var g := (b: bool) =>
                   Return(if b then 2*m + 1 else 2*m);
        Bind(Deconstruct, g);
    var (a, s') := ProbUnif(n / 2)(s);
    var (b, s'') := Deconstruct(s');
    calc {
      ProbUnif(n)(s).0;
    ==
      Bind(ProbUnif(n / 2), f)(s).0;
    ==
      f(a)(s').0;
    ==
      Bind(Deconstruct, b => Return(if b then 2*a + 1 else 2*a))(s').0;
    ==
      Return(if b then 2*a + 1 else 2*a)(s'').0;
    ==
      if b then 2*a + 1 else 2*a;
    }
  }

  lemma {:vcs_split_on_every_assert} ProbUnifCorrectnessEvenCaseIff(n: nat, s: RNG, m: nat)
    requires m % 2 == 0
    requires n > 0
    ensures
      var a := ProbUnif(n / 2)(s).0;
      var b := Deconstruct(ProbUnif(n / 2)(s).1).0;
      ProbUnif(n)(s).0 == m <==> (!b && 2*a == m)
  {
    var a := ProbUnif(n / 2)(s).0;
    var b := Deconstruct(ProbUnif(n / 2)(s).1).0;
    if ProbUnif(n)(s).0 == m {
      if (b && 2*a + 1 == m) {
        assert A: (2*a + 1) / 2 == 1 by {
          calc {
            (2*a + 1) / 2;
          == { LemmaAboutNatDivision(2*a + 1, 2); }
            ((2*a + 1) as real / 2 as real).Floor;
          == { assert (2*a + 1) as real / 2 as real == 1 as real; }
            (1 as real).Floor;
          ==
            1;
          }
        }
        assert m % 2 == 1 by { assert m == 2*a + 1; reveal A; assert m / 2 == 1 by { DivisionSubstituteAlternative(2, m, 2*a + 1); } }
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
      assert ProbUnif(n)(s).0 == m by { ProbUnifCorrectnessIff(n, s, m); }
    }
  }

  lemma {:vcs_split_on_every_assert} ProbUnifOddCaseIff(n: nat, s: RNG, m: nat)
    requires m % 2 == 1
    requires n > 0
    ensures
      var a := ProbUnif(n / 2)(s).0;
      var b := Deconstruct(ProbUnif(n / 2)(s).1).0;
      ProbUnif(n)(s).0 == m <==> (b && 2*a + 1 == m)
  {
    var a := ProbUnif(n / 2)(s).0;
    var b := Deconstruct(ProbUnif(n / 2)(s).1).0;
    if ProbUnif(n)(s).0 == m {
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
      assert ProbUnif(n)(s).0 == m by { ProbUnifCorrectnessIff(n, s, m); }
    }
  }

  lemma ProbUnifEvenCaseSetEquality(n: nat, m: nat)
    requires m % 2 == 0
    requires n > 0
    ensures
      var b_of := (s: RNG) => Deconstruct(ProbUnif(n / 2)(s).1).0;
      var a_of := (s: RNG) => ProbUnif(n / 2)(s).0;
      (iset s | ProbUnif(n)(s).0 == m) == (iset s | !b_of(s) && 2*a_of(s) == m)
  {
    var b_of := (s: RNG) => Deconstruct(ProbUnif(n / 2)(s).1).0;
    var a_of := (s: RNG) => ProbUnif(n / 2)(s).0;
    forall s ensures ProbUnif(n)(s).0 == m <==> (!b_of(s) && 2*a_of(s) == m) {
      ProbUnifCorrectnessEvenCaseIff(n, s, m);
    }
  }

  lemma ProbUnifOddCaseSetEquality(n: nat, m: nat)
    requires m % 2 == 1
    requires n > 0
    ensures
      var b_of := (s: RNG) => Deconstruct(ProbUnif(n / 2)(s).1).0;
      var a_of := (s: RNG) => ProbUnif(n / 2)(s).0;
      (iset s | ProbUnif(n)(s).0 == m) == (iset s | b_of(s) && 2*a_of(s) + 1 == m)
  {
    var b_of := (s: RNG) => Deconstruct(ProbUnif(n / 2)(s).1).0;
    var a_of := (s: RNG) => ProbUnif(n / 2)(s).0;
    forall s ensures ProbUnif(n)(s).0 == m <==> (b_of(s) && 2*a_of(s) + 1 == m) {
      ProbUnifOddCaseIff(n, s, m);
    }
  }

  lemma {:vcs_split_on_every_assert} ProbUnifEvenCase(n: nat, m: nat)
    requires m % 2 == 0
    requires n > 0
    ensures mu(iset s | ProbUnif(n)(s).0 == m) == mu(iset s | 2*ProbUnif(n / 2)(s).0 == m) / 2.0
  {
    var a_of := (s: RNG) => ProbUnif(n / 2)(s).0;
    var b_of := (s: RNG) => Deconstruct(ProbUnif(n / 2)(s).1).0;
    var A: iset<nat> := (iset x | 2*x == m);
    var E: iset<RNG> := (iset s | Deconstruct(s).0 == false);
    var f := (s: RNG) => ProbUnif(n / 2)(s).1;

    var e1 := (iset s | ProbUnif(n / 2)(s).1 in E);
    var e2 := (iset s | ProbUnif(n / 2)(s).0 in A);

    assert Eq1: (iset s | !b_of(s)) == e1 by {
      forall s ensures !b_of(s) <==> ProbUnif(n / 2)(s).1 in E {
      }
    }

    assert Eq2: (iset s | 2*a_of(s) == m) == e2 by {
      forall s ensures 2*a_of(s) == m <==> ProbUnif(n / 2)(s).0 in A {
      }
    }

    assert Eq3: (iset s | 2*a_of(s) == m) == (iset s | 2*ProbUnif(n / 2)(s).0 == m) by {
      forall s ensures 2*a_of(s) == m <==> 2*ProbUnif(n / 2)(s).0 == m {
      }
    }

    assert Eq4: e1 == PreImage(f, E) by {
      forall s ensures ProbUnif(n / 2)(s).1 in E <==> f(s) in E {
      }
    }

    assert E in event_space && mu(E) == 0.5 by {
      assert E == (iset s | Head(s) == false);
      HeadIsMeasurable(false);
    }

    assert Indep: mu(e1 * e2) == mu(e1) * mu(e2) by {
      assert AreIndepEvents(event_space, mu, e1, e2) by {
        assert IsIndepFunction(ProbUnif(n / 2)) by {
          assert IsIndepFn(ProbUnif(n / 2)) by {
            ProbUnifIsIndepFn(n / 2);
          }
        }
        assert E in event_space;
        assert IsIndepFunctionCondition(ProbUnif(n / 2), A, E);
      }
      AreIndepEventsConjunctElimination(e1, e2);
    }

    assert Prob: 0.5 == mu(e1) by {
      calc {
        0.5;
      ==
        mu(E);
      == { ProbUnifIsMeasurePreserving(n / 2); }
        mu(PreImage(f, E));
      == { reveal Eq4; }
        mu(e1);
      }
    }

    var p := (s: RNG) => s in (iset s | !b_of(s) && 2*a_of(s) == m) <==> s in (iset s | !b_of(s)) && s in (iset s | 2*a_of(s) == m);

    assert Inter: forall s :: p(s) by {
      forall s ensures !b_of(s) && 2*a_of(s) == m <==> !b_of(s) && 2*a_of(s) == m {
      }
    }

    assert MulSub: mu(e1) * mu(e2) == 0.5 * mu(e2) by {
      assert mu(e1) == 0.5 by { reveal Prob; }
      assert mu(e1) == 0.5 ==> mu(e1) * mu(e2) == 0.5 * mu(e2);
    }

    calc {
      mu(iset s | ProbUnif(n)(s).0 == m);
    == { ProbUnifEvenCaseSetEquality(n, m); }
      mu(iset s | !b_of(s) && 2*a_of(s) == m);
    == { assert (iset s | !b_of(s) && 2*a_of(s) == m) == (iset s | !b_of(s)) * (iset s | 2*a_of(s) == m) by { reveal Inter; } }
      mu((iset s | !b_of(s)) * (iset s | 2*a_of(s) == m));
    == { reveal Eq1; reveal Eq2; }
      mu(e1 * e2);
    == { reveal Indep; }
      mu(e1) * mu(e2);
    == { reveal MulSub; }
      0.5 * mu(e2);
    == { DivisionByTwo(mu(e2)); }
      mu(e2) / 2.0;
    == { reveal Eq2; }
      mu(iset s | 2*a_of(s) == m) / 2.0;
    == { reveal Eq3; }
      mu(iset s | 2*ProbUnif(n / 2)(s).0 == m) / 2.0;
    }
  }

  lemma {:vcs_split_on_every_assert} ProbUnifOddCase(n: nat, m: nat)
    requires m % 2 == 1
    requires n > 0
    ensures mu(iset s | ProbUnif(n)(s).0 == m) == mu(iset s | 2*ProbUnif(n / 2)(s).0 + 1 == m) / 2.0
  {
    var a_of := (s: RNG) => ProbUnif(n / 2)(s).0;
    var b_of := (s: RNG) => Deconstruct(ProbUnif(n / 2)(s).1).0;
    var A: iset<nat> := (iset x | 2*x + 1 == m);
    var E: iset<RNG> := (iset s | Deconstruct(s).0 == true);
    var f := (s: RNG) => ProbUnif(n / 2)(s).1;

    var e1 := (iset s | ProbUnif(n / 2)(s).1 in E);
    var e2 := (iset s | ProbUnif(n / 2)(s).0 in A);

    assert Eq1: (iset s | b_of(s)) == e1 by {
      forall s ensures b_of(s) <==> ProbUnif(n / 2)(s).1 in E {
      }
    }

    assert Eq2: (iset s | 2*a_of(s) + 1 == m) == e2 by {
      forall s ensures 2*a_of(s) + 1 == m <==> ProbUnif(n / 2)(s).0 in A {
      }
    }

    assert Eq3: (iset s | 2*a_of(s) + 1 == m) == (iset s | 2*ProbUnif(n / 2)(s).0 + 1 == m) by {
      forall s ensures 2*a_of(s) + 1 == m <==> 2*ProbUnif(n / 2)(s).0 + 1 == m {
      }
    }

    assert Eq4: e1 == PreImage(f, E) by {
      forall s ensures ProbUnif(n / 2)(s).1 in E <==> f(s) in E {
      }
    }

    assert E in event_space && mu(E) == 0.5 by {
      assert E == (iset s | Head(s) == true);
      HeadIsMeasurable(true);
    }

    assert Indep: mu(e1 * e2) == mu(e1) * mu(e2) by {
      assert AreIndepEvents(event_space, mu, e1, e2) by {
        assert IsIndepFunction(ProbUnif(n / 2)) by {
          assert IsIndepFn(ProbUnif(n / 2)) by {
            ProbUnifIsIndepFn(n / 2);
          }
        }
        assert E in event_space;
        assert IsIndepFunctionCondition(ProbUnif(n / 2), A, E);
      }
      AreIndepEventsConjunctElimination(e1, e2);
    }

    assert Prob: 0.5 == mu(e1) by {
      calc {
        0.5;
      ==
        mu(E);
      == { ProbUnifIsMeasurePreserving(n / 2); }
        mu(PreImage(f, E));
      == { reveal Eq4; }
        mu(e1);
      }
    }

    assert Prob2: mu(e1) * mu(e2) == 0.5 * mu(e2) by {
      reveal Prob;
    }

    calc {
      mu(iset s | ProbUnif(n)(s).0 == m);
    == { ProbUnifOddCaseSetEquality(n, m); }
      mu(iset s | b_of(s) && 2*a_of(s) + 1 == m);
    == { assert (iset s | b_of(s) && 2*a_of(s) + 1 == m) == (iset s | b_of(s)) * (iset s | 2*a_of(s) + 1 == m); }
      mu((iset s | b_of(s)) * (iset s | 2*a_of(s) + 1 == m));
    == { reveal Eq1; reveal Eq2; }
      mu(e1 * e2);
    == { reveal Indep; }
      mu(e1) * mu(e2);
    == { reveal Prob2; }
      0.5 * mu(e2);
    ==
      mu(e2) / 2.0;
    == { reveal Eq2; }
      mu(iset s | 2*a_of(s) + 1 == m) / 2.0;
    == { reveal Eq3; }
      mu(iset s | 2*ProbUnif(n / 2)(s).0 + 1 == m) / 2.0;
    }
  }

  lemma ProbUnifCaseSplit(n: nat, m: nat)
    requires n > 0
    ensures mu(iset s | ProbUnif(n)(s).0 == m) == if m % 2 == 0 then mu(iset s | 2*ProbUnif(n / 2)(s).0 == m) / 2.0 else mu(iset s | 2*ProbUnif(n / 2)(s).0 + 1 == m) / 2.0
  {
    if m % 2 == 0 {
      ProbUnifEvenCase(n, m);
    } else {
      ProbUnifOddCase(n, m);
    }
  }


}
