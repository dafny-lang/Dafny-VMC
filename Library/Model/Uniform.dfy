/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "Helper.dfy"
include "Monad.dfy"
include "Independence.dfy"
include "RandomNumberGenerator.dfy"
include "Quantifier.dfy"
include "WhileAndUntil.dfy"
include "MeasureTheory.dfy"

module Uniform {
  import opened Helper
  import opened Monad
  import opened Independence
  import opened RandomNumberGenerator
  import opened Quantifier
  import opened WhileAndUntil
  import opened MeasureTheory

  /************
   Definitions  
  ************/

  // Definition 48
  function ProbUnif(n: nat): (h: Hurd<nat>) {
    if n == 0 then
      Return(0)
    else
      var f := (m: nat) =>
                 var g := (b: bool) =>
                            Return(if b then 2*m + 1 else 2*m);
                 Bind(Deconstruct, g);
      Bind(ProbUnif(n / 2), f)
  }

/*   method ProbUnifImperative(n: nat, s: RNG): (t: (nat, RNG)) 
    ensures t == ProbUnif(n)(s)
  {
    var m := 0;
    var u := 0;
    while true {
      m := if Head(s) then 2*m + 1 else 2*m;
      s := Tail(s);
      u := 2 * u;
    }
  } */

/*   Bind(ProbUnif(n / 2), f)(s)
  ==
    var (m, s') := ProbUnif(n / 2)(s);
    f(m)(s')
  ==
    Bind(Deconstruct, (b: bool) => Return(if b then 2*m + 1 else 2*m))(s')
  ==
    (b, s'') := Deconstruct(s');
    Return(if b then 2 * m + 1 else 2 * m)(s'')
  ==
    (if b then 2*m + 1 else 2 *m, s'')
  ==
    (if Head(s') then 2*m + 1 else 2*m, Tail(s'))
  == */

  method ProbUnifImper(n: nat, s: RNG) returns (t: (nat, RNG)) 
    decreases *
    ensures t == ProbUnif(n)(s)
  {
    var m := 0;

    if n == 0 {
      t := (m, s);
      return;
    } else {
      var (b, s) := Deconstruct(s);
      m := if b then 2*m + 1 else 2*m;
      var n := n / 2;
    }

    while true
      decreases *
      invariant m >= 0 && (n == 0 ==> t == ProbUnif(n)(s))
    {
      if n == 0 {
        t := (m, s);
        return;
      } else {
        var (b, s) := Deconstruct(s);
        m := if b then 2*m + 1 else 2*m;
        var n := n / 2;
      }
    }
  }


  // Definition 49
  function ProbUniform(n: nat): (f: Hurd<nat>)
    requires n > 0
  {
    ProbUnifTerminates(n);
    ProbUntil(ProbUnif(n-1), (x: nat) => x < n)
  }

/*   method ProbUniformImperative(n: nat, s: RNG) returns (t: (nat, RNG))
    requires n > 0
    ensures t == ProbUniform(n)(s)
    decreases *
  {
    ProbUnifTerminates(n);
    t := ProbUntilImperative(ProbUnif(n-1), (x: nat) => x < n, s);
  }
 */


  method ProbUniformImper(n: nat, s: RNG) returns (t: (nat, RNG))
    requires n > 0
    ensures t == ProbUniform(n)(s)
    decreases *   
  {    
    while true 
      decreases *  
    {
      var x := ProbUnifImper(n-1, s);

      if x.0 < n {
        return (x.0, x.1);
      } 
    }
  } 

/* 


  method ProbUniformImperativeAlternative(n: nat, s: RNG) returns (t: (nat, RNG))
    requires n > 0
    ensures t == ProbUniform(n)(s)
    decreases *
  {
    ProbUnifTerminates(n);


    while true
      decreases *
    {
      if n == 1 {
        var (m, s) := (0, s);
      } else {
        var (m', s') := ProbUnif((n - 1) / 2)(s);
        var (m, s) := (if Head(s') then 2*m' + 1 else 2*m', Tail(s'));
      }
      if m < n {
        return (m, s);
      }
    }
  } */

  function ProbUniformInterval(a: int, b: int): (f: Hurd<int>)
    requires a < b
    ensures forall s :: f(s).0 == a + ProbUniform(b - a)(s).0
  {
    (s: RNG) =>
      var (x, s') := ProbUniform(b - a)(s);
      (a + x, s')
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

  ghost function UniformFullCorrectnessHelper(n: nat, i: nat): iset<RNG>
    requires 0 <= i < n
  {
    iset s | ProbUniform(n)(s).0 == i
  }

  // Equation (4.12) / PROB_BERN_UNIFORM
  lemma {:vcs_split_on_every_assert} UniformFullCorrectness(n: nat, i: nat)
    requires 0 <= i < n
    ensures
      var e := UniformFullCorrectnessHelper(n, i);
      && e in event_space
      && mu(e) == 1.0 / (n as real)
  {
    var e := UniformFullCorrectnessHelper(n, i);
    var p := (s: RNG) => ProbUnif(n-1)(s).0 < n;
    var q := (s: RNG) => ProbUnif(n-1)(s).0 == i;
    var e2 := iset s {:trigger q(s)} | ProbUnif(n-1)(s).0 == i;
    var b := ProbUnif(n-1);
    var c := (x: nat) => x < n;
    var d := (x: nat) => x == i;

    assert IsIndepFn(b) && ExistsStar(Helper2(b, c)) by {
      ProbUnifTerminates(n);
    }

    assert ProbUntilTerminates(b, c) by {
      ProbUntilProbabilityFraction(b, c, d);
    }

    var x := ConstructEvents(b, c, d);
    assert E0: x.0 == e;

    assert mu(e) == mu(e2) by {
      ProbUntilProbabilityFraction(b, c, d);
      assert E1: mu(x.0) == mu(x.1) / mu(x.2);
      assert E2: x.1 == e2 by {
        assert x.1 == (iset s | p(s) && q(s));
        assert (iset s | p(s) && q(s)) == e2;
      }
      assert E3: mu(x.2) == 1.0 by {
        assert x.2 == iset s | p(s);
        assert mu(iset s | p(s)) == 1.0 by {
          ProbUnifForAllStar(n);
        }
      }
      assert mu(e) == mu(x.0) by {
        assert e == x.0 by {
          reveal E0;
        }
      }
      assert mu(x.0) == mu(x.1) / mu(x.2) by {
        reveal E1;
      }
      assert mu(x.1) / mu(x.2) == mu(x.1) by {
        calc {
          mu(x.1) / mu(x.2);
        == { reveal E3; DivisionSubstitute(mu(x.1), mu(x.2), 1.0); DivisionByOne(mu(x.1)); }
          mu(x.1);
        }
      }
      assert mu(x.1) == mu(e2) by {
        assert x.1 == e2 by {
          reveal E2;
        }
      }
    }

    assert mu(e2) == 1.0 / (n as real) by {
      assert n >= 1;
      if n == 1 {
        assert mu(e2) == 1.0 / (n as real) by {
          assert i == 0;
          assert e2 == (iset s {:trigger true} | true) by {
            forall s ensures q(s) {
              assert ProbUnif(n-1)(s).0 == 0;
            }
          }
          RNGHasMeasure();
          assert 1.0 / (n as real) == 1.0 by {
            calc {
              1.0 / (n as real);
            == { assert n == 1; assert (n as real) == 1.0; DivisionByOne(1.0); }
              1.0;
            }
          }
        }
      } else {
        assert mu(e2) == 1.0 / (n as real) by {
          var k := Log(2, n);
          assert k > 0 by {
            assert n > 1;
          }
          assert Power(2, k) > 0 by {
            assert k > 0;
          }
          assert mu(e2) == 1.0 / (Power(2, k) as real) by {
            assert Power(2, k - 1) <= n - 1 < Power(2, k) by {
              calc {
                Power(2, k - 1);
              == { assert k == Log(2, n); }
                Power(2, Log(2, n) - 1);
              == { LemmaAboutPower(2, Log(2, n)); }
                Power(2, Log(2, n)) / 2;
              == { LemmaLogPower(2, n); assert Power(2, Log(2, n)) == n; DivisionSubstituteAlternative(2, Power(2, Log(2, n)), n); }
                n / 2;
              <= { LemmaDivisionByTwo(n); }
                n - 1;
              }
              calc {
                n - 1;
              <
                n;
              == { LemmaLogPower(2, n); }
                Power(2, Log(2, n));
              == { assert Log(2, n) == k; }
                Power(2, k);
              }
            }
            UniformPowerOfTwoCorrectness(n - 1, k);
            assert UniformPowerOfTwoCorrectnessHelper(n - 1, k, i);
          }
          assert 1.0 / (n as real) == 1.0 / (Power(2, k) as real) by {
            assert n == Power(2, k) by {
              assert k == Log(2, n);
              LemmaLogPower(2, n);
            }
          }
        }
      }
    }

    assert mu(e) == mu(e2);
    assert mu(e2) == 1.0 / (n as real);
    assert mu(e) == 1.0 / (n as real);

    assert e in event_space by {
      assert e == x.0 by {
        reveal E0;
      }
      assert e in event_space <==> x.0 in event_space;
      assert x.0 in event_space by {
        ProbUntilProbabilityFraction(b, c, d);
      }
    }
  }

  lemma {:vcs_split_on_every_assert} UniformFullIntervalCorrectness(a: int, b: int, i: int)
    requires a <= i < b
    ensures
      var e := iset s | ProbUniformInterval(a, b)(s).0 == i;
      && e in event_space
      && mu(e) == (1.0 / ((b-a) as real))
  {
    assert 0 <= i - a < b - a by {
      assert a <= i < b;
    }
    var e' := UniformFullCorrectnessHelper(b - a, i - a);
    assert e' in event_space by { UniformFullCorrectness(b - a, i - a); }
    assert mu(e') == (1.0 / ((b-a) as real)) by { UniformFullCorrectness(b - a, i - a); }
    var e := iset s | ProbUniformInterval(a, b)(s).0 == i;
    assert e == e' by {
      forall s ensures ProbUniformInterval(a, b)(s).0 == i <==> ProbUniform(b-a)(s).0 == i - a {
        assert ProbUniformInterval(a, b)(s).0 == a + ProbUniform(b - a)(s).0;
      }
    }
  }

  ghost predicate UniformPowerOfTwoCorrectnessHelper(n: nat, k: nat, m: nat)
    requires (n == 0 && k == 0) || (k != 0 && Power(2, k - 1) <= n < Power(2, k))
  {
    mu(iset s | ProbUnif(n)(s).0 == m) == if m < Power(2, k) then 1.0 / (Power(2, k) as real) else 0.0
  }

  // Equation (4.8)
  lemma {:vcs_split_on_every_assert} UniformPowerOfTwoCorrectness(n: nat, k: nat)
    requires (n == 0 && k == 0) || (k != 0 && Power(2, k - 1) <= n < Power(2, k))
    ensures forall m: nat :: UniformPowerOfTwoCorrectnessHelper(n, k, m)
  {
    forall m: nat ensures UniformPowerOfTwoCorrectnessHelper(n, k, m) {
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
            == { ProbUnifCorrectnessCaseSplit(n, m); }
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
            == { ProbUnifCorrectnessCaseSplit(n, m); }
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
            == { ProbUnifCorrectnessCaseSplit(n, m); }
              mu(iset s | 2 * ProbUnif(n / 2)(s).0 == m) / 2.0;
            == { assert (iset s | 2 * ProbUnif(n / 2)(s).0 == m) == (iset s | ProbUnif(n / 2)(s).0 == u); }
              mu(iset s | ProbUnif(n / 2)(s).0 == u) / 2.0;
            }
            if m < Power(2, k) {
              assert mu(iset s | ProbUnif(n / 2)(s).0 == u) == 1.0 / (Power(2, k - 1) as real) by {
                assert u < Power(2, k - 1);
                UniformPowerOfTwoCorrectness(n / 2, k - 1);
                assert UniformPowerOfTwoCorrectnessHelper(n / 2, k - 1, u);
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
              UniformPowerOfTwoCorrectness(n / 2, k - 1);
              assert UniformPowerOfTwoCorrectnessHelper(n / 2, k - 1, u);
              assert mu(iset s | ProbUnif(n)(s).0 == m) == 0.0;
            }
          } else {
            assert m == 2 * u + 1;
            calc {
              mu(iset s | ProbUnif(n)(s).0 == m);
            == { ProbUnifCorrectnessCaseSplit(n, m); }
              mu(iset s | 2 * ProbUnif(n / 2)(s).0 + 1 == m) / 2.0;
            == { assert (iset s | 2 * ProbUnif(n / 2)(s).0 + 1 == m) == (iset s | ProbUnif(n / 2)(s).0 == u); }
              mu(iset s | ProbUnif(n / 2)(s).0 == u) / 2.0;
            }
            if m < Power(2, k) {
              assert mu(iset s | ProbUnif(n / 2)(s).0 == u) == 1.0 / (Power(2, k - 1) as real) by {
                assert u < Power(2, k - 1);
                UniformPowerOfTwoCorrectness(n / 2, k - 1);
                assert UniformPowerOfTwoCorrectnessHelper(n / 2, k - 1, u);
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
              UniformPowerOfTwoCorrectness(n / 2, k - 1);
              assert UniformPowerOfTwoCorrectnessHelper(n / 2, k - 1, u);
              assert mu(iset s | ProbUnif(n)(s).0 == m) == 0.0;
            }
          }
        }
      }
    }
  }
  
  lemma {:axiom} ProbUnifTerminates(n: nat)
    requires n > 0
    ensures
      var b := ProbUnif(n - 1);
      var c := (x: nat) => x < n;
      && IsIndepFn(b)
      && ExistsStar(Helper2(b, c))
      && ProbUntilTerminates(b, c)

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
          == 
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

  lemma {:vcs_split_on_every_assert} ProbUnifCorrectnessOddCaseIff(n: nat, s: RNG, m: nat)
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

  lemma ProbUnifCorrectnessEvenCaseSetEquality(n: nat, m: nat)
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

  lemma ProbUnifCorrectnessOddCaseSetEquality(n: nat, m: nat)
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
      ProbUnifCorrectnessOddCaseIff(n, s, m);
    }
  }

  lemma {:vcs_split_on_every_assert} ProbUnifCorrectnessEvenCase(n: nat, m: nat)
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
    == { ProbUnifCorrectnessEvenCaseSetEquality(n, m); }
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

  lemma {:vcs_split_on_every_assert} ProbUnifCorrectnessOddCase(n: nat, m: nat)
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
    == { ProbUnifCorrectnessOddCaseSetEquality(n, m); }
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

  lemma ProbUnifCorrectnessCaseSplit(n: nat, m: nat)
    requires n > 0
    ensures mu(iset s | ProbUnif(n)(s).0 == m) == if m % 2 == 0 then mu(iset s | 2*ProbUnif(n / 2)(s).0 == m) / 2.0 else mu(iset s | 2*ProbUnif(n / 2)(s).0 + 1 == m) / 2.0
  {
    if m % 2 == 0 {
      ProbUnifCorrectnessEvenCase(n, m);
    } else {
      ProbUnifCorrectnessOddCase(n, m);
    }
  }


}