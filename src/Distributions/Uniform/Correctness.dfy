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
include "../UniformPowerOfTwo/Correctness.dfy"
include "Model.dfy"

module UniformCorrectness {
  import opened Helper
  import opened Monad
  import opened Independence
  import opened RandomNumberGenerator
  import opened Quantifier
  import opened WhileAndUntil
  import opened MeasureTheory
  import opened UniformPowerOfTwoModel
  import opened UniformPowerOfTwoCorrectness
  import opened UniformModel

  /************
   Definitions
  ************/


  method ProbUniformImper(n: nat, s: RNG) returns (t: (nat, RNG))
    requires n > 0
    ensures t == ProbUniform(n)(s)
    decreases *
  {
    var (u, s) := ProbUnif(n-1)(s);
    while true
      decreases *
    {
      if u < n {
        return (u, s);
      } else {
        var (u, s) := ProbUnif(n-1)(s);
      }
    }
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
            UnifCorrectness(n - 1, k);
            assert UnifIsCorrect(n - 1, k, i);
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

}
