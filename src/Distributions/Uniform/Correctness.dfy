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
  import Helper
  import Monad
  import Independence
  import RandomNumberGenerator
  import Quantifier
  import WhileAndUntil
  import MeasureTheory
  import UniformPowerOfTwoModel
  import UniformPowerOfTwoCorrectness
  import UniformModel

  /************
   Definitions
  ************/

  ghost function UniformFullCorrectnessHelper(n: nat, i: nat): iset<RandomNumberGenerator.RNG>
    requires 0 <= i < n
  {
    iset s | UniformModel.ProbUniform(n)(s).0 == i
  }

  /*******
   Lemmas
  *******/

  // Correctness theorem for UniformModel.ProbUniform
  // Equation (4.12) / PROB_BERN_UNIFORM
  lemma UniformFullCorrectness(n: nat, i: nat)
    requires 0 <= i < n
    ensures
      var e := UniformFullCorrectnessHelper(n, i);
      && e in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(e) == 1.0 / (n as real)
  {
    var e := UniformFullCorrectnessHelper(n, i);
    var p := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 < n;
    var q := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 == i;
    var e1 := iset s {:trigger UniformPowerOfTwoModel.ProbUnif(n-1)(s).0} | UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 == i;
    var e2 := iset s {:trigger UniformPowerOfTwoModel.ProbUnif(n-1)(s).0} | UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 < n;
    var b := UniformPowerOfTwoModel.ProbUnif(n-1);
    var c := (x: nat) => x < n;
    var d := (x: nat) => x == i;

    assert Independence.IsIndepFn(b) && Quantifier.ExistsStar(WhileAndUntil.Helper2(b, c)) by {
      UniformPowerOfTwoModel.ProbUnifTerminates(n);
    }

    assert WhileAndUntil.ProbUntilTerminates(b, c) by {
      WhileAndUntil.ProbUntilProbabilityFraction(b, c, d);
    }

    var x := WhileAndUntil.ConstructEvents(b, c, d);
    WhileAndUntil.ProbUntilProbabilityFraction(b, c, d);
    assert RandomNumberGenerator.mu(x.0) == RandomNumberGenerator.mu(x.1) / RandomNumberGenerator.mu(x.2);

    assert x.0 == e;
    assert x.1 == e1 by {
      assert forall s :: d(b(s).0) && c(b(s).0) <==> (UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 == i);
    }
    assert x.2 == e2 by {
      assert forall s :: c(b(s).0) <==> UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 < n;
    }

    assert RandomNumberGenerator.mu(e) == 1.0 / (n as real) by {
      assert n >= 1;
      if n == 1 {
        assert RandomNumberGenerator.mu(e1) == 1.0 by {
          assert e1 == iset s | true;
          RandomNumberGenerator.RNGHasMeasure();
        }

        assert RandomNumberGenerator.mu(e2) == (n as real) by {
          Helper.Log2LowerSuc(n-1);
          UniformPowerOfTwoCorrectness.UnifCorrectness2Inequality(n-1, n);
          assert Helper.Power(2, Helper.Log2(n-1)) == 1;
        }

        calc {
          RandomNumberGenerator.mu(e);
          RandomNumberGenerator.mu(e1) / RandomNumberGenerator.mu(e2);
          1.0 / (n as real);
        }
      } else {
        assert RandomNumberGenerator.mu(e1) == 1.0 / (Helper.Power(2, Helper.Log2(n-1)) as real) by {
          calc {
            i;
          < { assert i < n; }
            n;
          <= { Helper.Log2LowerSuc(n-1); }
            Helper.Power(2, Helper.Log2(n-1));
          }
          assert RandomNumberGenerator.mu(e1) == if i < Helper.Power(2, Helper.Log2(n-1)) then 1.0 / (Helper.Power(2, Helper.Log2(n-1)) as real) else 0.0 by {
            UniformPowerOfTwoCorrectness.UnifCorrectness2(n-1, i);
          }
        }
        assert RandomNumberGenerator.mu(e2) == (n as real) / (Helper.Power(2, Helper.Log2(n-1)) as real) by {
          assert n <= Helper.Power(2, Helper.Log2(n-1)) by {
            Helper.Log2LowerSuc(n-1);
          }
          UniformPowerOfTwoCorrectness.UnifCorrectness2Inequality(n-1, n);
        }
        calc {
          RandomNumberGenerator.mu(e);
          { assert e == x.0; assert e1 == x.1; assert e2 == x.2; assert RandomNumberGenerator.mu(x.0) == RandomNumberGenerator.mu(x.1) / RandomNumberGenerator.mu(x.2); }
          RandomNumberGenerator.mu(e1) / RandomNumberGenerator.mu(e2);
          { assert RandomNumberGenerator.mu(e1) == 1.0 / (Helper.Power(2, Helper.Log2(n-1)) as real); assert RandomNumberGenerator.mu(e2) == (n as real) / (Helper.Power(2, Helper.Log2(n-1)) as real); }
          (1.0 / (Helper.Power(2, Helper.Log2(n-1)) as real)) / ((n as real) / (Helper.Power(2, Helper.Log2(n-1)) as real));
          { Helper.SimplifyFractions(1.0, n as real, Helper.Power(2, Helper.Log2(n-1)) as real); }
          1.0 / (n as real);
        }
      }
    }
  }

  // Correctness theorem for UniformModel.ProbUniformInterval
  lemma UniformFullIntervalCorrectness(a: int, b: int, i: int)
    requires a <= i < b
    ensures
      var e := iset s | UniformModel.ProbUniformInterval(a, b)(s).0 == i;
      && e in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(e) == (1.0 / ((b-a) as real))
  {
    assert 0 <= i - a < b - a by {
      assert a <= i < b;
    }
    var e' := UniformFullCorrectnessHelper(b - a, i - a);
    assert e' in RandomNumberGenerator.event_space by { UniformFullCorrectness(b - a, i - a); }
    assert RandomNumberGenerator.mu(e') == (1.0 / ((b-a) as real)) by { UniformFullCorrectness(b - a, i - a); }
    var e := iset s | UniformModel.ProbUniformInterval(a, b)(s).0 == i;
    assert e == e' by {
      forall s ensures UniformModel.ProbUniformInterval(a, b)(s).0 == i <==> UniformModel.ProbUniform(b-a)(s).0 == i - a {
        assert UniformModel.ProbUniformInterval(a, b)(s).0 == a + UniformModel.ProbUniform(b - a)(s).0;
      }
    }
  }

  // Equation (4.10)
  lemma {:axiom} ProbUniformIsIndepFn(n: nat)
    requires n > 0
    ensures Independence.IsIndepFn(UniformModel.ProbUniform(n))
}
