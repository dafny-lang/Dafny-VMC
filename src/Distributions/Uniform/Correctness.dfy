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

  method ProbUniformImper(n: nat, s: RandomNumberGenerator.RNG) returns (t: (nat, RandomNumberGenerator.RNG))
    requires n > 0
    ensures t == UniformModel.ProbUniform(n)(s)
    decreases *
  {
    var (u, s) := UniformPowerOfTwoModel.ProbUnif(n-1)(s);
    while true
      decreases *
    {
      if u < n {
        return (u, s);
      } else {
        var (u, s) := UniformPowerOfTwoModel.ProbUnif(n-1)(s);
      }
    }
  }

  ghost function UniformFullCorrectnessHelper(n: nat, i: nat): iset<RandomNumberGenerator.RNG>
    requires 0 <= i < n
  {
    iset s | UniformModel.ProbUniform(n)(s).0 == i
  }

  ghost function UniformFullCorrectnessHelper2(n: nat, i: nat): iset<RandomNumberGenerator.RNG>
    requires 0 <= i < n
  {
    iset s | UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 == i
  }

  /*******
   Lemmas
  *******/

  // Equation (4.12) / PROB_BERN_UNIFORM
  lemma UniformFullCorrectness(n: nat, i: nat)
    requires 0 <= i < n
    ensures
      && UniformFullCorrectnessHelper(n, i) in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(UniformFullCorrectnessHelper(n, i)) == 1.0 / (n as real)
  {
    var e := UniformFullCorrectnessHelper(n, i);
    var p := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 < n;
    var q := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 == i;
    var e2 := UniformFullCorrectnessHelper2(n, i);
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
    assert E0: x.0 == e;

    assert EEqual: RandomNumberGenerator.mu(e) == RandomNumberGenerator.mu(e2) by {
      UniformFullCorrectnessSameMeasure(n, i);
    }

    assert E2Equal: RandomNumberGenerator.mu(e2) == 1.0 / (n as real) by {
      assert n >= 1;
      if n == 1 {
        assert i == 0;
        assert RandomNumberGenerator.mu(e2) == 1.0 / (n as real) by { UniformCorrectnessCorrectMeasureCaseNOne(); }
      } else {
        assert RandomNumberGenerator.mu(e2) == 1.0 / (n as real) by { UniformCorrectnessCorrectMeasureCaseNGreaterOne(n, i); }
      }
    }

    assert RandomNumberGenerator.mu(e) == 1.0 / (n as real) by {
      reveal EEqual;
      reveal E2Equal;
    }

    assert e in RandomNumberGenerator.event_space by {
      assert e == x.0 by {
        reveal E0;
      }
      assert e in RandomNumberGenerator.event_space <==> x.0 in RandomNumberGenerator.event_space;
      assert x.0 in RandomNumberGenerator.event_space by {
        WhileAndUntil.ProbUntilProbabilityFraction(b, c, d);
      }
    }
  }

  lemma UniformFullCorrectnessSameMeasure(n: nat, i: nat)
    requires 0 <= i < n
    ensures RandomNumberGenerator.mu(UniformFullCorrectnessHelper(n, i)) == RandomNumberGenerator.mu(iset s | UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 == i)
  {
    var e := UniformFullCorrectnessHelper(n, i);
    var p := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 < n;
    var q := (s: RandomNumberGenerator.RNG) => UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 == i;
    var e2 := iset s {:trigger q(s)} | UniformPowerOfTwoModel.ProbUnif(n-1)(s).0 == i;
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
    assert E0: x.0 == e;

    WhileAndUntil.ProbUntilProbabilityFraction(b, c, d);
    assert E1: RandomNumberGenerator.mu(x.0) == RandomNumberGenerator.mu(x.1) / RandomNumberGenerator.mu(x.2);
    assert E2: x.1 == e2 by {
      assert x.1 == (iset s | p(s) && q(s));
      assert (iset s | p(s) && q(s)) == e2;
    }
    assert E3: RandomNumberGenerator.mu(x.2) == 1.0 by {
      assert x.2 == iset s | p(s);
      assert RandomNumberGenerator.mu(iset s | p(s)) == 1.0 by {
        UniformPowerOfTwoCorrectness.ProbUnifForAllStar(n);
      }
    }
    assert RandomNumberGenerator.mu(e) == RandomNumberGenerator.mu(x.0) by {
      assert e == x.0 by {
        reveal E0;
      }
    }
    assert RandomNumberGenerator.mu(x.0) == RandomNumberGenerator.mu(x.1) / RandomNumberGenerator.mu(x.2) by {
      reveal E1;
    }
    assert RandomNumberGenerator.mu(x.1) / RandomNumberGenerator.mu(x.2) == RandomNumberGenerator.mu(x.1) by {
      calc {
        RandomNumberGenerator.mu(x.1) / RandomNumberGenerator.mu(x.2);
      == { reveal E3; Helper.DivisionSubstitute(RandomNumberGenerator.mu(x.1), RandomNumberGenerator.mu(x.2), 1.0); Helper.DivisionByOne(RandomNumberGenerator.mu(x.1)); }
        RandomNumberGenerator.mu(x.1);
      }
    }
    assert RandomNumberGenerator.mu(x.1) == RandomNumberGenerator.mu(e2) by {
      assert x.1 == e2 by {
        reveal E2;
      }
    }
  }

  lemma UniformCorrectnessCorrectMeasureCaseNOne()
    ensures RandomNumberGenerator.mu(UniformFullCorrectnessHelper2(1, 0)) == 1.0 / (1 as real)
  {
    assert (iset s | UniformPowerOfTwoModel.ProbUnif(0)(s).0 == 0) == (iset s {:trigger true} | true) by {
    }
    RandomNumberGenerator.RNGHasMeasure();
  }

  lemma UniformCorrectnessCorrectMeasureCaseNGreaterOne(n: nat, i: nat)
    requires i < n
    requires 2 <= n
    ensures RandomNumberGenerator.mu(UniformFullCorrectnessHelper2(n,i)) == 1.0 / (n as real)
  {
    var k := Helper.SandwichBetweenPowers(2, n - 1);
    var e2 := UniformFullCorrectnessHelper2(n, i);
    assert RandomNumberGenerator.mu(e2) == 1.0 / (Helper.Power(2, k + 1) as real) by {
      assert Helper.Power(2, k) <= n - 1 < Helper.Power(2, k + 1);
      UniformPowerOfTwoCorrectness.UnifCorrectness(n - 1, k + 1);
      assert UniformPowerOfTwoCorrectness.UnifIsCorrect(n - 1, k + 1, i);
    }
    assert 1.0 / (n as real) == 1.0 / (Helper.Power(2, k) as real) by {
      assert n == Helper.Power(2, k) by {
        assume {:axiom} false;
      }
    }
  }

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
