/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Correctness {
  import Permutations
  import Model
  import Rand
  import Uniform
  import Monad
  import Independence
  import RealArith

  lemma {:rlimit 1000} {:vcs_split_on_every_assert} CorrectnessFisherYates<T(!new)>(xs: seq<T>, p: seq<T>)
    requires Permutations.IsPermutationOf(p, xs)
    ensures
      var e := iset s | Model.Shuffle(xs)(s).Equals(p);
      && e in Rand.eventSpace
      && |Permutations.CalculateAllPermutationsOf(xs)| > 0
      && Rand.prob(e) == 1.0 / (|Permutations.CalculateAllPermutationsOf(xs)| as real)
  {
    var e := iset s | Model.Shuffle(xs)(s).Equals(p);
    assume {:axiom} e in Rand.eventSpace; // todo later

    if |xs| != 0 {
      var h := Uniform.Model.IntervalSample(0, |xs|); 
      var f :=        
        (j: int) requires 0 <= j < |xs| => 
          var zs := Permutations.Swap(xs, 0, j);
          Monad.Map(Model.Shuffle(zs[1..]), (ys: seq<T>) => [zs[0]] + ys);

      assert Independence.IsIndep(h) by {
        Uniform.Correctness.IntervalSampleIsIndep(0, |xs|);
      }    
      var j: int := Permutations.FirstOccurrence(xs, p[0]);
      var A: iset<int> := iset{j};
      var A2: iset<seq<T>> := iset xs | xs[1..] == p[1..];
      var E: iset<Rand.Bitstream> := Monad.BitstreamsWithValueIn(f(j), A2);
      var zs := Permutations.Swap(xs, 0, j)[1..];
      assert A1: Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A)) == 1.0 / |xs| as real by {
        calc {
          Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A));
          Rand.prob(iset s | Uniform.Model.IntervalSample(0, |xs|)(s).Equals(j));
          { Uniform.Correctness.UniformFullIntervalCorrectness(0, |xs|, j); }
          1.0 / |xs| as real;
        }
      }
      assert A2: Rand.prob(E) == 1.0 / (|Permutations.CalculateAllPermutationsOf(zs)| as real) by {
        calc {
          Rand.prob(E);
          Rand.prob(Monad.BitstreamsWithValueIn(f(j), A2));
          Rand.prob(iset s | f(j)(s).Result? && f(j)(s).value[1..] == p[1..]);
          Rand.prob(iset s | Model.Shuffle(zs)(s).Equals(p[1..]));
          1.0 / (|Permutations.CalculateAllPermutationsOf(zs)| as real);
        }
      }
      calc {
        Rand.prob(e);
        Rand.prob(iset s | Model.Shuffle(xs)(s).Equals(p));
        Rand.prob(iset s | Monad.Bind(h, f)(s).Equals(p));
        Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A) && s in Monad.BitstreamsWithRestIn(h, E));
        { Independence.ResultsIndependent(h, A, E); }
        Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A)) * Rand.prob(E);
        { reveal A1; reveal A2; }
        (1.0 / |xs| as real) * (1.0 / |Permutations.CalculateAllPermutationsOf(zs)| as real);
        { RealArith.SimplifyFractionsMultiplication(1.0, |xs| as real, 1.0, |Permutations.CalculateAllPermutationsOf(zs)| as real); }
        (1.0 * 1.0) / (|xs| as real * |Permutations.CalculateAllPermutationsOf(zs)| as real);
        { assert 1.0 * 1.0 == 1.0; assert |xs| as real * |Permutations.CalculateAllPermutationsOf(zs)| as real == (|xs| * |Permutations.CalculateAllPermutationsOf(zs)|) as real; }
        1.0 / ((|xs| * |Permutations.CalculateAllPermutationsOf(zs)|) as real);
        { assume {:axiom} |xs| * |Permutations.CalculateAllPermutationsOf(zs)| == |Permutations.CalculateAllPermutationsOf(xs)|; } // todo later
        1.0 / |Permutations.CalculateAllPermutationsOf(xs)| as real;
      }
    } else { 
      assume {:axiom} false; // todo later
    }
  }

}