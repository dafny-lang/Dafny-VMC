/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Correctness {
  import Model
  import Rand
  import Uniform
  import Monad
  import Independence
  import RealArith

  /************
   Definitions
  ************/

  // Number of permutations of s[i..] == [s[i], s[i+1], ..., s[|s|-1]]
  function NumberOfPermutationsOf<T(==)>(s: seq<T>, i: nat := 0): (n: nat)
    requires |s| != 0 ==> i <= |s| - 1
    decreases |s| - i
    ensures n != 0
  {
    if |s| == 0 || i == |s| - 1 then
      1
    else
      var multiplicity := multiset(s[i..])[s[i]];
      var length := |s[i..]|;
      (length / multiplicity) * NumberOfPermutationsOf(s, i+1)
  }

  /*******
   Lemmas
  *******/

  lemma {:axiom} CorrectnessFisherYates<T(!new)>(xs: seq<T>, p: seq<T>)
    requires multiset(p) == multiset(xs)
    ensures
      var e := iset s | Model.Shuffle(xs)(s).Equals(p);
      && e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (NumberOfPermutationsOf(xs) as real)
  /*   {
      CorrectnessFisherYatesGeneral(xs, p, 0);
    } */

  /*   lemma {:axiom} CorrectnessFisherYatesGeneral<T(!new)>(xs: seq<T>, p: seq<T>, i: nat)
      requires multiset(p) == multiset(xs)
      ensures
        var e := iset s | Model.Shuffle(xs, i)(s)[i..].Equals(p[i..]);
        && e in Rand.eventSpace
        && Rand.prob(e) == 1.0 / (NumberOfPermutationsOf(xs, i) as real) */
  /* {
    var e := iset s | Model.Shuffle(xs)(s).Equals(p);
    assume {:axiom} e in Rand.eventSpace; // todo later

    if |xs| != 0 {
      var h := Uniform.Model.IntervalSample(0, |xs|); 
      var f :=        
        (j: int) requires 0 <= j < |xs| => 
          var zs := Permutations.Swap(xs, 0, j);
          Monad.Map(Model.Shuffle(zs[1..]), (ys: seq<T>) => [zs[0]] + ys);
      var j: int := Permutations.FirstOccurrence(xs, p[0]);
      var A: iset<int> := iset{j};
      var B: iset<seq<T>> := iset xs | xs[1..] == p[1..];
      var E: iset<Rand.Bitstream> := Monad.BitstreamsWithValueIn(f(j), B);
      var zs := Permutations.Swap(xs, 0, j)[1..];
      assume {:axiom} false;
      assert Independence.IsIndep(h) by {
        Uniform.Correctness.IntervalSampleIsIndep(0, |xs|);
      }    
      assert Eq1: Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A)) == 1.0 / |xs| as real by {
        calc {
          Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A));
          Rand.prob(iset s | Uniform.Model.IntervalSample(0, |xs|)(s).Equals(j));
          { Uniform.Correctness.UniformFullIntervalCorrectness(0, |xs|, j); }
          1.0 / |xs| as real;
        }
      }
      assert Eq2: Rand.prob(E) == 1.0 / (|Permutations.CalculateAllPermutationsOf(zs)| as real) by {
        calc {
          Rand.prob(E);
          Rand.prob(Monad.BitstreamsWithValueIn(f(j), B));
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
        { reveal Eq1; reveal Eq2; }
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
  } */

}