/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Tests {
  import NatArith
  import RealArith
  import Helper
  import DafnyVMC

  method TestBernoulliIsWithin3SigmaOfTrueMean(
    n: nat,
    empiricalSum: real,
    successProb: real,
    description: string
  )
    requires n > 0
  {
    TestEmpiricalIsWithin3SigmaOfTrueMean(n, empiricalSum, successProb, successProb * (1.0 - successProb), description);
  }

  method TestEmpiricalIsWithin3SigmaOfTrueMean(
    n: nat,
    empiricalSum: real,
    trueMean: real,
    trueVariance: real,
    description: string
  )
    requires n > 0
  {
    var empiricalMean := empiricalSum / n as real;
    var diff := RealArith.Abs(empiricalMean - trueMean);
    var threshold := 3.0 * 3.0 * trueVariance;
    if diff * diff > threshold {
      print "Test failed: ", description, "\n";
      print "True mean: ", trueMean, "\n";
      print "Empirical mean: ", empiricalMean, "\n";
      print "Difference between empirical and true mean: ", diff, "\n";
      print "squared difference: ", diff * diff, "\n";
      print "sigma squared:      ", trueVariance, "\n";
    }
    expect diff * diff <= threshold, "Empirical mean should be within 3 sigma of true mean. This individual test may fail with probability of about 6.3e-5.";
  }

  method TestUniform(n: nat, u: nat, r: DafnyVMC.Random)
    decreases *
    requires n > 0
    requires u > 0
    modifies r
  {
    var k := NatArith.Log2Floor(u);
    var a := new nat[u](i => 0);
    var sum := 0;
    for i := 0 to n {
      var l := r.UniformSample(u);
      expect 0 <= l < u, "sample not in the right bound";
      a[l] := a[l] + 1;
      sum := sum + l;
    }
    for i := 0 to u {
      TestBernoulliIsWithin3SigmaOfTrueMean(n, a[i] as real, 1.0 / (u as real), "p(" + Helper.NatToString(i) + ")");
    }
    TestEmpiricalIsWithin3SigmaOfTrueMean(n, sum as real, (u - 1) as real / 2.0, (u * u - 1) as real / 12.0, "mean of Uniform(" + Helper.NatToString(u) + ")");
  }

  method TestUniformMean(n: nat, u: nat, r: DafnyVMC.Random)
    decreases *
    requires n > 0
    requires u > 0
    modifies r
  {
    var k := NatArith.Log2Floor(u);
    var sum := 0;
    for i := 0 to n {
      var l := r.UniformSample(u);
      expect 0 <= l < u, "sample not in the right bound";
      sum := sum + l;
    }
    TestEmpiricalIsWithin3SigmaOfTrueMean(n, sum as real, (u - 1) as real / 2.0, (u * u - 1) as real / 12.0, "mean of Uniform(" + Helper.NatToString(u) + ")");
  }

  method TestUniformInterval(n: nat, r: DafnyVMC.Random)
    decreases *
    requires n > 0
    modifies r
  {
    var a := 0;
    var b := 0;
    var c := 0;
    for i := 0 to n {
      var k := r.UniformIntervalSample(7,10);
      match k {
        case 7 => a := a + 1;
        case 8 => b := b + 1;
        case 9 => c := c + 1;
      }
    }
    TestBernoulliIsWithin3SigmaOfTrueMean(n, a as real, 1.0 / 3.0, "p(7)");
    TestBernoulliIsWithin3SigmaOfTrueMean(n, b as real, 1.0 / 3.0, "p(8)");
    TestBernoulliIsWithin3SigmaOfTrueMean(n, c as real, 1.0 / 3.0, "p(9)");
  }

  method TestBernoulli(n: nat, r: DafnyVMC.Random)
    decreases *
    requires n > 0
    modifies r
  {
    var t := 0;
    for i := 0 to n {
      var b := r.BernoulliSample(1, 5);
      if b {
        t := t + 1;
      }
    }
    TestBernoulliIsWithin3SigmaOfTrueMean(n, t as real, 0.2, "p(true)");
  }

  method TestBernoulli2(n: nat, r: DafnyVMC.Random)
    decreases *
    modifies r
  {
    var t := 0;
    for i := 0 to n {
      var b := r.BernoulliSample(0, 5);
      if b {
        t := t + 1;
      }
    }

    expect t == 0;
  }

  method TestBernoulli3(n: nat, r: DafnyVMC.Random)
    decreases *
    modifies r
  {
    var t := 0;
    for i := 0 to n {
      var b := r.BernoulliSample(5, 5);
      if b {
        t := t + 1;
      }
    }

    expect t == n;
  }

  method TestBernoulliExpNegLe1(n: nat, r: DafnyVMC.Random)
    decreases *
    requires n > 0
    modifies r
  {
    var t := 0;
    for i := 0 to n {
      var u := r.BernoulliExpNegSample(5108256, 10000000); // about -ln(0.6)
      if u {
        t := t + 1;
      }
    }
    TestBernoulliIsWithin3SigmaOfTrueMean(n, t as real, 0.6, "p(true)");
  }

  method TestBernoulliExpNeg(n: nat, r: DafnyVMC.Random)
    decreases *
    requires n > 0
    modifies r
  {
    var t := 0;
    for i := 0 to n {
      var u := r.BernoulliExpNegSample(12381, 5377); // about -ln(0.1)
      if u {
        t := t + 1;
      }
    }
    TestBernoulliIsWithin3SigmaOfTrueMean(n, t as real, 0.1, "p(true)");
  }

  method TestDiscreteLaplace(n: nat, r: DafnyVMC.Random)
    decreases *
    requires n > 0
    modifies r
  {
    var counts := map[-2 := 0, -1 := 0, 0 := 0, 1 := 0, 2 := 0];
    var sum := 0;
    for i := 0 to n
      invariant -2 in counts && -1 in counts && 0 in counts && 1 in counts && 2 in counts
    {
      var u := r.DiscreteLaplaceSample(7, 5);
      sum := sum + u;
      if u !in counts {
        counts := counts[ u := 1 ];
      } else {
        counts := counts[ u := counts[u] + 1 ];
      }
    }
    // Reference values computed with Wolfram Alpha:
    // https://www.wolframalpha.com/input?i=ReplaceAll%5B%28E%5E%5B1%2Ft%5D+-+1%29+%2F+%28E%5E%5B1%2Ft%5D+%2B+1%29+*+E%5E%28-Abs%5Bx%5D%2Ft%29%2C+%7Bt+-%3E+7%2F5%2C+x+-%3E+0%7D%5D
    // https://www.wolframalpha.com/input?i=ReplaceAll%5B%28E%5E%5B1%2Ft%5D+-+1%29+%2F+%28E%5E%5B1%2Ft%5D+%2B+1%29+*+E%5E%28-Abs%5Bx%5D%2Ft%29%2C+%7Bt+-%3E+7%2F5%2C+x+-%3E+1%7D%5D
    // https://www.wolframalpha.com/input?i=ReplaceAll%5B%28E%5E%5B1%2Ft%5D+-+1%29+%2F+%28E%5E%5B1%2Ft%5D+%2B+1%29+*+E%5E%28-Abs%5Bx%5D%2Ft%29%2C+%7Bt+-%3E+7%2F5%2C+x+-%3E+2%7D%5D
    TestBernoulliIsWithin3SigmaOfTrueMean(n, counts[0] as real, 0.3426949, "p(0)");
    TestBernoulliIsWithin3SigmaOfTrueMean(n, counts[1] as real, 0.1677634, "p(1)");
    TestBernoulliIsWithin3SigmaOfTrueMean(n, counts[-1] as real, 0.1677634, "p(-1)");
    TestBernoulliIsWithin3SigmaOfTrueMean(n, counts[2] as real, 0.0821272, "p(2)");
    TestBernoulliIsWithin3SigmaOfTrueMean(n, counts[-2] as real, 0.0821272, "p(-2)");
    var variance := 3.7575005; // variance of DiscreteLaplace(7/5) is (2*exp(5/7))/(exp(5/7)-1)^2
    TestEmpiricalIsWithin3SigmaOfTrueMean(n, sum as real, 0.0, variance, "mean");
  }

  method TestDiscreteGaussian(n: nat, r: DafnyVMC.Random)
    decreases *
    requires n > 0
    modifies r
  {
    var counts := map[-2 := 0, -1 := 0, 0 := 0, 1 := 0, 2 := 0];
    var sum := 0;
    for i := 0 to n
      invariant -2 in counts && -1 in counts && 0 in counts && 1 in counts && 2 in counts
    {
      var u := r.DiscreteGaussianSample(7, 5);
      sum := sum + u;
      if u !in counts {
        counts := counts[ u := 1 ];
      } else {
        counts := counts[ u := counts[u] + 1 ];
      }
    }
    // Reference values computed with Wolfram Alpha:
    // https://www.wolframalpha.com/input?i=ReplaceAll%5BE%5E%28-x%5E2+%2F+%282+*%CF%83%5E2%29%29+%2F+Sum%5BE%5E%28-y%5E2%2F%282+%CF%83%5E2%29%29%2C+%7By%2C+-Infinity%2C+Infinity%7D%5D%2C+%7Bx+-%3E+0%2C+%CF%83+-%3E+1.4%7D%5D
    // https://www.wolframalpha.com/input?i=ReplaceAll%5BE%5E%28-x%5E2+%2F+%282+*%CF%83%5E2%29%29+%2F+Sum%5BE%5E%28-y%5E2%2F%282+%CF%83%5E2%29%29%2C+%7By%2C+-Infinity%2C+Infinity%7D%5D%2C+%7Bx+-%3E+1%2C+%CF%83+-%3E+1.4%7D%5D
    // https://www.wolframalpha.com/input?i=ReplaceAll%5BE%5E%28-x%5E2+%2F+%282+*%CF%83%5E2%29%29+%2F+Sum%5BE%5E%28-y%5E2%2F%282+%CF%83%5E2%29%29%2C+%7By%2C+-Infinity%2C+Infinity%7D%5D%2C+%7Bx+-%3E+2%2C+%CF%83+-%3E+1.4%7D%5D
    TestBernoulliIsWithin3SigmaOfTrueMean(n, counts[0] as real, 0.284959, "p(0)");
    TestBernoulliIsWithin3SigmaOfTrueMean(n, counts[1] as real, 0.220797, "p(1)");
    TestBernoulliIsWithin3SigmaOfTrueMean(n, counts[-1] as real, 0.220797, "p(-1)");
    TestBernoulliIsWithin3SigmaOfTrueMean(n, counts[2] as real, 0.102713, "p(2)");
    TestBernoulliIsWithin3SigmaOfTrueMean(n, counts[-2] as real, 0.102713, "p(-2)");
    var varianceBound := 1.4 * 1.4; // variance of DiscreteGaussian(1.4) is < 1.4^2
    TestEmpiricalIsWithin3SigmaOfTrueMean(n, sum as real, 0.0, varianceBound, "mean");
  }

  method TestFisherYates<T(==, !new)>(n: nat, a: array<T>, r: DafnyVMC.Random, printer: ((T, nat)) -> string) 
    decreases *
    modifies r
    modifies a
    requires n > 0
  {
    var a := new (T, nat)[a.Length](i reads a requires 0 <= i < a.Length => (a[i], i));
    var numberOfPermutations: nat := NatArith.FactorialTraditional(a.Length);
    var numberOfObservedPermutations: map<seq<(T, nat)>, nat> := map[];
    
    for i := 0 to n {
      var aCopy := a;
      r.Shuffle(aCopy);
      var aCopyAsSeq := aCopy[..];
      if aCopyAsSeq in numberOfObservedPermutations {
        numberOfObservedPermutations := numberOfObservedPermutations[aCopyAsSeq := numberOfObservedPermutations[aCopyAsSeq] + 1];
      } else {
        numberOfObservedPermutations := numberOfObservedPermutations[aCopyAsSeq := 1];
      }
    }

    var items := numberOfObservedPermutations.Items;

    while items != {}
      decreases |items| 
     {
      var item :| item in items;
      items := items - {item};
      TestBernoulliIsWithin3SigmaOfTrueMean(n, item.1 as real, 1.0 / numberOfPermutations as real, "p(" + Helper.SeqToString(item.0, printer) + ")");
    }
  }
}
