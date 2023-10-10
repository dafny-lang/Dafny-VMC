/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module RandomExamples.ExternUniform {
  import Rationals
  import DafnyVMC

  method Main()
    decreases *
  {
    var n := 100000;
    var r: DafnyVMC.DRandomExternUniform := new DafnyVMC.DRandomExternUniform();

    var t := 0;
    for i := 0 to n {
      var b := r.CoinSample();
      if b {
        t := t + 1;
      }
    }
    print "Estimated parameter for CoinSample(): ", (t as real) / (n as real), " (should be around 0.5)\n";

    var a := 0;
    var b := 0;
    var c := 0;
    for i := 0 to n {
      var k := r.UniformSample(10);
      if k == 0 {
        a := a + 1;
      } else if k == 5 {
        b := b + 1;
      } else if k == 9 {
        c := c + 1;
      }
    }
    print "Estimated probabilities for UniformSample(10): ", (a as real) / (n as real), "; " , (b as real) / (n as real), "; " , (c as real) / (n as real), " (each should be around 0.1)\n";

    a := 0;
    b := 0;
    c := 0;
    for i := 0 to n {
      var k := r.UniformIntervalSample(7,10);
      if k == 7 {
        a := a + 1;
      } else if k == 8 {
        b := b + 1;
      } else {
        c := c + 1;
      }
    }
    print "Estimated probabilities for UniformIntervalSample(7,10): ", (a as real) / (n as real), "; ", (b as real) / (n as real), "; " , (c as real) / (n as real), " (each should be around 0.33)\n";

    t := 0;
    for i := 0 to n {
      var b := r.BernoulliSample(Rationals.Rational(1, 5));
      if b {
        t := t + 1;
      }
    }

    print "Estimated parameter for BernoulliSample(1, 5): ", (t as real) / (n as real), " (should be around 0.2)\n";

    t := 0;
    for i := 0 to n {
      var b := r.BernoulliSample(Rationals.Rational(0, 5));
      if b {
        t := t + 1;
      }
    }

    print "Estimated parameter for BernoulliSample(0, 5): ", (t as real) / (n as real), " (should be around 0.0)\n";

    t := 0;
    for i := 0 to n {
      var b := r.BernoulliSample(Rationals.Rational(5, 5));
      if b {
        t := t + 1;
      }
    }

    print "Estimated parameter for BernoulliSample(5, 5): ", (t as real) / (n as real), " (should be around 1.0\n";

    t := 0;
    for i := 0 to n {
      var u := r.BernoulliExpNegSample(Rationals.Rational(12381, 5377)); // about -ln(0.1)
      if u {
        t := t + 1;
      }
    }
    print "Estimated parameter for BernoulliExpNegSample(-ln(0.1)): ", (t as real) / (n as real), " (should be around 0.1)\n";

    var count0 := 0;
    var count1 := 0;
    var countneg1 := 0;
    for i := 0 to n {
      var u := r.DiscreteLaplaceSample(Rationals.Rational(7, 5));
      match u {
        case -1 => countneg1 := countneg1 + 1;
        case 0 => count0 := count0 + 1;
        case 1 => count1 := count1 + 1;
        case _ =>
      }
    }
    // Reference values computed with Wolfram Alpha:
    // https://www.wolframalpha.com/input?i=ReplaceAll%5B%28E%5E%5B1%2Ft%5D+-+1%29+%2F+%28E%5E%5B1%2Ft%5D+%2B+1%29+*+E%5E%28-Abs%5Bx%5D%2Ft%29%2C+%7Bt+-%3E+7%2F5%2C+x+-%3E+0%7D%5D
    // https://www.wolframalpha.com/input?i=ReplaceAll%5B%28E%5E%5B1%2Ft%5D+-+1%29+%2F+%28E%5E%5B1%2Ft%5D+%2B+1%29+*+E%5E%28-Abs%5Bx%5D%2Ft%29%2C+%7Bt+-%3E+7%2F5%2C+x+-%3E+1%7D%5D
    print "Estimated probabilities for DiscreteLaplaceSample(7/5): ", count0 as real / n as real, " (should be around 0.3426949) and ", count1 as real / n as real, ", ", countneg1 as real / n as real, " (should both be around 0.1677634)\n";

    count0 := 0;
    count1 := 0;
    countneg1 := 0;
    for i := 0 to n {
      var u := r.DiscreteGaussianSample(Rationals.Rational(7, 5));
      match u {
        case -1 => countneg1 := countneg1 + 1;
        case 0 => count0 := count0 + 1;
        case 1 => count1 := count1 + 1;
        case _ =>
      }
    }
    // Reference values computed with Wolfram Alpha:
    // https://www.wolframalpha.com/input?i=ReplaceAll%5BE%5E%28-x%5E2+%2F+%282+*%CF%83%5E2%29%29+%2F+Sum%5BE%5E%28-y%5E2%2F%282+%CF%83%5E2%29%29%2C+%7By%2C+-Infinity%2C+Infinity%7D%5D%2C+%7Bx+-%3E+0%2C+%CF%83+-%3E+1.4%7D%5D
    // https://www.wolframalpha.com/input?i=ReplaceAll%5BE%5E%28-x%5E2+%2F+%282+*%CF%83%5E2%29%29+%2F+Sum%5BE%5E%28-y%5E2%2F%282+%CF%83%5E2%29%29%2C+%7By%2C+-Infinity%2C+Infinity%7D%5D%2C+%7Bx+-%3E+1%2C+%CF%83+-%3E+1.4%7D%5D
    print "Estimated probabilities for DiscreteGaussianSample(1.4): ", count0 as real / n as real, " (should be around 0.284959) and ", count1 as real / n as real, ", ", countneg1 as real / n as real, " (should both be around 0.220797)\n";
  }
}
