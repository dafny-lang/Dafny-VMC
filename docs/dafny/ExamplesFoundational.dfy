/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

include "../../src/Dafny-VMC.dfy"

module RandomExamples {
  import DafnyVMC

  method Main()
    decreases *
  {
    var n := 100000;
    var r: DafnyVMC.DRandomFoundational := new DafnyVMC.DRandomFoundational();

    var t := 0;
    for i := 0 to n {
      var b := r.Coin();
      if b {
        t := t + 1;
      }
    }
    print "Estimated parameter for Coin(): ", (t as real) / (n as real), " (should be around 0.5)\n";

    var a := 0;
    var b := 0;
    var c := 0;
    for i := 0 to n {
      var k := r.Uniform(10);
      if k == 0 {
        a := a + 1;
      } else if k == 5 {
        b := b + 1;
      } else if k == 9 {
        c := c + 1;
      }
    }
    print "Estimated probabilities for Uniform(10): ", (a as real) / (n as real), "; " , (b as real) / (n as real), "; " , (c as real) / (n as real), " (each should be around 0.1)\n";

    a := 0;
    b := 0;
    c := 0;
    for i := 0 to n {
      var k := r.UniformInterval(7,10);
      if k == 7 {
        a := a + 1;
      } else if k == 8 {
        b := b + 1;
      } else {
        c := c + 1;
      }
    }
    print "Estimated probabilities for UniformInterval(7,10): ", (a as real) / (n as real), "; ", (b as real) / (n as real), "; " , (c as real) / (n as real), " (each should be around 0.33)\n";

    a := 0;
    b := 0;
    for i := 0 to n {
      var k := r.Geometric();
      if k == 5 {
        a := a + 1;
      } else if k == 10  {
        b := b + 1;
      }
    }
    print "Estimated probabilities for Geometric(0.5): " , (a as real) / (n as real), " (should be around 0.015625) and " , (b as real) / (n as real), " (should be around 0.00048828125) \n";

    t := 0;
    for i := 0 to n {
      var b := r.BernoulliRational(1, 5);
      if b {
        t := t + 1;
      }
    }

    print "Estimated parameter for BernoulliRational(1, 5): ", (t as real) / (n as real), " (should be around 0.2)\n";

    t := 0;
    for i := 0 to n {
      var b := r.BernoulliRational(0, 5);
      if b {
        t := t + 1;
      }
    }

    print "Estimated parameter for BernoulliRational(0, 5): ", (t as real) / (n as real), " (should be around 0.0)\n";

    t := 0;
    for i := 0 to n {
      var b := r.BernoulliRational(5, 5);
      if b {
        t := t + 1;
      }
    }

    print "Estimated parameter for BernoulliRational(5, 5): ", (t as real) / (n as real), " (should be around 1.0\n";

    t := 0;
    for i := 0 to n {
      var b := r.Bernoulli(0.2);
      if b {
        t := t + 1;
      }
    }

    print "Estimated parameter for Bernoulli(0.2): ", (t as real) / (n as real), " (should be around 0.2)\n";

    t := 0;
    for i := 0 to n {
      var u := r.BernoulliExpNeg(2.30258509299); // about -ln(0.1)
      if u {
        t := t + 1;
      }
    }
    print "Estimated parameter for BernoulliExpNeg(-ln(0.1)): ", (t as real) / (n as real), " (should be around 0.1)\n";

    var count0 := 0;
    var count1 := 0;
    var countneg1 := 0;
    for i := 0 to n {
      var u := r.DiscreteLaplace(5, 7); // DiscreteLaplace(7/5)
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
    print "Estimated probabilities for DiscreteLaplace(7/5): ", count0 as real / n as real, " (should be around 0.3426949) and ", count1 as real / n as real, ", ", countneg1 as real / n as real, " (should both be around 0.1677634)\n";

    count0 := 0;
    count1 := 0;
    countneg1 := 0;
    for i := 0 to n {
      var u := r.DiscreteGaussian(1.4);
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
    print "Estimated probabilities for DiscreteGaussian(1.4): ", count0 as real / n as real, " (should be around 0.284959) and ", count1 as real / n as real, ", ", countneg1 as real / n as real, " (should both be around 0.220797)\n";
  }
}
