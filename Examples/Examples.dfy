/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %verify "%s"

include "../Library/DRandom.dfy"

module RandomExamples {
  import opened DafnyLibraries

  method Main() 
    decreases *
  {
    var n := 100000;
    var r := new DRandom();

    var t := 0;
    for i := 0 to n 
    {
      var b := r.Coin();
      if b {
        t := t + 1;
      }
    }
    print "Estimated parameter for Coin(): ", (t as real) / (n as real), " (should be around 0.5)\n";

    var a := 0;
    var b := 0;
    var c := 0;
    for i := 0 to n 
      invariant a + b + c == i
    {
      var k := r.Uniform(3);
      if k == 0 {
        a := a + 1;
      } else if k == 1 {
        b := b + 1;
      } else {
        c := c + 1;
      }
    }
    print "Estimated parameters for Uniform(3): ", (a as real) / (n as real), "; " , (b as real) / (n as real), "; " , (c as real) / (n as real), " (each should be around 0.33)\n";

    a := 0;
    b := 0;
    c := 0;
    for i := 0 to n 
      invariant a + b + c == i
    {
      var k := r.UniformInterval(7,10);
      if k == 7 {
        a := a + 1;
      } else if k == 8 {
        b := b + 1;
      } else {
        c := c + 1;
      }
    }
    print "Estimated parameters for UniformInterval(7,10): ", (a as real) / (n as real), "; ", (b as real) / (n as real), "; " , (c as real) / (n as real), " (each should be around 0.33)\n";

    a := 0;
    b := 0;
    for i := 0 to n 
    {
      var k := r.Geometric();
      if k == 5 {
        a := a + 1;
      } else if k == 10  {
        b := b + 1;
      }
    }
    print "Estimated parameters for Geometric(0.5): " , (a as real) / (n as real), " (should be around 0.015625) and " , (b as real) / (n as real), " (should be around 0.00048828125) \n";

    t := 0;
    for i := 0 to n 
    {
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
    print "Estimated Bernoulli parameter for BernoulliExpNeg: ", (t as real) / (n as real), " (should be around 0.1)\n";
  }
}