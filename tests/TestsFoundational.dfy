/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

 include "../src/DRandom.dfy"
 include "Tests.dfy"

module TestsFoundational {
  import opened DafnyLibraries
  import Tests

  method {:test} TestCoin() {
    var r := new DRandomFoundational();
    Tests.TestCoin(1_000_000, r);
  }

  method {:test} TestUniform()
    decreases *
  {
    var r := new DRandomFoundational();
    Tests.TestUniform(1_000_000, r);
  }

  method {:test} TestUniformInterval()
    decreases *
  {
    var r := new DRandomFoundational();
    Tests.TestUniformInterval(1_000_000, r);
  }

  method {:test} TestGeometric()
    decreases *
  {
    var r := new DRandomFoundational();
    Tests.TestGeometric(1_000_000, r);
  }

  method {:test} TestBernoulliRational()
    decreases *
  {
    var n := 1000000;
    var r := new DRandomFoundational();

    var t := 0;
    for i := 0 to n {
      var b := r.BernoulliRational(1, 5);
      if b {
        t := t + 1;
      }
    }
    testBernoulliIsWithin3SigmaOfTrueMean(n, t as real, 0.2, "p(true)");
  }

  method {:test} TestBernoulliRational2()
    decreases *
  {
    var n := 1000000;
    var r := new DRandomFoundational();

    var t := 0;
    for i := 0 to n {
      var b := r.BernoulliRational(0, 5);
      if b {
        t := t + 1;
      }
    }

    expect t == 0;
  }  

  method {:test} TestBernoulliRational3()
    decreases *
  {
    var n := 1000000;
    var r := new DRandomFoundational();

    var t := 0;
    for i := 0 to n {
      var b := r.BernoulliRational(5, 5);
      if b {
        t := t + 1;
      }
    }

    expect t == n;
  }  

  method {:test} TestBernoulli()
    decreases *
  {
    var r := new DRandomFoundational();
    Tests.TestBernoulli(1_000_000, r);
  }

  method {:test} TestBernoulliExpNeg()
    decreases *
  {
    var r := new DRandomFoundational();
    Tests.TestBernoulliExpNeg(1_000_000, r);
  }

  method {:test} TestDiscreteLaplace()
    decreases *
  {
    var r := new DRandomFoundational();
    Tests.TestDiscreteLaplace(1_000_000, r);
  }

  method {:test} TestDiscreteGaussian()
    decreases *
  {
    var r := new DRandomFoundational();
    Tests.TestDiscreteGaussian(1_000_000, r);
  }
}
