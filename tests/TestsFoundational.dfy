/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

 include "../src/Dafny-VMC.dfy"
 include "Tests.dfy"

module TestsFoundational {
  import DafnyVMC
  import Tests

  method {:test} TestCoin() {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestCoin(1_000_000, r);
  }

  method {:test} TestUniform()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestUniform(1_000_000, r);
  }

  method {:test} TestUniformInterval()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestUniformInterval(1_000_000, r);
  }

  method {:test} TestGeometric()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestGeometric(1_000_000, r);
  }

  method {:test} TestBernoulliRational()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestBernoulliRational(1_000_000, r);
  }

  method {:test} TestBernoulliRational2()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestBernoulliRational2(1_000_000, r);
  }  

  method {:test} TestBernoulliRational3()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestBernoulliRational3(1_000_000, r);
  }  

  method {:test} TestBernoulli()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestBernoulli(1_000_000, r);
  }

  method {:test} TestBernoulliExpNeg()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestBernoulliExpNeg(1_000_000, r);
  }

  method {:test} TestDiscreteLaplace()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestDiscreteLaplace(1_000_000, r);
  }

  method {:test} TestDiscreteGaussian()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestDiscreteGaussian(1_000_000, r);
  }
}
