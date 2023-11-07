/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module TestsFoundational {
  import DafnyVMC
  import Tests

  method {:test} TestCoin() {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestCoin(1_000_000, r);
  }

  method {:test} TestUniform100()
    decreases *
  {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestUniform(1_000_000_000, 100, r);
  }

  method {:test} TestUniform10_000()
    decreases *
  {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestUniform(1_000_000_000, 10_000, r);
  }

  method {:test} TestUniform1_000_000()
    decreases *
  {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestUniform(1_000_000_000, 1_000_000, r);
  }

  method {:test} TestUniformInterval()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestUniformInterval(1_000_000, r);
  }

  method {:test} TestBernoulli()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestBernoulli(1_000_000, r);
  }

  method {:test} TestBernoulli2()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestBernoulli2(1_000_000, r);
  }

  method {:test} TestBernoulli3()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestBernoulli3(1_000_000, r);
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
