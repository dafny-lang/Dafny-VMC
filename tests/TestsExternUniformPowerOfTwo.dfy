/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module TestsExternUniform {
  import DafnyVMC
  import Tests

  method {:test} TestCoin() {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestCoin(1_000_000, r);
  }

  method {:test} TestUniform()
    decreases *
  {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestUniform(1_000_000, r);
  }

  method {:test} TestUniformInterval()
    decreases *
  {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestUniformInterval(1_000_000, r);
  }

  method {:test} TestBernoulli()
    decreases *
  {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestBernoulli(1_000_000, r);
  }

  method {:test} TestBernoulli2()
    decreases *
  {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestBernoulli2(1_000_000, r);
  }

  method {:test} TestBernoulli3()
    decreases *
  {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestBernoulli3(1_000_000, r);
  }

  method {:test} TestBernoulliExpNeg()
    decreases *
  {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestBernoulliExpNeg(1_000_000, r);
  }

  method {:test} TestDiscreteLaplace()
    decreases *
  {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestDiscreteLaplace(1_000_000, r);
  }

  method {:test} TestDiscreteGaussian()
    decreases *
  {
    var r := new DafnyVMC.DRandomExternUniformPowerOfTwo();
    Tests.TestDiscreteGaussian(1_000_000, r);
  }
}