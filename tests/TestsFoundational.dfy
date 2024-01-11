/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module TestsFoundational {
  import NatArith
  import DafnyVMC
  import Tests
  import Helper

  method {:test} TestCoin() {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestCoin(1_000_000, r);
  }

  method {:test} TestUniformPowerOfTwo_10()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestUniformPowerOfTwo(1_000_000, 10, r);
  }

  method {:test} TestUniformPowerOfTwo_100()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestUniformPowerOfTwo(1_000_000, 100, r);
  }

  // Test arguments that don't fit in 64 bits:
  method {:test} TestUniformPowerOfTwoMean_10Pow100()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestUniformPowerOfTwoMean(100_000, NatArith.Power(10, 100), r);
  }

  method {:test} TestUniform_10()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestUniform(1_000_000, 10, r);
  }

  method {:test} TestUniform_100()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestUniform(1_000_000, 100, r);
  }

  // Test arguments that don't fit in 64 bits:
  method {:test} TestUniformMean_10Pow100()
    decreases *
  {
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestUniformMean(100_000, NatArith.Power(10, 100), r);
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

  method {:test} TestFisherYatesIdentity()
    decreases *
  {
    var a: array<nat> := new nat[4](i => i); // [0, 1, 2, 3]
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestFisherYates(1_000_000, a, r, Helper.NatToString);
  }

  method {:test} TestFisherYatesConstant()
    decreases *
  {
    var a: array<nat> := new nat[4](i => 0); // [0, 0, 0, 0]
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestFisherYates(1_000_000, a, r, Helper.NatToString);
  }

  method {:test} TestFisherYatesMixed()
    decreases *
  {
    var a: array<nat> := new nat[] [0, 1, 1, 2]; // [0, 1, 1, 2]
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestFisherYates(1_000_000, a, r, Helper.NatToString);
  }

  method {:test} TestFisherYatesLengthZero()
    decreases *
  {
    var a: array<nat> := new nat[] []; // length 0
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestFisherYates(1_000_000, a, r, Helper.NatToString);
  }

  method {:test} TestFisherYatesLengthOne()
    decreases *
  {
    var a: array<nat> := new nat[] [0]; // length 1
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestFisherYates(1_000_000, a, r, Helper.NatToString);
  }

  method {:test} TestFisherYatesLengthEven()
    decreases *
  {
    var a: array<nat> := new nat[] [2, 1, 18, 2, 3, 4]; // length 6
    var r := new DafnyVMC.DRandomFoundational();
    Tests.TestFisherYates(1_000_000, a, r, Helper.NatToString);
  }

}
