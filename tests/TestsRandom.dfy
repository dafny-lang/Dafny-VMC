/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module TestsRandom {
  import NatArith
  import DafnyVMC
  import Helper
  import Tests

  method {:test} TestUniformPowerOfTwo_10()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestUniformPowerOfTwo(1_000_000, 10, r);
  }

  method {:test} TestUniformPowerOfTwo_100()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestUniformPowerOfTwo(1_000_000, 100, r);
  }

  // Test arguments that don't fit in 64 bits:
  method {:test} TestUniformPowerOfTwoMean_10Pow100()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestUniformPowerOfTwoMean(100_000, NatArith.Power(10, 100), r);
  }

  method {:test} TestUniform_10()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestUniform(1_000_000, 10, r);
  }

  method {:test} TestUniform_100()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestUniform(1_000_000, 100, r);
  }

  // Test arguments that don't fit in 64 bits:
  method {:test} TestUniformMean_10Pow100()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestUniformMean(100_000, NatArith.Power(10, 100), r);
  }

  method {:test} TestUniformInterval0()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestUniformInterval(1_000_000, 0, 1, r);
  }

  method {:test} TestUniformInterval1()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestUniformInterval(1_000_000, -5, 5, r);
  }

  method {:test} TestUniformInterval2()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestUniformInterval(1_000_000, -15, 15, r);
  }

  method {:test} TestUniformInterval3()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestUniformInterval(1_000_000, -30, -5, r);
  }

  method {:test} TestUniformInterval4()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestUniformInterval(1_000_000, -30, 30, r);
  }

  method {:test} TestBernoulli0()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestBernoulli(1_000_000, 1, 5, r);
  }

  method {:test} TestBernoulli1()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestBernoulli(1_000_000, 0, 5, r);
  }

  method {:test} TestBernoulli2()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestBernoulli(1_000_000, 5, 5, r);
  }


  method {:test} TestBernoulli3()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestBernoulli(1_000_000, 1, 100, r);
  }

  method {:test} TestBernoulliExpNegLe1()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestBernoulliExpNegLe1(1_000_000, r);
  }

  method {:test} TestBernoulliExpNeg()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestBernoulliExpNeg(1_000_000, r);
  }

  method {:test} TestDiscreteLaplace()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestDiscreteLaplace(1_000_000, r);
  }

  method {:test} TestDiscreteGaussian()
    decreases *
  {
    var r := new DafnyVMC.Random();
    Tests.TestDiscreteGaussian(1_000_000, r);
  }

  method {:test} TestFisherYatesIdentity()
    decreases *
  {
    var a: array<nat> := new nat[4](i => i); // [0, 1, 2, 3]
    var r := new DafnyVMC.Random();
    Tests.TestFisherYates(1_000_000, a, r, (x: (nat, nat)) => Helper.NatToString(x.0));
  }

  method {:test} TestFisherYatesConstant()
    decreases *
  {
    var a: array<nat> := new nat[4](i => 0); // [0, 0, 0, 0]
    var r := new DafnyVMC.Random();
    Tests.TestFisherYates(1_000_000, a, r, (x: (nat, nat)) => Helper.NatToString(x.0));
  }

  method {:test} TestFisherYatesMixed()
    decreases *
  {
    var a: array<nat> := new nat[] [0, 1, 1, 2]; // [0, 1, 1, 2]
    var r := new DafnyVMC.Random();
    Tests.TestFisherYates(1_000_000, a, r, (x: (nat, nat)) => Helper.NatToString(x.0));
  }

  method {:test} TestFisherYatesLengthZero()
    decreases *
  {
    var a: array<nat> := new nat[] []; // length 0
    var r := new DafnyVMC.Random();
    Tests.TestFisherYates(1_000_000, a, r, (x: (nat, nat)) => Helper.NatToString(x.0));
  }

  method {:test} TestFisherYatesLengthOne()
    decreases *
  {
    var a: array<nat> := new nat[] [0]; // length 1
    var r := new DafnyVMC.Random();
    Tests.TestFisherYates(1_000_000, a, r,  (x: (nat, nat)) => Helper.NatToString(x.0));
  }

  method {:test} TestFisherYatesLengthEven()
    decreases *
  {
    var a: array<nat> := new nat[] [2, 1, 18, 2, 3, 4]; // length 6
    var r := new DafnyVMC.Random();
    Tests.TestFisherYates(1_000_000, a, r, (x: (nat, nat)) => Helper.NatToString(x.0));
  }

}
