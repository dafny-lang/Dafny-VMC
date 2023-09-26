/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

 include "../src/Dafny-VMC.dfy"
 include "Tests.dfy"

module TestsExternUniform {
  import opened DafnyVMC
  import Tests

  method {:test} TestCoin() {
    var r := new DRandomExternUniform();
    Tests.TestCoin(1_000_000, r);
  }

  method {:test} TestUniform()
    decreases *
  {
    var r := new DRandomExternUniform();
    Tests.TestUniform(1_000_000, r);
  }

  method {:test} TestUniformInterval()
    decreases *
  {
    var r := new DRandomExternUniform();
    Tests.TestUniformInterval(1_000_000, r);
  }

  method {:test} TestGeometric()
    decreases *
  {
    var r := new DRandomExternUniform();
    Tests.TestGeometric(1_000_000, r);
  }

  method {:test} TestBernoulli()
    decreases *
  {
    var r := new DRandomExternUniform();
    Tests.TestBernoulli(1_000_000, r);
  }

  method {:test} TestBernoulliExpNeg()
    decreases *
  {
    var r := new DRandomExternUniform();
    Tests.TestBernoulliExpNeg(1_000_000, r);
  }

  method {:test} TestDiscreteLaplace()
    decreases *
  {
    var r := new DRandomExternUniform();
    Tests.TestDiscreteLaplace(1_000_000, r);
  }

  method {:test} TestDiscreteGaussian()
    decreases *
  {
    var r := new DRandomExternUniform();
    Tests.TestDiscreteGaussian(1_000_000, r);
  }
}
