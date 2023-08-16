/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "Uniform.dfy"
include "Monad.dfy"
include "RandomNumberGenerator.dfy"
include "Bernoulli.dfy"

module Model {
  import opened Monad
  import opened RandomNumberGenerator
  import opened Unif = Uniform
  import opened Bern = Bernoulli

  function Coin(s: RNG): (bool, RNG) {
    Monad.Deconstruct(s)
  }

  function Uniform(n: nat): Hurd<nat> 
    requires 0 < n 
  {
    Unif.ProbUniform(n)
  }

  function UniformInterval(a: int, b: int): (f: Hurd<int>)
    requires a < b
    ensures forall s :: f(s).0 == a + Uniform(b - a)(s).0
  {
    Unif.ProbUniformInterval(a, b)
  }

  function Bernoulli(p: Probability): Hurd<bool> {
    Bern.ProbBernoulli(p)
  }

}