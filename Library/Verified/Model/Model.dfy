include "Uniform.dfy"
include "Monad.dfy"
include "RandomNumberGenerator.dfy"

module Model {
  import opened Monad
  import opened RandomNumberGenerator
  import opened Unif = Uniform

  function Coin(s: RNG): (bool, RNG) {
    Monad.Deconstruct(s)
  }

  function Uniform(n: nat): Hurd<nat> 
    requires n > 0
  {
    Unif.ProbUnif(n)
  }

  function UniformInterval(a: int, b: int): Hurd<int>
    requires a < b
  {
    Unif.ProbUniformInterval(a, b)
  }

}