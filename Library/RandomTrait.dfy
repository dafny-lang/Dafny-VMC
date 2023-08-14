include "Verified/Model/Model.dfy"

module RandomTrait {
  import opened RandomNumberGenerator
  import Model

  trait {:termination false} RandomTrait {
    method Coin() returns (b: bool)

    method Uniform(n: nat) returns (u: nat)
      requires n > 0

    method UniformInterval(a: int, b: int) returns (u: int)
      requires a < b
  }
}