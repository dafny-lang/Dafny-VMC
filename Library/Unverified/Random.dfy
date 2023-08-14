include "../RandomTrait.dfy"

module {:extern "DafnyLibraries"} DafnyLibraries {
  import opened RandomTrait

  class {:extern} Random extends RandomTrait {
    constructor {:extern} ()
    
    method {:extern} Coin() returns (b: bool)
      modifies this`s

    method {:extern} Uniform(n: nat) returns (u: nat)
      modifies this`s
      requires n > 0

    method {:extern} UniformInterval(a: int, b: int) returns (u: int)
      modifies this`s
      requires a < b
  }
}