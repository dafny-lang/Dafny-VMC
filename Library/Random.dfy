include "Model/RandomNumberGenerator.dfy"
include "Model/Model.dfy"

module {:extern "DafnyLibraries"} DafnyLibraries {
  import opened RandomNumberGenerator
  import Model

  class {:extern} Random {
    ghost var s: RNG

    constructor {:extern} ()
    
    method {:extern} Coin() returns (b: bool)
      ensures Model.Coin(old(s)) == (b, s)

    method Uniform(n: nat) returns (u: nat)
      requires n > 0
      ensures Model.Uniform(n)(old(s)) == (u, s)
    {
      assume {:axiom} false;
      var v := 1;
      u := 0;
      while true {
        v := 2 * v;
        var b := Coin();
        u := 2 * u + if b then 1 else 0;
        if v >= n {
          if u < n {
            return;
          } else {
            v := v - n;
            u := u - n;
          }
        }
      }
    }
    
    method UniformInterval(a: int, b: int) returns (u: int)
      requires a < b
      ensures Model.UniformInterval(a, b)(old(s)) == (u, s)
    {
      var v := Uniform(b - a);
      u := a + v;
    }
  }
}