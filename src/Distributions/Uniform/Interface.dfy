/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Base/Interface.dfy"
include "Model.dfy"

module IUniform {
  import opened Base
  import opened UniformModel

  trait {:termination false} IUniform extends Base, IUnif {

    method Uniform(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures UniformModel.ProbUniform(n)(old(s)) == (u, s)

    method UniformInterval(a: int, b: int) returns (u: int)
      modifies this
      decreases *
      requires a < b
      ensures a <= u < b
      ensures UniformModel.ProbUniformInterval(a, b)(old(s)) == (u, s)
    {
      var v := Uniform(b - a);
      assert UniformModel.ProbUniform(b-a)(old(s)) == (v, s);
      assert UniformModel.ProbUniformInterval(a, b)(old(s)) == (a + v, s);
      u := a + v;
    }

  }

  trait {:termination false} IUnif extends Base {

    method Unif(n: nat) returns (u: nat)
      modifies this
      ensures UniformModel.ProbUnif(n)(old(s)) == (u, s)

  }
}
