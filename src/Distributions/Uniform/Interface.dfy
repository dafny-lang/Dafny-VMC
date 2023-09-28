/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Base/Interface.dfy"
include "../UniformPowerOfTwo/Interface.dfy"
include "Model.dfy"

module UniformInterface {
  import BaseInterface
  import UniformModel
  import UniformPowerOfTwoInterface

  trait {:termination false} IUniform extends BaseInterface.TBase, UniformPowerOfTwoInterface.IUniformPowerOfTwo {

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
}
