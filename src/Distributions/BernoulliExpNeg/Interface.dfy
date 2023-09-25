/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

module IBernoulliExpNeg {
  trait {:termination false} IBernoulliExpNeg {

    method BernoulliExpNeg(gamma: real) returns (c: bool)
      modifies this
      decreases *
      requires gamma >= 0.0

}
}
