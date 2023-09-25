/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

trait IBernoulliExpNeg {

  method BernoulliExpNeg(gamma: real) returns (c: bool)
    modifies this
    decreases *
    requires gamma >= 0.0

}
