/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Bitstream.Interface {
  import Rand

  trait {:termination false} Trait {
    ghost var s: Rand.Bitstream
  }
}
