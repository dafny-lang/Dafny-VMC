/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Model {
  import Monad
  import Rand
  import Permutations

  // TODO: add correct version
  function Shuffle<T>(xs: seq<T>): (f: Monad.Hurd<seq<T>>) {
    (s: Rand.Bitstream) =>
      Monad.Result(xs, s)
  }

}