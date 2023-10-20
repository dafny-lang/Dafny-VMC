/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Model {
  import Monad
  import Rationals

  ghost function Sample(scale: Rationals.Rational): Monad.Hurd<int> 
    requires scale.numer >= 1

}
