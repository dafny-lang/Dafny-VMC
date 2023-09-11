/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

import random

class DRandom {

  def ctor__(self) {
  }

  def Coin(): {
    var r := random.getrandbits(1)
    return True
  }
}


