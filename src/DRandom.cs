/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

using System;

namespace DafnyLibraries {
  public partial class DRandom : DRandomTrait {
    private Random r;

    public DRandom() {
      this.r = new Random();
    }

    public bool Coin() {
      return this.r.Next(2) == 0;
    }
  }
}


