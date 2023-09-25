/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

using System;

public partial class DRandomFoundational : DRandomTrait {
  private Random r;

  public DRandomFoundational() {
    this.r = new Random();
  }

  public bool Coin() {
    return this.r.Next(2) == 0;
  }
}
