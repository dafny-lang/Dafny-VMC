/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

using System;
using System.Numerics;

namespace DafnyLibraries {
  public partial class DRandomFoundational {
    private Random r;

    public DRandomFoundational() {
      this.r = new Random();
    }

    public bool Coin() {
      return this.r.Next(2) == 0;
    }
  }

  public partial class DRandomExternUniform {
    private Random r;

    public DRandomExternUniform() {
      this.r = new Random();
    }

    public bool Coin() {
      return this.r.Next(2) == 0;
    }

    public BigInteger Uniform(BigInteger n) {
      return new BigInteger(this.r.Next((int) n));
    }
  }  
}

