/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

package DafnyLibraries;

import java.security.SecureRandom;
import java.math.BigInteger;

class DRandomFoundational extends _ExternBase_DRandomFoundational {
  private SecureRandom s;

  public DRandomFoundational() {
    this.s = new SecureRandom();
  }

  @Override
  public boolean Coin() {
    return s.nextBoolean();
  }
}

class DRandomExternUniform extends _ExternBase_DRandomExternUniform {
  private SecureRandom s;

  public DRandomExternUniform() {
    this.s = new SecureRandom();
  }

  @Override
  public boolean Coin() {
    return s.nextBoolean();
  }

  @Override
  public int Uniform(int n) {
    return s.nextInt(n);
  }
}

