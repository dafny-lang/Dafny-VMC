/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

package DafnyLibraries;

import java.security.SecureRandom;
import java.math.BigInteger;

public class Random extends _ExternBase_Random {
  private SecureRandom s;

  public Random() {
    this.s = new SecureRandom();
  }

  @Override
  public boolean Coin() {
    return s.nextBoolean();
  }
}
