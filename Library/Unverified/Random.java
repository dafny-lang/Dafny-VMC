/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

package DafnyLibraries;

import java.security.SecureRandom;

public class Random extends _ExternBase_Random {
  private SecureRandom s;

  public Random() {
    this.s = new SecureRandom();
  }

  public boolean Coin() {
    return s.nextBoolean();
  }

  public int Uniform(int n) {
    return s.nextInt(n);
  }

  public int UniformInterval(int a, int b) {
    return s.nextInt(a, b);
  }

}
