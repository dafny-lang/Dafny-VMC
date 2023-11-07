/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

using System.Security.Cryptography;
using System.Numerics;

namespace Coin_mInterface {

    public class DRandomCoin {

      protected static RandomNumberGenerator rng = RandomNumberGenerator.Create();

      public static bool Coin() {
        return rng.GetInt32(2) == 0;
      }

  }

}