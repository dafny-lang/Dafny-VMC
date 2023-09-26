/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

using System;
using System.Numerics;

namespace BaseInterface {

    public class DRandomCoin {

      private static Random r = new Random();

      public static bool Coin() {
        return r.Next(2) == 0;
      }

  }

}

