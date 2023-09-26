/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

using System;
using System.Numerics;

namespace UniformImplementation {

    public class DRandomUniform {

      private static Random r = new Random();

      public static BigInteger Uniform(BigInteger n) {
      return new BigInteger(r.Next((int) n));
    }

  }

}
