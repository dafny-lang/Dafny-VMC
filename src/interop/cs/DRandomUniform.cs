/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

using System;
using System.Numerics;

namespace UniformImplementation {

    public class DRandomUniform {

      private static Random r = new Random();

      public static BigInteger UniformSample(BigInteger n) {
        // `(Int64) n` throws an `OverflowException` if `n` is too large to fit in an `Int64`
        // see https://learn.microsoft.com/en-us/dotnet/api/system.numerics.biginteger.op_explicit?view=net-7.0#system-numerics-biginteger-op-explicit(system-numerics-biginteger)-system-int64
        return new BigInteger(r.NextInt64((Int64) n));
      }

  }

}
