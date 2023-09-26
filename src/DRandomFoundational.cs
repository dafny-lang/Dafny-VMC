/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

using System;

namespace DafnyLibraries {
  public partial class DRandomFoundational : BaseInterface.TBase, UniformImplementation.TUnif, BernoulliImplementation.TBernoulli, GeometricImplementation.TGeometric, UniformImplementation.TUniformFoundational, BernoulliExpNegImplementation.TBernoulliExpNeg, DiscreteGaussianImplementation.TDiscreteGaussian, DiscreteLaplaceImplementation.TDiscreteLaplace {
    private Random r;

    public DRandomFoundational() {
      this.r = new Random();
    }

    public bool Coin() {
      return this.r.Next(2) == 0;
    }
  }
}

