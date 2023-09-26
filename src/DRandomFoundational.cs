/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

using System;

namespace DafnyLibraries {
  public partial class DRandomFoundational : BaseInterface.Base, UniformImplementation.Unif, BernoulliImplementation.Bernoulli, GeometricImplementation.Geometric, UniformImplementation.UniformFoundational, BernoulliExpNegImplementation.BernoulliExpNeg, DiscreteGaussianImplementation.DiscreteGaussian, DiscreteLaplaceImplementation.DiscreteLaplace {
    private Random r;

    public DRandomFoundational() {
      this.r = new Random();
    }

    public bool Coin() {
      return this.r.Next(2) == 0;
    }
  }
}

