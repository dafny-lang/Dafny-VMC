
module DafnyVMCTrait {
  import UniformPowerOfTwo
  import Uniform
  import Bernoulli
  import BernoulliExpNeg
  import DiscreteLaplace
  import DiscreteGaussian
  import FisherYates
  import opened Pos

  trait {:termination false} RandomTrait extends
      UniformPowerOfTwo.Implementation.Trait,
      Uniform.Implementation.Trait,
      Bernoulli.Implementation.Trait,
      BernoulliExpNeg.Implementation.Trait,
      DiscreteLaplace.Implementation.Trait,
      DiscreteGaussian.Implementation.Trait,
      FisherYates.Implementation.Trait
  {}

}
