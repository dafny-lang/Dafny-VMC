import DafnyVMC

def main():

    # STANDARD RNG
    print("\nSTANDARD RNG TESTS\n")
        
    r = DafnyVMC.Random()

    for i in range(1, 1000): 
        print("Testing Uniform("+str(i)+")")
        print(r.UniformSample(i))

        for j in range(1, 1000):
            print("Testing Bernoulli("+str(i)+"/"+str(j)+")\n")
            print(r.BernoulliSample(i, j), end="\n")

            print("Testing BernoulliExpNeg("+str(i)+"/"+str(j)+")\n")
            print(r.BernoulliExpNegSample(i, j), end="\n")

            print("Testing DiscreteGaussian("+str(i)+"/"+str(j)+")\n")
            print(r.DiscreteGaussianSample(i, j, 7), end="\n")

            print("Testing DiscreteLaPlace("+str(i)+"/"+str(j)+")\n")
            print(r.DiscreteLaplaceSample(i, j), end="\n")

    # Edge cases    
    print("Testing Bernoulli(1000000, 1)\n")
    print(r.BernoulliSample(1000000, 1), end="\n")
    print("Testing Bernoulli(1, 1000000)\n")
    print(r.BernoulliSample(1, 1000000), end="\n")

    print("Testing BernoulliExpNeg(1000000, 1)\n")
    print(r.BernoulliExpNegSample(1000000, 1), end="\n")
    print("Testing BernoulliExpNeg(1, 1000000)\n")
    print(r.BernoulliExpNegSample(1, 1000000), end="\n")

    print("Testing DiscreteGaussianSample(1000000, 1)\n")
    print(r.DiscreteGaussianSample(1000000, 1), end="\n")
    print("Testing DiscreteGaussianSample(1, 1000000)\n")
    print(r.DiscreteGaussianSample(1, 1000000), end="\n")

    print("Testing DiscreteLaplace(1000000, 1)\n")
    print(r.DiscreteLaplaceSample(1000000, 1), end="\n")
    print("Testing DiscreteLaplace(1, 1000000)\n")
    print(r.DiscreteLaplaceSample(1, 1000000), end="\n")

if __name__ == "__main__":
    main()