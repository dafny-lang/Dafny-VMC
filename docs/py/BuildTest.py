import DafnyVMC

def main():
    arr1 = [0, 1, 2]
    arr3 = ["aa", "bb", "cc"]
    num = 3
    den = 5

    # STANDARD RNG
    print("\nSTANDARD RNG TESTS\n")
        
    r = DafnyVMC.Random()

    print("Example of Uniform sampling")
    print(r.UniformSample(4))

    print("Example of Bernoulli sampling")
    print(r.BernoulliSample(num,den))

    print("Example of BernoulliExpNeg sampling")
    print(r.BernoulliExpNegSample(num,den))

    print("Example of DiscreteGaussian sampling")
    print(r.DiscreteGaussianSample(num,den))

    print("Example of DiscreteLaplace sampling")
    print(r.DiscreteLaplaceSample(num,den))

    print("Example of Fisher-Yates: BigInteger")
    r.Shuffle(arr1)
    print(arr1)

    print("Example of Fisher-Yates: String")
    r.Shuffle(arr3)
    print(arr3)

if __name__ == "__main__":
    main()