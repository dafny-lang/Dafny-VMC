import DafnyVMC

def main():
    arr1 = [0, 1, 2]
    arr2 = [float(0), float(1), float(2)]
    arr3 = ["aa", "bb", "cc"]
    arr4 = ['a', 'b', 'c']
    arr5 = [True, False, False, True]
    num = 1
    den = 1000

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

    print("Example of Fisher-Yates: int")
    arr1 = r.Shuffle(arr1)
    print(arr1)

    print("Example of Fisher-Yates: float")
    arr2 = r.Shuffle(arr2)
    print(arr2)

    print("Example of Fisher-Yates: str")
    arr3 = r.Shuffle(arr3)
    print(arr3)

    print("Example of Fisher-Yates: char/str")
    arr4 = r.Shuffle(arr4)
    print(arr4)

    print("Example of Fisher-Yates: boolean")
    arr5 = r.Shuffle(arr5)
    print(arr5)

if __name__ == "__main__":
    main()