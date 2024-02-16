import DafnyVMC
import _dafny

def main():
    arr1 = _dafny.Array([0, 1, 2], 1)
    arr2 = _dafny.Array([float(0), float(1), float(2)], 1)
    arr3 = _dafny.Array(["aa", "bb", "cc"], 1)
    arr4 = _dafny.Array(['a', 'b', 'c'], 1)
    arr5 = _dafny.Array([True, False, False, True], 1)
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

    print("Example of Fisher-Yates: int")
    r.Shuffle(arr1)
    r.PrintArray(arr1)

    print("Example of Fisher-Yates: float")
    r.Shuffle(arr2)
    r.PrintArray(arr2)

    print("Example of Fisher-Yates: str")
    r.Shuffle(arr3)
    r.PrintArray(arr3)

    print("Example of Fisher-Yates: char/str")
    r.Shuffle(arr4)
    r.PrintArray(arr4)

    print("Example of Fisher-Yates: boolean")
    r.Shuffle(arr5)
    r.PrintArray(arr5)

if __name__ == "__main__":
    main()