import DafnyVMC

def main():

    # STANDARD RNG
    print("\nSTANDARD RNG TESTS\n")
        
    r = DafnyVMC.Random()

    for i in range(1, 1000): 
        print("Testing Uniform("+str(i)+")")
        print(r.UniformSample(i))

        for j in range(1, i+1):
            print("Testing Bernoulli("+str(i)+"/"+str(j)+")\n")
            print(r.BernoulliSample(i, j), end="\n")
            print("Testing Bernoulli("+str(j)+"/"+str(i)+")\n")
            print(r.BernoulliSample(j, i), end="\n")

            print("Testing BernoulliExpNeg("+str(i)+"/"+str(j)+")\n")
            print(r.BernoulliExpNegSample(i, j), end="\n")
            print("Testing BernoulliExpNeg("+str(j)+"/"+str(i)+")\n")
            print(r.BernoulliExpNegSample(j, i), end="\n")

            print("Testing DiscreteGaussian("+str(i)+"/"+str(j)+")\n")
            print(r.DiscreteGaussianSample(i, j), end="\n")
            print("Testing DiscreteGaussian("+str(j)+"/"+str(i)+")\n")
            print(r.DiscreteGaussianSample(j, i), end="\n")

            print("Testing DiscreteLaPlace("+str(i)+"/"+str(j)+")\n")
            print(r.DiscreteLaplaceSample(i, j), end="\n")
            print("Testing DiscreteLaPlace("+str(j)+"/"+str(i)+")\n")
            print(r.DiscreteLaplaceSample(j, i), end="\n")

if __name__ == "__main__":
    main()