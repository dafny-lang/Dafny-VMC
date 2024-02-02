using System;
using System.Threading;
using System.Numerics;
using DafnyVMC;

class Check {
    public static void Main(string[] args) {
        BigInteger[] arr1 = {new BigInteger(0), new BigInteger(1), new BigInteger(2)};
        int[] arr2 = {0, 1, 2};
        string[] arr3 = {"aa", "bb", "cc"};
        char[] arr4 = {'a', 'b', 'c'};
        bool[] arr5 = {true, false, false, true};
        long[] arr6 = {111111L, 333333L, 999999L};
        short[] arr7 = {-3, 0, 3};
        //var gamma = new Rationals._IRational(BigInteger(3), BigInteger(5));
        
        /* STANDARD RNG */
        Console.WriteLine("\nSTANDARD RNG TESTS\n");
        
        var r = new DafnyVMC.Random();

        Console.WriteLine("Example of Coin sampling");
        Console.WriteLine(r.CoinSample());

        Console.WriteLine("Example of Uniform sampling");
        Console.WriteLine(r.UniformSample(new BigInteger(4)));

/*         Console.WriteLine("Example of Bernoulli sampling");
        Console.WriteLine(r.BernoulliSample(gamma));

        Console.WriteLine("Example of BernoulliExpNeg sampling");
        Console.WriteLine(r.BernoulliExpNegSample(gamma));

        Console.WriteLine("Example of DiscreteGaussian sampling");
        Console.WriteLine(r.DiscreteGaussianSample(gamma));

        Console.WriteLine("Example of DiscreteLaplace sampling");
        Console.WriteLine(r.DiscreteLaplaceSample(gamma)); */

/*         Console.WriteLine("Example of Fisher-Yates: BigInteger");
        r.Shuffle(arr1);
        Console.WriteLine(Arrays.toString(arr1));
 
        Console.WriteLine("Example of Fisher-Yates: int");
        r.Shuffle(arr2);
        Console.WriteLine(Arrays.toString(arr2));

        Console.WriteLine("Example of Fisher-Yates: String");
        r.Shuffle(arr3);
        Console.WriteLine(Arrays.toString(arr3));

        Console.WriteLine("Example of Fisher-Yates: char");
        r.Shuffle(arr4);
        Console.WriteLine(Arrays.toString(arr4));

        Console.WriteLine("Example of Fisher-Yates: boolean");
        r.Shuffle(arr5);
        Console.WriteLine(Arrays.toString(arr5));

        Console.WriteLine("Example of Fisher-Yates: long");
        r.Shuffle(arr6);
        Console.WriteLine(Arrays.toString(arr6));

        Console.WriteLine("Example of Fisher-Yates: short");
        r.Shuffle(arr7);
        Console.WriteLine(Arrays.toString(arr7)); */

        /* CUSTOM RNG */
        Console.WriteLine("\nCUSTOM RNG TESTS\n");

        var rng = new System.Random();
        var t = new DafnyVMC.Random(rng);

        Console.WriteLine("Example of Coin sampling");
        Console.WriteLine(t.CoinSample());

        Console.WriteLine("Example of Uniform sampling");
        Console.WriteLine(t.UniformSample(new BigInteger(4)));

/*         Console.WriteLine("Example of Bernoulli sampling");
        Console.WriteLine(t.BernoulliSample(gamma));

        Console.WriteLine("Example of BernoulliExpNeg sampling");
        Console.WriteLine(t.BernoulliExpNegSample(gamma));

        Console.WriteLine("Example of DiscreteGaussian sampling");
        Console.WriteLine(t.DiscreteGaussianSample(gamma));

        Console.WriteLine("Example of DiscreteLaplace sampling");
        Console.WriteLine(t.DiscreteLaplaceSample(gamma)); */

/*         Console.WriteLine("Example of Fisher-Yates: BigInteger");
        t.Shuffle(arr1);
        Console.WriteLine(Arrays.toString(arr1));

        Console.WriteLine("Example of Fisher-Yates: int");
        t.Shuffle(arr2);
        Console.WriteLine(Arrays.toString(arr2));

        Console.WriteLine("Example of Fisher-Yates: String");
        t.Shuffle(arr3);
        Console.WriteLine(Arrays.toString(arr3));

        Console.WriteLine("Example of Fisher-Yates: char");
        t.Shuffle(arr4);
        Console.WriteLine(Arrays.toString(arr4));

        Console.WriteLine("Example of Fisher-Yates: boolean");
        t.Shuffle(arr5);
        Console.WriteLine(Arrays.toString(arr5));

        Console.WriteLine("Example of Fisher-Yates: long");
        t.Shuffle(arr6);
        Console.WriteLine(Arrays.toString(arr6));

        Console.WriteLine("Example of Fisher-Yates: short");
        t.Shuffle(arr7);
        Console.WriteLine(Arrays.toString(arr7)); */
    }
}