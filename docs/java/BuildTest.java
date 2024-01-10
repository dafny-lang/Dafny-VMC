import DafnyVMC.*;
import dafny.TypeDescriptor;
import java.math.BigInteger;
import java.util.Arrays;

class Check {
    public static void main(String[] args) {
        DRandomExternUniformPowerOfTwo d = new DRandomExternUniformPowerOfTwo();

        // Example of Uniform sampling
        System.out.println(d.UniformSample(BigInteger.valueOf(4)));

        // Example of Fisher-Yates: BigInteger
        BigInteger[] arr1 = {BigInteger.valueOf(0), BigInteger.valueOf(1), BigInteger.valueOf(2)};
        d.Shuffle(TypeDescriptor.BIG_INTEGER, arr1);
        System.out.println(Arrays.toString(arr1));

        // Example of Fisher-Yates: int
        int[] arr2 = {0, 1, 2};
        d.Shuffle(TypeDescriptor.INT, arr2);
        System.out.println(Arrays.toString(arr2));

        // Example of Fisher-Yates: String
        String[] arr3 = {"aa", "bb", "cc"};
        d.Shuffle(TypeDescriptor.CHAR_ARRAY, arr3);
        System.out.println(Arrays.toString(arr3));

        // Example of Fisher-Yates: char
        char[] arr4 = {'a', 'b', 'c'};
        d.Shuffle(TypeDescriptor.CHAR, arr4);
        System.out.println(Arrays.toString(arr4));

    }
}