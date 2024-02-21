# VMC: a Library for Verified Monte Carlo Algorithms

The `DafnyVMC` module introduces utils for probabilistic reasoning in Dafny. At the moment, the API is intentionally limited in scope, and only supports compilation to Java. For the future, we plan to extend both the functionality and the range of supported languages.

## Java API Example

```java
import DafnyVMC.Random;
import java.math.BigInteger;
import java.util.Arrays;

class Test {
  public static void main(String[] args) {
    DafnyVMC.Random r = new DafnyVMC.Random();

    System.out.println("Example of Fisher-Yates shuffling");
    char[] arr = {'a', 'b', 'c'};
    r.Shuffle(arr);
    System.out.println(Arrays.toString(arr));
  
    System.out.println("Example of Bernoulli sampling");
    BigInteger num = BigInteger.valueOf(3);
    BigInteger den = BigInteger.valueOf(5);
    System.out.println(r.BernoulliSample(num,den));
  }
}
```

## Dafny Examples

To run the examples in the `docs/dafny` directory, use the following commands:

```bash
$ dafny build docs/dafny/ExamplesRandom.dfy --target:java src/interop/java/Full/Random.java src/interop/java/Part/Random.java dfyconfig.toml --no-verify
$ java -jar docs/dafny/ExamplesRandom.jar
```

## Java Examples

To run the examples in the `docs/java` directory, use the following commands:

```bash
$ export TARGET_LANG=java
$ bash scripts/build.sh
$ bash build/java/run.sh 
```

## Dafny Testing

To run the statistical tests in the `tests` directory, use the following commands:

```bash
$ dafny test --target:java src/interop/java/Full/Random.java src/interop/java/Part/Random.java tests/TestsRandom.dfy tests/Tests.dfy dfyconfig.toml --no-verify
```



