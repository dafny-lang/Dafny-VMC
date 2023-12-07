# VMC: a Library for Verified Monte Carlo Algorithms

The `DafnyVMC` module introduces utils for probabilistic reasoning in Dafny. At the moment, the API is intentionally limited in scope, and only supports compilation to Java. For the future, we plan to extend both the functionality and the range of supported languages.

There are two ways to use the library:
- The trait `DRandomFoundational` only needs fair coin flips as a primitive.
- The trait `DRandomExternUniformPowerOfTwo` also uses an external implementation of uniformly distributed random numbers.

To run the examples in the `docs` directory, use one of the following commands:

```bash
# Java Examples Foundational
$ dafny build docs/dafny/ExamplesFoundational.dfy --target:java src/interop/java/DRandomCoin.java src/interop/java/DRandomUniformPowerOfTwo.java dfyconfig.toml --no-verify
$ java -jar docs/dafny/ExamplesFoundational.jar
# Java Examples ExternUniformPowerOfTwo
$ dafny build docs/dafny/ExamplesExternUniformPowerOfTwo.dfy --target:java src/interop/java/DRandomCoin.java src/interop/java/DRandomUniformPowerOfTwo.java dfyconfig.toml --no-verify
$ java -jar docs/dafny/ExamplesExternUniformPowerOfTwo.jar
```

# Testing

To run the statistical tests in the `tests` diretory, use one of the following commands:

```bash
# Java Tests Foundational
$ dafny test --target:java src/interop/java/DRandomCoin.java src/interop/java/DRandomUniformPowerOfTwo.java tests/TestsFoundational.dfy tests/Tests.dfy dfyconfig.toml --no-verify
# Java Tests ExternUniformPowerOfTwo
$ dafny test --target:java src/interop/java/DRandomCoin.java src/interop/java/DRandomUniformPowerOfTwo.java tests/TestsExternUniformPowerOfTwo.dfy tests/Tests.dfy dfyconfig.toml --no-verify
```
