# VMC: a Library for Verified Monte Carlo Algorithms

The `DRandom` module introduces utils for probabilistic reasoning in Dafny. At the moment, the API is intentionally limited in scope, and only supports compilation to Java. For the future, we plan to extend both the functionality and the range of supported languages.

To use `DRandom` in your code, you must:

1. `include` and `import` the `DRandom` module as you would any other library module
2. incorporate the corresponding language-specific implementation file when building or running your program

For example, to run the examples in the `docs` directory, run one of the following.

```bash
# C#
$ dafny run docs/ExamplesFoundational.dfy --target:cs --input src/DRandomCoin.cs --input src/DRandomUniform.cs
$ dafny run docs/ExamplesExternUniform.dfy --target:cs --input src/DRandomCoin.cs --input src/DRandomUniform.cs
# Java
$ dafny run docs/ExamplesFoundational.dfy --target:java --input src/DRandomCoin.java --input src/DRandomUniform.java
$ dafny run docs/ExamplesExternUniform.dfy --target:java --input src/DRandomCoin.java --input src/DRandomUniform.java
```

(If you aren't using `dafny run` to run your program,
then you should instead integrate the appropriate language-specific implementation file in your build system.)

# Testing

To run the statistical tests, run one of the following:

```bash
# C#
$ dafny test --target:cs src/DRandomCoin.cs src/DRandomUniform.cs tests/TestsFoundational.dfy
$ dafny test --target:cs src/DRandomCoin.cs src/DRandomUniform.cs tests/TestsExternUniform.dfy
# Java#
$ dafny test --target:java src/DRandomCoin.java src/DRandomUniform.java tests/TestsFoundational.dfy
$ dafny test --target:java src/DRandomCoin.java src/DRandomUniform.java tests/TestsExternUniform.dfy

```
