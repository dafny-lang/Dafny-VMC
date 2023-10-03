# VMC: a Library for Verified Monte Carlo Algorithms

The `DafnyVMC` module introduces utils for probabilistic reasoning in Dafny. At the moment, the API is intentionally limited in scope, and only supports compilation to C# and Java. For the future, we plan to extend both the functionality and the range of supported languages.

To use `DafnyVMC` in your code, you must:

1. `include` and `import` the `DafnyVMC` module as you would any other library module
2. incorporate the corresponding language-specific implementation file when building or running your program

For example, to run the examples in the `docs` directory, run one of the following.

```bash
# C#
$ dafny run docs/dafny/ExamplesFoundational.dfy --target:cs --input src/interop/cs/DRandomCoin.cs --input src/interop/cs/DRandomUniform.cs
$ dafny run docs/dafny/ExamplesExternUniform.dfy --target:cs --input src/interop/cs/DRandomCoin.cs --input src/interop/cs/DRandomUniform.cs
# Java
$ dafny run docs/dafny/ExamplesFoundational.dfy --target:java --input src/interop/java/DRandomCoin.java --input src/interop/java/DRandomUniform.java
$ dafny run docs/dafny/ExamplesExternUniform.dfy --target:java --input src/interop/java/DRandomCoin.java --input src/interop/java/DRandomUniform.java
```

(If you aren't using `dafny run` to run your program,
then you should instead integrate the appropriate language-specific implementation file in your build system.)

# Testing

To run the statistical tests, run one of the following:

```bash
# C#
$ dafny test --target:cs src/interop/cs/DRandomCoin.cs src/interop/cs/DRandomUniform.cs tests/TestsFoundational.dfy
$ dafny test --target:cs src/interop/cs/DRandomCoin.cs src/interop/cs/DRandomUniform.cs tests/TestsExternUniform.dfy
# Java#
$ dafny test --target:java src/interop/cs/DRandomCoin.java src/interop/cs/DRandomUniform.java tests/TestsFoundational.dfy
$ dafny test --target:java src/interop/cs/DRandomCoin.java src/interop/cs/DRandomUniform.java tests/TestsExternUniform.dfy

```
