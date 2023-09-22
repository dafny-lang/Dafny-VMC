# VMC: a Library for Verified Monte Carlo Algorithms

The `DRandom` module introduces utils for probabilistic reasoning in Dafny. At the moment, the API is intentionally limited in scope, and only supports compilation to Java. For the future, we plan to extend both the functionality and the range of supported languages.

To use `DRandom` in your code, you must:

1. `include` and `import` the `DRandom` module as you would any other library module
2. incorporate the corresponding language-specific implementation file when building or running your program

For example, to run the `Examples.dfy` file in the `Examples` directory with the `DRandom` module, run one of the following.

```bash
# Java
$ dafny run Examples.dfy --target:java --input ../Library/DRandom.java
# C#
$ dafny run Examples.dfy --target:cs --input ../Library/DRandom.cs
```

(If you aren't using `dafny run` to run your program,
then you should instead integrate the appropriate language-specific implementation file in your build system.)

# Testing

To run the statistical tests in `Library/Tests.dfy`, run one of the following:

```bash
# Java
$ dafny test --target:java Library/DRandom.java Library/Tests.dfy
# C#
$ dafny test --target:cs Library/DRandom.cs Library/Tests.dfy
```
