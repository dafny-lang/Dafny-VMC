# VMC: a Library for Verified Monte Carlo Algorithms

The `Random` module introduces utils for probabilistic reasoning in Dafny. At the moment, the API is intentionally limited in scope, and only supports compilation to Java. For the future, we plan to extend both the functionality and the range of supported languages.

To use `Random` in your code, you must:

1. `include` and `import` the `Random` module as you would any other library module
2. incorporate the corresponding language-specific implementation file (that is, currently, `Library/Random.java`) when building or running your program

For example, to run the `Examples.dfy` file in the `Examples` directory with the `Random` module, run the following.

```bash
# Java
$ dafny run Examples.dfy --target:java --input ./Library/Random.java
```

(If you aren't using `dafny run` to run your program,
then you should instead integrate the appropriate language-specific implementation file in your build system.)
