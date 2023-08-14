# Probability Library

The `Random` module introduces utils for probabilistic reasoning in Dafny. At the moment, the API is intentionally limited in scope, and only supports compilation to Java. For the future, we plan to extend both the functionality and the range of supported languages.

To use `Random` in your code, you must:

1. `include` and `import` the `Random` module (either from `Verified/` or `Unverified/`) as you would any other library module
2. incorporate the corresponding language-specific implementation file (that is, currently, `Random.java`) when building or running your program

For example, to run the `RandomExamples.dfy` file in the `Examples` directory with the (unverified) `Random` module, run the following.

```bash
# Java
$ dafny run RandomExamples.dfy --target:java --input Unverified/Random.java
```

(If you aren't using `dafny run` to run your program,
then you should instead integrate the appropriate language-specific implementation file in your build system.)