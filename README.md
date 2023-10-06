# VMC: a Library for Verified Monte Carlo Algorithms

The `DafnyVMC` module introduces utils for probabilistic reasoning in Dafny. At the moment, the API is intentionally limited in scope, and only supports compilation to C# and Java. For the future, we plan to extend both the functionality and the range of supported languages.

To run the examples in the `docs` directory, use one of the following commands:

```bash
# C# ExamplesFoundational
$ dafny build docs/dafny/ExamplesFoundational.dfy --target:cs src/interop/cs/DRandomCoin.cs src/interop/cs/DRandomUniform.cs dfyconfig.toml --no-verify
$ dotnet docs/dafny/ExamplesFoundational.dll
# C# ExamplesExternUniform
$ dafny build docs/dafny/ExamplesExternUniform.dfy --target:cs src/interop/cs/DRandomCoin.cs src/interop/cs/DRandomUniform.cs dfyconfig.toml --no-verify
$ dotnet docs/dafny/ExamplesExternUniform.dll
# Java ExamplesFoundational
$ dafny build docs/dafny/ExamplesFoundational.dfy --target:java src/interop/java/DRandomCoin.java src/interop/java/DRandomUniform.java dfyconfig.toml --no-verify
$ java -jar docs/dafny/ExamplesFoundational.jar
# Java ExamplesExternUniform
$ dafny build docs/dafny/ExamplesExternUniform.dfy --target:java src/interop/java/DRandomCoin.java src/interop/java/DRandomUniform.java dfyconfig.toml --no-verify
$ java -jar docs/dafny/ExamplesExternUniform.jar
```

# Testing

To run the statistical tests in the `tests` diretory, use one of the following commands:

```bash
# C# TestsFoundational
$ dafny test --target:cs src/interop/cs/DRandomCoin.cs src/interop/cs/DRandomUniform.cs tests/TestsFoundational.dfy tests/Tests.dfy dfyconfig.toml --no-verify 
# C# TestsExternUniform
$ dafny test --target:cs src/interop/cs/DRandomCoin.cs src/interop/cs/DRandomUniform.cs tests/TestsExternUniform.dfy tests/Tests.dfy dfyconfig.toml --no-verify 
# Java TestsFoundational
$ dafny test --target:java src/interop/cs/DRandomCoin.java src/interop/cs/DRandomUniform.java tests/TestsFoundational.dfy tests/Tests.dfy dfyconfig.toml --no-verify 
# Java TestsExternUniform
$ dafny test --target:java src/interop/cs/DRandomCoin.java src/interop/cs/DRandomUniform.java tests/TestsExternUniform.dfy tests/Tests.dfy dfyconfig.toml --no-verify 

```
