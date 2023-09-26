#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

echo Running C\# tests...
echo "Running tests/TestsFoundational.dfy:"
time $DAFNY test --target:cs src/DRandomCoin.cs src/DRandomUniform.cs tests/TestsFoundational.dfy
echo "Running tests/TestsExternUniform.dfy:"
time $DAFNY test --target:cs src/DRandomCoin.cs src/DRandomUniform.cs tests/TestsExternUniform.dfy

echo Running C\# documentation...
echo "Running docs/ExamplesFoundational.dfy"
$DAFNY run docs/ExamplesFoundational.dfy --target:cs --input src/DRandomCoin.cs --input src/DRandomUniform.cs
echo "docs/ExamplesExternUniform.dfy"
$DAFNY run docs/ExamplesExternUniform.dfy --target:cs --input src/DRandomCoin.cs --input src/DRandomUniform.cs

echo Running Java tests...
echo "Running tests/TestsFoundational.dfy:"
$DAFNY test --target:java src/DRandomCoin.java src/DRandomUniform.java tests/TestsFoundational.dfy
echo "Running tests/TestsExternUniform.dfy:"
$DAFNY test --target:java src/DRandomCoin.java src/DRandomUniform.java tests/TestsExternUniform.dfy

echo Running Java documentation...
echo "Running docs/ExamplesFoundational.dfy"
$DAFNY run docs/ExamplesFoundational.dfy --target:java --input src/DRandomCoin.java --input src/DRandomUniform.java
echo "Running tests/TestsExternUniform.dfy:"
$DAFNY run docs/ExamplesExternUniform.dfy --target:java --input src/DRandomCoin.java --input src/DRandomUniform.java