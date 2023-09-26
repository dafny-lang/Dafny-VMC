#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

if [ -z ${LANG+x} ]
then
  echo "Set the LANG variable"
  exit 1
fi

echo Running $LANG tests...
echo "Running tests/TestsFoundational.dfy:"
time $DAFNY test --target:$LANG interop/$LANG/DRandomCoin.$LANG interop/$LANG/DRandomUniform.$LANG tests/TestsFoundational.dfy
echo "Running tests/TestsExternUniform.dfy:"
time $DAFNY test --target:$LANG interop/$LANG/DRandomCoin.$LANG interop/$LANG/DRandomUniform.$LANG tests/TestsExternUniform.dfy

echo Running $LANG documentation...
echo "Running docs/ExamplesFoundational.dfy"
$DAFNY run docs/ExamplesFoundational.dfy --target:$LANG --input interop/$LANG/DRandomCoin.$LANG --input interop/$LANG/DRandomUniform.$LANG
echo "docs/ExamplesExternUniform.dfy"
$DAFNY run docs/ExamplesExternUniform.dfy --target:$LANG --input interop/$LANG/DRandomCoin.$LANG --input interop/$LANG/DRandomUniform.$LANG

# echo Running Java tests...
# echo "Running tests/TestsFoundational.dfy:"
# $DAFNY test --target:java interop/java/DRandomCoin.java interop/java/DRandomUniform.java tests/TestsFoundational.dfy
# echo "Running tests/TestsExternUniform.dfy:"
# $DAFNY test --target:java interop/java/DRandomCoin.java interop/java/DRandomUniform.java tests/TestsExternUniform.dfy

# echo Running Java documentation...
# echo "Running docs/ExamplesFoundational.dfy"
# $DAFNY run docs/ExamplesFoundational.dfy --target:java --input interop/java/DRandomCoin.java --input interop/java/DRandomUniform.java
# echo "Running tests/TestsExternUniform.dfy:"
# $DAFNY run docs/ExamplesExternUniform.dfy --target:java --input interop/java/DRandomCoin.java --input interop/java/DRandomUniform.java