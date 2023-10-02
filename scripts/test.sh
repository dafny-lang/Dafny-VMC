#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

if [ -z ${TARGET_LANG+x} ]
then
  echo "Set the TARGET_LANG variable"
  exit 1
fi

echo Running $TARGET_LANG tests...
echo "Running tests/TestsFoundational.dfy:"
time $DAFNY test --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG tests/TestsFoundational.dfy
echo "Running tests/TestsExternUniform.dfy:"
time $DAFNY test --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG tests/TestsExternUniform.dfy

echo Running $TARGET_LANG documentation...
echo "Running docs/ExamplesFoundational.dfy"
$DAFNY run docs/dafny/ExamplesFoundational.dfy --target:$TARGET_LANG --input src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG --input src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG
echo "docs/ExamplesExternUniform.dfy"
$DAFNY run docs/dafny/ExamplesExternUniform.dfy --target:$TARGET_LANG --input src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG --input src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG
