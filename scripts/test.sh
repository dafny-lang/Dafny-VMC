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
time $DAFNY test --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG tests/TestsFoundational.dfy Tests.toml --no-verify
echo "Running tests/TestsExternUniform.dfy:"
time $DAFNY test --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG tests/TestsExternUniform.dfy Tests.toml --no-verify

echo Running $TARGET_LANG documentation...
echo "Running docs/dafny/ExamplesFoundational.dfy"
$DAFNY run DocsFoundational.toml --target:$TARGET_LANG --input src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG --input src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG --no-verify
echo "Running docs/dafny/ExamplesExternUniform.dfy"
$DAFNY run DocsExternUniform.toml --target:$TARGET_LANG --input src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG --input src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG --no-verify
