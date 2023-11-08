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
time $DAFNY test --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniformPowerOfTwo.$TARGET_LANG tests/TestsFoundational.dfy tests/Tests.dfy dfyconfig.toml --no-verify
echo "Running tests/TestsExternUniform.dfy:"
time $DAFNY test --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniformPowerOfTwo.$TARGET_LANG tests/TestsExternUniformPowerOfTwo.dfy tests/Tests.dfy dfyconfig.toml  --no-verify

echo Running $TARGET_LANG documentation...

echo "Building docs/dafny/ExamplesFoundational.dfy..." 
$DAFNY build docs/dafny/ExamplesFoundational.dfy --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniformPowerOfTwo.$TARGET_LANG dfyconfig.toml --no-verify
echo "Executing compiled docs/dafny/ExamplesFoundational.dfy:" 

echo "Building docs/dafny/ExamplesExternUniformPowerOfTwo.dfy..." 
$DAFNY build docs/dafny/ExamplesExternUniformPowerOfTwo.dfy --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniformPowerOfTwo.$TARGET_LANG dfyconfig.toml --no-verify
echo "Executing compiled docs/dafny/ExamplesExternUniformPowerOfTwo.dfy:" 