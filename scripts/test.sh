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
time $DAFNY test --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG tests/TestsFoundational.dfy tests/Tests.dfy dfyconfig.toml --no-verify
echo "Running tests/TestsExternUniform.dfy:"
time $DAFNY test --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG tests/TestsExternUniform.dfy tests/Tests.dfy dfyconfig.toml  --no-verify

echo Running $TARGET_LANG documentation...

echo "Building docs/dafny/ExamplesFoundational.dfy..." 
$DAFNY build docs/dafny/ExamplesFoundational.dfy --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG dfyconfig.toml --no-verify
echo "Executing compiled docs/dafny/ExamplesFoundational.dfy:" 
if [ $TARGET_LANG==cs ]
then
  dotnet docs/dafny/ExamplesFoundational.dll
else
  java -cp ExamplesFoundational-java:ExamplesFoundational-java/DafnyRuntime.jar ExamplesFoundational
fi

echo "Building docs/dafny/ExamplesExternUniform.dfy..." 
$DAFNY build docs/dafny/ExamplesExternUniform.dfy --target:$TARGET_LANG src/interop/$TARGET_LANG/DRandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/DRandomUniform.$TARGET_LANG dfyconfig.toml --no-verify
echo "Executing compiled docs/dafny/ExamplesExternUniform.dfy:" 
if [ $TARGET_LANG==cs ]
then
  dotnet docs/dafny/ExamplesExternUniform.dll
else
  java -cp ExamplesExternUniform-java:ExamplesExternUniform-java/DafnyRuntime.jar ExamplesExternUniform
fi