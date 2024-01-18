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
echo "Running tests/TestsRandom.dfy:"
time $DAFNY test --target:$TARGET_LANG src/interop/$TARGET_LANG/Extern/Random.$TARGET_LANG tests/TestsRandom.dfy tests/Tests.dfy src/DafnyVMC.dfy src/DafnyVMCTrait.dfy dfyconfig.toml  --no-verify

echo Running $TARGET_LANG documentation...

echo "Building docs/dafny/ExamplesRandom.dfy..." 
$DAFNY build docs/dafny/ExamplesRandom.dfy --target:$TARGET_LANG src/interop/$TARGET_LANG/Extern/Random.$TARGET_LANG src/DafnyVMC.dfy src/DafnyVMCTrait.dfy  dfyconfig.toml --no-verify
echo "Executing compiled docs/dafny/ExamplesRandom.dfy:" 
if [ "$TARGET_LANG" = "java" ]
then
  java -jar docs/dafny/ExamplesRandom.jar
fi