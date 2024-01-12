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
echo "Running tests/TestsRandomCoin.dfy:"
time $DAFNY test --target:$TARGET_LANG src/interop/$TARGET_LANG/Minus/RandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/RandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/Minus/Random.$TARGET_LANG src/interop/$TARGET_LANG/Random.$TARGET_LANG tests/TestsRandomCoin.dfy tests/Tests.dfy dfyconfig.toml --no-verify
echo "Running tests/TestsRandom.dfy:"
time $DAFNY test --target:$TARGET_LANG src/interop/$TARGET_LANG/Minus/RandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/RandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/Minus/Random.$TARGET_LANG src/interop/$TARGET_LANG/Random.$TARGET_LANG tests/TestsRandom.dfy tests/Tests.dfy dfyconfig.toml  --no-verify

echo Running $TARGET_LANG documentation...

echo "Building docs/dafny/ExamplesRandomCoin.dfy..." 
$DAFNY build docs/dafny/ExamplesRandomCoin.dfy --target:$TARGET_LANG src/interop/$TARGET_LANG/Minus/RandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/RandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/Minus/Random.$TARGET_LANG src/interop/$TARGET_LANG/Random.$TARGET_LANG  dfyconfig.toml --no-verify
echo "Executing compiled docs/dafny/ExamplesRandomCoin.dfy:" 
if [ "$TARGET_LANG" = "java" ]
then
  java -jar docs/dafny/ExamplesRandomCoin.jar
fi

echo "Building docs/dafny/ExamplesRandom.dfy..." 
$DAFNY build docs/dafny/ExamplesRandom.dfy --target:$TARGET_LANG src/interop/$TARGET_LANG/Minus/RandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/RandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/Minus/Random.$TARGET_LANG src/interop/$TARGET_LANG/Random.$TARGET_LANG  dfyconfig.toml --no-verify
echo "Executing compiled docs/dafny/ExamplesRandom.dfy:" 
if [ "$TARGET_LANG" = "java" ]
then
  java -jar docs/dafny/ExamplesRandom.jar
fi