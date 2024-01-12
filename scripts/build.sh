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

$DAFNY build --target:$TARGET_LANG src/interop/$TARGET_LANG/Minus/RandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/RandomCoin.$TARGET_LANG src/interop/$TARGET_LANG/Minus/Random.$TARGET_LANG src/interop/$TARGET_LANG/Random.$TARGET_LANG src/Dafny-VMC.dfy -o build/$TARGET_LANG/Dafny-VMC dfyconfig.toml --no-verify