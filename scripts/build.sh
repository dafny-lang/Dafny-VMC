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

$DAFNY build --target:$TARGET_LANG src/interop/$TARGET_LANG/DafnyVMC.$TARGET_LANG src/interop/$TARGET_LANG/Random.$TARGET_LANG src/DafnyVMC.dfy -o build/$TARGET_LANG/DafnyVMC dfyconfig.toml --no-verify