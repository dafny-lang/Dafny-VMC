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

if [ "$TARGET_LANG" = "java" ]
then
  $DAFNY build --target:$TARGET_LANG src/interop/$TARGET_LANG/Full/Random.$TARGET_LANG src/interop/$TARGET_LANG/Full/CustomRandom.$TARGET_LANG src/interop/$TARGET_LANG/Part/Random.$TARGET_LANG -o build/$TARGET_LANG/DafnyVMC dfyconfig.toml --no-verify
else
  $DAFNY build --target:$TARGET_LANG src/interop/$TARGET_LANG/Full/Random.$TARGET_LANG src/interop/$TARGET_LANG/Part/Random.$TARGET_LANG -o build/$TARGET_LANG/DafnyVMC dfyconfig.toml --no-verify
fi
