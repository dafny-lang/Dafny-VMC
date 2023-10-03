#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

echo "Formatting all Dafny files..."
$DAFNY format dfyconfig.toml
