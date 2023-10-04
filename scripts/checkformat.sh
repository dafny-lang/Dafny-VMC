#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

echo "Checking the formatting of all Dafny files..."
echo "Run \`DAFNY=dafny scripts/format.sh\` to fix any errors."
$DAFNY format --check dfyconfig.toml
