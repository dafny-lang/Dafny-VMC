#!/bin/bash

set -e

if [ -z ${DAFNY+x} ]
then
  echo "Set the DAFNY variable"
  exit 1
fi

$DAFNY audit dfyconfig.toml | grep -v '{:termination false}\|{:extern}\|decreases *\|Dafny auditor completed\|Dafny program verifier\|No terms found to trigger on\|Compiled declaration has no body' | sed 's/Warning: //' | sed 's/Possible mitigation: .*//' | sed '/^$/d' | sort > audit.log
