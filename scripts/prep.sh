#!/bin/bash

VERSION=https://github.com/dafny-lang/dafny/releases/download/v4.4.0/dafny-4.4.0-x64-ubuntu-20.04.zip

wget $VERSION
unzip `basename $VERSION` 

set -o pipefail
          curl -sSfL https://github.com/leanprover/elan/releases/download/v1.4.2/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
          ./elan-init -y --default-toolchain none
          echo "$HOME/.elan/bin" >> $GITHUB_PATH
