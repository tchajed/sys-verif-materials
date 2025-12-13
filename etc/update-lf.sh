#!/bin/bash

set -eu

# src/software_foundations is the *.v files from lf.tgz, with some caveats:
# - no *Test.v files, which produce autograder output
# - the lf/ directory level is removed

wget --no-verbose -O - 'https://softwarefoundations.cis.upenn.edu/lf-current/lf.tgz' |
  gtar --warning=no-unknown-keyword -z -xf - --wildcards "*.v" "*/LICENSE"

rm lf/*Test.v

mkdir -p src/software_foundations
mv lf/* src/software_foundations/
rm -r lf
