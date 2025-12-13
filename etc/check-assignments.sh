#!/bin/bash

## Generate assignment outputs and compile them

set -eu

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
# run from repository root
cd "$DIR/.."

assignments=src/sys_verif/assignments

./etc/template exercise src/sys_verif/rocq/assignment1_part2.v \
  --output $assignments/assignment1_part2_ex.v
./etc/template solution src/sys_verif/rocq/assignment1_part2.v \
  --output $assignments/assignment1_part2_soln.v
make $assignments/assignment1_part2_ex.vo $assignments/assignment1_part2_soln.vo
