#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

export LEAN_NUM_THREADS=1
lean --version
lake --version
printf 'Mathlib revision: '
git -C .lake/packages/mathlib rev-parse HEAD
nice -n 10 lake build
nice -n 10 lake env lean -DwarningAsError=true Audit.lean
printf '%s\n' 'Axiom guards passed: only the listed standard Lean foundations.' \
  'Verified scope: the 136 optimum for the full 56-tile coloured model, including the upper bound without connectedness and a checked historical construction.' \
  'Model conditions: exact numbered inventory, rotations only, matching sides, once-traced scored loops, and no holes.'
