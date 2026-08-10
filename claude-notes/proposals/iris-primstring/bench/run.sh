#!/usr/bin/env bash
# Run from this directory with the Iris switch active (or via `opam exec`).
#!/bin/bash
# usage: run.sh N M mode...
set -u
N=$1; M=$2; shift 2
for mode in "$@"; do
  f="b_${N}_${M}_${mode}"
  python3 gen.py $f.v $N $M $mode > /dev/null
  s=$( { /usr/bin/time -f '%e %M' opam exec --switch=/shared/xv6rocq -- rocq compile -q -d hconstr $f.v > $f.log; } 2>&1 )
  tree=$(grep 'tree size' $f.log | awk '{print $4}' | sort -rn | head -1)
  bind=$(grep 'bindings'  $f.log | awk '{print $3}' | sort -rn | head -1)
  echo "$N $M $mode $tree $bind $s"
done
