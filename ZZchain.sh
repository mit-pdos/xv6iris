#!/usr/bin/env bash
cd /shared/xv6iris-3-fliptree/iris
for f in "$@"; do
  timeout 1500 opam exec --switch=/shared/xv6rocq -- coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel -R ../user-rocq User -w -notation-overridden $f.v > ../ZZlocal-$f.log 2>&1
  rc=$?; echo "== $f EXIT=$rc"
  if [ $rc -ne 0 ]; then grep -n 'Error' -A 30 ../ZZlocal-$f.log | grep -v '^[0-9]*-[A-Za-z0-9_]* : \|^[0-9]*-[A-Z][a-zA-Z0-9_]*,\? [a-zA-Z0-9_, ]*: ' | head -45; fi
done
