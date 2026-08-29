#!/usr/bin/env bash
# INTR lane build driver. Runs on the GCP VM inside the synced tree.
# Emits sentinel lines: MAKEEXIT=<n>, GREEN=<g>/<n>, RED <file>, DONE
set -u
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

for d in model-xv6iris kernel-rocq user-rocq; do
  cd "$ROOT/$d"
  [ -f CoqMakefile ] || opam exec --switch=/shared/xv6rocq -- coq_makefile -f _CoqProject -o CoqMakefile >/dev/null 2>&1
  opam exec --switch=/shared/xv6rocq -- make -f CoqMakefile -j180 -k > "$ROOT/ZZ-$d.log.aux" 2>&1
  echo "SUBEXIT[$d]=$?"
done

cd "$ROOT/iris"
opam exec --switch=/shared/xv6rocq -- coq_makefile -f _CoqProject -o CoqMakefile >/dev/null 2>&1
opam exec --switch=/shared/xv6rocq -- make -f CoqMakefile -j180 -k > "$ROOT/ZZ-iris.log.aux" 2>&1
ME=$?
echo "MAKEEXIT=$ME"

n=0; g=0
while read -r f; do
  n=$((n+1)); b="${f%.v}"
  if [ -f "$b.vo" ]; then g=$((g+1)); else echo "RED $b"; fi
done < <(grep -E '^[A-Za-z].*\.v$' _CoqProject)
echo "GREEN=$g/$n"
echo "--- first errors ---"
grep -n "^File \|^Error" "$ROOT/ZZ-iris.log.aux" | head -80
echo DONE
