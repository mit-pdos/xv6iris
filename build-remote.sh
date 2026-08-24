#!/bin/bash
# Remote full build in the SAFE form (drives each sub-tree through its own
# generated CoqMakefile; touches no dump rule, so the tracked image cannot
# move) -- see claude-notes/remote-build-gcp.md "Daily use".
ulimit -s unlimited
touch kernel-rocq/*.v user-rocq/*.v
set -e
for d in model-xv6iris kernel-rocq user-rocq; do
  ( cd "$d" && { coq_makefile -f _CoqProject -o CoqMakefile >/dev/null 2>&1 || true; } && \
    make -f CoqMakefile -j192 )
done
cd iris
coq_makefile -f _CoqProject -o CoqMakefile >/dev/null 2>&1 || true
make -f CoqMakefile -j180 -k
