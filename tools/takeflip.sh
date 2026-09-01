#!/bin/bash
# Take flip's version of a file when main has no unique Lemma/Definition names.
# Usage: tools/takeflip.sh File...   Prints VERDICT per file; copies when safe.
for f in "$@"; do
  m=iris/$f.v; t=/shared/flip63/iris/$f.v
  if [ ! -f "$t" ]; then echo "$f: NOT-ON-FLIP"; continue; fi
  monly=$(comm -23 \
    <(grep -oE "^ *(Lemma|Definition|Fixpoint|Global Instance|Corollary) [A-Za-z0-9_']+" "$m" | awk '{print $NF}' | sort -u) \
    <(grep -oE "^ *(Lemma|Definition|Fixpoint|Global Instance|Corollary) [A-Za-z0-9_']+" "$t" | awk '{print $NF}' | sort -u))
  if [ -z "$monly" ]; then
    cp "$t" "$m"; echo "$f: TAKEN (no main-only names)"
  else
    echo "$f: KEEP-MERGE (main-only: $(echo $monly | tr '\n' ' ' | head -c 200))"
  fi
done
