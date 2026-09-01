#!/bin/bash
# 3-way merge helper for the tso-cutover branch: base = merge-base(main, tso-flip),
# ours = worktree, theirs = /shared/flip63.  Usage: tools/merge3.sh File [File...]
# Leaves conflict markers in place; prints the conflict count per file.
set -u
MB=$(git merge-base origin/main origin/tso-flip)
for f in "$@"; do
  b=$(mktemp); t=/shared/flip63/iris/$f.v
  if ! git show "$MB:iris/$f.v" > "$b" 2>/dev/null; then
    echo "$f: NO BASE (new file?)"; rm -f "$b"; continue
  fi
  if [ ! -f "$t" ]; then echo "$f: NOT ON FLIP"; rm -f "$b"; continue; fi
  if git merge-file -q "iris/$f.v" "$b" "$t" 2>/dev/null; then
    echo "$f: CLEAN"
  else
    echo "$f: $(grep -c '^<<<<<<<' iris/$f.v) conflicts"
  fi
  rm -f "$b"
done
