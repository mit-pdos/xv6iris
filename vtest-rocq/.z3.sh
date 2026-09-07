#!/usr/bin/env bash
cd "$(dirname "$0")/vtest-rocq" || exit 1
F="-R . VTest -R ../iris xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel -w -notation-overridden"
timeout 600 rocq compile -q $F ZT.v 2>&1 \
  | grep -vE "^Warning|comment-term|because it|applications of|abstract-large" \
  | tr '\n' ' ' | sed 's/ *: string \* list Z/\n/g'
