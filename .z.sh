#!/usr/bin/env bash
cd "$(dirname "$0")/vtest-rocq" || exit 1
rm -f CoqMakefile && rocq makefile -f _CoqProject -o CoqMakefile >/dev/null 2>&1
s=$(date +%s)
if timeout 900 make -f CoqMakefile -j 32 >/tmp/vc.log 2>&1; then
  echo "GREEN ($(grep -c 'Pass.v$' _CoqProject) proofs) in $(( $(date +%s)-s ))s"
else echo "RED"; grep -E '^File |^Error' /tmp/vc.log|head -8; fi
