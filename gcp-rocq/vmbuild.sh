#!/bin/bash
# vmbuild.sh <tree> <logname> [new iris files relative to iris/ ...]
#
# Incremental build of ONE checkout's iris/ on the GCP VM, from that checkout's
# root: syncs the tree, removes the build products of every dirty or new iris
# file (so an edited file is rebuilt even when the sync keeps its mtime),
# builds with -k, then prints the compile count, the first Error lines and
# the make exit.  The full log stays on the VM at /tmp/<logname>.log:
#   gcp-rocq/run-on-gcp -q --no-sync bash -c 'grep -n -B2 -A25 "^Error" /tmp/<logname>.log'
# Run it for the checkout you are in and no other (sibling checkouts belong to
# other sessions); one build per tree at a time.
set -u
TREE=${1:?tree, e.g. xv6iris-2}; shift
LOG=${1:-build}; shift || true
cd /shared/$TREE || exit 9
FILES=$( (git diff --name-only; git diff --cached --name-only; git ls-files --others --exclude-standard) \
         | grep '^iris/.*\.v$' | sed 's|^iris/||' | sort -u | tr '\n' ' ')
FILES="$FILES $*"
/shared/$TREE/gcp-rocq/run-on-gcp -q bash -c "
  cd /mnt/rocq/trees/_shared_$TREE/iris || exit 9
  for f in $FILES; do rm -f \${f%.v}.vo \${f%.v}.vos \${f%.v}.vok \${f%.v}.glob; done
  rm -f CoqMakefile CoqMakefile.conf
  coq_makefile -f _CoqProject -o CoqMakefile >/dev/null 2>&1
  (make -f CoqMakefile -j180 -k > /tmp/$LOG.log 2>&1; echo EXIT=\$? >> /tmp/$LOG.log)
  echo COMPILED=\$(grep -c 'ROCQ compile' /tmp/$LOG.log)
  grep -n 'Error' /tmp/$LOG.log | head -40
  tail -1 /tmp/$LOG.log"
