#!/usr/bin/env bash
# ec2-gate.sh -- the coordinator's GATE: sync local main to the EC2 mirror's main checkout and build the
# whole tree there, in dependency order, with the false-green traps from claude-notes/durable-notes.md and
# the ec2-build-mirror memory guarded.  Run from the coordinator's checkout (/shared/xv6iris) on main.
#
#   ec2-gate.sh             sync main to the mirror, then start the DETACHED build (model-xv6iris, kernel-rocq,
#                           user-rocq, iris, each with its CoqMakefile regenerated); returns at once
#   ec2-gate.sh --status    print the build log; it ends in BUILD_RC=<n> when done (0 = green)
#   ec2-gate.sh --audit-now start the three audits detached (~7.5 min each) -- after --status shows BUILD_RC=0
#   ec2-gate.sh --audits    print the audit log (AUDITS_DONE marks the end; counts: system 13, echo 14, tree 13)
set -euo pipefail
HOST="${EC2_HOST:-ec2-44-202-245-129.compute-1.amazonaws.com}"
KEY="${EC2_KEY:-/shared/xv6iris/aws/ags-fk.pem}"
LOCAL=/shared/xv6iris; REMOTE=/shared/xv6iris
SSH=(ssh -i "$KEY" -o BatchMode=yes -o ServerAliveInterval=30 "ubuntu@$HOST")
SCP=(scp -q -i "$KEY")

case "${1:-}" in
  --status) "${SSH[@]}" 'cat /tmp/gate-build.log 2>/dev/null || echo "(no build log)"; echo "-- full log tail:"; tail -3 /tmp/gate-build-full.log 2>/dev/null | cut -c1-160'; exit 0 ;;
  --audits) "${SSH[@]}" 'cat /tmp/gate-audit.log 2>/dev/null || echo "(no audit log)"'; exit 0 ;;
  --audit-now)
    cat > /tmp/gate-audit.sh <<'EOS'
cd /shared/xv6iris && eval $(opam env --switch=/shared/xv6rocq --set-switch)
echo "AUDITS at $(git rev-parse --short HEAD)"
for t in audit-only audit-tree-only audit-pipe-only; do
  echo "== $t"; /usr/bin/time -f %es make -s $t 2>&1 | grep -Ev '^(Warning|make)' | tail -30
done
echo AUDITS_DONE
EOS
    "${SCP[@]}" /tmp/gate-audit.sh "ubuntu@$HOST:/tmp/gate-audit.sh"
    "${SSH[@]}" 'nohup bash /tmp/gate-audit.sh > /tmp/gate-audit.log 2>&1 < /dev/null & echo "audits started -> ec2-gate.sh --audits"'
    exit 0 ;;
  "") ;;
  *) echo "unknown option $1" >&2; exit 2 ;;
esac

br="$(git -C $LOCAL branch --show-current)"
[ "$br" = main ] || { echo "GATE RED (local checkout is on '$br', not main)"; exit 1; }
[ -z "$(git -C $LOCAL status --short)" ] || { echo "GATE RED (local main is dirty)"; git -C $LOCAL status --short | head; exit 1; }
sha="$(git -C $LOCAL rev-parse HEAD)"

# 1. ship main by bundle, fast-forward the mirror's main (never reset --hard in the same script as a build)
tmp="$(mktemp -d)"; git -C $LOCAL bundle create "$tmp/main.bundle" main >/dev/null 2>&1
"${SCP[@]}" "$tmp/main.bundle" "ubuntu@$HOST:/tmp/gate-main.bundle"; rm -rf "$tmp"
"${SSH[@]}" "set -e; cd $REMOTE; [ -z \"\$(git status --short)\" ] || { echo 'GATE RED (mirror dirty)'; git status --short | head; exit 1; }; \
  git fetch -q /tmp/gate-main.bundle main:refs/heads/synced; [ \"\$(git branch --show-current)\" = main ] || git checkout -q main; \
  git merge -q --ff-only synced; [ \"\$(git rev-parse HEAD)\" = $sha ] || { echo 'GATE RED (mirror HEAD != local after ff)'; exit 1; }; \
  echo \"mirror at \$(git rev-parse --short HEAD)\""

# 2. the build, DETACHED (a Spec change rebuilds a large cone; longer than an ssh session should hold)
cat > /tmp/gate-build.sh <<'EOS'
set -o pipefail
# NO global OCAMLRUNPARAM: l=4e9 as a global knob SEGFAULTS UShRound.v's heaviest Qed at the default stack
# (measured 2026-09-18: knob+8MB = SIGSEGV in 9 s, no knob = green in 18 s).  The one file that needs it
# (UserMemCert.v, per the EC2 memory note) gets it in a targeted second pass if pass 1 leaves it red.
cd /shared/xv6iris && eval $(opam env --switch=/shared/xv6rocq --set-switch) && ulimit -s unlimited
rm -f /tmp/gate-build-full.log
echo "BUILD at $(git rev-parse --short HEAD) stack=$(ulimit -s)"
rc=0
for d in model-xv6iris kernel-rocq user-rocq iris; do
  ( cd $d && rocq makefile -f _CoqProject -o CoqMakefile >/dev/null 2>&1 && make -f CoqMakefile -j30 -k ) >> /tmp/gate-build-full.log 2>&1 \
    || { rc=$?; echo "pass 1 FAILED in $d rc=$rc";
         if [ "$d" = iris ]; then
           echo "pass 2 (targeted OCAMLRUNPARAM=l=4e9 for the big-stack files)";
           ( cd iris && OCAMLRUNPARAM=l=4000000000 make -f CoqMakefile -j30 -k ) >> /tmp/gate-build-full.log 2>&1 && rc=0 || rc=$?
           echo "pass 2 rc=$rc";
         fi;
         [ $rc -eq 0 ] || break; }
  echo "built $d"
done
if grep -Eq 'Error|Segmentation fault|Anomaly' /tmp/gate-build-full.log; then
  echo '---- errors (all passes):'; grep -E 'Error|Segmentation fault|Anomaly' -B3 -A8 /tmp/gate-build-full.log | tail -80
  [ $rc -eq 0 ] && echo "(errors above were resolved by a later pass)"
fi
small=$(find iris -name '*.vo' -size -1k | head)
[ -z "$small" ] || { echo "suspiciously small .vo: $small"; rc=1; }
echo "BUILD_RC=$rc"
EOS
"${SCP[@]}" /tmp/gate-build.sh "ubuntu@$HOST:/tmp/gate-build.sh"
"${SSH[@]}" 'nohup bash /tmp/gate-build.sh > /tmp/gate-build.log 2>&1 < /dev/null & echo started'
echo "GATE: build detached at ${sha:0:10}; poll with --status (BUILD_RC=0 = green), then --audit-now, then --audits"
