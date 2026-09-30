#!/usr/bin/env bash
# ec2-lane.sh -- build an app-pipe lane's worktree on the EC2 mirror.
#
#   ec2-lane.sh <lane> sync                 mirror this worktree's SOURCES (.v, _CoqProject) into the lane's remote clone
#   ec2-lane.sh <lane> check File.v [...]   sync, then FAST statement check (make File.vos) -- catches a broken
#                                           statement, NOT a broken proof (opaque proofs are skipped)
#   ec2-lane.sh <lane> build [make targets] sync, then start make -j6 targets in iris/ (default: the whole iris tree)
#                                           DETACHED on the mirror (nohup) and return at once -- a tool-call timeout can
#                                           no longer kill the build; then `wait` (below) for the result
#   ec2-lane.sh <lane> wait                 poll the detached build every 60 s until it ends; prints errors with
#                                           context and "RC=<n>" LAST -- trust ONLY that line.  If your tool call
#                                           times out, just run `wait` again: the build is still running remotely
#   ec2-lane.sh <lane> run '<shell>'        run a command in the remote clone's iris/ with the opam env set
#   ec2-lane.sh <lane> pull <path> [...]    copy files FROM the remote clone into this worktree (paths relative to the
#                                           tree root, e.g. iris/UCodeShP.v) -- for generated tracked files (make gen-ucode)
#
# <lane> names the local worktree /shared/xv6iris-pipe-<lane> and the remote clone of the same name.
# The remote clone is FULLY BUILT at the base SHA, so dependencies never need building -- never run
# rocq/coqc/make LOCALLY.  Host and key: EC2_HOST / EC2_KEY (defaults below; the hostname changes
# on every restart of the box -- the coordinator updates it).
#
# Sync = rsync --checksum of every *.v and _CoqProject under the four proof subtrees, deleting remote
# sources that no longer exist locally, NOT preserving mtimes (so make rebuilds exactly what changed).
# Build artifacts (.vo/.vos/.glob) are never touched by the sync.
set -euo pipefail
LANE="${1:?lane}"; CMD="${2:?sync|check|build|run}"; shift 2
HOST="${EC2_HOST:-ec2-44-202-245-129.compute-1.amazonaws.com}"
KEY="${EC2_KEY:-/shared/xv6iris/aws/ags-fk.pem}"
LOCAL="/shared/xv6iris-pipe-$LANE"; REMOTE="/shared/xv6iris-pipe-$LANE"
SSH=(ssh -i "$KEY" -o BatchMode=yes -o ServerAliveInterval=30 "ubuntu@$HOST")
# no global OCAMLRUNPARAM: l=4e9 segfaults UShRound.v's heaviest Qed (2026-09-18); UserMemCert alone needs it (gate handles)
ENV='eval $(opam env --switch=/shared/xv6rocq --set-switch) && ulimit -s unlimited'
[ -e "$LOCAL/.git" ] || { echo "no worktree $LOCAL" >&2; exit 2; }

sync() {
  local out
  out="$(rsync -rlpgoD --checksum --delete --out-format='%n' \
      --include='*/' --include='*.v' --include='_CoqProject' --include='*.py' --include='*.txt' --include='*.json' --exclude='*' \
      -e "ssh -i $KEY -o BatchMode=yes" \
      "$LOCAL/iris" "$LOCAL/kernel-rocq" "$LOCAL/user-rocq" "$LOCAL/model-xv6iris" "$LOCAL/tools" \
      "ubuntu@$HOST:$REMOTE/" | grep -v '/$' || true)"
  if [ -n "$out" ]; then echo "synced:" >&2; printf '  %s\n' $out >&2; fi
}

remote() {  # run in remote iris/; the log is filtered; RC printed LAST and taken from the command itself
  "${SSH[@]}" "cd $REMOTE/iris && $ENV && ( $1 ) > /tmp/lane-$LANE-$$.log 2>&1; rc=\$?; \
     grep -Ev '^(COQC|ROCQC|COQDEP|ROCQDEP|make\[|Warning: (No common logical root|In this case|Otherwise|in orphan))' /tmp/lane-$LANE-$$.log | tail -40; \
     if grep -Eq 'Error|Segmentation fault|Anomaly' /tmp/lane-$LANE-$$.log; then echo '---- errors, with context:'; grep -E 'Error|Segmentation fault|Anomaly' -B3 -A8 /tmp/lane-$LANE-$$.log | tail -120; rc=\${rc:-1}; [ \$rc -eq 0 ] && rc=1; fi; \
     echo RC=\$rc"
}

case "$CMD" in
  sync)  sync ;;
  check) sync
         tgts=""; for f in "$@"; do f="${f#iris/}"; tgts="$tgts ${f%.v}.vos"; done
         remote "make -f CoqMakefile -j6 $tgts" ;;
  build) sync
         "${SSH[@]}" "cd $REMOTE/iris && rm -f /tmp/lane-$LANE-build.log && nohup bash -c '$ENV && ulimit -s unlimited && make -f CoqMakefile -j6 -k $*; echo RC=\$?' > /tmp/lane-$LANE-build.log 2>&1 < /dev/null & echo 'build started detached; run: ec2-lane.sh $LANE wait'" ;;
  wait)  "${SSH[@]}" "until grep -q '^RC=' /tmp/lane-$LANE-build.log 2>/dev/null; do sleep 60; done; \
           grep -Ev '^(COQC|ROCQC|ROCQ compile|ROCQ DEP|COQDEP|ROCQDEP|make\[|Warning: (No common logical root|In this case|Otherwise|in orphan))' /tmp/lane-$LANE-build.log | tail -30; \
           if grep -Eq 'Error|Segmentation fault|Anomaly' /tmp/lane-$LANE-build.log; then echo '---- errors, with context:'; grep -E 'Error|Segmentation fault|Anomaly' -B3 -A8 /tmp/lane-$LANE-build.log | tail -120; fi; \
           grep '^RC=' /tmp/lane-$LANE-build.log | tail -1" ;;
  run)   remote "$*" ;;
  pull)  for f in "$@"; do scp -q -i "$KEY" "ubuntu@$HOST:$REMOTE/$f" "$LOCAL/$f" && echo "pulled $f"; done ;;
  *) echo "unknown command $CMD" >&2; exit 2 ;;
esac
