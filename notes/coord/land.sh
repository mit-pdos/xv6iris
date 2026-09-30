#!/bin/bash
# usage: land.sh [nolaunch]  -- in verify worktree with commit(s) on detached HEAD atop origin/lean
# builds on GCP (unless nolaunch: build already launched), checks layering, pushes, ff main tree
set -u
V=/shared/lean-xv6/.claude/worktrees/verify; R=/shared/xv6rocq/gcp-rocq/run-on-gcp
cd $V || exit 1
if [ "${1:-}" != nolaunch ] && [ "${1:-}" != postpush ]; then
  timeout 300 $R --sync-only 2>&1 | tail -1
  timeout 120 $R --no-sync bash -lc 'export PATH=$HOME/.elan/bin:$PATH; rm -f /mnt/rocq/coord-verify.log; setsid nohup bash -c "lake build Xv6 MachCSL > /mnt/rocq/coord-verify.log 2>&1; echo EXIT=\$? >> /mnt/rocq/coord-verify.log" >/dev/null 2>&1 < /dev/null & echo launched' 2>&1 | tail -1
fi
until timeout 120 $R --no-sync bash -lc 'grep -q "^EXIT=" /mnt/rocq/coord-verify.log' >/dev/null 2>&1; do sleep 45; done
timeout 120 $R --no-sync bash -lc 'grep -E "error|Build completed|EXIT=" /mnt/rocq/coord-verify.log | head -20'
tools/check_layering.sh | tail -1 | tee /dev/stderr | grep -q "layering: ok" || { echo LAYERING-FAIL; exit 2; }
timeout 120 $R --no-sync bash -lc 'grep -q "^EXIT=0" /mnt/rocq/coord-verify.log' >/dev/null 2>&1 || { echo BUILD-FAIL; exit 3; }
retry() { for i in 1 2 3 4 5 6 7 8 9 10; do "$@" && return 0; sleep 6; done; return 1; }  # github ssh auth is flaky
if [ "${1:-}" != postpush ]; then
retry git fetch -q origin && git rebase -q origin/lean && retry git push -q origin HEAD:lean || { echo PUSH-FAIL; exit 4; }
fi
cd /shared/lean-xv6
for f in $(git diff --name-only HEAD origin/lean); do
  test -f $f || continue
  if git show origin/lean:$f 2>/dev/null | cmp -s - $f; then
    git ls-files --error-unmatch $f >/dev/null 2>&1 && git checkout -q -- $f || rm $f
  elif ! git ls-files --error-unmatch $f >/dev/null 2>&1 || ! git diff --quiet -- $f; then echo "DIFFERS $f"; fi
done
retry git fetch -q origin; git merge --ff-only -q origin/lean && git log --oneline -1 || { echo "FF-FAIL (pushed, main tree not updated)"; exit 6; }
cd $V && timeout 300 $R --no-sync bash -lc "mkdir -p /mnt/rocq/lean-seed && rm -rf /mnt/rocq/lean-seed/.lake.new && cp -a .lake /mnt/rocq/lean-seed/.lake.new && rm -rf /mnt/rocq/lean-seed/.lake && mv /mnt/rocq/lean-seed/.lake.new /mnt/rocq/lean-seed/.lake && echo seed-refreshed" 2>&1 | tail -1
