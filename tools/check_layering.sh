#!/usr/bin/env bash
# The Spec/Proof/Link layering rules (claude-notes/design/spec-modules.md in
# the Rocq prototype):
#   - a Spec<F> file imports no Code* or Proof* file (directly);
#   - a Proof<F> file imports no Link* file and no other Proof* file;
#   - only Link* files import Proof* files.
# Exit status 1 if a rule is violated.
set -u
cd "$(dirname "$0")/.."
bad=0
for f in Xv6/Spec*.lean MachCSL/Spec*.lean; do
  [ -f "$f" ] || continue
  if grep -qE '^import (Xv6|MachCSL)\.(Code|Proof|Link)[A-Z]' "$f"; then echo "layering: $f imports a Code/Proof/Link file"; bad=1; fi
done
for f in Xv6/Proof*.lean MachCSL/Proof*.lean; do
  [ -f "$f" ] || continue
  if grep -qE '^import (Xv6|MachCSL)\.(Proof|Link)[A-Z]' "$f"; then echo "layering: $f imports a Proof/Link file"; bad=1; fi
done
for f in Xv6/*.lean MachCSL/*.lean; do
  case "$(basename "$f")" in Link*|Proof*) continue;; esac
  if grep -qE '^import (Xv6|MachCSL)\.Proof[A-Z]' "$f"; then echo "layering: $f imports a Proof file"; bad=1; fi
done
[ $bad = 0 ] && echo "layering: ok"
exit $bad
