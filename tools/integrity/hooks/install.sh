#!/usr/bin/env bash
# Install the integrity hooks and the `git integrity` alias for THIS repository (all worktrees
# share the hooks directory). Idempotent. The previous hooks are kept as *.before-integrity.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
hooks=$(git rev-parse --git-common-dir)/hooks
for h in pre-commit commit-msg; do
  if [ -e "$hooks/$h" ] && [ ! -L "$hooks/$h" ] && ! cmp -s "$hooks/$h" "$here/$h"; then
    mv "$hooks/$h" "$hooks/$h.before-integrity"
  fi
  ln -sfn "$here/$h" "$hooks/$h"
done
ln -sfn "$here/pre-commit" "$hooks/pre-merge-commit"
git config alias.integrity '!python3 "$(git rev-parse --show-toplevel)/tools/integrity/integrity.py" check'
git config alias.integrity-audit '!python3 "$(git rev-parse --show-toplevel)/tools/integrity/integrity.py" audit'
echo "installed: $hooks/{pre-commit,pre-merge-commit,commit-msg} -> $here; aliases git integrity, git integrity-audit"
