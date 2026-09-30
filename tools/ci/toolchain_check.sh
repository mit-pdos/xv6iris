#!/usr/bin/env bash
# tools/ci/toolchain_check.sh [--with-lake]
#
# Is this the toolchain the tree pins?  The counterpart of Rocq's
# `make toolchain-check` (which re-exports the opam switch and diffs it
# against opam/xv6rocq.export): here the pins are files, so the check is that
# they AGREE, and -- with --with-lake -- that the toolchain actually on PATH
# and the packages actually fetched are the pinned ones.
#
# Always (text only, runs anywhere):
#   * lean-toolchain, model/Lean_RV64D/lean-toolchain and
#     vendor/lean-sail/lean-toolchain name the same Lean (three lake packages
#     compiled into one build: a mismatch makes .olean files incompatible);
#   * every git dependency of lakefile.toml is in lake-manifest.json at the
#     same revision (a manifest left behind after a lakefile bump makes lake
#     silently build the OLD dependency).
# With --with-lake (CI and build machines; see
# README: "Build"):
#   * `lake --version` reports the Lean of lean-toolchain;
#   * each fetched package under .lake/packages is at its manifest revision.
#
# Exit 0 when everything agrees, 1 with the differences otherwise.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
with_lake=0
[ "${1:-}" = "--with-lake" ] && with_lake=1
bad=0
want=$(tr -d '[:space:]' < lean-toolchain)
for f in model/Lean_RV64D/lean-toolchain vendor/lean-sail/lean-toolchain; do
  have=$(tr -d '[:space:]' < "$f" 2>/dev/null || echo missing)
  if [ "$have" != "$want" ]; then
    echo "toolchain-check: $f is '$have', lean-toolchain is '$want'"; bad=1
  fi
done
python3 - <<'PY' || bad=1
import json, re, sys
lake = open("lakefile.toml", encoding="utf-8").read()
man = {p["name"]: p for p in json.load(open("lake-manifest.json"))["packages"]}
bad = 0
for blk in lake.split("[[require]]")[1:]:
    blk = blk.split("[[")[0]
    get = lambda k: (re.search(r'^%s\s*=\s*"([^"]*)"' % k, blk, re.M) or [None, None])[1]
    name, rev, path = get("name"), get("rev"), get("path")
    ent = man.get(name)
    if ent is None:
        print(f"toolchain-check: lakefile.toml requires `{name}`, lake-manifest.json has no such package"); bad = 1
    elif rev is not None and rev not in (ent.get("rev"), ent.get("inputRev")):
        print(f"toolchain-check: `{name}` is pinned at {rev} in lakefile.toml, "
              f"at {ent.get('inputRev')} -> {ent.get('rev')} in lake-manifest.json"); bad = 1
    elif path is not None and ent.get("dir") != path:
        print(f"toolchain-check: `{name}` is at path {path} in lakefile.toml, {ent.get('dir')} in lake-manifest.json"); bad = 1
sys.exit(bad)
PY
if [ "$with_lake" -eq 1 ]; then
  command -v lake >/dev/null 2>&1 || export PATH="$HOME/.elan/bin:$PATH"
  ver=${want##*:v}
  if ! lake --version 2>/dev/null | grep -q "Lean version $ver)"; then
    echo "toolchain-check: lake reports '$(lake --version 2>&1 | head -1)', lean-toolchain pins $want"; bad=1
  fi
  python3 - <<'PY' || bad=1
import json, os, subprocess, sys
bad = 0
man = json.load(open("lake-manifest.json"))
for p in man["packages"]:
    if p.get("type") != "git":
        continue
    d = os.path.join(man.get("packagesDir", ".lake/packages"), p["name"])
    if not os.path.isdir(d):
        print(f"toolchain-check: package `{p['name']}` is not fetched ({d})"); bad = 1
        continue
    have = subprocess.run(["git", "-C", d, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if have != p["rev"]:
        print(f"toolchain-check: {d} is at {have}, lake-manifest.json pins {p['rev']}"); bad = 1
sys.exit(bad)
PY
fi
if [ "$bad" -eq 0 ]; then
  echo "toolchain-check: ok ($want$([ "$with_lake" -eq 1 ] && echo ', lake and fetched packages match'))"
fi
exit "$bad"
