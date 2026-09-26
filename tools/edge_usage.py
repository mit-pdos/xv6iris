#!/usr/bin/env python3
"""For a chain of modules (e.g. a critical path printed by tools/import_graph.py), show how
much each module actually uses from its predecessor, and which of its imports are thin.

Usage:
  tools/edge_usage.py needs.tsv [--path FILE | MOD MOD ...] [--times build.log]
FILE may be import_graph.py output: lines `  Mod   12.3s  cum ...` after `critical path:`.
For each consecutive pair P -> C it prints the number of distinct constants of P that C's
declarations reference (kind: const/indirect/extra/dup), example constants, and C's
total number of needed modules.
"""
import argparse, re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from import_shake import load  # noqa


def read_path(f):
    mods, on = [], False
    for line in open(f):
        if line.startswith("critical path:"):
            on = True
            continue
        if on:
            m = re.match(r"^\s+(\S+)\s+[0-9.]+s\s+cum", line)
            if not m:
                if mods:
                    break
                continue
            mods.append(m.group(1))
    return mods


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("needs")
    ap.add_argument("mods", nargs="*")
    ap.add_argument("--path")
    ap.add_argument("--times")
    a = ap.parse_args()
    imports, needs, decls, _ = load(a.needs)
    mods = read_path(a.path) if a.path else a.mods
    t = {}
    if a.times:
        from import_graph import read_times
        t = read_times(a.times)
    for p, c in zip(mods, mods[1:]):
        n = needs.get(c, {}).get(p)
        direct = p in imports.get(c, [])
        ndecl = len(decls.get(p, []))
        if n:
            kind, user, used, cnt, ex = n
            print(f"{p} -> {c} [{t.get(c, 0):.1f}s]: {kind} {cnt} of {ndecl} decls used"
                  f"{'' if direct else ' (NOT a direct import)'}; e.g. {' '.join(ex[:6])}")
        else:
            print(f"{p} -> {c} [{t.get(c, 0):.1f}s]: NOTHING used directly from {p} ({ndecl} decls)"
                  f"{'' if direct else ' (not a direct import)'}")


if __name__ == "__main__":
    main()
