#!/usr/bin/env python3
"""Apply an import-edit file (`Mod -Imp` / `Mod +Imp` lines, as written by
tools/import_shake.py) to the sources under ROOT.

Usage: tools/apply_import_edits.py EDITS ROOT [--only-local]
Removes the matching `import Imp` line and appends `import Imp` after the last import line.
"""
import collections, os, re, sys


def path_of(root, m):
    r = m.split(".")[0]
    rel = m.replace(".", "/") + ".lean"
    if r == "LeanRV64D":
        return os.path.join(root, "model/Lean_RV64D", rel)
    if r == "Sail":
        return os.path.join(root, "vendor/lean-sail", rel)
    return os.path.join(root, rel)


def main():
    edits_file, root = sys.argv[1], sys.argv[2]
    rm, add = collections.defaultdict(set), collections.defaultdict(list)
    for line in open(edits_file):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        m, op = line.split()
        if op[0] == "-":
            rm[m].add(op[1:])
        elif op[0] == "+":
            add[m].append(op[1:])
    n = 0
    for m in set(rm) | set(add):
        p = path_of(root, m)
        lines = open(p, encoding="utf-8").read().split("\n")
        out, last_imp = [], -1
        for ln in lines:
            mm = re.match(r"^\s*import\s+(\S+)\s*(--.*)?$", ln)
            if mm and mm.group(1) in rm[m]:
                continue
            out.append(ln)
            if mm:
                last_imp = len(out) - 1
        ins = [f"import {x}" for x in add[m]]
        out[last_imp + 1:last_imp + 1] = ins  # last_imp == -1: prepend
        open(p, "w", encoding="utf-8").write("\n".join(out))
        n += 1
    print(f"edited {n} files")


if __name__ == "__main__":
    main()
