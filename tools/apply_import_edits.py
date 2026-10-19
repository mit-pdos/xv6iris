#!/usr/bin/env python3
"""Apply an import-edit file (`Mod -Imp` / `Mod +Imp` lines, as written by
tools/import_shake.py) to the sources under ROOT.

Usage: tools/apply_import_edits.py EDITS ROOT
Removes the matching `import Imp` line and appends `import Imp` after the last import line
(or, when every import was removed, where the first one stood).  Edits to `Sail.*` and
`LeanRV64D.*` are skipped: lean-sail is a fetched package used unmodified, and the generated
model is rewritten by tools/regen_sail_model.sh.
"""
import collections, os, re, sys


def path_of(root, m):
    r = m.split(".")[0]
    rel = m.replace(".", "/") + ".lean"
    if r == "LeanRV64D":
        return os.path.join(root, "model/Lean_RV64D", rel)
    if r == "Sail":
        return os.path.join(root, ".lake/packages/Sail", rel)
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
    n, skipped = 0, 0
    for m in set(rm) | set(add):
        if m.split(".")[0] in ("Sail", "LeanRV64D"):
            skipped += 1
            continue
        p = path_of(root, m)
        lines = open(p, encoding="utf-8").read().split("\n")
        out, last_imp, first_rm = [], -1, -1
        for ln in lines:
            mm = re.match(r"^\s*import\s+(\S+)\s*(--.*)?$", ln)
            if mm and mm.group(1) in rm[m]:
                if first_rm < 0:
                    first_rm = len(out)
                continue
            out.append(ln)
            if mm:
                last_imp = len(out) - 1
        ins = [f"import {x}" for x in add[m]]
        # every import removed: put the new ones where the first old one was (after
        # any header comment), not at the top of the file
        at = last_imp + 1 if last_imp >= 0 else max(first_rm, 0)
        out[at:at] = ins
        open(p, "w", encoding="utf-8").write("\n".join(out))
        n += 1
    print(f"edited {n} files" + (f" (skipped {skipped} in lean-sail or the generated model)" if skipped else ""))


if __name__ == "__main__":
    main()
