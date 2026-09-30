#!/usr/bin/env python3
"""Collapse blank-line runs that deletions created: for each changed file, a run
of k>=2 blank lines is shrunk to the longest run the HEAD version had (min 1)."""
import subprocess, re, sys, os
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
files = subprocess.check_output(['git', 'diff', '--name-only'], cwd=ROOT).decode().split()
n = 0
for f in files:
    if not f.endswith('.lean'): continue
    try:
        old = subprocess.check_output(['git', 'show', 'HEAD:' + f], cwd=ROOT).decode()
    except subprocess.CalledProcessError:
        continue
    mx = max([len(m.group(0)) - 1 for m in re.finditer(r'\n(?:[ \t]*\n)+', old)] + [1])
    mx = max(1, mx - 0)
    new = open(os.path.join(ROOT, f)).read()
    def sh(m):
        k = m.group(0).count('\n') - 1
        return '\n' + '\n' * min(k, max(1, mx)) if k > 1 else m.group(0)
    new2 = re.sub(r'\n(?:[ \t]*\n)+', sh, new)
    if new2 != new:
        open(os.path.join(ROOT, f), 'w').write(new2); n += 1
print('collapsed in', n, 'files')
