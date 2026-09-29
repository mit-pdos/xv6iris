#!/usr/bin/env python3
"""Merge upstream/main into the Iris-master upgrade branch, re-running the scripted migration on
upstream's new content instead of fighting textual conflicts with it.

Run inside the integration worktree AFTER `git merge --no-commit --no-ff upstream/main` (so the
merge is recorded with both parents). For every path upstream changed since the merge base B:
  - iris/*.v: result = merge3(ours=O, base=mig(B), theirs=mig(U)), where mig = the deterministic
    migration pipeline (migrate-master.sed, unwrap.pl, migrate_imports.py). Our manual fixes are
    exactly O - mig(B), so they are replayed onto the migrated upstream version; upstream's new
    code gets the scripted renames. Files we never touched: mig(U).
  - other files: plain merge3(O, B, U).
  - added upstream: mig(U) / U.  Deleted upstream: deleted (reported if we had changed it).
Writes the results, stages them, and prints the paths left with conflict markers.
Usage: merge_upstream.py [UPSTREAM_REF]   (default upstream/main)"""
import os, subprocess, sys, tempfile
T = os.path.dirname(os.path.abspath(__file__))   # the migration scripts live beside this file
UP = sys.argv[1] if len(sys.argv) > 1 else 'upstream/main'
def git(*a, check=True, text=True):
    return subprocess.run(['git', *a], capture_output=True, text=text, check=check).stdout
def show(rev, path):
    r = subprocess.run(['git', 'show', f'{rev}:{path}'], capture_output=True)
    return r.stdout.decode('utf-8', 'surrogateescape') if r.returncode == 0 else None
def mig(text):
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, 'F.v'); open(p, 'w', encoding='utf-8').write(text)
        subprocess.run(['sed', '-E', '-i', '-f', f'{T}/migrate-master.sed', p], check=True)
        subprocess.run(['perl', '-0pi', f'{T}/unwrap.pl', p], check=True)
        subprocess.run(['python3', f'{T}/migrate_imports.py', p], check=True)
        return open(p, encoding='utf-8').read()
def merge3(ours, base, theirs):
    with tempfile.TemporaryDirectory() as d:
        fs = []
        for n, t in (('ours', ours), ('base', base), ('theirs', theirs)):
            p = os.path.join(d, n); open(p, 'w', encoding='utf-8', errors='surrogateescape').write(t); fs.append(p)
        r = subprocess.run(['git', 'merge-file', '-L', 'ours', '-L', 'base(migrated)', '-L', 'upstream(migrated)',
                            '-p', *fs], capture_output=True)
        return r.stdout.decode('utf-8', 'surrogateescape'), r.returncode   # returncode = number of conflicts
base = git('merge-base', 'HEAD', UP).strip()
changes = [l.split('\t') for l in git('diff', '--no-renames', '--name-status', base, UP).splitlines()]
conflicts, notes = [], []
for st, path in changes:
    in_scope = path.startswith('iris/') and path.endswith('.v')
    O = show('HEAD', path); B = show(base, path); U = show(UP, path)
    if st == 'D':
        if O is not None and O != B: notes.append(f'deleted upstream, had our changes: {path}')
        if os.path.exists(path): git('rm', '-q', '-f', path)
        continue
    if st == 'M' and O is None:
        notes.append(f'modified upstream, deleted by us (kept deleted): {path}'); continue
    if not in_scope and (O is None or O == B):
        git('checkout', UP, '--', path); continue          # exact upstream file (mode, bytes)
    if st == 'A':
        res, nconf = mig(U), 0
        if O is not None and O != U: res, nconf = merge3(O, '', res)
    elif st == 'M':
        if O == B: res, nconf = mig(U), 0
        elif in_scope: res, nconf = merge3(O, mig(B), mig(U))
        else: res, nconf = merge3(O, B, U)
    else:
        notes.append(f'unhandled status {st}: {path}'); continue
    os.makedirs(os.path.dirname(path) or '.', exist_ok=True)
    open(path, 'w', encoding='utf-8', errors='surrogateescape').write(res)
    git('add', path)
    if nconf: conflicts.append((path, nconf))
for n in notes: print('NOTE', n)
for p, n in conflicts: print(f'CONFLICT {p} ({n})')
print(f'{len(changes)} upstream paths processed; {len(conflicts)} with conflicts')
