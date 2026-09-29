#!/usr/bin/env python3
"""Deterministic reconstruction of trial commit 113114c54 (Iris master): (1) weakestpre no longer
re-exports language: after the first `From iris.program_logic Require Import lifting.` or
`… weakestpre.` line, add `From iris.program_logic Require Import language.` unless the file
already imports language from iris.program_logic; (2) stdpp's list files are `Module Export list`:
requalify `[stdpp.]list_relations.X` / `list_monad.X` / `list_basics.X` to `….list.X`
(rounds 4 and 6 of the trial did these by hand).
Usage: migrate_imports.py FILE... (in place)."""
import re, sys
IMP = re.compile(r'^From iris\.program_logic Require Import (?:[\w.]+ )*(?:lifting|weakestpre)(?: [\w.]+)*\.\s*$')
HAS = re.compile(r'^From iris\.program_logic Require (Import|Export) .*\blanguage\b', re.M)
for p in sys.argv[1:]:
    s = open(p, encoding='utf-8').read(); t = s
    if not HAS.search(t):
        L = t.split('\n')
        for i, l in enumerate(L):
            if IMP.match(l):
                L.insert(i + 1, 'From iris.program_logic Require Import language.'); break
        t = '\n'.join(L)
    t = re.sub(r'\b((?:stdpp\.)?(?:list_relations|list_monad|list_basics))\.(?!list\.)([A-Za-z_][A-Za-z0-9_\']*)', r'\1.list.\2', t)
    if t != s: open(p, 'w', encoding='utf-8').write(t)
