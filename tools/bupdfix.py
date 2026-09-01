#!/usr/bin/env python3
"""Convert CtxMorph instance proofs from the wand class to the bupd class.

Within each `Instance ... CtxMorph ... Proof. ... Qed.` block:
  - `iDestruct (<something>_morph ... ) as`   -> `iMod (...) as`
  - `iDestruct (ctx_morph<...> ... ) as`      -> `iMod (...) as`
  - ensure the block's final closer starts with `iModIntro.` (or `by iFrame`)
    when an iMod was introduced and no iModIntro/iApply-of-==∗ already closes.
Idempotent-ish; prints what it changed.  Usage: bupdfix.py FILE...
"""
import re, sys

def fix_block(body):
    changed = False
    pat = re.compile(r'iDestruct \((ctx_morph[A-Za-z0-9_]*|[A-Za-z0-9_]+_morph)\b')
    body2 = pat.sub(lambda m: 'iMod (' + m.group(1), body)
    if body2 != body:
        changed = True
        body = body2
    if changed and 'iModIntro' not in body:
        # find final closer line(s): last statement before end
        lines = body.rstrip().split('\n')
        for i in range(len(lines) - 1, -1, -1):
            t = lines[i].strip()
            if not t or t.startswith('(*'):
                continue
            if t.startswith('iFrame') or t.startswith('by iFrame'):
                indent = lines[i][:len(lines[i]) - len(lines[i].lstrip())]
                if t.startswith('by iFrame') and t.endswith('.') and t.count('.') == 1:
                    break  # `by iFrame.` handles the modality via done
                lines[i] = indent + 'iModIntro. ' + t
                body = '\n'.join(lines) + '\n'
            break
    return body, changed

def main(path):
    s = open(path).read()
    out = []
    idx = 0
    nfix = 0
    inst = re.compile(r'((?:Global |Local )?Instance [^.]*?CtxMorph.*?Proof\.)(.*?)(\bQed\.)', re.S)
    for m in inst.finditer(s):
        out.append(s[idx:m.start(2)])
        body, ch = fix_block(m.group(2))
        if ch:
            nfix += 1
        out.append(body)
        out.append(m.group(3))
        idx = m.end(3)
    out.append(s[idx:])
    if nfix:
        open(path, 'w').write(''.join(out))
    print(f"{path}: {nfix} instance proofs converted")

for p in sys.argv[1:]:
    main(p)
