#!/usr/bin/env python3
"""Drop the in-page arguments from call sites (Rocq drift theme B, c5bce82eb).

The instruction fact lost its in-page clause (`pc % 4096 <= 4092`), so the
per-program catalog lemmas (`echo_uis`, `cat_uis`, `grep_uis`, `ushm_uis`,
`secc_uis`, `init_uis`) and the stub builders (`stub_of_text`,
`exit_stub_of_text`) no longer take their in-page arguments.  This rewrites
every call site by deleting the explicit arguments at the listed positions
(0-based, counted after the function name; each argument is a balanced
`(...)`/`⟨...⟩`/`[...]` group or a whitespace-delimited atom).

Usage: tools/drop_inpage_args.py FILE...   (edits in place; prints a summary)
Re-runnable on regenerated files (e.g. sh's catalogs after an image bump): a
call whose argument list is too short to contain the positions is left alone
and reported.
"""
import re
import sys

# name -> positions of the explicit arguments to delete
DROP = {
    'echo_uis': [6], 'cat_uis': [6], 'grep_uis': [6], 'ushm_uis': [6],
    'secc_uis': [6], 'init_uis': [6],
    'stub_of_text': [12, 13, 14],
    'exit_stub_of_text': [9, 10],
}

OPEN = {'(': ')', '⟨': '⟩', '[': ']', '{': '}'}
CLOSE = set(OPEN.values())
STOP = {'$$', 'with', ':=', '|', '·', 'at', 'in', '=>', '<;>'}


def parse_args(s, i, need):
    """From index i (just after the name), parse up to `need` args.
    Returns list of (start, end) spans, possibly shorter than need."""
    spans = []
    n = len(s)
    while len(spans) < need:
        j = i
        while j < n and s[j] in ' \t\n':
            j += 1
        if j >= n:
            break
        c = s[j]
        if c in OPEN:
            depth = 0
            k = j
            stack = []
            while k < n:
                ch = s[k]
                if ch in OPEN:
                    stack.append(OPEN[ch])
                elif ch in CLOSE:
                    if not stack or stack[-1] != ch:
                        return spans
                    stack.pop()
                    if not stack:
                        k += 1
                        break
                k += 1
            else:
                return spans
            spans.append((j, k))
            i = k
        elif c in CLOSE:
            break
        else:
            k = j
            while k < n and s[k] not in ' \t\n' and s[k] not in OPEN and s[k] not in CLOSE:
                k += 1
            tok = s[j:k]
            if tok in STOP or tok.startswith('--'):
                break
            spans.append((j, k))
            i = k
    return spans


def process(path):
    s = open(path, encoding='utf-8').read()
    names = '|'.join(sorted(DROP, key=len, reverse=True))
    pat = re.compile(r'(?<![\w.`\'«])(' + names + r')(?![\w\'])')
    out = []
    pos = 0
    done = 0
    skipped = []
    for m in pat.finditer(s):
        if m.start() < pos:
            continue
        pre = s[max(0, m.start() - 8):m.start()]
        if pre.endswith('theorem ') or pre.endswith('lemma '):
            continue
        name = m.group(1)
        drop = DROP[name]
        spans = parse_args(s, m.end(), max(drop) + 1)
        if len(spans) < max(drop) + 1:
            line = s.count('\n', 0, m.start()) + 1
            skipped.append(line)
            continue
        # delete the spans (with the whitespace before each)
        cut = []
        for d in drop:
            a, b = spans[d]
            prev_end = spans[d - 1][1] if d > 0 else m.end()
            cut.append((prev_end, b))
        seg = []
        last = pos
        for a, b in cut:
            seg.append(s[last:a])
            last = b
        out.append(''.join(seg))
        pos = last
        done += 1
    out.append(s[pos:])
    new = ''.join(out)
    if new != s:
        open(path, 'w', encoding='utf-8').write(new)
    return done, skipped


def main():
    tot = 0
    for p in sys.argv[1:]:
        d, sk = process(p)
        tot += d
        if d or sk:
            print(f'{p}: {d} call(s) rewritten' + (f'; left alone at lines {sk}' if sk else ''))
    print(f'total {tot}')


if __name__ == '__main__':
    main()
