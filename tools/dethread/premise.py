#!/usr/bin/env python3
"""R1c phase 2 -- kill the tie premises that de-threading turned into
`icfg_X = icfg_X`.

For every declaration in the cut, find the PREMISE CHAIN (the `->`-separated
segments between the binders and the first `-∗`), spot the trivial ties, and
report / rewrite:
  * the premise itself (with its `->`),
  * the positional argument at every application (position = the
    declaration's explicit-binder count + the premise's index),
  * the name the proof's `intros` gives it.
"""
import sys, os, re, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dethread import strip_comments, parse_binders, declarations, skip_ws, OPEN, CLOSE, IDENT
from rewrite import (analyse_file, decl_end, args_of, IDCHAR, NAMEDARG)

SCR = os.path.dirname(os.path.abspath(__file__))
IRIS = os.path.join(SCR, '..', 'iris')

TIE = re.compile(r'^\s*⌜?\s*icfg_(dev|nib|ist|log)\s*=\s*icfg_\1\s*⌝?\s*$')

def body_start(t, kind, regions):
    """offset just past the `:=` (Definition) or the statement's leading
       binders (Lemma / Parameter)."""
    i = regions[-1][1]
    # skip ':=' or ',' or ':'
    while i < len(t) and t[i] in ' \n\t\r':
        i += 1
    if t.startswith(':=', i):
        i += 2
    elif t[i:i+1] in (',', ':'):
        i += 1
    return i

def skip_lets(t, i):
    n = 0
    while True:
        j = skip_ws(t, i)
        if not t.startswith('let', j) or re.match('[' + IDCHAR + ']', t[j+3:j+4] or ' '):
            return i, n
        # find the matching ' in ' at depth 0
        depth = 0
        k = j + 3
        while k < len(t):
            c = t[k]
            if c in OPEN:
                depth += 1
            elif c in CLOSE:
                depth -= 1
            elif depth == 0 and re.match(r'\bin\b', t[k:k+2]) and t[k-1] in ' \n\t' \
                    and (k+2 >= len(t) or t[k+2] in ' \n\t'):
                break
            k += 1
        i = k + 2
        n += 1

def premises(t, i):
    """from i, split the `->` chain at depth 0, stopping at the first `-∗`
       or the terminating `.`.  Returns [(start, end)] per premise, where the
       span EXCLUDES the trailing `->`, plus the arrow spans."""
    out = []
    depth = 0
    start = i
    n = len(t)
    while i < n:
        c = t[i]
        if c == '"':
            j = t.find('"', i + 1)
            i = (j + 1) if j >= 0 else n
            continue
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth < 0:
                break
        elif depth == 0:
            if t.startswith('-∗', i):
                break
            if t.startswith('->', i):
                out.append((start, i, i + 2))
                i += 2
                start = i
                continue
            if c == '.' and (i + 1 >= n or t[i+1] in ' \n\t\r'):
                break
        i += 1
    return out


def scan(path):
    """[(kind, name, nargs, [(premise_index, span, arrowspan, field)])]"""
    raw = open(path, encoding='utf-8').read()
    t = strip_comments(raw)
    out = []
    for kind, name, nspan, regions, dstart in declarations(t):
        bs = []
        for (lo, hi) in regions:
            bs += parse_binders(t, lo, hi)
        nargs = sum(len(b['names']) for b in bs if b['kind'] == 'explicit')
        i = body_start(t, kind, regions)
        i, nlets = skip_lets(t, i)
        ps = premises(t, i)
        ties = []
        for idx, (s, e, ae) in enumerate(ps):
            m = TIE.match(t[s:e])
            if m:
                ties.append((idx, (s, e), (e, ae), m.group(1)))
        if ties:
            out.append((kind, name, nargs, nlets, len(ps), ties, dstart))
    return raw, t, out


if __name__ == '__main__':
    import sys
    tot = 0
    for f in sys.argv[1:]:
        raw, t, res = scan(f)
        if not res:
            continue
        print('=== ' + os.path.basename(f))
        for (kind, name, nargs, nlets, npr, ties, dstart) in res:
            print('   %-10s %-34s nargs=%-3d lets=%d npr=%-3d ties=%s' % (
                kind, name, nargs, nlets, npr,
                ' '.join('%d:%s@%d' % (i, fl, nargs + i) for (i, _, _, fl) in ties)))
            tot += len(ties)
    print('total tie premises:', tot)
