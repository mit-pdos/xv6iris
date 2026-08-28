#!/usr/bin/env python3
"""R1c de-threading tool.

Phase 1 (analyse): over a given set of .v files, find every declaration that
binds one of the four R1c names at its R1c type, and record which EXPLICIT
argument positions of that declaration disappear.

Phase 2 (rewrite): over the whole tree, drop those positional arguments at
every application of the declaration's name (bare or module-qualified), then
delete the binders and rename the remaining token uses to the icfg field.

Everything the tool cannot prove safe is REPORTED, never guessed.
"""
import re, sys, os, json, collections

TARGET = {
    ('dev',   'mword 32'): 'icfg_dev',
    ('nib',   'nat'):      'icfg_nib',
    ('inodestart', 'Z'):   'icfg_ist',
    ('g',     'log_names'):    'icfg_log',
    ('γ',     'log_names'):    'icfg_log',
    ('glog',  'log_names'):    'icfg_log',
    ('γlog',  'log_names'):    'icfg_log',
}
TOKENS = set(n for (n, _) in TARGET)

IDENT = r"[A-Za-z_Ͱ-Ͽἀ-῿'][A-Za-z0-9_'Ͱ-Ͽἀ-῿]*"

# ---------------------------------------------------------------- lexing

def strip_comments(s):
    """return a same-length string with (* *) replaced by spaces"""
    out = list(s)
    i, depth = 0, 0
    n = len(s)
    while i < n:
        if s.startswith('(*', i):
            depth += 1
            out[i] = out[i+1] = ' '
            i += 2
            continue
        if s.startswith('*)', i) and depth:
            depth -= 1
            out[i] = out[i+1] = ' '
            i += 2
            continue
        if depth:
            if s[i] != '\n':
                out[i] = ' '
        i += 1
    return ''.join(out)

OPEN = '([{'
CLOSE = ')]}'

def skip_ws(t, i):
    while i < len(t) and t[i].isspace():
        i += 1
    return i

def match_group(t, i):
    """t[i] is an opener; return index just past the matching closer"""
    depth = 0
    while i < len(t):
        c = t[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return len(t)

def find_top(t, i, stops):
    """scan from i, return (index, stop) of the first stop string at depth 0"""
    depth = 0
    while i < len(t):
        c = t[i]
        if c in OPEN:
            depth += 1
            i += 1
            continue
        if c in CLOSE:
            depth -= 1
            i += 1
            continue
        if depth == 0:
            for s in stops:
                if t.startswith(s, i):
                    # ':=' must win over ':'
                    if s == ':' and t.startswith(':=', i):
                        continue
                    return i, s
        i += 1
    return -1, None

# ------------------------------------------------------------- binders

def parse_binders(t, lo, hi):
    """Parse the binder region t[lo:hi].  Return a list of records:
         {'kind': 'explicit'|'implicit', 'span': (a,b), 'names': [(name, span)],
          'type': str, 'typespan': (a,b)}
       Explicit groups contribute to positional argument numbering."""
    out = []
    i = lo
    while i < hi:
        i = skip_ws(t, i)
        if i >= hi:
            break
        c = t[i]
        if c == '`':
            j = i + 1
            j = skip_ws(t, j)
            if j < hi and t[j] in OPEN:
                e = match_group(t, j)
                out.append({'kind': 'implicit', 'span': (i, e), 'names': [], 'type': ''})
                i = e
                continue
            i += 1
            continue
        if c == '{':
            e = match_group(t, i)
            out.append({'kind': 'implicit', 'span': (i, e), 'names': [], 'type': ''})
            i = e
            continue
        if c == '(':
            e = match_group(t, i)
            inner = t[i+1:e-1]
            k, s = find_top(inner, 0, [':'])
            if k < 0:
                out.append({'kind': 'explicit', 'span': (i, e), 'names': [], 'type': ''})
            else:
                names = []
                for m in re.finditer(IDENT, inner[:k]):
                    names.append((m.group(0), (i+1+m.start(), i+1+m.end())))
                ty = inner[k+1:].strip()
                out.append({'kind': 'explicit', 'span': (i, e), 'names': names,
                            'type': ty, 'typespan': (i+1+k+1, e-1)})
            i = e
            continue
        # a bare identifier binder (rare in this tree, e.g. `forall x, ...`)
        m = re.match(IDENT, t[i:hi])
        if m:
            out.append({'kind': 'explicit', 'span': (i, i+m.end()),
                        'names': [(m.group(0), (i, i+m.end()))], 'type': None})
            i += m.end()
            continue
        i += 1
    return out

DECLKW = r'(?:^|\n)\s*(?:Local\s+|Global\s+|Program\s+|#\[[^\]]*\]\s*)*(Definition|Lemma|Theorem|Corollary|Fact|Remark|Parameter|Axiom|Fixpoint|Instance)\s+(' + IDENT + r')'

def declarations(t):
    """yield (kind, name, namespan, regions, decl_start).  REGIONS is the list
       of binder regions: the header's own, plus the statement's leading
       `forall` when there is one -- a Module Type Parameter and a
       `Lemma X : forall ...` both put every binder there."""
    for m in re.finditer(DECLKW, t):
        kind, name = m.group(1), m.group(2)
        lo = m.end()
        if kind in ('Parameter', 'Axiom'):
            k, s = find_top(t, lo, [':'])
            if k < 0:
                continue
            regions = [(lo, k)]
            k += 1
        else:
            k, s = find_top(t, lo, [':=', ':'])
            if k < 0:
                continue
            regions = [(lo, k)]
            if s != ':':
                yield (kind, name, m.span(2), regions, m.start(1))
                continue
            k += 1
        j = skip_ws(t, k)
        if t.startswith('forall', j) and not re.match(IDENT, t[j+6:j+7]):
            j2 = j + 6
            k2, s2 = find_top(t, j2, [','])
            if k2 >= 0:
                regions.append((j2, k2))
        yield (kind, name, m.span(2), regions, m.start(1))


def analyse(path):
    raw = open(path, encoding='utf-8').read()
    t = strip_comments(raw)
    res = []
    for kind, name, nspan, regions, dstart in declarations(t):
        bs = []
        for (lo_, hi_) in regions:
            bs += parse_binders(t, lo_, hi_)
        blo, bhi = regions[0][0], regions[-1][1]
        pos = 0
        drops = []
        for b in bs:
            if b['kind'] != 'explicit':
                continue
            ty = (b['type'] or '').strip()
            for nm, sp in b['names']:
                if (nm, ty) in TARGET:
                    drops.append((pos, nm, TARGET[(nm, ty)]))
                pos += 1
        if drops:
            res.append({'kind': kind, 'name': name, 'binders': bs,
                        'blo': blo, 'bhi': bhi, 'drops': drops, 'nargs': pos})
    return raw, t, res

# --------------------------------------------------------------- apply

def args_of(t, i):
    """Read a maximal application argument list starting at i (just past head).
       Return list of (start, end) spans."""
    out = []
    while True:
        j = skip_ws(t, i)
        if j >= len(t):
            break
        c = t[j]
        if c in OPEN:
            e = match_group(t, j)
            out.append((j, e))
            i = e
            continue
        if c == '@':
            # explicit-arguments application: refuse
            return None
        m = re.match(r"(?:" + IDENT + r"(?:\." + IDENT + r")*|_|[0-9]+(?:%[A-Za-z]+)?)", t[j:])
        if m:
            w = m.group(0)
            if w in ('with', 'as', 'in', 'then', 'else', 'end', 'forall', 'fun',
                     'let', 'if', 'match', 'return', 'do'):
                break
            out.append((j, j + m.end()))
            i = j + m.end()
            continue
        break
    return out

def main():
    cmd = sys.argv[1]
    files = sys.argv[2:]
    if cmd == 'analyse':
        table = {}
        for f in files:
            raw, t, res = analyse(f)
            for r in res:
                table.setdefault(r['name'], []).append(
                    {'file': os.path.basename(f), 'drops': [d[0] for d in r['drops']],
                     'names': [d[1] for d in r['drops']], 'nargs': r['nargs'],
                     'kind': r['kind']})
        json.dump(table, sys.stdout, ensure_ascii=False, indent=1)
    else:
        raise SystemExit('unknown cmd')

if __name__ == '__main__':
    main()
