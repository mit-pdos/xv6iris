#!/usr/bin/env python3
"""Checks that no declaration NAMES an ambient config field -- `icfg_*` from
`IcacheRef.icfg`, `fsc_*` from `FsCfg.fscfg` -- outside a binder group or
enclosing `Context` that carries the class (`icfg` / `fscfg`, or the `fileG`
that projects to both), and that a file naming `fsc_*` requires `FsCfg`.

  run: python3 tools/dethread_check.py [IRIS_DIR]      (default: ./iris)

WHY IT IS NOT JUST STYLE (rank 1b's memory bomb, claude-notes/durable-notes.md):
a field named where the class is out of scope is NOT a type error.  Typeclass
resolution goes hunting for `fileG Σ` with `Σ` unknown and does not come back
-- two such declarations reached 190 GB before they were killed, and the build
log says only `Error 143`.  De-thread a declaration ONLY where the class is
already reachable; a declaration outside that scope is below the contract
surface by construction and keeps its parameters.

Exit status is 0 when the count is zero.  Three declarations are EXEMPT and
they are structural, not excused: `FsCfg` is where `fscfg` is declared, and
`IcacheRef.icfg_alloc` / `FsCfgSnap.fs_cfg_alloc_snap` are the ALLOCATORS,
which bind the instance existentially INSIDE the statement (`⊢ |==> ∃ (ICFG :
icfg) …, ⌜icfg_dev = dv⌝ ∗ …`) where no header scan can see it.
"""
import sys, os, re

IDENT = r"[A-Za-z_Ͱ-Ͽἀ-῿'][A-Za-z0-9_'Ͱ-Ͽἀ-῿]*"
OPEN, CLOSE = '([{', ')]}'

ICFG_FIELD = re.compile(r'\bicfg_[a-z]+\b')
FSC_FIELD = re.compile(r'\bfsc_[a-z]+\b')
HAS_ICFG = re.compile(r'\bicfg\b|\bfileG\b')
HAS_FSCFG = re.compile(r'\bfscfg\b|\bfileG\b')

EXEMPT_FILE = {'FsCfg'}
EXEMPT_DECL = {('IcacheRef', 'icfg_alloc'), ('FsCfgSnap', 'fs_cfg_alloc_snap')}

DECLKW = (r'(?:^|\n)\s*(?:Local\s+|Global\s+|Program\s+|#\[[^\]]*\]\s*)*'
          r'(Definition|Lemma|Theorem|Corollary|Fact|Remark|Parameter|Axiom'
          r'|Fixpoint|Instance)\s+(' + IDENT + r')')


def strip_comments(s):
    """same length, `(* … *)` blanked (nesting-aware), newlines kept"""
    out, i, depth, n = list(s), 0, 0, len(s)
    while i < n:
        if s.startswith('(*', i):
            depth += 1
            out[i] = out[i + 1] = ' '
            i += 2
            continue
        if s.startswith('*)', i) and depth:
            depth -= 1
            out[i] = out[i + 1] = ' '
            i += 2
            continue
        if depth and s[i] != '\n':
            out[i] = ' '
        i += 1
    return ''.join(out)


def skip_ws(t, i):
    while i < len(t) and t[i].isspace():
        i += 1
    return i


def find_top(t, i, stops):
    """first `stops` string at bracket depth 0, as (index, stop)"""
    depth = 0
    while i < len(t):
        c = t[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0:
            for s in stops:
                if t.startswith(s, i):
                    if s == ':' and t.startswith(':=', i):
                        continue
                    return i, s
        i += 1
    return -1, None


def declarations(t):
    """(name, binder-region text, declaration start) per declaration.  The
       binder region is the header's own PLUS the statement's leading
       `forall`, which is where a `Parameter` and a `Lemma X : forall …` put
       every binder."""
    for m in re.finditer(DECLKW, t):
        kind, name, lo = m.group(1), m.group(2), m.end()
        if kind in ('Parameter', 'Axiom'):
            k, s = find_top(t, lo, [':'])
            if k < 0:
                continue
            regions, k = [(lo, k)], k + 1
        else:
            k, s = find_top(t, lo, [':=', ':'])
            if k < 0:
                continue
            regions = [(lo, k)]
            if s != ':':
                yield name, ''.join(t[a:b] for a, b in regions), m.start(1)
                continue
            k += 1
        j = skip_ws(t, k)
        if t.startswith('forall', j) and not re.match(IDENT, t[j + 6:j + 7]):
            k2, _ = find_top(t, j + 6, [','])
            if k2 >= 0:
                regions.append((j + 6, k2))
        yield name, ''.join(t[a:b] for a, b in regions), m.start(1)


def decl_end(t, i):
    """end of the declaration: its terminating `.`, or its `Qed.`"""
    depth, n = 0, len(t)
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
        elif c == '.' and depth <= 0 and (i + 1 >= n or t[i + 1] in ' \n\t\r'):
            break
        i += 1
    j = skip_ws(t, i + 1)
    if t.startswith('Proof', j):
        m = re.search(r'\b(Qed|Defined|Admitted|Abort)\.', t[j:])
        if m:
            return j + m.end()
    return i + 1


def scopes(t):
    """Section/Module open+close and Context events, with what each Context
       brings into scope"""
    ev = []
    for m in re.finditer(r'(?:^|\n)[ \t]*(Section|End|Context|Module)\b([^\n]*)', t):
        kw = m.group(1)
        if kw == 'Context':
            i, depth, j = m.end(1), 0, m.end(1)
            while j < len(t):
                c = t[j]
                if c in OPEN:
                    depth += 1
                elif c in CLOSE:
                    depth -= 1
                elif c == '.' and depth == 0 and (j + 1 >= len(t) or t[j + 1] in ' \n\t\r'):
                    break
                j += 1
            ev.append((m.start(1), 'ctx', bool(HAS_ICFG.search(t[i:j])),
                       bool(HAS_FSCFG.search(t[i:j]))))
        elif kw == 'End':
            ev.append((m.start(1), 'close', False, False))
        else:
            ev.append((m.start(1), 'open', False, False))
    return ev


def in_scope(ev, pos):
    """(icfg reachable, fscfg reachable) at pos -- a Context dies with the
       Section that opened it"""
    stack = [[]]
    for p, kind, hi, hf in ev:
        if p >= pos:
            break
        if kind == 'open':
            stack.append([])
        elif kind == 'close':
            if len(stack) > 1:
                stack.pop()
        else:
            stack[-1].append((hi, hf))
    return (any(a for fr in stack for a, _ in fr),
            any(b for fr in stack for _, b in fr))


def main():
    iris = sys.argv[1] if len(sys.argv) > 1 else 'iris'
    proj = os.path.join(iris, '_CoqProject')
    if not os.path.exists(proj):
        sys.exit('no %s -- give the iris directory as the argument' % proj)
    files = sorted(set(
        re.findall(r'([A-Za-z0-9_]+)\.v',
                   '\n'.join(l for l in open(proj, encoding='utf-8')
                             if not l.lstrip().startswith('#')))))
    bad = 0
    for b in files:
        p = os.path.join(iris, b + '.v')
        if not os.path.exists(p):
            continue
        t = strip_comments(open(p, encoding='utf-8').read())
        if not (ICFG_FIELD.search(t) or FSC_FIELD.search(t)):
            continue
        if (b not in EXEMPT_FILE and FSC_FIELD.search(t)
                and not re.search(r'Require\s+(Import\s+|Export\s+)?[^.\n]*\bFsCfg\b', t)):
            print('%s: names fsc_* but does not Require FsCfg' % b)
            bad += 1
        ev = scopes(t)
        for name, binders, dstart in declarations(t):
            if (b, name) in EXEMPT_DECL:
                continue
            body = t[dstart:decl_end(t, dstart)]
            si, sf = in_scope(ev, dstart)
            si = si or bool(HAS_ICFG.search(binders))
            sf = sf or bool(HAS_FSCFG.search(binders))
            if ICFG_FIELD.search(body) and not si:
                print('%s: %s names icfg_* with no icfg in scope' % (b, name))
                bad += 1
            if FSC_FIELD.search(body) and not sf:
                print('%s: %s names fsc_* with no fscfg in scope' % (b, name))
                bad += 1
    print('%d declarations out of scope' % bad)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
