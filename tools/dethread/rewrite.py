#!/usr/bin/env python3
"""R1c rewriter.  See dethread.py for the parsing primitives."""
import sys, os, re, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dethread import (strip_comments, parse_binders, declarations, find_top,
                      match_group, skip_ws, TARGET, IDENT, OPEN, CLOSE)

SCR = os.path.dirname(os.path.abspath(__file__))
IRIS = os.environ.get('R1C_IRIS') or os.path.join(SCR, '..', 'iris')

# declarations whose class is NOT in scope: they stay threaded (memory bomb).
NOSCOPE = {
    ('ProofWritei.v', 'wi16_pre_spend'), ('ProofWritei.v', 'wi16_pre_join'),
    ('SpecDirlink.v', 'dl16_post'), ('SpecDirlink.v', 'ireg_blocks_ok'),
    ('SpecWritei.v', 'wi16_post'), ('SpecWritei.v', 'wi16_spend_any'),
}
# untyped binders the parser cannot classify: drop these names explicitly.
MANUAL = {
    ('FsSyscalls.v', 'fs_world_persistent'): {'glog', 'inodestart', 'nib', 'dev'},
    ('FsSyscalls.v', 'fs_world_all'):        {'glog', 'inodestart', 'nib', 'dev'},
    ('ProofKexecTail.v', 'fs_fabric_mk'):    {'g'},
    ('SpecItrunc.v', 'bm_paid_intro'):       {'γ'},
    ('SpecItrunc.v', 'bm_paidS_intro'):      {'γ'},
    ('SpecItrunc.v', 'bm_paidS_elim'):       {'γ'},
    ('SpecItrunc.v', 'bm_paid_elim'):        {'γ'},
    ('SpecCreate.v', 'create_locked_mk'):    {'dev'},
}

IDCHAR = "A-Za-z0-9_'Ͱ-Ͽἀ-῿"
def tokre(tok):
    return re.compile('(?<![' + IDCHAR + '.])' + re.escape(tok) + '(?![' + IDCHAR + '])')

# ------------------------------------------------------------------ spans

def decl_end(t, kind, blo, bhi):
    """end offset of the declaration's whole text (incl. Qed for proofs)"""
    # find the terminating '.' at depth 0 after the header
    i = bhi
    depth = 0
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
        elif c == '.' and depth <= 0:
            nxt = t[i+1] if i + 1 < n else ' '
            prv = t[i-1] if i else ' '
            if nxt in ' \n\t\r' and prv not in '.':
                break
        i += 1
    end = i + 1
    j = skip_ws(t, end)
    if t.startswith('Proof', j):
        for m in re.finditer(r'\b(Qed|Defined|Admitted|Abort)\.', t[j:]):
            return j + m.end()
    return end


def analyse_file(path):
    raw = open(path, encoding='utf-8').read()
    t = strip_comments(raw)
    base = os.path.basename(path)
    out = []
    for kind, name, nspan, regions, dstart in declarations(t):
        if (base, name) in NOSCOPE:
            continue
        blo, bhi = regions[0][0], regions[-1][1]
        manual = MANUAL.get((base, name), set())
        bs = []
        for (lo_, hi_) in regions:
            bs += parse_binders(t, lo_, hi_)
        pos = 0
        drops = []          # (position, name, field, name_span, group)
        for b in bs:
            if b['kind'] != 'explicit':
                continue
            ty = (b['type'] or '').strip()
            for nm, sp in b['names']:
                fld = TARGET.get((nm, ty))
                if fld is None and nm in manual:
                    fld = TARGET.get((nm, 'log_names')) if nm in ('g', 'γ', 'glog') else \
                          {'dev': 'icfg_dev', 'nib': 'icfg_nib',
                           'inodestart': 'icfg_ist'}.get(nm)
                if fld:
                    drops.append((pos, nm, fld, sp, b))
                pos += 1
        if drops:
            out.append({'kind': kind, 'name': name, 'blo': blo, 'bhi': bhi,
                        'dstart': dstart, 'drops': drops, 'nargs': pos,
                        'end': decl_end(t, kind, blo, bhi)})
    return raw, t, out

# ------------------------------------------------------------- application

NAMEDARG = re.compile(r'^\(\s*[' + IDCHAR + r']+\s*:=')

def args_of(t, i, limit):
    """positional arguments of an application.  A NAMED argument
       `(x := v)` binds an implicit and does not occupy a position."""
    out = []
    while i < limit:
        j = skip_ws(t, i)
        if j >= limit:
            break
        c = t[j]
        if c in OPEN:
            e = match_group(t, j)
            m2 = re.match(r'%[' + IDCHAR + r']+', t[e:])
            if m2:
                e += m2.end()
            if c == '(' and NAMEDARG.match(t[j:e]):
                i = e
                continue
            out.append((j, e))
            i = e
            continue
        if t.startswith('ltac:', j) or t.startswith('constr:', j) or t.startswith('uconstr:', j):
            k = j + t[j:].index(':') + 1
            k = skip_ws(t, k)
            if k < len(t) and t[k] in OPEN:
                e = match_group(t, k)
                out.append((j, e))
                i = e
                continue
            break
        m = re.match(r"(?:[" + IDCHAR + r"]+(?:\.[" + IDCHAR + r"]+)*|[∅⊤⊥]|_)", t[j:])
        if m:
            w = m.group(0)
            if w in ('with', 'as', 'in', 'then', 'else', 'end', 'forall', 'fun',
                     'let', 'if', 'match', 'return', 'do', 'at', 'by', 'using'):
                break
            e = j + m.end()
            m2 = re.match(r'%[' + IDCHAR + r']+', t[e:])
            if m2:
                e += m2.end()
            out.append((j, e))
            i = e
            continue
        break
    return out

EXPECT = {'dev', 'nib', 'inodestart', 'g', 'γ', 'glog', 'γlog',
          "dev'", "nib'", "inodestart'", "g'", "γ'", "glog'", 'cdev',
          'icfg_dev', 'icfg_nib', 'icfg_ist', 'icfg_log', '_'}
# the names records' projections (fclose_names & co.) lose these fields too
PROJ = re.compile(r'^\(\s*(fcn|frn|fwn|fsn|un)_(dev|nib|inodestart|log|ist|glog|lg)\s+'
                  r'[' + IDCHAR + r']+\s*\)$')

def expected(a):
    return a in EXPECT or bool(PROJ.match(a))

def main():
    mode = sys.argv[1]
    cut = [l.strip() for l in open(os.path.join(SCR, 'cut.txt')) if l.strip()]
    allf = sorted(set(re.findall(
        r'([A-Za-z0-9_]+)\.v',
        '\n'.join(l for l in open(os.path.join(IRIS, '_CoqProject'), encoding='utf-8')
                  if not l.lstrip().startswith('#')))))

    # ---- pass 1: the drop table.  A name may be declared in more than one
    # file (a Proof lemma inside a Section vs the Module Type's Parameter,
    # which carries the section variables as leading arguments).  Uses INSIDE
    # a declaring file take that file's signature; every other file takes the
    # sealed one, which is the Spec's.
    local = collections.defaultdict(dict)
    table = {}
    conflicts = []

    def public(b):
        return b.startswith('Spec') or b.startswith('Fs')

    for b in cut:
        p = os.path.join(IRIS, b + '.v')
        raw, t, decls = analyse_file(p)
        for d in decls:
            key = d['name']
            ds = tuple(sorted(x[0] for x in d['drops']))
            local[b][key] = ds
            if key in table and table[key][0] != ds:
                conflicts.append((key, table[key], (ds, b)))
                if not public(b):
                    continue
            table[key] = (ds, b)
    if conflicts:
        print('CONFLICTING DROP SETS (resolved file-locally):', file=sys.stderr)
        for c in conflicts:
            print('  ', c, file=sys.stderr)
    if mode == 'table':
        for k in sorted(table):
            print(k, table[k][0], table[k][1])
        print('total declarations:', len(table), file=sys.stderr)
        return

    names = sorted(table, key=len, reverse=True)
    headre = re.compile('(?<![' + IDCHAR + r'.])((?:[' + IDCHAR + r']+\.)*)(' +
                        '|'.join(re.escape(n) for n in names) + ')(?![' + IDCHAR + '])')

    stats = collections.Counter()
    problems = []
    for b in allf:
        p = os.path.join(IRIS, b + '.v')
        if not os.path.exists(p):
            continue
        raw = open(p, encoding='utf-8').read()
        t = strip_comments(raw)
        edits = []          # (start, end, replacement)
        declnames = set()
        declared_here = set()
        for kind, nmx, nspan, regions, dstart in declarations(t):
            declnames.add(nspan)
            declared_here.add(nmx)
        # ---- application argument drops (whole tree)
        for m in headre.finditer(t):
            nm = m.group(2)
            if m.span(2) in declnames:
                continue
            if m.group(1) == '':
                if nm in local[b]:
                    ds = local[b][nm]
                elif nm in declared_here:
                    continue            # a different declaration of the same name
                else:
                    ds = table[nm][0]
            else:
                ds = table[nm][0]
            args = args_of(t, m.end(), len(t))
            if len(args) <= max(ds):
                problems.append('%s:%d %s: only %d args, need >%d' %
                                (b, t[:m.start()].count('\n') + 1, nm, len(args), max(ds)))
                continue
            ok = True
            for k in ds:
                a = t[args[k][0]:args[k][1]]
                if not expected(a):
                    ok = False
            if not ok:
                problems.append('%s:%d %s: args %s' %
                                (b, t[:m.start()].count('\n') + 1, nm,
                                 [t[args[k][0]:args[k][1]] for k in ds]))
                continue
            for k in ds:
                s, e = args[k]
                # swallow the preceding whitespace
                s2 = s
                while s2 > 0 and t[s2-1] in ' ':
                    s2 -= 1
                if s2 == s:
                    edits.append((s, e, ''))
                else:
                    edits.append((s2, e, ''))
            stats['apps'] += 1
        # ---- binder removal + rename, in the cut only
        if b in cut:
            raw2, t2, decls = analyse_file(p)
            dropped_spans = [(s, e) for (s, e, _) in edits]
            for d in decls:
                groups = {}
                for pos, nm, fld, sp, grp in d['drops']:
                    groups.setdefault(id(grp), (grp, []))[1].append((nm, sp))
                for gid, (grp, items) in groups.items():
                    gs, ge = grp['span']
                    keep = [n for (n, _) in grp['names'] if n not in [i[0] for i in items]]
                    if keep:
                        rep = '(' + ' '.join(keep) + ' : ' + grp['type'].strip() + ')'
                        edits.append((gs, ge, rep))
                    else:
                        s2 = gs
                        while s2 > 0 and t[s2-1] in ' ':
                            s2 -= 1
                        edits.append((s2 if s2 < gs else gs, ge, ''))
                    stats['binders'] += len(items)
                # rename the token inside the declaration span
                toks = {nm: fld for (_, nm, fld, _, _) in d['drops']}
                lo, hi = d['dstart'], d['end']
                for nm, fld in toks.items():
                    for m in tokre(nm).finditer(t, lo, hi):
                        s, e = m.span()
                        if any(s >= a and e <= bnd for (a, bnd) in dropped_spans):
                            continue
                        if any(s >= grp['span'][0] and e <= grp['span'][1]
                               for (_, _, _, _, grp) in d['drops']):
                            continue
                        edits.append((s, e, fld))
                        stats['renames'] += 1
        if not edits:
            continue
        edits.sort(key=lambda x: (-x[0], -x[1]))
        seen = set()
        out = raw
        last = len(raw) + 1
        for (s, e, r) in edits:
            if e > last:
                problems.append('%s: overlapping edit at %d-%d' % (b, s, e))
                continue
            out = out[:s] + r + out[e:]
            last = s
        if mode == 'apply':
            open(p, 'w', encoding='utf-8').write(out)
        stats['files'] += 1

    print('stats:', dict(stats), file=sys.stderr)
    if problems:
        print('PROBLEMS (%d):' % len(problems), file=sys.stderr)
        for x in problems:
            print('  ', x, file=sys.stderr)

if __name__ == "__main__":
    main()
