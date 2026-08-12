#!/usr/bin/env python3
"""relayout_shift.py -- the SHIFT-AWARE relayout map.  Use this one whenever a
function GAINED OR LOST an instruction; use relayout_map.py when it only moved.

WHY BOTH EXIST.  relayout_map.py compares the old and new images AT THE SAME
OFFSET.  That is exact while both agree on where instructions start, and it is
what you want for a pure relayout.  The moment a function gains an instruction
every later offset names a DIFFERENT instruction in the two images, and the
comparison is between two unrelated things:

  * usually that shows up as a shape change, and relayout_map.py quarantines
    everything at or above the first one (it has to -- it cannot tell which
    of the two instructions is "the same" one);
  * occasionally the two unrelated instructions share a shape, and then the
    difference looks exactly like a moved immediate.  On CodeKexec.v that
    proposed rewriting phase B's tail (`ld s6,480(sp)` / `j +0x64`) with phase
    D's `ld s11,440(sp)` / `j +0x72`.  Both `ldsp`+`cj`; it typechecks.

So on a reshaped function relayout_map.py is SAFE but nearly useless: on
CodeVmfault.v it calls 48 of 55 offsets reshaped and can apply almost nothing.

WHAT THIS DOES INSTEAD.  It ALIGNS the two instruction streams with difflib
over NUMBER-NORMALISED ASTs -- so an immediate-only or register-only change
still aligns, and only a genuine insertion or deletion falls out of the
alignment.  From the alignment it derives:

  offmap     old offset -> new offset   (the shift, per instruction)
  immmap     the non-register immediates that really changed, per aligned pair
  regmap     register-field changes -- REPORTED, never applied, same rule as
             relayout_map.py: a moved register means gcc recompiled the
             function and the proof needs a human
  UNALIGNED  the inserted/deleted instructions themselves

THE `UNALIGNED` LIST IS THE CHECK, and it is also the most useful output in
the file: it should be exactly the instructions the C change added or removed,
and if it is bigger than that, the alignment is wrong and nothing else here
should be trusted.  On the psz bump it was 1 entry for kwait, 2 for sys_pipe
(two copyout call sites), 1 for filestat -- and on vmfault it printed, with no
help, precisely the semantic diff: the deleted `jal myproc`, the deleted
`ld a5,72(a0)` (p->sz), the deleted `ld a0,80(s1)` (p->pagetable) and the
inserted `li s4,0`.

It also caught something the same-offset view actively MISREPORTS: filestat's
epilogue shifts by +4, not the +2 it appears to, because old 0x4e/0x50 were
already `ld s2`/`ld s3`.  "The epilogue grew a saved register" was an artifact.

`apply` rewrites anchored immediates, remaps the ANCHOR OFFSETS themselves
(which relayout_map.py never has to do), and renumbers `Code<F>.v` lemma
names, single-pass.

TWO KNOWN GAPS, both wanting a human afterwards:
  * it does not rewrite an immediate on a continuation line whose anchor is
    several lines back (fix those by hand; `residue` in relayout_map.py still
    finds them);
  * hypothesis-name renumbering is NOT done, and cannot be done naively --
    prefixes like `Hrga5` mix a register name with an offset.

Usage:
    relayout_shift.py CodeVmfault.v vmfault
    relayout_shift.py CodeKwait.v kwait --proof ProofKwait.v --prefix kwi [--alias KW] [--write]

ALWAYS finish with `relayout_map.py residue <Code> <Proof> [ALIAS...]`.
"""
import sys, os, re, difflib
sys.path.insert(0, '/shared/xv6iris-4/tools')
import relayout_map as R

def align(code_file, sym):
    old = R.parse_code(R.read_old(code_file))
    new = R.parse_code(open(os.path.join(R.IRIS, code_file)).read())
    ol = [(k[1], v[0], v[1]) for k, v in sorted(old.items()) if k[0] == sym]
    nl = [(k[1], v[0], v[1]) for k, v in sorted(new.items()) if k[0] == sym]
    norm = lambda a: R.NUM_RE.sub('#', a)
    sm = difflib.SequenceMatcher(None, [norm(a) for _, a, _ in ol],
                                       [norm(a) for _, a, _ in nl])
    offmap, immmap, regmap, unaligned = {}, {}, {}, []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            for i, j in zip(range(i1, i2), range(j1, j2)):
                oo, _, on = ol[i]; no, _, nn = nl[j]
                offmap[oo] = no
                ip, rp = [], []
                for (o, oreg), (n, nreg) in zip(on, nn):
                    if o == n: continue
                    (rp if (oreg or nreg) else ip).append((o, n))
                if ip: immmap[oo] = ip
                if rp: regmap[oo] = rp
        else:
            for i in range(i1, i2): unaligned.append(('OLD', ol[i][0], ol[i][1]))
            for j in range(j1, j2): unaligned.append(('NEW', nl[j][0], nl[j][1]))
    return offmap, immmap, regmap, unaligned

ANCHOR = r'(?:KernelSyms\.)?\b(%s)\b\s*\+\s*(0x[0-9a-fA-F]+|\d+)'

def apply(proof_file, sym, prefix, offmap, immmap, aliases, write):
    path = os.path.join(R.IRIS, proof_file)
    text = open(path).read()
    names = {sym} | R.find_aliases(text, sym) | set(aliases)
    names = sorted(names, key=len, reverse=True)
    anchor_re = re.compile(ANCHOR % '|'.join(map(re.escape, names)))
    lines = text.split('\n')
    cur, out, log = None, [], []
    for ln, line in enumerate(lines, 1):
        spans = [(m.span(2), int(m.group(2), 0)) for m in anchor_re.finditer(line)]
        if spans:
            cur = spans[-1][1]
        keys = []
        if cur is not None:
            keys = [cur, cur + 4]
        pairs = [c for k in keys for c in immmap.get(k, ())]
        # freeze the anchor-offset spans
        pieces, off = [], 0
        for k, ((a, b), v) in enumerate(spans):
            pieces.append(line[off:a]); pieces.append('\x00%d\x00' % k); off = b
        pieces.append(line[off:])
        body = ''.join(pieces)
        if pairs:
            m = {}
            for o, n in pairs:
                if o in m and m[o] != n: m[o] = None
                else: m.setdefault(o, n)
            def rep(mo):
                v = int(mo.group(0), 0)
                if v in m and m[v] is not None:
                    nv = m[v]
                    log.append((ln, mo.group(0), nv))
                    return ('0x%x' % nv) if mo.group(0).startswith('0x') else str(nv)
                return mo.group(0)
            body = R.NUM_RE.sub(rep, body)
        # splice back the (possibly remapped) offsets
        for k, ((a, b), v) in enumerate(spans):
            nv = offmap.get(v, v)
            if nv != v: log.append((ln, 'OFF 0x%x' % v, nv))
            orig = line[a:b]
            body = body.replace('\x00%d\x00' % k,
                                ('0x%x' % nv) if orig.lower().startswith('0x') else str(nv))
        out.append(body)
    text2 = '\n'.join(out)
    # lemma-name renumbering, single pass
    lem = re.compile(r'\b' + re.escape(prefix) + r'([0-9a-f]{2,3})\b')
    def lrep(mo):
        v = int(mo.group(1), 16)
        nv = offmap.get(v)
        if nv is None: return mo.group(0)
        return prefix + ('%02x' % nv)
    text2 = lem.sub(lrep, text2)
    if write:
        open(path, 'w').write(text2)
    else:
        sys.stdout.writelines(difflib.unified_diff(text.split('\n'), text2.split('\n'),
                                                   'a', 'b', lineterm='', n=1))
        print()
    return log

if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('code'); ap.add_argument('sym')
    ap.add_argument('--proof'); ap.add_argument('--prefix')
    ap.add_argument('--alias', action='append', default=[])
    ap.add_argument('--write', action='store_true')
    a = ap.parse_args()
    offmap, immmap, regmap, unal = align(a.code, a.sym)
    print('== shifts ==')
    for o in sorted(offmap):
        if offmap[o] != o: print('   0x%03x -> 0x%03x' % (o, offmap[o]))
    print('== immediates ==')
    for o in sorted(immmap): print('   0x%03x: %s' % (o, immmap[o]))
    print('== REGISTERS REALLOCATED ==')
    for o in sorted(regmap): print('   0x%03x: %s' % (o, regmap[o]))
    print('== UNALIGNED ==')
    for t, o, ast in unal: print('   %s 0x%03x %s' % (t, o, ast[:100]))
    if a.proof:
        log = apply(a.proof, a.sym, a.prefix, offmap, immmap, a.alias, a.write)
        print('== %d substitutions ==' % len(log))
        for ln, o, n in log: print('   line %d: %s -> %s' % (ln, o, n))
