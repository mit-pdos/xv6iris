#!/usr/bin/env python3
"""user_relayout.py -- re-point the hand-written user-tier proofs from one dump of
the user images to another (the playbook's "USER-IMAGE RELAYOUT").

Generalises tools/sh_rebase/ (sh only, hand-written region tables) to all seven
verified programs (cat echo init sh seccomp sync grep), with every map built
from CONTENT: the OLD `Xv6/User/<P>Image.lean` read from a git revision, the
NEW one from the working tree.

WHAT IT MAPS, per program P (old value -> new value):

  text     every instruction's pc, function by function through the symbol
           table (offset in the function kept; widths checked equal).  A
           function whose instruction count/widths changed is RESHAPED and is
           not mapped (reported; its pcs are hand work, tools/sh_rebase/genctor.py
           style).  The old end of text maps to the new end.
  rodata   every .rodata byte, by content: each NUL-terminated object
           (strings, `digits`) is located in the new .rodata (preceded by a NUL
           or the section start); interior addresses follow their object.  The
           `_rodata` SECTION START is mapped by symbol only where no object
           sits: the two can move differently (cat's 0x9b0 is the section
           start AND its first string, and maps as the string, to 0x9c0,
           while `_rodata` went to 0x9b8).
           .eh_frame is not mapped: a literal there is reported.
  temps    auipc results: a MOVED auipc's result maps to the new auipc's
           result; an UNMOVED auipc's result is pinned and never remapped.
           When it is also a moved pc/rodata address of P (sh's 0x1082,
           0x1110) the literal is read as the ADDRESS in a file that never
           names the auipc's own pc (sh's free/malloc walks), and is left and
           reported as a COLLISION in a file that does.
  geom     the R-X segment's filesz (`0xedc`-style).
  imm      every instruction whose encoding changed under the text map: its
           immediates (tools/sh_rebase/rvdec.py tokens), rewritten on lines
           that mention its NEW pc in the spelling found there (`0x39c#21`,
           `2096906#21`); an old immediate token left anywhere in P's files is
           reported (stated outside its instruction: an `assert`, a
           restated sign extension, a block lemma).
  size     the ELF file length (`<P>ElfRaw.elfSize`, decimal) -- in every
           Xv6/*.lean file, the old length is a distinctive 5-digit token.

Which program a literal belongs to: the programs a LINE names (`User.Cat`,
`cat_uis`, `ushm_uis`, `ushI_<pc>`, ...) else the programs its FILE names; a
literal that two candidate programs map differently is left and reported
(AMBIGUOUS).  Values given with --keep P:0xV,... are never remapped (round
constants inside a moved range: sh's `0x1000` page).

What it rewrites in a line: hex literals `0xV` (bare or `#64`; never other
`#W` -- those are immediates; never `+0xK` -- offsets), sh's fact names
`ush{I,MI,RI,EI}_<pc>`, objdump comment targets `7d8 <fprintf>` /
`9b0 <malloc+0xf6>` (offset recomputed), the changed instructions' asm
operands in comments (`addi a1,a1,-1680`), sh fact docstrings
"/-- `0xPC  asm` -/" (re-read from the new dump), and the immediates/sizes
above.  An old immediate stated away from its instruction's pc (a block
lemma's argument, a `show ukItypeVal …`) is rewritten when unambiguous (one
new value, no unmoved instruction of P carries it), else reported.

--as P reads every FILE as about P: the load-address-parametric ulib tables
(Xv6/Ulib*Code.lean) name no program but spell cat's objdump in comments,
and putc's `jal write` immediate is in the table.

ONE-SHOT: every address sweep is one-shot (playbook §4b-bis) -- running it a
second time over rewritten files re-maps new values as if old.  Run with no
--apply first (a dry run printing every edit), review, then --apply once.

REPORTS (stdout): the per-program move table, reshaped functions, every
collision/ambiguity/eh_frame/unattributed literal, round-valued remaps (a
multiple of 0x100: check it is an address), residual old immediates, and
`Sym.«f» + 0xK` offsets whose two ends moved differently (`write + 0x90 =
putc`: the offset is a literal no address map sees).

NOT MAPPED (by hand, from the report): offsets between two symbols
(`write + 0x90 = putc`, `ulibWriteAt base = base - 0x90`), values two
programs of a file map differently (AMBIGUOUS: `UshCat`'s cat filesz is an
unmoved sh pc), RESHAPED functions, .eh_frame literals, and prose
addresses of a program the line does not name.

Usage:
  tools/user_relayout.py --old-rev REV [--apply] [--keep P:0xV,...] [--as P] [FILES...]

The chroot bump (old images at 269f3cfa8, new at b72cbac1):
  tools/user_relayout.py --old-rev 269f3cfa8 --keep Sh:0x1000,0xfe0 --apply
  tools/user_relayout.py --old-rev 269f3cfa8 --as Cat --apply Xv6/Ulib{Vprintf,Fprintf,Printf,Putc}Code.lean \
      Xv6/ProofUlibPutc.lean
(no FILES: every Xv6/*.lean that names a user program, generated User/ files
excluded).
"""
import argparse
import collections
import glob
import os
import re
import subprocess
import sys

R = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.join(R, 'tools', 'sh_rebase'))
from rvdec import decode, bits, sext  # noqa: E402

PROGS = ['Cat', 'Echo', 'Init', 'Sh', 'Seccomp', 'Sync', 'Grep']
NAMES = {
    'Cat': r'User\.Cat\b|\bcat_uis\b',
    'Echo': r'User\.Echo\b|\becho_uis\b',
    'Init': r'User\.Init\b|\binit_uis\b',
    'Sh': r'User\.Sh\b|\bush[A-Z]\w*|\bushm?_\w+|\bush(?:I|MI|RI|EI)_[0-9a-f]+\b',
    'Seccomp': r'User\.Seccomp\b|\bsecc_uis\b',
    'Sync': r'User\.Sync\b|\bsync_uis\b',
    'Grep': r'User\.Grep\b|\bgrep_uis\b',
}
NAMES_RE = {p: re.compile(v) for p, v in NAMES.items()}
ENTRY = re.compile(r'^\s*⟨(0x[0-9a-f]+), (\d+), (0x[0-9a-f]+)⟩,?\s*$')


class Image:
    def __init__(self, text):
        self.ins = []
        asm = None
        for line in text.split('\n'):
            m = re.match(r'\s*-- (.*)', line)
            if m:
                asm = m.group(1)
                continue
            m = ENTRY.match(line)
            if m:
                self.ins.append((int(m.group(1), 16), int(m.group(2)), int(m.group(3), 16), asm))
        self.pc = {a: (w, e, s) for a, w, e, s in self.ins}
        self.syms = {}
        self.symsize = {}
        for m in re.finditer(r'def «([^»]+)» : Nat := (0x[0-9a-f]+)(?:\s*-- size (0x[0-9a-f]+))?', text):
            self.syms[m.group(1)] = int(m.group(2), 16)
            if m.group(3):
                self.symsize[m.group(1)] = int(m.group(3), 16)
        g = dict(re.findall(r'def (textHi|rodataEnd) : Nat := (0x[0-9a-f]+)', text))
        self.textHi = int(g['textHi'], 16)
        c = re.search(r'def code : USeg where\n\s*vaddr := (0x[0-9a-f]+)\n\s*size := (0x[0-9a-f]+)\n'
                      r'\s*rows := \[(.*?)\]', text, re.S)
        rows = re.findall(r'^\s*0x([0-9a-f]+),?\s*(?:--.*)?$', c.group(3), re.M)
        self.filesz = int(c.group(2), 16)
        self.bytes = b''.join(bytes.fromhex(r.rjust(64, '0')) for r in rows)[:self.filesz]
        self.funcs = sorted((a, n) for n, a in self.syms.items()
                            if a < self.textHi and n not in self.symsize and not n.startswith('_'))
        self.ro_lo = self.syms['_rodata']
        ro_objs = [(a, self.symsize[n]) for n, a in self.syms.items() if n in self.symsize and a < 0x1000 * 64
                   and self.ro_lo <= a < self.filesz]
        self.ro_hi = max([a + s for a, s in ro_objs] + [self.ro_lo])
        # .rodata ends at the last NUL-terminated object before .eh_frame ("zR" augmentation)
        k = self.bytes.find(b'zR\x00', self.ro_lo)
        self.eh_lo = (k - 9) if k > 0 else self.filesz  # the CIE: length, id, version, "zR"
        self.ro_hi = max(self.ro_hi, self.eh_lo)

    def auipcs(self):
        return {a: a + (sext(bits(e, 31, 12), 20) << 12)
                for a, w, e, s in self.ins if w == 4 and (e & 0x7f) == 0x17}


def git_show(rev, path):
    return subprocess.run(['git', '-C', R, 'show', '%s:%s' % (rev, path)], check=True,
                          capture_output=True, text=True).stdout


def ro_objects(img):
    """NUL-terminated runs of non-NUL bytes in [ro_lo, eh_lo)."""
    out = []
    a = img.ro_lo
    while a < img.eh_lo:
        if img.bytes[a] == 0:
            a += 1
            continue
        b = img.bytes.index(b'\x00', a)
        out.append((a, img.bytes[a:b + 1]))
        a = b + 1
    return out


class Prog:
    def __init__(self, P, old, new, oldelf, newelf):
        self.P, self.old, self.new = P, old, new
        self.report = collections.defaultdict(list)
        self.tmap = {}
        self.reshaped = []
        nf = dict((n, a) for a, n in new.funcs)
        ofl = old.funcs + [(old.textHi, None)]
        for (a, n), (b, _) in zip(ofl, ofl[1:]):
            olds = [(x, w) for x, w, e, s in old.ins if a <= x < b]
            if n not in nf:
                self.reshaped.append((n, a, None))
                continue
            d = nf[n] - a
            if not all(x + d in new.pc and new.pc[x + d][0] == w for x, w in olds):
                self.reshaped.append((n, a, nf[n]))
                continue
            for x, w in olds:
                self.tmap[x] = x + d
        self.tmap[old.textHi] = new.textHi
        # rodata by content
        self.dmap = {}
        nobjs = ro_objects(new)
        for a, s in ro_objects(old):
            cands = [b for b, t in nobjs if t == s]
            if len(cands) != 1:
                cands = [b for b, t in nobjs if t.endswith(s)]  # a tail-merged string
                cands = [b + len(t) - len(s) for b, t in nobjs if t.endswith(s)]
            if len(cands) != 1:
                self.report['rodata-unplaced'].append('%#x %r -> %s' % (a, s[:24], [hex(c) for c in cands]))
                continue
            for k in range(len(s)):
                self.dmap[a + k] = cands[0] + k
        self.sec_start = (old.ro_lo, new.ro_lo)
        # auipc temporaries
        oa, na = old.auipcs(), new.auipcs()
        self.pinned = set()
        self.pinsrc = {}
        self.temps = {}
        for a, v in oa.items():
            n = self.tmap.get(a)
            if n is None:
                continue
            nv = na.get(n)
            if n == a and nv == v:
                self.pinned.add(v)
                self.pinsrc.setdefault(v, []).append(a)
            elif nv is not None:
                self.temps[v] = nv
        self.geom = {old.filesz: new.filesz} if old.filesz != new.filesz else {}
        self.size = (oldelf, newelf)
        # changed encodings and their immediates
        self.imms = []
        for a, w, e, s in old.ins:
            n = self.tmap.get(a)
            if n is None:
                continue
            nw, ne, ns = new.pc[n]
            if ne == e:
                continue
            do, dn = decode(e, w), decode(ne, nw)
            if do is None or dn is None:
                self.report['imm-nodecode'].append('%#x %s | %s' % (a, s, ns))
                continue
            to = re.findall(r'(\d+)#(\d+)', do)
            tn = re.findall(r'(\d+)#(\d+)', dn)
            pairs = [((int(x), int(wx)), (int(y), int(wy))) for (x, wx), (y, wy) in zip(to, tn) if x != y]
            self.imms.append((a, n, pairs, s, ns))
        self.oldimm = collections.defaultdict(set)
        for a, n, pairs, s, ns in self.imms:
            for (x, w), (y, _) in pairs:
                self.oldimm[(x, w)].add((y, n))
        self.unmoved_imm = set()
        for a, w, e, s in old.ins:
            if self.tmap.get(a) == a and new.pc.get(a, (0, e))[1] == e:
                d = decode(e, w)
                if d:
                    for x, wx in re.findall(r'(\d+)#(\d+)', d):
                        self.unmoved_imm.add((int(x), int(wx)))

    def mapv(self, v, as_pc=False):
        """(new value, kind) or (v, None).  as_pc: a pinned auipc result read as the address."""
        moved_t = self.tmap.get(v)
        moved_d = self.dmap.get(v)
        hit = None
        if moved_t is not None and moved_t != v:
            hit = (moved_t, 'text')
        elif moved_d is not None and moved_d != v:
            hit = (moved_d, 'rodata')
        elif v in self.temps and self.temps[v] != v:
            hit = (self.temps[v], 'temp')
        elif v in self.geom:
            hit = (self.geom[v], 'geom')
        elif v == self.sec_start[0] and self.sec_start[0] != self.sec_start[1]:
            hit = (self.sec_start[1], 'section')
        if hit and v in self.pinned and hit[1] != 'temp' and not as_pc:
            return v, 'collision'
        return hit if hit else (v, None)

    def table(self):
        o, n = self.old, self.new
        moves = collections.OrderedDict()
        for a in sorted(self.tmap):
            d = self.tmap[a] - a
            if d:
                moves.setdefault(('text', d), [a, a])[1] = a
        for a in sorted(self.dmap):
            d = self.dmap[a] - a
            moves.setdefault(('rodata', d), [a, a])[1] = a
        rows = ['%s %+#x on [%#x, %#x]' % (k, d, lo, hi) for (k, d), (lo, hi) in moves.items()]
        rows.append('textHi %#x->%#x  _rodata %#x->%#x  filesz %#x->%#x  elf %d->%d'
                    % (o.textHi, n.textHi, o.ro_lo, n.ro_lo, o.filesz, n.filesz, self.size[0], self.size[1]))
        return rows


def load(old_rev):
    progs = {}
    for P in PROGS:
        oi = Image(git_show(old_rev, 'Xv6/User/%sImage.lean' % P))
        ni = Image(open(os.path.join(R, 'Xv6/User/%sImage.lean' % P)).read())
        es = lambda t: int(re.search(r'def elfSize : Nat := (\d+)', t).group(1))
        oe = es(git_show(old_rev, 'Xv6/User/%sElfRaw.lean' % P))
        ne = es(open(os.path.join(R, 'Xv6/User/%sElfRaw.lean' % P)).read())
        progs[P] = Prog(P, oi, ni, oe, ne)
    return progs


HEX = re.compile(r'(?<![\w#+])0x([0-9a-fA-F]+)(?![\w])(#64)?')
FNAME = re.compile(r'\b(ush(?:I|MI|RI|EI))_([0-9a-f]+)\b')
OBJ = re.compile(r'(?<![\w#])([0-9a-f]{2,5}) <([A-Za-z_.0-9]+)(\+0x[0-9a-f]+)?>')
SYMOFF = re.compile(r'User\.(\w+)\.Sym\.«(\w+)» \+ 0x([0-9a-f]+) = User\.\1\.Sym\.«(\w+)»')


def symname(img, v):
    best = None
    for n, a in img.syms.items():
        if a <= v and not n.startswith('_') and (best is None or a > best[1]):
            best = (n, a)
    return best


class Rewriter:
    def __init__(self, progs, keep, as_prog=None):
        self.as_prog = as_prog
        self.progs = progs
        self.keep = keep
        self.report = collections.defaultdict(list)
        self.edits = []

    def cands(self, line, filep):
        if self.as_prog:
            return filep
        lp = [P for P in PROGS if NAMES_RE[P].search(line)]
        return lp if lp else filep

    def mapv(self, v, cands, where, kind_ok=None):
        res = {}
        for P in cands:
            if v in self.keep.get(P, ()):
                res[P] = (v, 'keep')
                continue
            nv, k = self.progs[P].mapv(v)
            if k == 'collision':
                srcs = self.progs[P].pinsrc[v]
                if any(re.search(r'(?<![\w#])0x%x(?![\w#])' % a, self.text) for a in srcs):
                    self.report['COLLISION left (the file names the auipc: resolve by hand)'].append(
                        '%s %s %#x (auipc at %s)' % (where, P, v, [hex(a) for a in srcs]))
                    res[P] = (v, k)
                else:
                    nv, k = self.progs[P].mapv(v, as_pc=True)
                    self.report['collision resolved as an address (the file never names the auipc %s)'
                                % P].append('%s %#x->%#x' % (where, v, nv))
                    res[P] = (nv, k)
            else:
                res[P] = (nv, k)
            if k is None:
                eh = self.progs[P].old
                if eh.eh_lo <= v < eh.filesz and v != eh.eh_lo:
                    self.report['eh_frame literal (not mapped)'].append('%s %s %#x' % (where, P, v))
        vals = {nv for nv, k in res.values()}
        if len(vals) > 1:
            self.report['AMBIGUOUS (programs disagree)'].append(
                '%s %#x %s' % (where, v, {P: hex(nv) for P, (nv, k) in res.items()}))
            return v, None
        if not cands:
            return v, None
        nv, k = next(iter(res.values()))
        if nv != v and v % 0x100 == 0:
            self.report['round value remapped (check it is an address)'].append('%s %#x->%#x' % (where, v, nv))
        return nv, (k if nv != v else None)

    def line(self, s, cands, where):
        if not cands:
            return s

        def namesub(m):
            v = int(m.group(2), 16)
            nv, k = self.mapv(v, ['Sh'], where)
            return '%s_%x' % (m.group(1), nv) if k else m.group(0)

        def hexsub(m):
            if m.group(2) is None and s2[m.end():m.end() + 1] == '#':
                return m.group(0)
            v = int(m.group(1), 16)
            nv, k = self.mapv(v, cands, where)
            return ('0x%x%s' % (nv, m.group(2) or '')) if k else m.group(0)

        def objsub(m):
            v = int(m.group(1), 16)
            nv, k = self.mapv(v, cands, where)
            if not k:
                return m.group(0)
            if m.group(3) and len(cands) == 1:
                sn = symname(self.progs[cands[0]].new, nv)
                if sn:
                    off = nv - sn[1]
                    return '%x <%s%s>' % (nv, sn[0], ('+%#x' % off) if off else '')
            return '%x <%s%s>' % (nv, m.group(2), m.group(3) or '')

        s2 = FNAME.sub(namesub, s)
        s2 = HEX.sub(hexsub, s2)
        s2 = OBJ.sub(objsub, s2)
        # immediates of changed instructions, on lines naming the new pc
        for P in cands:
            pr = self.progs[P]
            for a, n, pairs, so, sn in pr.imms:
                pcre = r'(?<![\w#])0x%x(?![\w#])' % n
                if P == 'Sh':
                    pcre += r'|\bush(?:I|MI|RI|EI)_%x\b' % n
                if not re.search(pcre, s2):
                    continue
                for (x, w), (y, _) in pairs:
                    tok = re.compile(r'(?<![\w#])(?:0x%x|%d)#%d(?![\w])' % (x, x, w))
                    def isub(m, y=y, w=w):
                        return ('0x%x#%d' % (y, w)) if m.group(0).startswith('0x') else ('%d#%d' % (y, w))
                    s2 = tok.sub(isub, s2)
        # asm text in comments ("0x44  addi a1,a1,-1680"): the changed instruction's old
        # objdump operands -> the new ones (jal/branch targets are the hex map's)
        for P in cands:
            for a, n, pairs, so, sn in self.progs[P].imms:
                mo = re.match(r'(\w+)\s+([^#<]*?)\s*(?:#|<|$)', so.replace('\t', ' '))
                mn = re.match(r'(\w+)\s+([^#<]*?)\s*(?:#|<|$)', sn.replace('\t', ' '))
                if not mo or not mn or mo.group(1) in ('jal', 'j') or mo.group(2) == mn.group(2):
                    continue
                pat = re.compile(re.escape(mo.group(1)) + r'(\s+)' + re.escape(mo.group(2)) + r'(?![\w(])')
                s2 = pat.sub(lambda m, mn=mn: mn.group(1) + m.group(1) + mn.group(2), s2)
        # docstrings of sh facts
        if 'Sh' in cands:
            def docsub(m):
                pc = int(m.group(1), 16)
                if pc in self.progs['Sh'].new.pc:
                    return '/-- `0x%x  %s` -/' % (pc, self.progs['Sh'].new.pc[pc][2].replace('\t', ' '))
                return m.group(0)
            s2 = re.sub(r'/-- `0x([0-9a-f]+)  [^`]*` -/', docsub, s2)
        # residual old immediates (stated outside their instruction: a block lemma's argument,
        # a `show ukItypeVal ...`): rewritten when unambiguous -- one new value, and no unmoved
        # instruction of the program carries the old one -- else reported
        for P in cands:
            pr = self.progs[P]
            for (x, w), ys in pr.oldimm.items():
                tok = re.compile(r'(?<![\w#])(?:0x%x|%d)#%d(?![\w])' % (x, x, w))
                newvals = {y for y, n in ys}
                for m in tok.finditer(s2):
                    if len(newvals) == 1 and (x, w) not in pr.unmoved_imm and len(cands) == 1:
                        self.report['residual old immediate rewritten (unambiguous)'].append(
                            '%s %s %s -> %d (the instruction at %s)' % (where, P, m.group(0), *newvals,
                                                                       sorted(hex(n) for y, n in ys)))
                    else:
                        amb = ' (ALSO an unmoved instruction\'s immediate)' if (x, w) in pr.unmoved_imm else ''
                        self.report['residual old immediate LEFT (ambiguous: fix by hand)'].append(
                            '%s %s %s -> %s%s' % (where, P, m.group(0), sorted((y, hex(n)) for y, n in ys), amb))
                if len(newvals) == 1 and (x, w) not in pr.unmoved_imm and len(cands) == 1:
                    y = next(iter(newvals))
                    s2 = tok.sub(lambda m, y=y, w=w: ('0x%x#%d' % (y, w)) if m.group(0).startswith('0x')
                                 else ('%d#%d' % (y, w)), s2)
        # symbol offsets whose ends moved differently
        for m in SYMOFF.finditer(s2):
            P = m.group(1)
            if P in self.progs:
                o, n = self.progs[P].old.syms, self.progs[P].new.syms
                f, g, k = m.group(2), m.group(4), int(m.group(3), 16)
                if f in n and g in n and n[g] - n[f] != k:
                    self.report['symbol offset literal moved (fix by hand)'].append(
                        '%s %s: %s + %#x = %s, now %#x' % (where, P, f, k, g, n[g] - n[f]))
        return s2

    def file(self, path):
        txt = open(path).read()
        self.text = txt
        rel = os.path.relpath(path, R)
        filep = [self.as_prog] if self.as_prog else [P for P in PROGS if NAMES_RE[P].search(txt)]
        out = []
        for i, l in enumerate(txt.split('\n'), 1):
            where = '%s:%d' % (rel, i)
            l2 = self.line(l, self.cands(l, filep), where)
            for P in PROGS:
                o, n = self.progs[P].size
                if o != n and re.search(r'(?<!\w)%d(?!\w)' % o, l2):
                    l2 = re.sub(r'(?<!\w)%d(?!\w)' % o, str(n), l2)
                    self.report['ELF length rewritten'].append('%s %s %d->%d' % (where, P, o, n))
            if l2 != l:
                self.edits.append((where, l, l2))
            out.append(l2)
        return '\n'.join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--old-rev', required=True, help='revision whose Xv6/User/<P>{Image,ElfRaw}.lean are the OLD images')
    ap.add_argument('--apply', action='store_true')
    ap.add_argument('--keep', action='append', default=[], help='P:0xV,0xW  values never remapped in P')
    ap.add_argument('--quiet-edits', action='store_true')
    ap.add_argument('--as', dest='as_prog', choices=PROGS,
                    help='read every FILE as about this program (the load-address-parametric ulib tables,\n'
                         'whose comments spell one program\'s objdump)')
    ap.add_argument('files', nargs='*')
    a = ap.parse_args()
    progs = load(a.old_rev)
    keep = collections.defaultdict(set)
    for k in a.keep:
        P, vs = k.split(':', 1)
        keep[P] |= {int(v, 16) for v in vs.split(',')}
    print('== move table (old -> new)')
    for P in PROGS:
        pr = progs[P]
        for r in pr.table():
            print('  %-8s %s' % (P, r))
        for n, x, y in pr.reshaped:
            print('  %-8s RESHAPED %s %s -> %s (not mapped)' % (P, n, hex(x), y and hex(y)))
        coll = sorted(v for v in pr.pinned if pr.mapv(v)[1] == 'collision')
        if coll:
            print('  %-8s pinned auipc results that are also moved addresses: %s' % (P, [hex(v) for v in coll]))
        for k, v in pr.report.items():
            for x in v:
                print('  %-8s %s: %s' % (P, k, x))
        for a_, n, pairs, so, sn in pr.imms:
            print('  %-8s imm %#x->%#x %s  [%s | %s]' % (P, a_, n, ['%d#%d->%d' % (x, w, y) for (x, w), (y, _) in pairs],
                                                        so, sn))
    files = a.files or sorted(f for f in glob.glob(os.path.join(R, 'Xv6', '*.lean'))
                              if any(NAMES_RE[P].search(open(f).read()) for P in PROGS))
    rw = Rewriter(progs, keep, a.as_prog)
    for f in files:
        t = open(f).read()
        t2 = rw.file(f)
        if a.apply and t2 != t:
            open(f, 'w').write(t2)
    if not a.quiet_edits:
        print('== edits (%d lines)' % len(rw.edits))
        for w, l, l2 in rw.edits:
            print('  %s\n    - %s\n    + %s' % (w, l.strip()[:200], l2.strip()[:200]))
    for k, v in rw.report.items():
        print('== %s (%d)' % (k, len(v)))
        for x in sorted(set(v)):
            print('  ', x)
    print('== files changed: %d' % len({w.split(':')[0] for w, _, _ in rw.edits}))


if __name__ == '__main__':
    main()
