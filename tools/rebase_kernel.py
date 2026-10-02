#!/usr/bin/env python3
"""Rebase the Lean proofs from one kernel ELF to another.

The proofs name kernel addresses literally (`0x80001ae0#64`), and spell the
immediates of the instructions they step through (`1420#12`, `6#20`,
`2096876#21`, `66#13`).  When the kernel is rebuilt from a later revision,
functions and data move and every relocation-dependent immediate changes.
This tool rewrites, in every non-generated `Xv6/*.lean`:

* every address literal inside the old image (text, data, bss, rodata) to
  the corresponding address in the new image -- text by the address's
  offset in its function, data/bss by its offset in its symbol, rodata
  strings by content;
* on every line that applies an instruction rule (`wp_s_<mn> c _ <pc>#64
  <rvc> <imm>#<w> ...`), the immediate, re-derived from the new
  instruction at the new pc (I/S-type `#12`, U-type `#20`, J-type `#21`,
  B-type `#13`);
* the `auipc`/`lui` helper lemmas (`theorem x : BitVec.signExtend 64
  (N#20 ++ 0#12) = 0xM#64`) named in a `with [x]` clause of a rewritten
  rule line.

Everything it cannot map is reported (functions whose instruction stream
changed, symbols that disappeared, ambiguous strings).  Functions whose
instructions sit at the same offsets and differ only in immediates
(struct strides, displacements, constants) are listed apart, as
"immediates only": their pcs map by offset.

Usage: tools/rebase_kernel.py OLD_ELF NEW_ELF [--objdump OBJDUMP] [--dry-run] [--intervals FILE] [FILES...]
       tools/rebase_kernel.py --fixup OLD_ELF NEW_ELF [--intervals FILE] ...
       tools/rebase_kernel.py --symbolic OLD_ELF NEW_ELF [--intervals FILE]
                              [--proc-array SYM:COUNT] [--proc-fields +START:DELTA,...] ...
       tools/rebase_kernel.py --symbolize NEW_ELF ... / --bridge NEW_ELF ...

--intervals FILE routes the pcs inside a RESHAPED function (one that gained
or lost instructions) by per-function shift intervals instead of the plain
offset, in the literal, --fixup and --symbolic passes (format: see
parse_intervals).  --symbolic is the pass for the symbolic tree (see its
section below).

The full pipeline for a new kernel build (the generated files first):
  1. tools/dump_kernel.py --kernel NEW_ELF --rev REV   (Xv6/KernelImage.lean, KernelTree)
  2. tools/gen_kernel_data.py --kernel NEW_ELF         (Xv6/KernelData.lean byte lists)
  3. tools/dump_elf_image.py --kernel NEW_ELF --rev REV (MachCSL/KernelElf.lean: the
     language's boot image, MachCSL.bootImage; Xv6.bootImage_wf checks 1-2 against it)
  4. this tool (literal pass, then --fixup once, then --symbolic once, each with
     the same --intervals), then the manual residue.
"""
import argparse, os, re, subprocess, sys, glob

OBJ = 'riscv64-linux-gnu-objdump'

def run(args):
    return subprocess.run(args, capture_output=True, text=True, check=True).stdout

def symbols(elf):
    d = {}
    for l in run([OBJ, '-t', elf]).splitlines():
        m = re.match(r'^([0-9a-f]{16}) (.{7}) (\S+)\t([0-9a-f]{16}) (\S+)$', l)
        if m:
            addr, sec, size, name = int(m.group(1), 16), m.group(3), int(m.group(4), 16), m.group(5)
            if sec in ('.text', '.data', '.bss', '.rodata'):
                d[name] = (addr, size, sec)
    return d

def functions(elf):
    """name -> (start, [(addr, mnemonic, operands, comment)])"""
    fs, cur = {}, None
    for l in run([OBJ, '-d', '--no-show-raw-insn', elf]).splitlines():
        m = re.match(r'^([0-9a-f]+) <([^>]+)>:$', l)
        if m:
            cur = m.group(2); fs[cur] = (int(m.group(1), 16), []); continue
        m = re.match(r'^\s*([0-9a-f]+):\t(.*)$', l)
        if m and cur:
            t = m.group(2)
            cm = None
            if '#' in t:
                t, cm = t.split('#', 1); cm = cm.strip()
            t = re.sub(r'\s+', ' ', t).strip()
            parts = t.split(' ', 1)
            fs[cur][1].append((int(m.group(1), 16), parts[0], parts[1] if len(parts) > 1 else '', cm))
    return fs

def section_bytes(elf, sec):
    out = run([OBJ, '-s', '-j', sec, elf])
    base, data = None, bytearray()
    for l in out.splitlines():
        m = re.match(r'^ ([0-9a-f]+) ((?:[0-9a-f]{2,8} ?){1,4})\s', l)
        if m:
            a = int(m.group(1), 16)
            if base is None: base = a
            for w in m.group(2).split():
                data += bytes.fromhex(w)
    return base, bytes(data)

def norm(name, start, ins):
    """the instruction stream up to relocation: symbolic data references, jump targets"""
    res = []
    for a, mn, ops, cm in ins:
        t = mn + ' ' + ops
        if mn == 'mv': t = 'addi ' + ops + ',0'; mn = 'addi'
        if mn == 'auipc': t = 'auipc ' + ops.split(',')[0] + ',?'
        symc = None
        if cm:
            mc = re.match(r'([0-9a-f]+) <([^>]+)>', cm)
            if mc: symc = re.sub(r'\+0x[0-9a-f]+$', '', mc.group(2))
        if symc and mn in ('addi', 'ld', 'lw', 'sd', 'sw', 'lbu', 'sb', 'lhu', 'sh', 'lwu', 'lh', 'lb'):
            t = re.sub(r'-?\d+\(', '(', t); t = re.sub(r',-?\d+$', '', t); t += '<' + symc + '>'
        m = re.search(r'([0-9a-f]{8}) <([^>]+)>', t)
        if m:
            tgt = int(m.group(1), 16); base = re.sub(r'\+0x[0-9a-f]+$', '', m.group(2))
            t = t[:m.start()] + ('<+%x>' % (tgt - start) if base == name else '<' + base + '>') + t[m.end():]
        res.append(t)
    return res

def norm_imm(name, start, ins):
    """`norm` with every immediate and displacement blanked (jump targets kept), keyed by offset:
    equal for two functions whose instructions differ only in stride/displacement/constant fields"""
    res = []
    for t, (a, mn, ops, cm) in zip(norm(name, start, ins), ins):
        k = t.find('<')
        head, tail = (t, '') if k < 0 else (t[:k], t[k:])
        res.append((a - start, re.sub(r'(?<![\w.])-?(?:0x[0-9a-f]+|\d+)(?![\w])', 'N', head) + tail))
    return res

def parse_intervals(path):
    """--intervals FILE: per reshaped function its old-offset -> new-offset map, one line each,
    `f:+START:DELTA[,+START:DELTA...]` (`#` starts a comment).  DELTA (`+N`/`-N`, hex or decimal)
    applies from old offset START up to the next START; `x` marks the old offsets from START on as
    unmapped (the replaced region: rewritten by hand, reported).  Offsets below the first START map
    to themselves."""
    iv = {}
    with open(path) as fh:
        text = fh.read()
    for raw in text.split('\n'):
        line = raw.split('#', 1)[0].strip()
        if not line: continue
        f, rest = line.split(':', 1)
        for item in rest.split(','):
            item = item.strip()
            if not item: continue
            st, d = item.rsplit(':', 1)
            iv.setdefault(f.strip(), []).append((int(st.strip().lstrip('+'), 0),
                                                 None if d.strip() in ('x', 'X') else int(d.strip(), 0)))
    for f in iv: iv[f].sort()
    return iv

class Rebase:
    def __init__(self, old, new, intervals=None, tables=None):
        """`tables` (tests): (symbols, symbols, functions, functions, rodata, rodata) of old and new
        in place of reading the two ELFs"""
        if tables is None:
            tables = (symbols(old), symbols(new), functions(old), functions(new),
                      section_bytes(old, '.rodata'), section_bytes(new, '.rodata'))
        self.so, self.sn, self.fo, self.fn, (self.ro_base, self.ro), (self.rn_base, self.rn) = tables
        self.iv = intervals or {}
        self.changed = set()
        self.imm_only = set()   # same instructions at the same offsets, only immediates differ
        self.first_diff = {}
        for f, (s, ins) in self.fo.items():
            if f not in self.fn: self.changed.add(f); self.first_diff[f] = 0; continue
            a, b = norm(f, s, ins), norm(f, *self.fn[f])
            oa = [x[0] - s for x in ins]; ob = [x[0] - self.fn[f][0] for x in self.fn[f][1]]
            if a != b or oa != ob:
                if oa == ob and norm_imm(f, s, ins) == norm_imm(f, *self.fn[f]):
                    self.imm_only.add(f); continue
                self.changed.add(f)
                k = 0
                while k < min(len(a), len(b)) and a[k] == b[k] and oa[k] == ob[k]: k += 1
                self.first_diff[f] = ins[k][0] if k < len(ins) else s + 0x100000
        self.text_lo = min(s for s, _ in self.fo.values())
        self.text_hi = max(s + sum(0 for _ in ins) for s, ins in self.fo.values())
        self.new_ins = {}
        for f, (s, ins) in self.fn.items():
            for a, mn, ops, cm in ins: self.new_ins[a] = (mn, ops, cm)
        self.old_ins = {}
        for f, (s, ins) in self.fo.items():
            for a, mn, ops, cm in ins: self.old_ins[a] = (f, mn, ops, cm)
        self.report = []

    def newoff(self, f, o):
        """old offset `o` in text function `f` -> its new offset (None: inside a replaced region)"""
        d = 0
        for st, dd in self.iv.get(f, ()):
            if o >= st: d = dd
            else: break
        return None if d is None else o + d

    def func_of(self, a):
        best = None
        for f, (s, ins) in self.fo.items():
            if ins and s <= a <= ins[-1][0] + 4 and (best is None or s > best[1]): best = (f, s)
        return best

    def map_addr(self, a, where):
        """old address -> new address, or None"""
        # text
        fb = self.func_of(a)
        if fb:
            f, s = fb
            if f not in self.fn:
                self.report.append('%s: %#x in %s, which is gone' % (where, a, f)); return None
            if f in self.iv:
                n = self.newoff(f, a - s)
                if n is None:
                    self.report.append('%s: %#x in %s at old +%#x: inside a replaced interval, left' % (where, a, f, a - s))
                    return None
                return self.fn[f][0] + n
            if f in self.changed and a >= self.first_diff[f]:
                self.report.append('%s: %#x in %s at/after its first changed instruction (%#x); mapped by offset' %
                                   (where, a, f, self.first_diff[f]))
            return self.fn[f][0] + (a - s)
        # data / bss
        for n, (s, sz, sec) in self.so.items():
            if sec in ('.data', '.bss') and sz > 0 and s <= a < s + sz:
                if n not in self.sn:
                    self.report.append('%s: %#x in %s (%s), which is gone' % (where, a, n, sec)); return None
                return self.sn[n][0] + (a - s)
        # rodata symbols
        for n, (s, sz, sec) in self.so.items():
            if sec == '.rodata' and sz > 0 and s <= a < s + sz and n in self.sn:
                return self.sn[n][0] + (a - s)
        # the rodata tail (from `digits` on: the tables) moves as one block
        if 'digits' in self.so and 'digits' in self.sn and a >= self.so['digits'][0] and a < self.ro_base + len(self.ro):
            return a + (self.sn['digits'][0] - self.so['digits'][0])
        # rodata strings by content
        if self.ro_base <= a < self.ro_base + len(self.ro):
            off = a - self.ro_base
            end = self.ro.find(b'\0', off)
            if end < 0: end = len(self.ro)
            s = self.ro[off:end]
            # the string as the tail of a NUL-terminated string (proofs may point inside one)
            start = self.ro.rfind(b'\0', 0, off) + 1
            full = self.ro[start:end + 1]
            cands = []
            k = -1
            while True:
                k = self.rn.find(full, k + 1)
                if k < 0: break
                if k == 0 or self.rn[k - 1] == 0: cands.append(k)
            if len(cands) == 1:
                return self.rn_base + cands[0] + (off - start)
            self.report.append('%s: rodata %#x %r: %d candidates' % (where, a, bytes(full), len(cands)))
            return None
        if a == self.so.get('end', (None,))[0]: return self.sn['end'][0]
        self.report.append('%s: %#x unmapped' % (where, a)); return None

    # ---- immediates ----
    def imm_of(self, mn_rule, a):
        """the immediate field of the new instruction at `a`, for a rule named wp_s_<mn_rule>: (value, width)"""
        if a not in self.new_ins: return None
        mn, ops, cm = self.new_ins[a]
        if mn_rule in ('auipc', 'lui'):
            if mn not in ('auipc', 'lui'): return None
            return (int(ops.split(',')[1], 16) & 0xfffff, 20)
        if mn_rule in ('jal', 'j') or mn_rule.startswith('branch'):
            mt = re.search(r'([0-9a-f]{8}) <', ops)
            if not mt: return None
            tgt = int(mt.group(1), 16)
            if mn_rule in ('jal', 'j'): return ((tgt - a) & 0x1fffff, 21)
            return ((tgt - a) & 0x1fff, 13)
        # I/S-type: `N(reg)` or trailing `,N`
        if mn in ('jal', 'j', 'auipc', 'lui', 'ret') or mn.startswith('b'): return None
        if mn in ('mv', 'nop'): return (0, 12)
        if mn == 'seqz': return (1, 12)
        if mn == 'not': return (0xfff, 12)
        if mn == 'sext.w' or mn == 'zext.b' or mn in ('li',):
            m = re.search(r',(-?\d+)$', ops)
            return ((int(m.group(1)) & 0xfff, 12) if m else (0, 12))
        m = re.search(r'(-?\d+)\(', ops)
        if m: return (int(m.group(1)) & 0xfff, 12)
        m = re.search(r',(-?\d+)$', ops)
        if m: return (int(m.group(1)) & 0xfff, 12)
        m = re.search(r',(0x[0-9a-f]+)$', ops)
        if m: return (int(m.group(1), 16) & 0xfff, 12)
        return None

ADDR_RE = re.compile(r'0x80[0-9a-fA-F]{6}\b')
RULE_RE = re.compile(r'\((wp_s_(\w+?))(?:_[a-z_]+)?\s+\S+\s+_\s+0x80[0-9a-fA-F]{6}#64\s+(true|false)\s+(\(?)(0x[0-9a-fA-F]+|-?\d+)#(12|13|20|21)')
RULE_MNEMONICS = {'addi', 'addiw', 'andi', 'ori', 'xori', 'sltiu', 'slti', 'ld', 'lw', 'lwu', 'lbu', 'lb', 'lh', 'lhu',
                  'sd', 'sw', 'sb', 'sh', 'auipc', 'lui', 'jal', 'j', 'branch', 'branch0', 'push', 'pop', 'jalr'}

def rebase_file(rb, path, dry):
    src = open(path).read()
    lines = src.split('\n')
    out = []
    helper_updates = {}  # lemma name -> (old N, new N)
    for i, line in enumerate(lines):
        where = '%s:%d' % (path, i + 1)
        new = line
        # 1. address literals
        def repl(m):
            a = int(m.group(0), 16)
            b = rb.map_addr(a, where)
            if b is None: return m.group(0)
            return ('0x%08x' % b) if m.group(0)[2:].islower() or m.group(0)[2:].isdigit() else ('0x%08X' % b)
        new = ADDR_RE.sub(repl, new)
        # 2. immediates on rule lines (the pc on the line is now the NEW pc)
        m = RULE_RE.search(new)
        if m:
            base = m.group(2)
            # the rule name's mnemonic: wp_s_<mn> possibly with suffixes (wp_s_lw_noff, wp_s_sd_mint ...)
            full = m.group(1)
            mn = None
            for cand in sorted(RULE_MNEMONICS, key=len, reverse=True):
                if full == 'wp_s_' + cand or full.startswith('wp_s_' + cand + '_'):
                    mn = cand; break
            if mn is None and re.match(r'wp_s_(add|sub|sll|srl|sra|and|or|xor|slt|sltu|subw|addw|srli|slli|srai|ret|fence|csrr|mul|div|rem)', full):
                mn = None
            if mn:
                pc = int(re.search(r'0x80[0-9a-fA-F]{6}#64', new).group(0)[:-3], 16)
                r = rb.imm_of(mn, pc)
                tok_old = m.group(5); w = int(m.group(6))
                if r is None:
                    rb.report.append('%s: cannot derive immediate for %s at new pc %#x' % (where, full, pc))
                elif r[1] != w:
                    rb.report.append('%s: immediate width %d but rule %s expects %d' % (where, w, full, r[1]))
                else:
                    old_val = int(tok_old, 16) if tok_old.startswith('0x') else int(tok_old) & ((1 << w) - 1)
                    if old_val != r[0]:
                        tok_new = ('0x%x' % r[0]) if tok_old.startswith('0x') else str(r[0])
                        s, e = m.start(5), m.end(5)
                        new = new[:s] + tok_new + new[e:]
                        if mn in ('auipc', 'lui'):
                            # a helper lemma on this or the next line: `with [name]`
                            ctx = new + ' ' + (lines[i + 1] if i + 1 < len(lines) else '')
                            mw = re.search(r'with \[([A-Za-z0-9_\']+)', ctx)
                            if mw: helper_updates[mw.group(1)] = (old_val, r[0])
        out.append(new)
    text = '\n'.join(out)
    # 3. helper lemmas
    for name, (o, n) in helper_updates.items():
        pat = re.compile(r'(theorem\s+' + re.escape(name) + r'\s*:\s*BitVec\.signExtend 64 \()(0x[0-9a-fA-F]+|\d+)(#20 \+\+ 0#12\) = )(0x[0-9a-fA-F]+|\d+)(#64)')
        mm = pat.search(text)
        if not mm:
            rb.report.append('%s: helper lemma %s for auipc/lui imm %#x -> %#x not found/recognized' % (path, name, o, n))
            continue
        val = (n << 12) & 0xffffffff
        if val & 0x80000000: val |= 0xffffffff00000000
        text = text[:mm.start()] + mm.group(1) + ('0x%x' % n if mm.group(2).startswith('0x') else str(n)) + mm.group(3) + \
               ('0x%x' % val) + mm.group(5) + text[mm.end():]
    if text != src and not dry:
        open(path, 'w').write(text)
    return text != src

def main():
    global OBJ
    ap = argparse.ArgumentParser()
    ap.add_argument('old'); ap.add_argument('new')
    ap.add_argument('--objdump', default=OBJ)
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--intervals', metavar='FILE', help='per-function shift intervals for reshaped functions')
    ap.add_argument('files', nargs='*')
    a = ap.parse_args()
    OBJ = a.objdump
    rb = Rebase(a.old, a.new, parse_intervals(a.intervals) if a.intervals else None)
    print('functions whose instruction stream changed:', sorted(rb.changed))
    if rb.imm_only: print('functions whose immediates only changed:', sorted(rb.imm_only))
    files = a.files or [f for f in sorted(glob.glob('Xv6/*.lean'))
                        if os.path.basename(f) not in ('KernelImage.lean', 'KernelTree.lean', 'KernelText.lean')]
    changed = []
    for f in files:
        if rebase_file(rb, f, a.dry_run): changed.append(f)
    print('rewritten %d files' % len(changed))
    for r in rb.report: print('REPORT', r)

if __name__ == '__main__' and not (len(sys.argv) > 1 and sys.argv[1] in ('--fixup', '--symbolize', '--bridge', '--symbolic')):
    main()

# ---------------------------------------------------------------------------
# The fix-up pass: what the literal pass cannot see.  Run AFTER the literal
# pass (hex literals are already NEW addresses; decimal literals and the
# immediates inside address-arithmetic lemmas are still OLD).
#
# * decimal address literals (`2147559352`) -> mapped;
# * `PC#64 + (BitVec.signExtend 64 (U#20 ++ 0#12) + I#64)`: U and I re-derived
#   from the `auipc` at the (new) PC and the instruction after it;
# * `kernelData_byte N ADDR`: N := ADDR - 0x80007000 (the rodata index);
# * machine-mode rule lines (`st_step wp_m_...`, `entry_step wp_m_...`) whose
#   pc is the `-- 8000007c: ...` comment above: the comment's pc mapped and the
#   immediate re-derived;
# * bare `8000xxxx` addresses inside comments: mapped.

DEC_RE = re.compile(r'(?<![\w.#])(2147[0-9]{6})(?![\w])')
P1_RE = re.compile(r'(0x80[0-9a-fA-F]{6})#64( : BitVec 64\))? \+ \(BitVec\.signExtend 64 \((0x[0-9a-fA-F]+|\d+)#20 \+\+ (?:0#12|\(0#12 : BitVec 12\))\) \+\s*(?:(0x[0-9a-fA-F]+|\d+)#64|BitVec\.signExtend 64 \((\d+)#12\))\)')
P3_RE = re.compile(r'(0x80[0-9a-fA-F]{6})#64 \+ BitVec\.signExtend 64 \((\d+)#21\)')
NEG_RE = re.compile(r'(?<![\w.#])(1844674407[0-9]{10})(?![\w])')
KDB2_RE = re.compile(r'\b(kernelData_byte|hb) (\d+) (0x[0-9a-fA-F]+) (0x[0-9a-fA-F]{2})\b')
KDB_RE = re.compile(r'kernelData_byte (\d+) (0x[0-9a-fA-F]+)')
CMT_PC_RE = re.compile(r'--\s*([0-9a-f]{8}):')
MRULE_RE = re.compile(r'(wp_m_\w+.*?\s)(true|false)\s+(\(?)(0x[0-9a-fA-F]+|-?\d+)#(12|13|20|21)')
BARE_RE = re.compile(r'(?<![0-9a-fA-Fx_])(8000[0-9a-f]{4})(?![0-9a-fA-F_])')

def imm_signed(rb, a):
    """the I/S-type immediate of the instruction at new pc `a`, as a 64-bit two's-complement literal"""
    r = rb.imm_of('addi', a)
    if r is None: return None
    v = r[0]
    if v >= 0x800: v -= 0x1000
    return v & 0xffffffffffffffff

def fixup_file(rb, path, dry):
    src = open(path).read()
    lines = src.split('\n')
    out = []
    pending_pc = None
    for i, line in enumerate(lines):
        where = '%s:%d' % (path, i + 1)
        new = line
        is_comment = new.lstrip().startswith('--')
        # comments: bare old addresses -> new
        if '--' in new:
            cpos = new.index('--')
            head, tail = new[:cpos], new[cpos:]
            def crep(m):
                b = rb.map_addr(int(m.group(1), 16), where + ' (comment)')
                return ('%08x' % b) if b is not None else m.group(1)
            mc = CMT_PC_RE.search(tail)
            if mc: pending_pc = int(mc.group(1), 16)
            tail = BARE_RE.sub(crep, tail)
            new = head + tail
        if not is_comment:
            # decimal address literals
            def drep(m):
                a = int(m.group(1))
                if not (0x80000000 <= a < 0x80100000): return m.group(1)
                b = rb.map_addr(a, where)
                return str(b) if b is not None else m.group(1)
            new = DEC_RE.sub(drep, new)
            # address-arithmetic lemmas
            def p1rep(m):
                pc = int(m.group(1), 16)
                r = rb.imm_of('auipc', pc)
                if r is None:
                    rb.report.append('%s: no auipc at new pc %#x' % (where, pc)); return m.group(0)
                nxt = pc + 4
                iv = imm_signed(rb, nxt)
                if iv is None:
                    rb.report.append('%s: no I/S immediate at new pc %#x' % (where, nxt)); return m.group(0)
                u = ('0x%x' % r[0]) if m.group(3).startswith('0x') else str(r[0])
                pre = m.group(1) + '#64' + (m.group(2) or '')
                if m.group(5) is not None:
                    return '%s + (BitVec.signExtend 64 (%s#20 ++ (0#12 : BitVec 12)) + BitVec.signExtend 64 (%d#12))' % (pre, u, iv & 0xfff)
                return '%s + (BitVec.signExtend 64 (%s#20 ++ 0#12) + %d#64)' % (pre, u, iv)
            new = P1_RE.sub(p1rep, new)
            def p3rep(m):
                pc = int(m.group(1), 16)
                r = rb.imm_of('jal', pc)
                if r is None:
                    rb.report.append('%s: no jal at new pc %#x' % (where, pc)); return m.group(0)
                return '%s#64 + BitVec.signExtend 64 (%d#21)' % (m.group(1), r[0])
            new = P3_RE.sub(p3rep, new)
            def nrep(m):
                n = int(m.group(1)); a = (1 << 64) - n
                if not (0x80000000 <= a < 0x80100000): return m.group(1)
                b = rb.map_addr(a, where + ' (negated)')
                return str((1 << 64) - b) if b is not None else m.group(1)
            new = NEG_RE.sub(nrep, new)
            def kdb2(m):
                a = int(m.group(3), 16)
                if rb.rn_base <= a < rb.rn_base + len(rb.rn):
                    return '%s %d %s 0x%02x' % (m.group(1), a - 0x80007000, m.group(3), rb.rn[a - rb.rn_base])
                return m.group(0)
            new = KDB2_RE.sub(kdb2, new)
            # rodata indices
            new = KDB_RE.sub(lambda m: 'kernelData_byte %d %s' % (int(m.group(2), 16) - 0x80007000, m.group(2)), new)
            # machine-mode rule lines
            mm = MRULE_RE.search(new)
            if mm and pending_pc is not None:
                npc = rb.map_addr(pending_pc, where)
                if npc is not None:
                    mn = None
                    full = re.search(r'wp_m_(\w+)', mm.group(1)).group(1)
                    for cand in sorted(RULE_MNEMONICS, key=len, reverse=True):
                        if full == cand or full.startswith(cand + '_'): mn = cand; break
                    if full.startswith('li'): mn = 'addi'
                    if mn:
                        r = rb.imm_of(mn, npc)
                        w = int(mm.group(5)); tok = mm.group(4)
                        if r is not None and r[1] == w:
                            old_val = int(tok, 16) if tok.startswith('0x') else int(tok) & ((1 << w) - 1)
                            if old_val != r[0]:
                                tok_new = ('0x%x' % r[0]) if tok.startswith('0x') else str(r[0])
                                new = new[:mm.start(4)] + tok_new + new[mm.end(4):]
                        elif r is None:
                            rb.report.append('%s: cannot derive immediate for wp_m_%s at new pc %#x' % (where, full, npc))
                pending_pc = None
            elif not is_comment and new.strip():
                if 'wp_m_' in new or 'st_step' in new or 'entry_step' in new: pending_pc = None
        out.append(new)
    text = '\n'.join(out)
    if text != src and not dry:
        open(path, 'w').write(text)
    return text != src

def fixup_main():
    global OBJ
    ap = argparse.ArgumentParser()
    ap.add_argument('old'); ap.add_argument('new')
    ap.add_argument('--objdump', default=OBJ)
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--intervals', metavar='FILE', help='per-function shift intervals for reshaped functions')
    ap.add_argument('files', nargs='*')
    a = ap.parse_args(sys.argv[2:])
    OBJ = a.objdump
    rb = Rebase(a.old, a.new, parse_intervals(a.intervals) if a.intervals else None)
    files = a.files or [f for f in sorted(glob.glob('Xv6/*.lean'))
                        if os.path.basename(f) not in ('KernelImage.lean', 'KernelTree.lean', 'KernelText.lean', 'KernelData.lean')]
    changed = [f for f in files if fixup_file(rb, f, a.dry_run)]
    print('fixed up %d files' % len(changed))
    for r in rb.report: print('REPORT', r)

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == '--fixup':
    fixup_main()

# ---------------------------------------------------------------------------
# The symbolization pass (phase 2): every kernel address literal becomes a
# symbol of the dump plus an offset.
#
#   0x80001954#64        -> KA.«cpuid»                (text, offset 0)
#   0x8000195c#64        -> (KA.«cpuid» + 0x8#64)     (text, offset 8)
#   0x80012430#64        -> KA.«pid_lock»             (data / bss / rodata objects)
#   0x80007030#64        -> KStr.«uart0»              (rodata strings, by content)
#   0x80001954           -> KernelSyms.«cpuid»        (bare Nat forms)
#
# `KA.«s» : BitVec 64 := BitVec.ofNat 64 KernelSyms.«s»` and `KStr.«t»` are
# emitted by tools/dump_kernel.py.  Comments are left alone.  Decimal address
# literals are reported, not rewritten (they sit in `toNat` arithmetic that
# needs a hand-written bound).
#
# For every `auipc` rule line the pass also emits a BRIDGING lemma
# `KA.«f» + LIT#64 = <target>` (the normal form `k_norm` folds the
# materialized address to, versus the symbol the proof wants) and names it in
# the `with [...]` clause of the following I/S-type rule line.

HEX_RE = re.compile(r'0x(80[0-9a-fA-F]{6})(#64)?\b')

def sym_of(rb, a):
    """(kind, name, off) for a NEW address `a`, or None"""
    if a == 0x80000000: return None   # 2^31 / KERNBASE: a layout constant, not the `_entry` symbol
    best = None
    for f, (s, ins) in rb.fn.items():
        if ins and s <= a <= ins[-1][0] + 4 and (best is None or s > best[1]): best = (f, s)
    if best: return ('text', best[0], a - best[1])
    for n, (s, sz, sec) in rb.sn.items():
        if sec in ('.data', '.bss', '.got') and sz > 0 and s <= a < s + sz: return ('data', n, a - s)
    for n, (s, sz, sec) in rb.sn.items():
        if sec == '.rodata' and sz > 0 and s <= a < s + sz: return ('data', n, a - s)
    if rb.rn_base <= a < rb.rn_base + len(rb.rn):
        off = a - rb.rn_base
        start = rb.rn.rfind(b'\0', 0, off) + 1
        end = rb.rn.find(b'\0', off)
        sbytes = bytes(rb.rn[start:end])
        if 1 <= len(sbytes) <= 64 and all(32 <= c < 127 or c in (9, 10, 13) for c in sbytes):
            text = sbytes.decode('ascii').replace('\\', '\\\\').replace('\n', '\\n').replace('\t', '\\t').replace('\r', '\\r')
            # the dump names duplicates `_2`, `_3`...: count earlier occurrences
            k = 0; p = -1
            while True:
                p = rb.rn.find(sbytes + b'\0', p + 1)
                if p < 0 or p >= start: break
                if p == 0 or rb.rn[p - 1] == 0: k += 1
            name = text if k == 0 else '%s_%d' % (text, k + 1)
            return ('str', name, off - start)
    for n, (s, sz, sec) in rb.sn.items():
        if sz == 0 and s == a and sec in ('.data', '.bss', '.got', '.rodata'): return ('data', n, 0)
    # anonymous rodata (switch tables): relative to `etext`, the section start
    if rb.rn_base <= a < rb.rn_base + len(rb.rn) and 'etext' in rb.sn: return ('data', 'etext', a - rb.sn['etext'][0])
    return None

def lean_name(n):
    return '«%s»' % n.replace('.', '_').replace('$', '_')

def symbolize_file(rb, path, dry):
    src = open(path).read()
    lines = src.split('\n')
    out = []
    pre = '' if re.search(r'^open .*\bMachCSL\b', src, re.M) else 'MachCSL.'
    for i, line in enumerate(lines):
        where = '%s:%d' % (path, i + 1)
        cpos = line.find('--')
        code, comment = (line, '') if cpos < 0 else (line[:cpos], line[cpos:])
        if re.match(r'^\s*\(0x[0-9a-fA-F]+, 0x[0-9a-fA-F]+\),?\s*$', code):
            out.append(line); continue
        def rep(m):
            a = int(m.group(1), 16)
            r = sym_of(rb, a)
            if r is None:
                rb.report.append('%s: %#x has no symbol' % (where, a)); return m.group(0)
            kind, name, off = r
            bv = m.group(2) is not None
            if kind == 'str':
                base = pre + ('KStr.' if bv else 'KernelStr.') + lean_name(name)
            else:
                base = pre + ('KA.' if bv else 'KernelSyms.') + lean_name(name)
            if off == 0: return base
            return '(%s + 0x%x#64)' % (base, off) if bv else '(%s + 0x%x)' % (base, off)
        code = HEX_RE.sub(rep, code)
        # decimal BitVec address literals (`2147492532#64`)
        def drep64(m):
            a = int(m.group(1))
            if not (0x80000000 <= a < 0x80100000): return m.group(0)
            r = sym_of(rb, a)
            if r is None: return m.group(0)
            kind, name, off = r
            base = pre + ('KStr.' if kind == 'str' else 'KA.') + lean_name(name)
            return base if off == 0 else '(%s + 0x%x#64)' % (base, off)
        code = re.sub(r'(?<![\w.])(\d{10})#64', drep64, code)
        # address-arithmetic lemmas `(KA.«f» + OFF#64) + (signExtend (U#20 ++ 0#12) + I#64)`: the
        # normaliser now folds these to `KA.«f» + LIT#64`, so state them that way
        def foldrep(m):
            f = m.group(1); off = int(m.group(2), 16) if m.group(2) else 0
            u = int(m.group(4), 16) if m.group(4).startswith('0x') else int(m.group(4))
            hi = (u << 12) & 0xffffffff
            if hi & 0x80000000: hi |= 0xffffffff00000000
            if m.group(5) is not None:
                iv = int(m.group(5), 16) if m.group(5).startswith('0x') else int(m.group(5))
            else:
                iv = int(m.group(6)); iv = iv - 0x1000 if iv >= 0x800 else iv
            L = (off + hi + iv) & 0xffffffffffffffff
            return '%sKA.«%s» + 0x%x#64' % (pre, f, L)
        code = re.sub(r'\(?(?:MachCSL\.)?KA\.«([^»]+)»(?: \+ 0x([0-9a-fA-F]+)#64)?\)?( : BitVec 64\))? \+ \(BitVec\.signExtend 64 \((0x[0-9a-fA-F]+|\d+)#20 \+\+ (?:0#12|\(0#12 : BitVec 12\))\) \+\s*(?:(0x[0-9a-fA-F]+|\d+)#64|BitVec\.signExtend 64 \((\d+)#12\))\)', foldrep, code)
        # `jumpPc E = E` lemmas: the literal fold no longer applies; `decide` sees through the symbols
        code = re.sub(r"((?:theorem|have) [\w']+ : jumpPc [^:]*:= by) simp only \[jumpPc, BitVec\.reduceAnd\]", r'\1 decide', code)
        if re.match(r'^\s*simp only \[jumpPc, BitVec\.reduceAnd\]\s*$', code) and i > 0 and re.search(r"(?:theorem|have) [\w']+ : jumpPc .*:= by\s*$", lines[i - 1]):
            code = code.replace('simp only [jumpPc, BitVec.reduceAnd]', 'decide')
        # the Spec-level address definitions and the unfoldings of the symbols
        code = re.sub(r'BitVec\.ofNat 64 KernelSyms\.(«[^»]+»)', r'KA.\1', code)
        code = re.sub(r',\s*KernelSyms\.«[^»]+»', '', code)
        code = re.sub(r'KernelSyms\.«[^»]+»,\s*', '', code)
        for m in DEC_RE.finditer(code):
            a = int(m.group(1))
            if 0x80000000 <= a < 0x80100000: rb.report.append('%s: decimal address literal %d left as is' % (where, a))
        out.append(code + comment)
    text = '\n'.join(out)
    if text != src and not dry: open(path, 'w').write(text)
    return text != src

def symbolize_main():
    global OBJ
    ap = argparse.ArgumentParser()
    ap.add_argument('new')
    ap.add_argument('--objdump', default=OBJ)
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('files', nargs='*')
    a = ap.parse_args(sys.argv[2:])
    OBJ = a.objdump
    rb = Rebase(a.new, a.new)
    files = a.files or [f for f in sorted(glob.glob('Xv6/*.lean'))
                        if os.path.basename(f) not in ('KernelImage.lean', 'KernelTree.lean', 'KernelText.lean', 'KernelData.lean')]
    changed = [f for f in files if symbolize_file(rb, f, a.dry_run)]
    print('symbolized %d files' % len(changed))
    for r in rb.report: print('REPORT', r)

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == '--symbolize':
    symbolize_main()

# ---------------------------------------------------------------------------
# Bridging lemmas: after symbolization the normaliser folds a `jal` target or an
# `auipc`+`addi`/load/store address to `KA.«f» + LIT#64`, where the proof
# needs the symbol the code refers to (`KA.«initlock»`, `KA.«kmem» + 0x18#64`).
# In the literal world both sides folded to the same number; now each site
# gets `theorem f_br_LIT : KA.«f» + LIT#64 = <symbol> := by decide`, named in
# the `with [...]` clause of the rule line that produces the value.

SYMPC_RE = re.compile(r'\(KA\.«([^»]+)» \+ 0x([0-9a-fA-F]+)#64\)|KA\.«([^»]+)»')
SRULE_RE = re.compile(r'\((wp_s_(\w+?))(?:_[a-z_]+)?\s+\S+\s+_\s+(\(KA\.«[^»]+» \+ 0x[0-9a-fA-F]+#64\)|KA\.«[^»]+»)\s+(true|false)')

def target_expr(rb, a, bv=True):
    r = sym_of(rb, a)
    if r is None: return None
    kind, name, off = r
    base = ('KStr.' if kind == 'str' else 'KA.') + lean_name(name)
    return base if off == 0 else '(%s + 0x%x#64)' % (base, off)

def bridge_file(rb, path, dry):
    src = open(path).read()
    lines = src.split('\n')
    lemmas = {}      # (f, L, target) -> name
    inserts = []     # (line index of enclosing theorem start, text)
    withs = {}       # line index -> [names]
    def enclosing_start(i):
        j = i
        while j > 0 and not re.match(r'^(theorem|def|instance|lemma|example|private theorem) ', lines[j]): j -= 1
        # walk back over `set_option ... in` / docstring / attribute lines
        k = j
        while k > 0 and (lines[k - 1].startswith('set_option') or lines[k - 1].startswith('/--') or lines[k - 1].startswith('@[') or lines[k - 1].startswith('attribute') or (lines[k - 1].strip() != '' and not lines[k - 1].startswith(('theorem', 'def', 'instance', 'end', 'namespace', 'open', 'variable', 'section', '/-!')) and k - 1 > 0 and lines[k - 2].startswith('/--'))):
            k -= 1
        return k
    for i, line in enumerate(lines):
        m = SRULE_RE.search(line)
        if not m: continue
        full, mn_ = m.group(1), m.group(2)
        pcm = SYMPC_RE.search(m.group(3))
        f = pcm.group(1) or pcm.group(3); off = int(pcm.group(2), 16) if pcm.group(2) else 0
        if f not in rb.fn: continue
        pc = rb.fn[f][0] + off
        ins = rb.new_ins.get(pc)
        if ins is None: continue
        mn, ops, cm = ins
        L = None; tgt = None
        if mn in ('jal', 'j') and full in ('wp_s_jal', 'wp_s_j'):
            mt = re.search(r'([0-9a-f]{8}) <', ops)
            if not mt: continue
            T = int(mt.group(1), 16)
            L = (off + (T - pc)) & 0xffffffffffffffff
            tgt = target_expr(rb, T)
        elif full.startswith('wp_s_') and cm and mn in ('addi', 'mv', 'ld', 'lw', 'lwu', 'lbu', 'lb', 'lh', 'lhu', 'sd', 'sw', 'sb', 'sh'):
            # the value/address materialised from an `auipc` base: LIT = (base's auipc offset + U<<12 + I)
            mc = re.match(r'([0-9a-f]+) <', cm)
            if not mc: continue
            T = int(mc.group(1), 16)
            # which auipc? the closest earlier `auipc` in the function writing the base register
            base_reg = None
            mo = re.match(r'\w+,(-?\d+)\((\w+)\)', ops) or re.match(r'\w+,(\w+),-?\d+', ops) or re.match(r'\w+,(\w+)$', ops)
            if mo: base_reg = mo.group(2) if mo.lastindex == 2 else mo.group(1)
            a = pc - 4; apc = None
            fs = rb.fn[f][0]
            while a >= fs:
                if a in rb.new_ins and rb.new_ins[a][0] == 'auipc' and rb.new_ins[a][1].split(',')[0] == base_reg:
                    apc = a; break
                a -= 2
            if apc is None: continue
            U = int(rb.new_ins[apc][1].split(',')[1], 16)
            hi = (U << 12) & 0xffffffff
            if hi & 0x80000000: hi |= 0xffffffff00000000
            r = rb.imm_of('addi', pc)
            if r is None: continue
            I = r[0] if r[0] < 0x800 else r[0] - 0x1000
            L = ((apc - fs) + hi + I) & 0xffffffffffffffff
            if ((fs + L) & 0xffffffffffffffff) != T:
                rb.report.append('%s: bridging mismatch at %#x: computed %#x, code says %#x' % (path, pc, (fs + L) & 0xffffffffffffffff, T)); continue
            tgt = target_expr(rb, T)
        if L is None or tgt is None: continue
        if tgt == 'KA.%s' % lean_name(f) or tgt.startswith('(KA.%s + ' % lean_name(f)): continue
        key = (f, L, tgt)
        if key not in lemmas:
            name = '%s_br_%x' % (f.replace('.', '_').replace('$', '_'), L)
            lemmas[key] = name
            if ('theorem %s ' % name) not in src:
                inserts.append((enclosing_start(i), 'theorem %s : KA.%s + 0x%x#64 = %s := by decide\n' % (name, lean_name(f), L, tgt)))
        # the `with [...]` clause: on the line holding `$$`, or the next line if that is a `with`/`next` continuation
        j = i
        while j < len(lines) and '$$' not in lines[j]: j += 1
        if j >= len(lines): continue
        if j + 1 < len(lines) and re.match(r'^\s+(with \[|next )', lines[j + 1]): j += 1
        if lemmas[key] in lines[j]: continue
        withs.setdefault(j, []).append(lemmas[key])
    if not inserts and not withs:
        return False
    for j, names in withs.items():
        names = [n for k, n in enumerate(names) if n not in names[:k]]
        l = lines[j]
        if ' with [' in l:
            l = l.replace(' with [', ' with [' + ', '.join(names) + ', ', 1)
        elif ' next ' in l:
            l = l.replace(' next ', ' with [' + ', '.join(names) + '] next ', 1)
        else:
            l = l.rstrip() + ' with [' + ', '.join(names) + ']'
        lines[j] = l
    for j, text in sorted(inserts, key=lambda x: -x[0]):
        lines.insert(j, text.rstrip('\n'))
        lines.insert(j + 1, '')
    text = '\n'.join(lines)
    if text != src and not dry: open(path, 'w').write(text)
    return True

def bridge_main():
    global OBJ
    ap = argparse.ArgumentParser()
    ap.add_argument('new')
    ap.add_argument('--objdump', default=OBJ)
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('files', nargs='*')
    a = ap.parse_args(sys.argv[2:])
    OBJ = a.objdump
    rb = Rebase(a.new, a.new)
    files = a.files or [f for f in sorted(glob.glob('Xv6/*.lean'))
                        if os.path.basename(f) not in ('KernelImage.lean', 'KernelTree.lean', 'KernelText.lean', 'KernelData.lean')]
    changed = [f for f in files if bridge_file(rb, f, a.dry_run)]
    print('bridged %d files' % len(changed))
    for r in rb.report: print('REPORT', r)

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == '--bridge':
    bridge_main()

# ---------------------------------------------------------------------------
# The symbolic pass: the tree after --symbolize names text pcs and data
# addresses relative to a symbol, and the literal pass cannot see those.
# `--symbolic OLD_ELF NEW_ELF` rewrites, symbol-relative:
#
# * the offset of `KA.«s» + N#64`, `KA.«s» + (N#64 ...`, `<alias> + N#64`
#   (`def xAddr : BitVec 64 := KA.«s»`), `<palias> N#64` / `<palias> (N#64`
#   (`abbrev p (o : BitVec 64) : BitVec 64 := KA.«s» + o`) and the Nat
#   `KernelSyms.«s» + N`:
#   - inside text function s (its extent from the disassembly, so size-0
#     assembler labels such as kernelvec count): by --intervals, else kept;
#   - inside the process table (--proc-array SYM:COUNT, default proc:64): by
#     slot and field, the stride being each image's table size / COUNT and the
#     field map --proc-fields (`+START:DELTA,...`, the --intervals syntax);
#   - inside any other data object: kept;
#   - outside s, a text symbol, equal to `o + sext(U<<12)` for an old auipc at
#     +o of s: the auipc intermediate, re-derived from the new auipc;
#   - otherwise (folded jal/auipc targets): the absolute old address mapped as
#     the literal pass maps it, re-expressed relative to s's new start;
# * the immediate right after a text pc (`pc) true|false IMM`, `pc) IMM#w`,
#   `pc + BitVec.signExtend 64 IMM#w`, and the I part of an auipc fold
#   `pc + (BitVec.signExtend 64 (U#20 ++ 0#12) + I)`), but only where the
#   literal equals the OLD instruction's immediate at the old pc and the
#   mnemonic is unchanged (anything else is reported, not guessed);
# * `theorem X_br_<hex>` names whose hex is the first literal on their line:
#   renamed after the new literal, everywhere (collisions reported).
#
# Lines folding two literals onto one symbol (`KA.«f» + A#64 + B#64`, B not a
# 2/4 step) are reported and left.  The pass is one-shot like every address
# sweep: run it once per bump (on an unchanged image it proposes nothing).

M64 = (1 << 64) - 1
SNUM = r'(0x[0-9a-fA-F]+|\d+)'
SDBL_RE = re.compile(r'KA\.«[^»]+» \+ \S+#64 \+ (?!4#64|2#64)(?:0x[0-9a-f]+|\d+)#64')
SIMM_AFTER = re.compile(r'\)?\s+(?:true|false)\s+\(?(?:BitVec\.ofNat (\d+) (\d+)|(-?)(0x[0-9a-fA-F]+|\d+)#(\d+))')
SIMM_POS = re.compile(r'\)?\s+\(?(-?)(0x[0-9a-fA-F]+|\d+)#(12|13|20|21)(?![\w#])')
SIMM_SE = re.compile(r'\)?\s*\+\s*\(?BitVec\.signExtend 64 \(?(-?)(0x[0-9a-fA-F]+|\d+)#(\d+)')
SP1_I = re.compile(r'#20\s*\+\+\s*(?:0#12|\(0#12 : BitVec 12\))\)\s*\)?\s*\+\s*(?:BitVec\.signExtend 64 \(?(-?)(0x[0-9a-fA-F]+|\d+)#12|(-?)(0x[0-9a-fA-F]+|\d+)#64)')
SP1_TAIL = re.compile(r'#20\s*\+\+\s*(?:0#12|\(0#12 : BitVec 12\))\)\s*\)?\s*\+\s*$')
SP1_NEXT = re.compile(r'\s*(?:BitVec\.signExtend 64 \(?(-?)(0x[0-9a-fA-F]+|\d+)#12|(-?)(0x[0-9a-fA-F]+|\d+)#64)')
SKS_RE = re.compile(r'KernelSyms\.«([^»]+)» \+ ' + SNUM + r'(?![#\w])')
SBR_RE = re.compile(r'\s*(?:private\s+)?theorem\s+(\S+_br_)([0-9a-f]+)\s*:')

def sxu(u):
    v = u << 12
    return v - (1 << 32) if v & 0x80000000 else v

def imm_w(ins, pc, W):
    """the W-bit immediate field of instruction `ins` = (mn, ops, cm) at pc, or None"""
    mn, ops = ins[0], ins[1]
    if W in (13, 21):
        m = re.search(r'([0-9a-f]+) <', ops)
        return ((int(m.group(1), 16) - pc) & ((1 << W) - 1)) if m else None
    if W == 20:
        return (int(ops.split(',')[1].split()[0], 16) & 0xfffff) if mn in ('auipc', 'lui') else None
    if mn in ('jal', 'j', 'auipc', 'lui', 'ret') or mn.startswith('b'): return None
    if mn in ('mv', 'nop', 'sext.w'): return 0
    if mn == 'seqz': return 1
    if mn == 'not': return (1 << W) - 1
    for r, base in ((r'(-?\d+)\(', 10), (r',(-?\d+)$', 10), (r',(0x[0-9a-f]+)$', 16)):
        m = re.search(r, ops)
        if m: return int(m.group(1), base) & ((1 << W) - 1)
    return None

def fmt_like(tok, v):
    """v in the spelling of literal token `tok` (hex/decimal, case)"""
    if not tok.startswith('0x'): return str(v)
    return ('0x%X' if any(c in 'ABCDEF' for c in tok[2:]) else '0x%x') % v

class Symbolic:
    def __init__(self, rb, proc_array='proc:64', proc_fields=None, got=(None, None)):
        self.rb = rb
        self.got = got   # the .got section (vma, size) of each image: its slots move with it
        self.report = rb.report
        self.stats = {'offsets': 0, 'nat_offsets': 0, 'immediates': 0, 'intermediates': 0, 'renames': 0}
        self.ln = {}
        for k in list(rb.so) + list(rb.sn) + list(rb.fo) + list(rb.fn):
            self.ln.setdefault(k.replace('.', '_').replace('$', '_'), k)
        # text extents from the disassembly (size-0 labels included)
        self.ext = {f: (ins[-1][0] - s + 4 if ins else 0) for f, (s, ins) in rb.fo.items()}
        self.auipcs = {f: [(a - s, int(ops.split(',')[1].split()[0], 16) & 0xfffff)
                           for a, mn, ops, cm in ins if mn == 'auipc'] for f, (s, ins) in rb.fo.items()}
        self.proc = None
        if proc_array:
            sym, cnt = proc_array.rsplit(':', 1); cnt = int(cnt, 0)
            if sym in rb.so and sym in rb.sn and rb.so[sym][1] and rb.sn[sym][1]:
                so_, sn_ = rb.so[sym][1], rb.sn[sym][1]
                if so_ % cnt or sn_ % cnt:
                    self.report.append('--proc-array %s: size %#x / %#x not a multiple of %d' % (sym, so_, sn_, cnt))
                else:
                    fields = []
                    if proc_fields:
                        for item in proc_fields.split(','):
                            st, d = item.strip().rsplit(':', 1)
                            fields.append((int(st.strip().lstrip('+'), 0), int(d.strip(), 0)))
                    self.proc = (sym, so_ // cnt, sn_ // cnt, sorted(fields))
                    if so_ != sn_ and not fields:
                        self.report.append('--proc-array %s: stride %d -> %d with no --proc-fields: fields kept' %
                                           (sym, so_ // cnt, sn_ // cnt))
        self.pending = []
        self.renames = {}

    def text_newoff(self, f, o, where):
        rb = self.rb
        n = rb.newoff(f, o)
        if n is None:
            self.report.append('%s: %s+%#x inside a replaced interval, left' % (where, f, o)); return None
        if f not in rb.iv and f in rb.changed and rb.fo[f][0] + o >= rb.first_diff[f]:
            self.report.append('%s: %s+%#x at/after its first changed instruction (%#x); mapped by offset' %
                               (where, f, o, rb.first_diff[f]))
        return n

    def remap(self, lf, off, where):
        """(new offset, (old, new) offsets if a pc inside text function f else None, f)"""
        rb = self.rb
        f = self.ln.get(lf, lf)
        if f in rb.fo:
            if f not in rb.fn:
                self.report.append('%s: text symbol %s is gone' % (where, f)); return off, None, f
            if 0 <= off <= self.ext[f]:
                n = self.text_newoff(f, off, where)
                return (off, None, f) if n is None else (n, (off, n), f)
        elif f in rb.so and f in rb.sn:
            s, sz, sec = rb.so[f]
            if self.proc and f == self.proc[0] and 0 <= off <= sz:
                _, os_, ns_, fields = self.proc
                slot, fld = divmod(off, os_)
                d = 0
                for st, dd in fields:
                    if fld >= st: d = dd
                return slot * ns_ + fld + d, None, f
            if (sec in ('.data', '.bss', '.rodata') and 0 <= off <= sz) or (sec == '.bss' and sz == 0):
                return off, None, f
        elif f == '_GLOBAL_OFFSET_TABLE_':
            return off, None, f
        else:
            self.report.append('%s: %s is not a text/data/bss/rodata symbol of both images: +%#x kept' % (where, f, off))
            return off, None, f
        if f in rb.fo:
            for o, u in self.auipcs[f]:
                if (o + sxu(u)) & M64 == off:
                    n = self.text_newoff(f, o, where)
                    ni = rb.new_ins.get(rb.fn[f][0] + n) if n is not None else None
                    if ni is None or ni[0] != 'auipc':
                        self.report.append('%s: %s+%#x: auipc intermediate at +%#x with no new auipc' % (where, f, off, o))
                        return off, None, f
                    v = (n + sxu(int(ni[1].split(',')[1].split()[0], 16) & 0xfffff)) & M64
                    if v != off: self.stats['intermediates'] += 1
                    return v, None, f
        so_ = rb.fo[f][0] if f in rb.fo else rb.so[f][0]
        sn_ = rb.fn[f][0] if f in rb.fn else rb.sn[f][0]
        a = (so_ + off) & M64
        go, gn = self.got
        if go and gn and go[0] <= a < go[0] + go[1]:
            b = a - go[0] + gn[0]
        else:
            b = rb.map_addr(a, where)
        if b is None: return off, None, f
        return (b - sn_) & M64, None, f

    def ins_pair(self, f, oo, no):
        rb = self.rb
        pco, pcn = rb.fo[f][0] + oo, rb.fn[f][0] + no
        o, n = rb.old_ins.get(pco), rb.new_ins.get(pcn)
        return (pco, o[1:] if o else None, pcn, n)

    def fix_i(self, text, m2, f, oo, no, where):
        """the I part of an auipc fold: the immediate of the instruction after the auipc"""
        pco, o2, pcn, n2 = self.ins_pair(f, oo + 4, no + 4)
        if not o2 or not n2: return text
        io2, in2 = imm_w(o2, pco, 12), imm_w(n2, pcn, 12)
        if io2 is None or in2 is None: return text
        if m2.group(2) is not None: ng, dg, a, b, sty = m2.group(1), m2.group(2), m2.start(1), m2.end(2), 12
        else: ng, dg, a, b, sty = m2.group(3), m2.group(4), m2.start(3), m2.end(4), 64
        dv = int(dg, 0)
        if ((-dv if ng else dv) & 0xfff) != io2:
            self.report.append('%s: auipc fold I part at %s+%#x is not the old immediate %d' % (where, f, no + 4, io2))
            return text
        if in2 == io2: return text
        sv = in2 - 4096 if in2 >= 2048 else in2
        tok = fmt_like(dg, in2) if (sty == 12 and not ng) else ('-' if sv < 0 else '') + fmt_like(dg, abs(sv))
        self.stats['immediates'] += 1
        return text[:a] + tok + text[b:]

    def fix_imm_at(self, line, pos, f, oo, no, where):
        pco, o, pcn, n = self.ins_pair(f, oo, no)
        if not o or not n: return line
        kind = m = None
        for k, R in (('after', SIMM_AFTER), ('se', SIMM_SE), ('pos', SIMM_POS)):
            m = R.match(line, pos)
            if m: kind = k; break
        if not kind: return line
        if kind == 'after' and m.group(1):
            W, digits, neg, s0, e0 = int(m.group(1)), m.group(2), '', m.start(2), m.end(2)
        elif kind == 'after':
            neg, digits, W, s0, e0 = m.group(3), m.group(4), int(m.group(5)), m.start(3), m.end(4)
        else:
            neg, digits, W, s0, e0 = m.group(1), m.group(2), int(m.group(3)), m.start(1), m.end(2)
        if W not in (6, 12, 13, 20, 21): return line
        if o[0] != n[0]:
            self.report.append('%s: %s+%#x mnemonic changed %s -> %s' % (where, f, no, o[0], n[0])); return line
        v = int(digits, 16) if digits.startswith('0x') else int(digits)
        v = (-v if neg else v) & ((1 << W) - 1)
        io, inew = imm_w(o, pco, W), imm_w(n, pcn, W)
        if io is None or inew is None: return line
        if v != io:
            if v != inew and kind != 'pos':
                self.report.append('%s: %s+%#x immediate %d#%d is neither the old %d nor the new %d' %
                                   (where, f, no, v, W, io, inew))
            return line
        out = line
        if inew != io:
            if neg:
                sv = inew - (1 << W) if inew >= (1 << (W - 1)) else inew
                tok = ('-' if sv < 0 else '') + fmt_like(digits, abs(sv))
            else:
                tok = fmt_like(digits, inew)
            out = line[:s0] + tok + line[e0:]
            self.stats['immediates'] += 1
        if W == 20 and o[0] == 'auipc' and kind == 'se':
            e_u = e0 + len(out) - len(line)
            m2 = SP1_I.match(out, e_u)
            if m2: out = self.fix_i(out, m2, f, oo, no, where)
            elif SP1_TAIL.match(out, e_u): self.pending.append((f, oo, no))
            else: self.report.append('%s: auipc fold at %s+%#x: I part not recognised' % (where, f, no))
        return out

    def patterns(self, srcs):
        alias, palias = {}, {}
        for src in srcs:
            for m in re.finditer(r'^(?:noncomputable )?(?:def|abbrev) (\S+) : BitVec 64 := \(?KA\.«([^»]+)»\)?\s*$', src, re.M):
                alias.setdefault(m.group(1), set()).add(m.group(2))
            for m in re.finditer(r'^(?:noncomputable )?(?:def|abbrev) (\S+) \((\w+) : BitVec 64\) : BitVec 64 := KA\.«([^»]+)» \+ (\w+)\s*$', src, re.M):
                if m.group(2) == m.group(4): palias.setdefault(m.group(1), set()).add(m.group(3))
        alias = {k: next(iter(v)) for k, v in alias.items() if len(v) == 1}
        palias = {k: next(iter(v)) for k, v in palias.items() if len(v) == 1}
        res = [(re.compile(r'KA\.«([^»]+)» \+ ' + SNUM + r'#64'), lambda m: m.group(1), 'ka'),
               (re.compile(r'KA\.«([^»]+)» \+ \(' + SNUM + r'#64'), lambda m: m.group(1), 'kap')]
        alt = lambda d: '|'.join(sorted(map(re.escape, d), key=len, reverse=True))
        if alias:
            res.append((re.compile(r'(?<![\w.\'«])(' + alt(alias) + r') \+ ' + SNUM + r'#64'), lambda m: alias[m.group(1)], 'alias'))
        if palias:
            res.append((re.compile(r'(?<![\w.\'])(' + alt(palias) + r') \(?' + SNUM + r'#64'), lambda m: palias[m.group(1)], 'palias'))
        return res

    def process(self, path, src, pats):
        lines = src.split('\n')
        for i, line in enumerate(lines):
            where = '%s:%d' % (path, i + 1)
            if self.pending:
                f, oo, no = self.pending.pop()
                m2 = SP1_NEXT.match(line)
                if m2: line = self.fix_i(line, m2, f, oo, no, where)
                else: self.report.append('%s: the auipc fold\'s I part not found on this line' % where)
            if SDBL_RE.search(line) and not line.lstrip().startswith('--'):
                self.report.append('%s: double-literal fold, left for hand' % where); lines[i] = line; continue
            occ = []
            for R, symf, kind in pats:
                for m in R.finditer(line): occ.append((m.start(2), m.end(2), m.end(), symf(m), m.group(2), kind))
            occ.sort(key=lambda x: x[0])
            for s2, e2, me, f, tok, kind in reversed(occ):
                off = int(tok, 16) if tok.startswith('0x') else int(tok)
                n, pc, f2 = self.remap(f, off, where)
                if pc and kind != 'kap': line = self.fix_imm_at(line, me, f2, pc[0], pc[1], where)
                if n != off:
                    line = line[:s2] + fmt_like(tok, n) + line[e2:]; self.stats['offsets'] += 1
            for m in reversed(list(SKS_RE.finditer(line))):
                tok = m.group(2)
                off = int(tok, 16) if tok.startswith('0x') else int(tok)
                n, _, _ = self.remap(m.group(1), off, where)
                if n != off:
                    line = line[:m.start(2)] + fmt_like(tok, n) + line[m.end(2):]; self.stats['nat_offsets'] += 1
            mt = SBR_RE.match(lines[i])
            if mt and occ:
                R0 = pats[0][0]
                mo, mn = R0.search(lines[i]), R0.search(line)
                if mo and mn:
                    oo, nn = int(mo.group(2), 0), int(mn.group(2), 0)
                    if mt.group(2) == '%x' % oo and oo != nn:
                        self.renames[mt.group(1) + mt.group(2)] = mt.group(1) + '%x' % nn
            lines[i] = line
        return '\n'.join(lines)

    def run(self, files):
        srcs = {}
        for p in files:
            with open(p) as fh: srcs[p] = fh.read()
        pats = self.patterns(srcs.values())
        out = {p: self.process(p, s, pats) for p, s in srcs.items()}
        if self.renames:
            names = set()
            for t in out.values(): names.update(re.findall(r'theorem\s+(\S+)', t))
            for k, v in sorted(self.renames.items()):
                if v in names and v not in self.renames: self.report.append('RENAME COLLISION %s -> %s' % (k, v))
            pat = re.compile(r'(?<![\w.\'])(' + '|'.join(re.escape(k) for k in sorted(self.renames, key=len, reverse=True)) + r')(?![\w\'])')
            out = {p: pat.sub(lambda m: self.renames[m.group(1)], t) for p, t in out.items()}
            self.stats['renames'] = len(self.renames)
        return srcs, out

def section_range(elf, sec):
    """(vma, size) of section `sec`, or None"""
    for l in run([OBJ, '-h', elf]).splitlines():
        p = l.split()
        if len(p) > 3 and p[1] == sec: return int(p[3], 16), int(p[2], 16)
    return None

def symbolic_main():
    global OBJ
    ap = argparse.ArgumentParser(prog='rebase_kernel.py --symbolic')
    ap.add_argument('old'); ap.add_argument('new')
    ap.add_argument('--objdump', default=OBJ)
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--intervals', metavar='FILE', help='per-function shift intervals for reshaped functions')
    ap.add_argument('--proc-array', default='proc:64', metavar='SYM:COUNT',
                    help='the table mapped by slot and field (stride = size / COUNT in each image); "" for none')
    ap.add_argument('--proc-fields', metavar='+START:DELTA,...', help='field-offset shifts inside one slot')
    ap.add_argument('files', nargs='*')
    a = ap.parse_args(sys.argv[2:])
    OBJ = a.objdump
    rb = Rebase(a.old, a.new, parse_intervals(a.intervals) if a.intervals else None)
    print('functions whose instruction stream changed:', sorted(rb.changed))
    if rb.imm_only: print('functions whose immediates only changed:', sorted(rb.imm_only))
    files = a.files or [f for f in sorted(glob.glob('Xv6/*.lean'))
                        if os.path.basename(f) not in ('KernelImage.lean', 'KernelTree.lean', 'KernelText.lean', 'KernelData.lean')]
    sp = Symbolic(rb, a.proc_array or None, a.proc_fields, (section_range(a.old, '.got'), section_range(a.new, '.got')))
    srcs, out = sp.run(files)
    changed = [p for p in files if out[p] != srcs[p]]
    if not a.dry_run:
        for p in changed:
            with open(p, 'w') as fh: fh.write(out[p])
    print('symbolic: %d files %s; %s' % (len(changed), 'would change' if a.dry_run else 'rewritten',
                                         ', '.join('%s %d' % kv for kv in sp.stats.items())))
    for r in rb.report: print('REPORT', r)

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == '--symbolic':
    symbolic_main()
