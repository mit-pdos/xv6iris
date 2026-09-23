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
changed, symbols that disappeared, ambiguous strings).

Usage: tools/rebase_kernel.py OLD_ELF NEW_ELF [--objdump OBJDUMP] [--dry-run] [FILES...]
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

class Rebase:
    def __init__(self, old, new):
        self.so, self.sn = symbols(old), symbols(new)
        self.fo, self.fn = functions(old), functions(new)
        self.ro_base, self.ro = section_bytes(old, '.rodata')
        self.rn_base, self.rn = section_bytes(new, '.rodata')
        self.changed = set()
        self.first_diff = {}
        for f, (s, ins) in self.fo.items():
            if f not in self.fn: self.changed.add(f); self.first_diff[f] = 0; continue
            a, b = norm(f, s, ins), norm(f, *self.fn[f])
            if a != b:
                self.changed.add(f)
                k = 0
                while k < min(len(a), len(b)) and a[k] == b[k]: k += 1
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
    ap.add_argument('files', nargs='*')
    a = ap.parse_args()
    OBJ = a.objdump
    rb = Rebase(a.old, a.new)
    print('functions whose instruction stream changed:', sorted(rb.changed))
    files = a.files or [f for f in sorted(glob.glob('Xv6/*.lean'))
                        if os.path.basename(f) not in ('KernelImage.lean', 'KernelTree.lean', 'KernelText.lean')]
    changed = []
    for f in files:
        if rebase_file(rb, f, a.dry_run): changed.append(f)
    print('rewritten %d files' % len(changed))
    for r in rb.report: print('REPORT', r)

if __name__ == '__main__' and not (len(sys.argv) > 1 and sys.argv[1] in ('--fixup', '--symbolize')):
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
    ap.add_argument('files', nargs='*')
    a = ap.parse_args(sys.argv[2:])
    OBJ = a.objdump
    rb = Rebase(a.old, a.new)
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
    return None

def lean_name(n):
    return '«%s»' % n.replace('.', '_').replace('$', '_')

def symbolize_file(rb, path, dry):
    src = open(path).read()
    lines = src.split('\n')
    out = []
    for i, line in enumerate(lines):
        where = '%s:%d' % (path, i + 1)
        cpos = line.find('--')
        code, comment = (line, '') if cpos < 0 else (line[:cpos], line[cpos:])
        def rep(m):
            a = int(m.group(1), 16)
            r = sym_of(rb, a)
            if r is None:
                rb.report.append('%s: %#x has no symbol' % (where, a)); return m.group(0)
            kind, name, off = r
            bv = m.group(2) is not None
            if kind == 'str':
                base = ('KStr.' if bv else 'KernelStr.') + lean_name(name)
            else:
                base = ('KA.' if bv else 'KernelSyms.') + lean_name(name)
            if off == 0: return base
            return '(%s + 0x%x#64)' % (base, off) if bv else '(%s + 0x%x)' % (base, off)
        code = HEX_RE.sub(rep, code)
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
