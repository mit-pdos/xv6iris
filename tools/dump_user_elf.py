#!/usr/bin/env python3
"""Dump an xv6 USER program ELF (user/_<prog>) into Lean data (union DU3).

Writes, for program <P> (module name, e.g. Echo):

  Xv6/User/<P>Image.lean   the .text instructions (address, width, encoding),
                            in the kernel's KernelImage format (with the
                            objdump line as a comment), the symbols, the
                            geometry (entry, PT_LOAD table, base/end,
                            rodata end), and the FILE-BACKED bytes of every
                            PT_LOAD segment as `USeg`s (rows of 32 bytes,
                            one big-endian hex Nat per row, a hexdump line);
  Xv6/User/<P>ElfRaw.lean  the literal file, byte for byte (DWARF and all),
                            rows of 32 bytes, 128 rows to a page, every
                            page `@[irreducible]` (only `decide +kernel`
                            reads it: Xv6/ElfUser.lean's sanity checks);

then runs tools/gen_user_text.py for the search tree and the per-program
text facts (Xv6/User/<P>Tree.lean, Xv6/User/<P>Text.lean).

A user program is linked at virtual address 0 (user/user.ld), with TWO
PT_LOADs: R-X (.text, .rodata, .eh_frame) at 0 and RW- (.data, .bss) at the
next page.  Addresses are user virtual addresses.

The dumper refuses a file that embeds its own build directory (the xv6 build
passes -ffile-prefix-map=$(CURDIR)=., so the files are byte-identical across
build trees; Rocq's user-rocq/*ElfRaw.v are the same bytes).

Usage: tools/dump_user_elf.py --elf PATH --module P [--rev REV] [--outdir Xv6/User]
"""
import argparse, hashlib, os, re, struct, subprocess, sys

INSTR_RE = re.compile(r'^\s*([0-9a-f]+):\t([0-9a-f ]+?)\s*(?:\t(.*))?$')
SYM_RE = re.compile(r'^\s*([0-9a-f]+) <([A-Za-z0-9_.$]+)>:$')
ROW, PAGE_ROWS = 32, 128


def rows_of(bs):
    out = []
    for i in range(0, len(bs), ROW):
        chunk = bs[i:i + ROW]
        chunk = chunk + b'\0' * (ROW - len(chunk))
        out.append(int.from_bytes(chunk, 'big'))
    return out


def fmt_row(v):
    return '0' if v == 0 else '0x%064x' % v


def lean_name(n):
    n = n.replace('.', '_').replace('$', '_')
    return n if re.match(r'^[A-Za-z_][A-Za-z0-9_]*$', n) else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--elf', required=True)
    ap.add_argument('--module', required=True)
    ap.add_argument('--outdir', default='Xv6/User')
    ap.add_argument('--objdump', default='riscv64-linux-gnu-objdump')
    ap.add_argument('--rev', default='unknown')
    ap.add_argument('--chunk', type=int, default=500)
    a = ap.parse_args()
    P = a.module
    elf = open(a.elf, 'rb').read()
    builddir = os.path.dirname(os.path.dirname(os.path.abspath(a.elf))).encode()
    assert builddir not in elf, 'the ELF embeds its build directory (no -ffile-prefix-map?)'
    assert elf[:4] == b'\x7fELF' and elf[4] == 2 and elf[5] == 1, 'expects a little-endian ELF64'
    md5 = hashlib.md5(elf).hexdigest()
    entry, phoff, shoff = struct.unpack_from('<QQQ', elf, 0x18)
    phentsize, phnum, shentsize, shnum, shstrndx = struct.unpack_from('<HHHHH', elf, 0x36)
    loads, phdrs = [], []
    for i in range(phnum):
        ty, fl, off, va, pa, fsz, msz, al = struct.unpack_from('<IIQQQQQQ', elf, phoff + i * phentsize)
        if ty == 1:
            loads.append((va, fsz, msz, fl, off))
            phdrs.append((ty, fl, off, va, pa, fsz, msz, al))
    assert len(loads) == 2 and loads[0][3] == 5 and loads[1][3] == 6, 'expects R-X then RW- PT_LOADs'
    shdrs = []
    for i in range(shnum):
        nm, ty, fl, ad, off, sz = struct.unpack_from('<IIQQQQ', elf, shoff + i * shentsize)
        shdrs.append((nm, ty, fl, ad, off, sz))
    strtab = shdrs[shstrndx]
    def sname(nm):
        o = strtab[4] + nm
        return elf[o:elf.index(b'\0', o)].decode()
    aw = [s[3] for s in shdrs if (s[2] & 2) and (s[2] & 1)]
    mem_base = min(l[0] for l in loads)
    mem_end = max(l[0] + l[2] for l in loads)
    rodata_end = min(aw) if aw else mem_end
    text = [s for s in shdrs if sname(s[0]) == '.text'][0]
    text_lo, text_hi = text[3], text[3] + text[5]

    out = subprocess.run([a.objdump, '-d', '-z', '--section=.text', a.elf],
                         check=True, capture_output=True, text=True).stdout
    instrs, syms = [], []
    prev_zero_end = None
    for line in out.splitlines():
        m = SYM_RE.match(line)
        if m:
            syms.append((m.group(2), int(m.group(1), 16)))
            continue
        m = INSTR_RE.match(line)
        if not m:
            continue
        addr = int(m.group(1), 16)
        for w in m.group(2).split():
            width = len(w) // 2
            enc = int(w, 16)
            zero = width == 2 and enc == 0
            if not (zero and prev_zero_end == addr):
                instrs.append((addr, width, enc, (m.group(3) or '').strip()))
            prev_zero_end = addr + 2 if zero else None
            addr += width
    # cross-check every instruction against the file bytes of the R-X segment
    va0, fsz0, _, _, off0 = loads[0]
    for ad, w, e, _ in instrs:
        assert int.from_bytes(elf[off0 + ad - va0: off0 + ad - va0 + w], 'little') == e, hex(ad)

    os.makedirs(a.outdir, exist_ok=True)
    img = os.path.join(a.outdir, '%sImage.lean' % P)
    src = 'user/_%s' % os.path.basename(a.elf).lstrip('_')
    with open(img, 'w') as f:
        f.write('-- AUTO-GENERATED by tools/dump_user_elf.py from %s (xv6-riscv %s, md5 %s); do not edit.\n'
                % (src, a.rev, md5))
        f.write('-- The user program `%s`: its .text instructions (address, width in bytes, instruction word),\n'
                '-- symbols, geometry, and the file-backed bytes of its two PT_LOAD segments.\n' % P.lower())
        f.write('import Xv6.UserTextDefs\n\nnamespace Xv6.User.%s\n\nopen Xv6.User\n\n' % P)
        chunks = [instrs[i:i + a.chunk] for i in range(0, len(instrs), a.chunk)]
        for ci, ch in enumerate(chunks):
            f.write('def textChunk%d : List UInstr := [\n' % ci)
            f.write(',\n'.join('  -- %s\n  ⟨0x%x, %d, 0x%0*x⟩' % (asm.replace('\n', ' '), ad, w, 2 * w, e)
                               for ad, w, e, asm in ch))
            f.write('\n]\n\n')
        f.write('/-- All %d instructions of `.text` [0x%x, 0x%x), in address order. -/\n'
                % (len(instrs), text_lo, text_hi))
        f.write('def text : List UInstr :=\n  ' + ' ++ '.join('textChunk%d' % i for i in range(len(chunks))) + '\n\n')
        f.write('/-! ## Geometry (the ELF header, the PT_LOAD table, the section table) -/\n\n')
        f.write('/-- `e_entry` (`start`, NOT the lowest text address). -/\ndef entry : Nat := 0x%x\n' % entry)
        f.write('/-- (vaddr, filesz, memsz, flags) per PT_LOAD, in program-header order. -/\n')
        f.write('def segments : List (Nat × Nat × Nat × Nat) :=\n  [%s]\n'
                % ', '.join('(0x%x, 0x%x, 0x%x, %d)' % l[:4] for l in loads))
        f.write('def memBase : Nat := 0x%x\ndef memEnd : Nat := 0x%x\n' % (mem_base, mem_end))
        f.write('/-- The lowest allocated writable section address. -/\ndef rodataEnd : Nat := 0x%x\n' % rodata_end)
        f.write('def textLo : Nat := 0x%x\ndef textHi : Nat := 0x%x\n\n' % (text_lo, text_hi))
        for si, (va, fsz, msz, fl, off) in enumerate(loads):
            nm = 'code' if si == 0 else 'data'
            what = ('the R-X segment: .text, .rodata, .eh_frame (the TEXT heap)' if si == 0
                    else 'the RW- segment\'s file-backed part: .data (the .bss is its zero tail)')
            assert off % ROW == 0, 'segment file offset not row-aligned'
            f.write('/-- The file bytes of %s: [0x%x, 0x%x).  The rows are the FILE\'s, from the\n'
                    'segment\'s offset 0x%x (row %d of `%sElfRaw.elfRows`); the last may run past `size`. -/\n'
                    % (what, va, va + fsz, off, off // ROW, P))
            f.write('def %s : USeg where\n  vaddr := 0x%x\n  size := 0x%x\n  rows := [' % (nm, va, fsz))
            rs = rows_of(elf)[off // ROW: off // ROW + (fsz + ROW - 1) // ROW]
            if rs:
                f.write('\n' + '\n'.join('    %s%s  -- 0x%x' % (fmt_row(r), ',' if i + 1 < len(rs) else '', va + i * ROW)
                                          for i, r in enumerate(rs)) + '\n  ')
            f.write(']\n\n')
        f.write('end Xv6.User.%s\n\n' % P)
        # symbols
        f.write('/-! The symbols (functions first, then data objects), as user virtual addresses. -/\n')
        f.write('namespace Xv6.User.%s.Sym\n\n' % P)
        seen = set()
        for name, ad in syms:
            ln = lean_name(name)
            if ln is None or ln in seen:
                continue
            seen.add(ln)
            f.write('def «%s» : Nat := 0x%x\n' % (ln, ad))
        symtab = subprocess.run([a.objdump, '-t', a.elf], check=True, capture_output=True, text=True).stdout
        dsyms = []
        for line in symtab.splitlines():
            m = re.match(r'^([0-9a-f]{16}) (.{7}) (\S+)\t([0-9a-f]{16}) (\S+)$', line)
            if m and m.group(3) in ('.data', '.bss', '.rodata', '.sdata', '.sbss', '.srodata'):
                ln = lean_name(m.group(5))
                if ln is None or ln in seen:
                    continue
                seen.add(ln)
                dsyms.append((ln, int(m.group(1), 16), int(m.group(4), 16)))
        for ln, ad, sz in sorted(dsyms, key=lambda x: x[1]):
            f.write('def «%s» : Nat := 0x%x  -- size 0x%x\n' % (ln, ad, sz))
        f.write('\nend Xv6.User.%s.Sym\n' % P)
    print('wrote %s: %d instructions, %d symbols' % (img, len(instrs), len(seen)), file=sys.stderr)

    raw = os.path.join(a.outdir, '%sElfRaw.lean' % P)
    rs = rows_of(elf)
    pages = [rs[i:i + PAGE_ROWS] for i in range(0, len(rs), PAGE_ROWS)]
    with open(raw, 'w') as f:
        f.write('-- AUTO-GENERATED by tools/dump_user_elf.py from %s (xv6-riscv %s, md5 %s); do not edit.\n'
                % (src, a.rev, md5))
        f.write('/-\nTHE LITERAL FILE `%s` (Rocq `user-rocq/%sElfRaw.v`): %d bytes, DWARF and all --\n'
                'the binary exec() runs and mkfs packs into fs.img.  Rows of 32 bytes, one\n'
                'big-endian hex `Nat` per row (a hexdump line; the last row zero-padded), 128\n'
                'rows to a page.  Every page is `@[irreducible]`: only `decide +kernel`\n'
                '(Xv6/ElfUser.lean) reads it.\n-/\nimport Xv6.UserTextDefs\n\nnamespace Xv6.User.%s\n\n'
                % (src, P, len(elf), P))
        f.write('/-- The file\'s size in bytes. -/\ndef elfSize : Nat := %d\n\n' % len(elf))
        f.write('/-- Its PT_LOAD headers, in program-header order (what `Xv6.elfLoads` must read). -/\n'
                'def elfLoadsLit : List ElfPhdr :=\n  [%s]\n\n'
                % ',\n   '.join('⟨%d, %d, 0x%x, 0x%x, 0x%x, 0x%x, 0x%x, 0x%x⟩' % ph for ph in phdrs))
        bss = [(l[0] + l[1], l[2] - l[1]) for l in loads if l[2] > l[1]]
        assert len(bss) == 1
        f.write('/-- The .bss: the one zero tail (the writable segment\'s `[vaddr + filesz, vaddr + memsz)`). -/\n'
                'def bssLo : Nat := 0x%x\ndef bssSize : Nat := 0x%x\n\n' % bss[0])
        for pi, pg in enumerate(pages):
            f.write('@[irreducible] def elfPage%d : List Nat := [\n' % pi)
            f.write(',\n'.join('  %s' % fmt_row(r) for r in pg))
            f.write('\n]\n\n')
        f.write('/-- All %d rows. -/\ndef elfRows : List Nat :=\n  %s\n\n'
                % (len(rs), ' ++ '.join('elfPage%d' % i for i in range(len(pages)))))
        # the same rows as a balanced tree indexed by row number (random access
        # in O(log n) for the ELF header/section reads of Xv6/ElfUser.lean)
        tdefs = []
        def tlit(lo, hi):
            if lo >= hi:
                return '.leaf'
            mid = (lo + hi) // 2
            return '(.node %s %d %s %s)' % (tlit(lo, mid), mid - lo, fmt_row(rs[mid]), tlit(mid + 1, hi))
        def tbuild(lo, hi):
            if hi - lo <= 256:
                name = 'elfTreeChunk%d' % len(tdefs)
                tdefs.append((name, tlit(lo, hi)))
                return name
            mid = (lo + hi) // 2
            left = tbuild(lo, mid)
            right = tbuild(mid + 1, hi)
            return '(.node %s %d %s %s)' % (left, mid - lo, fmt_row(rs[mid]), right)
        top = tbuild(0, len(rs))
        f.write('section\nset_option maxRecDepth 4096\n\n')
        for name, body in tdefs:
            f.write('@[irreducible] def %s : RowTree :=\n  %s\n\n' % (name, body))
        f.write('/-- The rows as an index-keyed balanced tree (`RowTree.get`). -/\n'
                'def elfTree : RowTree :=\n  %s\n\nend\n\n' % top)
        f.write('/-- The file, as the general ELF semantics reads it (`Xv6.ElfBytes`). -/\n'
                'def elf : ElfBytes := rowsBytes elfRows elfSize\n\nend Xv6.User.%s\n' % P)
    print('wrote %s: %d bytes' % (raw, len(elf)), file=sys.stderr)
    subprocess.check_call([os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen_user_text.py'),
                           '--image', img, '--module', P, '--outdir', a.outdir])


if __name__ == '__main__':
    main()
