#!/usr/bin/env python3
"""Regenerate the byte lists of Xv6/KernelData.lean (the `.rodata` section,
and the initialized writable image `.data`/`.got`/`.got.plt`) from the kernel
ELF.  Only the `rodataChunkN` / `dataInitChunkN` lists are rewritten; the
definitions and theorems after them are kept.

Usage: tools/gen_kernel_data.py [--kernel PATH] [--objdump OBJDUMP]
The kernel must be the SAME build as Xv6/KernelImage.lean (check with
tools/dump_kernel.py --check, or compare `<argraw>`'s address): the switch
jump tables in .rodata are text-relative, so a rebuilt kernel's .rodata
differs there even when its strings agree.
"""
import argparse, re, subprocess

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--kernel', default='xv6-riscv/kernel/kernel')
    ap.add_argument('--out', default='Xv6/KernelData.lean')
    ap.add_argument('--objdump', default='riscv64-linux-gnu-objdump')
    ap.add_argument('--chunk', type=int, default=400)
    a = ap.parse_args()
    src = open(a.out).read()
    # `.rodata` -> rodataChunkN; the initialized WRITABLE image `[_data, _bss)`
    # (`.data`, `.got`, `.got.plt`) -> dataInitChunkN
    for sects, name in ((['.rodata'], 'rodataChunk'), (['.data', '.got', '.got.plt'], 'dataInitChunk')):
        args = [a.objdump, '-s']
        for sec in sects:
            args += ['-j', sec]
        out = subprocess.run(args + [a.kernel], capture_output=True, text=True, check=True).stdout
        rb = {}
        for line in out.splitlines():
            m = re.match(r'\s*([0-9a-f]+) ((?:[0-9a-f]{2,8} ?){1,4})', line)
            if m and line.startswith(' '):
                base = int(m.group(1), 16); hx = m.group(2).replace(' ', '')
                for i in range(0, len(hx), 2):
                    rb[base + i // 2] = int(hx[i:i + 2], 16)
        addrs = sorted(rb)
        # replace each chunk list body
        chunks = [addrs[i:i + a.chunk] for i in range(0, len(addrs), a.chunk)]
        for n, ch in enumerate(chunks):
            body = ',\n'.join(f'  (0x{x:08x}, 0x{rb[x]:02x})' for x in ch)
            pat = re.compile(rf'(def {name}{n} : List \(Nat × Nat\) := \[\n)(.*?)(\])', re.S)
            assert pat.search(src), f'{name}{n} not found'
            src = pat.sub(lambda m: m.group(1) + body + m.group(3), src, count=1)
        print(f'{name}: {len(addrs)} bytes, {len(chunks)} chunks')
    open(a.out, 'w').write(src)
    print(f'written to {a.out}')

if __name__ == '__main__':
    main()
