import struct, sys, os
R = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
D = os.path.join(R, 'scratch', 'd1img')
def info(path):
    img = open(path, 'rb').read()
    B = lambda n: img[n * 1024:(n + 1) * 1024]
    magic, size, nblocks, ninodes, nlog, logstart, inodestart, bmapstart = struct.unpack_from('<8I', B(1))
    out = {}
    for inum in range(1, ninodes):
        blk = inodestart + inum // 16
        off = (inum % 16) * 64
        ty, maj, mi, nl, sz = struct.unpack_from('<hhhhI', B(blk), off)
        if ty == 0:
            continue
        addrs = list(struct.unpack_from('<13I', B(blk), off + 12))
        nb = (sz + 1023) // 1024
        direct = addrs[:12][:nb]
        ind = []
        if nb > 12:
            ind = list(struct.unpack_from('<256I', B(addrs[12])))[:nb - 12]
        out[inum] = (ty, nl, sz, direct, addrs[12] if nb > 12 else None, ind)
    return out
def ranges(l):
    r = []
    for x in l:
        if r and r[-1][1] == x - 1: r[-1][1] = x
        else: r.append([x, x])
    return ' ++ '.join("List.range' %d %d" % (a, b - a + 1) for a, b in r)
old = info(os.path.join(D, 'pinfs/xv6-riscv/fs.img'))
new = info(os.path.join(D, 'mainfs/xv6-riscv/fs.img'))
for i in sorted(set(old) | set(new)):
    o = old.get(i); n = new.get(i)
    f = lambda t: None if t is None else (t[0], t[1], t[2], ranges(t[3] + t[5]), t[4])
    print(i, f(o)); print(' ', f(n), '' if f(o) == f(n) else '  CHANGED')
