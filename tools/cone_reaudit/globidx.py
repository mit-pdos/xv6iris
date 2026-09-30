import os, re, glob, sys
ROOT = os.environ['ROCQ_TREE']
dirs = {'iris': 'xv6iris', 'model-xv6iris': 'Riscv', 'kernel-rocq': 'Kernel', 'user-rocq': 'User'}
out = open(sys.argv[1], 'w')
for d, lib in dirs.items():
    for f in glob.glob(os.path.join(ROOT, d, '**', '*.glob'), recursive=True):
        mod = None
        for line in open(f, errors='replace'):
            line = line.rstrip('\n')
            if line.startswith('F'):
                mod = line[1:]
                continue
            if line.startswith('R') or line.startswith('DIGEST'):
                continue
            p = line.split(' ')
            if len(p) < 4:
                continue
            pos = p[1]
            out.write('%s\t%s\t%s\t%s\t%s\n' % (mod, p[2], p[3], p[0], pos))
out.close()
