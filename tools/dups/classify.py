import re, sys
d = open(sys.argv[1]).read()
parts = re.split(r'^diff \S+ a/(\S+) b/\S+\n', d, flags=re.M)
it = iter(parts[1:])
pats = {'A': r'uwkPpn|utlbAD|utlbInv|utlbOk|pteAD|ptePpn',
        'B': r'runRW_of_runRead|runRW_ro|rotransfer|Read-only transfer|read-only bridge',
        'C': r'uxaXget_congr|ukRegs_congr|uke_', 'D': r'trapArm|tickOpt',
        'E': r'uslot_fupd|uslotFupd', 'F': r'seccCons',
        'G': r'halfBytes|bytes2|ByteWord2|align2|two-byte|TWO-BYTE'}
for f, body in zip(it, it):
    lines = [l for l in body.split('\n') if l[:1] in '+-' and not l.startswith(('+++', '---'))]
    txt = '\n'.join(lines)
    print(f, ''.join(k for k, p in pats.items() if re.search(p, txt)))
