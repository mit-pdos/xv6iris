import re, glob, os
R = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
D = os.path.join(R, 'scratch', 'd1img')
SH = re.compile(r'ushCode|User\.Sh\.|\bush[RMEI]?I_[0-9a-f]+|ushm_uis|ush_uis|\bShSyms\b|Sh\.Sym')
EXCL = {'UInitShPure', 'UInitShSlot', 'ProofShExeccmd', 'ProofShRedircmd', 'ProofShPipecmd', 'UshAlloc'}
for f in sorted(glob.glob(R + '/Xv6/*.lean')):
    if os.path.basename(f)[:-5] in EXCL:
        continue
    if SH.search(open(f).read()):
        print(os.path.relpath(f, R))
