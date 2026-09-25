import re,glob,collections
import sys
W=(sys.argv[1] if len(sys.argv)>1 else '.').rstrip('/')+'/'
# optional: only edit these files (paths relative to the root, e.g. Xv6/SysMkdirParts.lean);
# the script is NOT idempotent on `fun {hlc GF}` lambdas, so on an already-swept
# tree pass exactly the files that have not been swept yet
ONLY=set(a.replace('/','.')[:-5] for a in sys.argv[2:])
files={}
for f in glob.glob(W+'Xv6/*.lean')+glob.glob(W+'MachCSL/*.lean'):
    files[f[len(W):-5].replace('/','.')]=f
imp={m:[l.split()[1] for l in open(f) if l.startswith('import ')] for m,f in files.items()}
rv=collections.defaultdict(set)
for m,ims in imp.items():
    for i in ims: rv[i].add(m)
T=set(['Xv6.ProcDefs']); st=['Xv6.ProcDefs']
while st:
    x=st.pop()
    for y in rv[x]:
        if y not in T: T.add(y); st.append(y)
structs={}
for m in T:
    s=open(files[m]).read()
    for mm in re.finditer(r'^structure (\w+)[^\n]*where\n((?:  .*\n|\n)*?)(?=^\S)', s, re.M):
        structs[mm.group(1)]=('[IrefslotG GF]' in mm.group(2))
changed=0; lam=0; unknown=[]
for m in T:
    if ONLY and m not in ONLY: continue
    f=files[m]; s=open(f).read(); o=s
    if '[CtokG GF] [WchG GF]' in s: continue
    out=[]
    for mm in re.finditer(r'fun \{hlc GF\} ', s):
        i=mm.start(); pre=s[:i]
        t=max(pre.rfind('\ntheorem '),pre.rfind('\nlemma '))
        cand=re.findall(r':\s*([A-Z][A-Z0-9_]*)\s*:=', pre[t:])
        if not cand: unknown.append((m,s[i:i+60])); continue
        stn=cand[-1]
        if stn not in structs: unknown.append((m,'nostruct '+stn)); continue
        if structs[stn]: out.append(mm.end())
    for p in reversed(out): s=s[:p]+'_ _ '+s[p:]; lam+=1
    s=s.replace('[IrefslotG GF]','[IrefslotG GF] [CtokG GF] [WchG GF]')
    if s!=o: open(f,'w').write(s); changed+=1
print(changed,lam); print(unknown)
