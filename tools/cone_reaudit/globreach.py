import os, re, sys, collections, glob as G
ROOT=os.environ['ROCQ_TREE']
dirs={'iris':'xv6iris','model-xv6iris':'Riscv','kernel-rocq':'Kernel','user-rocq':'User'}
DECLK={'def','prf','thm','lem','inst','abbrev','ind','rec','constr','proj','class','meth','coe','ax','scheme','mod','modtype','not','var','canonstruc','fact','corr','prop','defax','inst'}
decls={}      # key -> (file, kind)
charges=collections.defaultdict(set)
filedecls=collections.defaultdict(list)
for d,lib in dirs.items():
  for f in G.glob(os.path.join(ROOT,d,'**','*.glob'),recursive=True):
    mod=None; cur=None; lastind=None
    for line in open(f,errors='replace'):
      line=line.rstrip('\n')
      if line.startswith('F'): mod=line[1:]; continue
      if line.startswith('DIGEST'): continue
      if line.startswith('R'):
        m=re.match(r'R(\d+):(\d+) (\S+) (\S+) (\S+) (\S+)',line)
        if not m or cur is None: continue
        tl,tsp,tn,tk=m.group(3),m.group(4),m.group(5),m.group(6)
        charges[cur].add((tl,tsp,tn))
        continue
      p=line.split(' ')
      if len(p)<4: continue
      k=p[0]
      if k not in DECLK: continue
      key=(mod,p[2],p[3])
      decls[key]=(mod,k)
      filedecls[mod].append(key)
      if k in ('ind','rec','class'): lastind=key
      if k in ('constr','proj','meth') and lastind:
        charges[key].add(lastind); charges[lastind].add(key)
      if k=='mod':
        pass
      cur=key
# module membership
modmembers=collections.defaultdict(set)
for key,(mod,k) in decls.items():
  sp=key[1]
  if sp!='<>':
    parts=sp.split('.')
    for i in range(1,len(parts)+1):
      modmembers[(mod,'.'.join(parts[:i-1]) or '<>',parts[i-1])].add(key)

def walk(roots):
  seen=set(roots); todo=list(roots)
  while todo:
    k=todo.pop()
    for t in list(charges.get(k,())) + list(modmembers.get(k,())):
      if t in decls and t not in seen:
        seen.add(t); todo.append(t)
  return seen
roots={'U':('xv6iris.UInitUnion','<>','union_adequacy_closed'),
       'S':('xv6iris.SystemAdequacy','<>','xv6_fs_adequacy_xv6\u03a3'),
       'P':('xv6iris.ProofUser','UserProof','wp_user_exec_closed')}
import sys
with open(os.path.join(os.environ.get('OUT','.'),'cone_globreach.txt'),'w') as f:
  for r,k in roots.items():
    if k not in decls: print('MISSING',k,file=sys.stderr)
    s=walk([k])
    for (m,sp,n) in s:
      f.write('%s %s\n'%(r,'.'.join([m]+([] if sp=='<>' else [sp])+[n])))
    print(r,len(s))
