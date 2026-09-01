#!/usr/bin/env bash
# Profiling round: full forced iris rebuild with per-sentence TIMING=1,
# then aggregate every sentence >= 3s into /tmp/timing-report.txt.
# Sentinels: TIMEEXIT=<n>, REPORT=<path>, DONE
set -u
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT/iris"
opam exec --switch=/shared/xv6rocq -- make -f CoqMakefile -B -j180 -k TIMING=1 > "$ROOT/ZZ-timing.log.aux" 2>&1
echo "TIMEEXIT=$?"

python3 - <<'PYEOF'
import glob, re, os
rows=[]
for tf in glob.glob('*.v.timing'):
    src=tf[:-7]  # foo.v
    try: text=open(src).read()
    except OSError: continue
    for ln in open(tf):
        m=re.match(r'Line (\d+) +Chars (\d+)-(\d+) +\[(.*?)\] +([0-9.]+) secs', ln)
        if not m: continue
        line,a,b,name,secs=int(m.group(1)),int(m.group(2)),int(m.group(3)),m.group(4),float(m.group(5))
        if secs < 3.0: continue
        stmt=text[a:b].strip().replace('\n',' ')[:90]
        rows.append((secs,src,line,stmt))
rows.sort(reverse=True)
with open('/tmp/timing-report.txt','w') as f:
    total=sum(r[0] for r in rows)
    f.write(f"sentences >=3s: {len(rows)}, their total {total:.0f}s\n")
    nq=[r for r in rows if not r[3].startswith('Qed')]
    f.write(f"NON-QED among them: {len(nq)}, total {sum(r[0] for r in nq):.0f}s\n\n")
    f.write("== TOP 120 (all) ==\n")
    for secs,src,line,stmt in rows[:120]:
        tag='QED   ' if stmt.startswith('Qed') else 'TACTIC'
        f.write(f"{secs:8.1f}s {tag} {src}:{line}  {stmt}\n")
    f.write("\n== TOP 120 NON-QED ==\n")
    for secs,src,line,stmt in nq[:120]:
        f.write(f"{secs:8.1f}s {src}:{line}  {stmt}\n")
print("report written")
PYEOF
echo "REPORT=/tmp/timing-report.txt"
# per-file wall totals from the timing files, top 40
python3 - <<'PYEOF'
import glob, re
tot={}
for tf in glob.glob('*.v.timing'):
    s=0.0
    for ln in open(tf):
        m=re.search(r'([0-9.]+) secs', ln)
        if m: s+=float(m.group(1))
    tot[tf[:-7]]=s
with open('/tmp/timing-files.txt','w') as f:
    for k,v in sorted(tot.items(), key=lambda kv:-kv[1])[:40]:
        f.write(f"{v:8.1f}s {k}\n")
print("file totals written")
PYEOF
echo DONE
