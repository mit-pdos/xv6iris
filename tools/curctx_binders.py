#!/usr/bin/env python3
"""Give every declaration that (transitively) needs the ambient context an
explicit `[CurCtx]` binder, instead of a section-wide `variable [CurCtx]`
(which Lean includes in every theorem, pure ones too, and which then breaks
callers that have no instance).  Processes files in dependency order and
carries the set of context-needing names across files."""
import re, sys
SEEDS = {'bytesPointsTo','ctxBytes','ctxByte','↦ₘ','ctxTok','ownCtx','curCtx','ctxToken'}
HDR = re.compile(r'^(?P<pre>(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*)(?P<kw>theorem|def|abbrev|instance|lemma|structure|macro|syntax|elab|scoped notation|notation)\b(?P<rest>.*)$')
names = set(SEEDS)
def process(path):
    global names
    src = open(path).read()
    lines = src.split('\n')
    out = []
    # strip the blanket bits
    lines = [l for l in lines if l.strip() != 'variable [CurCtx]' and l.strip() != 'set_option linter.unusedSectionVars false']
    lines = [l.replace('variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CurCtx]','variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF]') for l in lines]
    # find declaration starts
    starts = [i for i,l in enumerate(lines) if HDR.match(l) and not l.startswith(' ')]
    starts.append(len(lines))
    changed = False
    for si in range(len(starts)-1):
        a, b = starts[si], starts[si+1]
        block = '\n'.join(lines[a:b])
        m = HDR.match(lines[a])
        kw = m.group('kw'); rest = m.group('rest')
        if kw in ('macro','syntax','elab','scoped notation','notation','structure'):
            continue
        # name
        nm = None
        mm = re.match(r'\s+([^\s(:{\[]+)', rest)
        if mm and kw != 'instance':
            nm = mm.group(1)
        needs = any(re.search(r'(?<![\w.])'+re.escape(n)+r'(?![\w])', block) if n.isidentifier() or '_' in n or "'" in n else (n in block) for n in names)
        if not needs:
            continue
        if nm: names.add(nm)
        if '[CurCtx]' in lines[a]:
            continue
        if kw == 'instance':
            if re.match(r'\s+:', rest):
                lines[a] = m.group('pre') + 'instance [CurCtx]' + rest
            else:
                # named instance
                mm2 = re.match(r'(\s+[^\s(:{\[]+)(.*)$', rest)
                lines[a] = m.group('pre') + 'instance' + mm2.group(1) + ' [CurCtx]' + mm2.group(2)
        else:
            mm2 = re.match(r'(\s+[^\s(:{\[]+)(.*)$', rest)
            lines[a] = m.group('pre') + kw + mm2.group(1) + ' [CurCtx]' + mm2.group(2)
        changed = True
    new = '\n'.join(lines)
    if new != src:
        open(path,'w').write(new)
    print(path, 'ok', len(names))
for p in sys.argv[1:]:
    process(p)
