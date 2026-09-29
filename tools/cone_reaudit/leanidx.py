"""Index Lean declarations and Rocq-name mentions.

Output (json): {
  'decls': {norm: [ 'File:leanName', ...]},
  'doc': {rocqtoken: ['File:leanName', ...]}   # token in the docstring right before a decl
  'mention': {rocqtoken: ['File', ...]}         # token anywhere in a comment
}
"""
import os, re, json, sys, collections, glob

ROOT = sys.argv[1]
OUT = sys.argv[2]

DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom|example)\s+'
                  r'(?:\(priority[^)]*\)\s*)?([^\s:({\[]+)')
FIELD = re.compile(r'^\s{2,4}([A-Za-z_][A-Za-z0-9_\'!?.]*)\s*(?::|\{|\(|\[)')
CTOR = re.compile(r'^\s*\|\s*([A-Za-z_][A-Za-z0-9_\'!?]*)')
TOK = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def norm(s):
    s = s.split('.')[-1]
    return re.sub(r"[_'«»]", '', s).lower()


decls = collections.defaultdict(set)
doc = collections.defaultdict(set)
mention = collections.defaultdict(set)
files = []
for d in ('Xv6', 'MachCSL'):
    files += glob.glob(os.path.join(ROOT, d, '**', '*.lean'), recursive=True)
for f in files:
    rel = os.path.relpath(f, ROOT)
    txt = open(f, errors='replace').read()
    lines = txt.split('\n')
    # comments: collect tokens
    for m in re.finditer(r'/-.*?-/|--[^\n]*', txt, re.S):
        for t in TOK.findall(m.group(0)):
            if '_' in t or len(t) > 3:
                mention[t].add(rel)
    # docstring-then-decl
    pending_doc = None
    in_struct = False
    in_doc = False
    buf = []
    for i, l in enumerate(lines):
        if in_doc:
            buf.append(l)
            if '-/' in l:
                in_doc = False
                pending_doc = '\n'.join(buf)
            continue
        if l.lstrip().startswith('/--'):
            buf = [l]
            if '-/' in l[l.index('/--') + 3:]:
                pending_doc = l
                l = re.sub(r'^\s*/--.*?-/\s*', '', l)
                if not l.strip():
                    continue
            else:
                in_doc = True
                continue
        m = DECL.match(l)
        if m:
            kind, name = m.group(1), m.group(2)
            name = name.strip('«»')
            decls[norm(name)].add(rel + ':' + name)
            if pending_doc:
                for t in TOK.findall(pending_doc):
                    doc[t].add(rel + ':' + name)
            pending_doc = None
            in_struct = kind in ('structure', 'class', 'inductive')
            continue
        if in_struct:
            if l.strip() == '' or (l and not l[0].isspace()):
                in_struct = False
            else:
                mm = FIELD.match(l) or CTOR.match(l)
                if mm:
                    decls[norm(mm.group(1))].add(rel + ':' + mm.group(1))
                    if pending_doc:
                        for t in TOK.findall(pending_doc):
                            doc[t].add(rel + ':' + mm.group(1))
                    pending_doc = None
        if l.strip() and not l.lstrip().startswith('--') and not l.lstrip().startswith('@['):
            if not DECL.match(l):
                pass

json.dump({'decls': {k: sorted(v) for k, v in decls.items()},
           'doc': {k: sorted(v) for k, v in doc.items()},
           'mention': {k: sorted(v) for k, v in mention.items()}}, open(OUT, 'w'))
print(len(files), 'files', len(decls), 'norm names', len(doc), 'doc tokens', len(mention), 'mention tokens')
