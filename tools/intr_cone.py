#!/usr/bin/env python3
"""The INTERRUPT ARM'S FUNCTOR CONE -- the structural half of the strong
instance (claude-notes/design/ni-strong-instance.md, option C / ruling R4).

The kernel proofs are sealed functors over module types (Spec*.v's
`Module Type X`), instantiated once each in Link*.v (`Module X := XProof A
B C.`).  usertrap's device/timer arm reaches exactly two callees, devintr
and yield, so "a quiet round runs no allocator" is, structurally, the
statement that NO module in the instantiation cone of `Devintr` and
`Yield` implements KALLOC or KFREE.  This script reads every `Module ... :=
F args.`, every functor header `Module F (a : T) ... : R.`, every plain
module `Module M : R.` and every `Declare Module M : R.` under iris/, walks
the cone from the roots, and fails if an implementation of a forbidden
module type (or a forbidden functor) is in it.

Names are resolved the way Rocq scopes them for this tree: an argument of
an instantiation in file F is first a module defined in F itself (the
local `Module T := ...` inside a proof functor's body), then a Link-level
instance (the global namespace, which must be unambiguous).

It is a check of the PROOF TREE'S SHAPE, not a theorem in the logic: it
says the interrupt arm's proof could not have applied kalloc's or kfree's
contract, because no module in scope supplies it.  The in-logic form is
the permit sweep the design note costs.

usage: tools/intr_cone.py [--roots Devintr,Yield] [--forbid KALLOC,KFREE]
                          [--iris iris] [--verbose]
exit 0 = PASS, 1 = FAIL (a forbidden implementation is in the cone),
2 = the tree could not be parsed or resolved as expected.
"""
import argparse, collections, glob, os, re, sys

def strip_comments(s):
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith('(*', i): depth += 1; i += 2; continue
        if depth and s.startswith('*)', i): depth -= 1; i += 2; continue
        if not depth: out.append(s[i])
        i += 1
    return ''.join(out)

def sentences(text):
    return re.split(r'\.(?=\s|$)', text)

HDR = re.compile(r'^\s*(Declare\s+)?Module\s+(?:Import\s+|Export\s+)?([A-Za-z0-9_]+)\s*(.*)$', re.S)
ARG = re.compile(r'\(\s*([A-Za-z0-9_]+)\s*:\s*([A-Za-z0-9_.]+)\s*\)')
ASSUMED = '<assumed>'

def last(q): return q.split('.')[-1]

def parse(iris):
    """functors[name] = (file, [arg types], result type)
       local[(file, name)] = (functor, [arg names])   -- every instantiation
       glob[name] = (file, functor, [arg names])      -- Link-level ones"""
    functors, local, glob_, dup = {}, {}, {}, collections.defaultdict(set)
    for f in sorted(glob.glob(os.path.join(iris, '*.v'))):
        base = os.path.basename(f)
        text = strip_comments(open(f, encoding='utf-8', errors='replace').read())
        for s in sentences(text):
            m = HDR.match(s)
            if not m: continue
            declared, name, rest = bool(m.group(1)), m.group(2), m.group(3).strip()
            if rest.startswith('Type'): continue
            if declared:
                res = last(rest[1:].strip()) if rest.startswith(':') else None
                functors[ASSUMED + name] = (base, [], res)
                inst = (ASSUMED + name, [])
            elif ':=' in rest:
                toks = rest.split(':=', 1)[1].split()
                if not toks: continue
                inst = (last(toks[0]), [last(t) for t in toks[1:]])
            elif rest.startswith('(') or rest.startswith(':') or rest.startswith('<:'):
                args = ARG.findall(rest) if rest.startswith('(') else []
                tail = rest[rest.rfind(')') + 1:].strip() if args else rest
                tail = tail[2:] if tail.startswith('<:') else tail[1:] if tail.startswith(':') else ''
                functors[name] = (base, [last(t) for _, t in args], last(tail.strip()) if tail.strip() else None)
                if args: continue
                # a plain module (`Module M : R.`, e.g. LinkPrintk's assumed
                # general path) is also an instance of itself: a leaf
                inst = (name, [])
            else:
                continue
            local[(base, name)] = inst
            if base.startswith('Link'):
                if name in glob_ and glob_[name][1:] != inst: dup[name].add(base); dup[name].add(glob_[name][0])
                glob_[name] = (base,) + inst
    return functors, local, glob_, dup

def cone(roots, functors, local, glob_):
    """nodes are (file, name) instances; returns them in visit order"""
    seen, order, missing = set(), [], []
    stack = [(glob_[r][0], r) for r in roots]
    while stack:
        node = stack.pop()
        if node in seen: continue
        seen.add(node); order.append(node)
        base, name = node
        fn, args = local[node]
        def resolve(a):
            # the caller's own file first, then the Link-level namespace,
            # then a plain module (no arguments) defined anywhere, which the
            # tree names directly (`Module UGrc := UexecGen UserProof.`)
            if (base, a) in local: return (base, a)
            if a in glob_: return (glob_[a][0], a)
            if a in functors and not functors[a][1] and (functors[a][0], a) in local:
                return (functors[a][0], a)
            return None
        if fn not in functors:
            # an alias of another instance (`Module X := Y.`)
            r = resolve(fn)
            if r: stack.append(r)
            else: missing.append((name, fn))
        for a in args:
            r = resolve(a)
            if r: stack.append(r)
            else: missing.append((name, a))
    return order, missing

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--roots', default='Devintr,Yield')
    ap.add_argument('--forbid', default='KALLOC,KFREE')
    ap.add_argument('--forbid-functors', default='KallocProof,KfreeProof')
    ap.add_argument('--iris', default='iris')
    ap.add_argument('--verbose', action='store_true')
    a = ap.parse_args()
    functors, local, glob_, dup = parse(a.iris)
    roots = a.roots.split(',')
    forbid_t, forbid_f = set(a.forbid.split(',')), set(a.forbid_functors.split(','))
    if dup:
        print(f'intr_cone: Link-level names defined differently in several files: {dict(dup)}'); return 2
    bad = [r for r in roots if r not in glob_]
    if bad:
        print(f'intr_cone: root(s) not instantiated in any Link file: {bad}'); return 2
    order, missing = cone(roots, functors, local, glob_)
    if missing:
        print(f'intr_cone: unresolved names in the cone: {missing}'); return 2
    rows, hits, types, assumed = [], [], set(), []
    for base, name in order:
        fn, args = local[(base, name)]
        res = functors.get(fn, (None, None, None))[2]
        if res: types.add(res)
        if fn.startswith(ASSUMED): assumed.append((name, res))
        if fn in forbid_f or res in forbid_t: hits.append((name, fn, res))
        rows.append((name, fn, args, base, res))
    print(f'intr_cone: roots {roots}: {len(rows)} instances, {len(types)} module types in the cone '
          f'({len(functors)} functors, {len(local)} instantiations parsed); '
          f'assumed: {[n for n, _ in assumed] or "none"}')
    if a.verbose:
        for name, fn, args, base, res in sorted(rows):
            shown = 'ASSUMED' if fn.startswith(ASSUMED) else f'{fn} {" ".join(args)}'.strip()
            print(f'  {name:<20} := {shown:<60} [{base}; : {res}]')
        print('  module types:', ' '.join(sorted(types)))
    if hits:
        print('intr_cone: FAIL -- forbidden implementation(s) in the cone:')
        for name, fn, res in hits: print(f'  {name} := {fn} (: {res})')
        return 1
    print(f'intr_cone: PASS -- none of {sorted(forbid_t)} is implemented in the cone')
    return 0

if __name__ == '__main__':
    sys.exit(main())
