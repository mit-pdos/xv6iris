#!/usr/bin/env python3
"""drop_sym_aliases.py -- retire the per-file entry-address aliases.

Most files that talk about a function's code introduce a short alias for its
entry address:

    Notation AQ := KernelSyms.acquire.
    ...  instr (mword_of_int (AQ + 0x24)) ...

The alias buys nothing -- it is not shorter in any meaningful way and it is
not stable -- while 16 of the names mean DIFFERENT functions in different
files: [CI] is clockintr, consoleinit AND copyin; [UI] is uartinit, uartintr
AND userinit; [FD] is fdalloc, filedup AND free_desc.  Anything that reasons
across files (a checker, a rewriter, a reader) has to carry a per-file
resolution table to avoid resolving a pc into the wrong function, and getting
that wrong is silent: the address still elaborates, it just names another
function's instruction.

So spell the symbol directly: `KernelSyms.acquire + 0x24`.

Aliases are resolved from the file's OWN definitions plus those of the modules
it Requires, and substitution is word-boundary anchored.
"""

import argparse
import glob
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_decode as G

# `Local Notation` / `Local Definition` are just as common as the bare forms;
# missing the prefix leaves the definition in place and then SUBSTITUTES INTO
# IT -- `Local Notation KernelSyms.argint := KernelSyms.argint.`
NOTATION = r'^[ \t]*(?:Local\s+)?Notation\s+%s\s*:=\s*KernelSyms\.\w+\s*\.[ \t]*\n'
DEFN = r'^[ \t]*(?:Local\s+)?Definition\s+%s\s*:\s*Z\s*:=\s*KernelSyms\.\w+\s*\.[ \t]*\n'
DEF_PATS = [r'Notation\s+([A-Za-z_][A-Za-z_0-9]*)\s*:=\s*KernelSyms\.(\w+)\s*\.',
            r'Definition\s+([A-Za-z_][A-Za-z_0-9]*)\s*:\s*Z\s*:=\s*KernelSyms\.(\w+)\s*\.']


def own_aliases(path, syms):
    body = G.strip_comments(open(path).read())
    out = {}
    for pat in DEF_PATS:
        for nm, base in re.findall(pat, body):
            if base in syms:
                out[nm] = base
    return out


REQ_RE = re.compile(r'Require\s+(?:Import|Export)?\s*([A-Za-z_][A-Za-z_0-9. ]*)\.')


def requires_of(body):
    out = []
    for mod in REQ_RE.findall(body):
        out.extend(x.strip() for x in mod.split() if x.strip())
    return out


# A name can be BOTH an address alias and a module/section name -- SpecPlicinit
# has `Notation PLICINIT := KernelSyms.plicinit.` and `Module Type PLICINIT.`
# in the same file (different namespaces, which Coq allows).  Never substitute
# on a line that DECLARES something.
DECL_START = re.compile(r'^[ \t]*(?:Module|End|Section|Include|Declare|Export|Import)\b', re.M)


def protected_spans(text):
    """Character ranges a substitution must not touch.

    A declaration is protected to its TERMINATING period, not just to end of
    line: a sealed functor's parameter list spans several lines --

        Module MainProof
          (Cpuid : CPUID) (Consoleinit : CONSOLEINIT) ...

    -- and CPUID is both a module type here and an address alias elsewhere, so
    a line-only guard renames the module type on the continuation lines."""
    out = []
    # An iIntros/intros parenthesised list introduces BINDER NAMES, and those
    # collide with the aliases too: `iIntros (CID8 Hs8 ms MP)` names a variable
    # MP, it does not mention myproc's entry address.
    for m in re.finditer(r'\b(?:i?Intros|iDestruct[^(\n]*as)\s*\([^)\n]*\)', text):
        out.append(m.span())
    for m in DECL_START.finditer(text):
        i, n = m.end(), len(text)
        while i < n:
            if text[i] == '.' and not (i + 1 < n and (text[i + 1].isalnum() or text[i + 1] == '_')):
                break
            i += 1
        out.append((m.start(), min(i + 1, n)))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--iris', default='iris')
    ap.add_argument('--kernel-rocq', default='kernel-rocq')
    ap.add_argument('--dry-run', action='store_true')
    args = ap.parse_args()

    syms = G.load_syms(os.path.join(args.kernel_rocq, 'KernelSyms.v'))
    files = sorted(glob.glob(os.path.join(args.iris, '*.v')))
    per_file = {os.path.basename(p)[:-2]: own_aliases(p, syms) for p in files}
    req_cache = {os.path.basename(p)[:-2]: requires_of(G.strip_comments(open(p).read()))
                 for p in files}

    n_files = n_sub = n_def = 0
    for p in files:
        raw = open(p).read()
        body = G.strip_comments(raw)
        stem = os.path.basename(p)[:-2]

        # What this file can see.  Requires are TRANSITIVE for the purposes of
        # a Notation being in scope, so close over them -- a one-level map
        # leaves an alias unsubstituted in a file that reaches it indirectly,
        # while the defining file has already dropped the definition.
        vis = {}
        seen, todo = set(), list(requires_of(body))
        while todo:
            nm = todo.pop()
            if nm in seen:
                continue
            seen.add(nm)
            vis.update(per_file.get(nm, {}))
            todo.extend(req_cache.get(nm, ()))
        vis.update(per_file[stem])
        # A name BOUND LOCALLY in this file is that binding, not the alias:
        # ProofFdalloc's `iIntros (CID8 Hs8 ms MP)` names a regfile MP and the
        # file never uses myproc's address at all, so substituting MP there
        # breaks the proof.  Drop such names unless this file is the one that
        # DEFINES the alias.
        bound = set()
        for m in re.finditer(r'\b(?:i?Intros|iDestruct[^(\n]*as)\s*\(([^)\n]*)\)', body):
            bound.update(re.findall(r'[A-Za-z_][A-Za-z_0-9]*', m.group(1)))
        for m in re.finditer(r'\bset\s*\(\s*([A-Za-z_][A-Za-z_0-9]*)\s*:=', body):
            bound.add(m.group(1))
        for nm in bound - set(per_file[stem]):
            vis.pop(nm, None)
        if not vis:
            continue

        out = raw
        # drop this file's own definitions first, so the substitution below
        # cannot rewrite the very line that introduces the alias
        for nm in per_file[stem]:
            for pat in (NOTATION % re.escape(nm), DEFN % re.escape(nm)):
                out, k = re.subn(pat, '', out, flags=re.M)
                n_def += k
        # Substitute line by line, SKIPPING declaration lines outright: a name
        # can be both an address alias and a module/section name (SpecPlicinit
        # has `Notation PLICINIT := KernelSyms.plicinit.` and `Module Type
        # PLICINIT.` in one file), and rewriting the declaration renames the
        # module.
        spans = protected_spans(out)

        def shielded(pos):
            return any(x <= pos < y for x, y in spans)

        # Character-level, over the whole file: a protected region (an iIntros
        # binder list, a functor's parameter list) can start mid-line, so a
        # line-level guard either over- or under-protects.
        for nm, base in sorted(vis.items(), key=lambda kv: -len(kv[0])):
            def repl(m, base=base):
                if shielded(m.start()):
                    return m.group(0)
                pre = out[:m.start()].rstrip()
                post = out[m.end():].lstrip()
                # a BINDER `( X : T )` -- as opposed to an ASCRIPTION `X : T`
                if pre.endswith('(') and post.startswith(':') and not post.startswith(':='):
                    return m.group(0)
                # a MODULE QUALIFICATION `ASL.wp_...`
                if post.startswith('.') and len(post) > 1 and (post[1].isalpha() or post[1] == '_'):
                    return m.group(0)
                return 'KernelSyms.%s' % base
            out, k = re.subn(r'(?<![A-Za-z_0-9.])%s(?![A-Za-z_0-9])' % re.escape(nm), repl, out)
            n_sub += k
            spans = protected_spans(out)
        if out != raw:
            n_files += 1
            if not args.dry_run:
                open(p, 'w').write(out)

    print("%s %d file(s): %d alias definitions removed, %d occurrences rewritten"
          % ('would touch' if args.dry_run else 'touched', n_files, n_def, n_sub))
    return 0


if __name__ == '__main__':
    sys.exit(main())
