#!/usr/bin/env python3
"""Give every opaque proof in iris/ the minimal `Proof using` Rocq computes for it.

`-vos` skips a proof only if it is told up front what the proof captures; with no
annotation Rocq has to RUN the proof to find out, so the whole edit-check loop
(`run-on-gcp --check`) depends on these being present.  The MINIMAL set is what
Rocq would have computed anyway, so an annotation added here changes no lemma's
type -- unlike a blanket `Set Default Proof Using`, which over-captures for some
proofs (growing argument lists the sealed functors are matched against) and
under-captures for others (section HYPOTHESES never appear in a statement).

Input is a build log made with `-set "Suggest Proof Using=yes"`; Rocq prints the
options minimal-first and this takes the first.

NOT touched:
  * AUTO-GENERATED files -- their generators emit the annotation themselves, so
    a hand-edit here would be reverted by the next `make gen-code`/`gen-ucode`
    and would fail `check-decode`/`check-ucode`.
  * `Let` declarations.  Rocq SUGGESTS an annotation for these and then refuses
    it -- *Let does not support Proof using* -- so taking the suggestion breaks
    the build.
  * anonymous `Goal`s (Rocq calls them `Unnamed_thm`).  The ones here are
    `Fail set_solver. Abort.` tripwires -- they define nothing, so there is
    nothing to annotate.
"""

import argparse, collections, os, re, sys

DECL = re.compile(r'^\s*(?:#\[[^\]]*\]\s*)?(?:Local\s+|Global\s+|Program\s+)*'
                  r'(?:Lemma|Theorem|Corollary|Fact|Remark|Property|Example|Instance)\s+'
                  r"([A-Za-z_][A-Za-z0-9_']*)")
LET = re.compile(r"^\s*(?:Local\s+)?Let\s+([A-Za-z_][A-Za-z0-9_']*)")
PROOF = re.compile(r'^(\s*)Proof\s*\.(.*)$')
PROOF_USING = re.compile(r'^\s*Proof\s+using\b')


def parse_log(path):
    """-> {file: [(lemma name, minimal `Proof using ...` line)]}, in file order."""
    out = collections.defaultdict(list)
    cur = None
    lines = open(path, errors='replace').read().split('\n')
    i = 0
    while i < len(lines):
        m = re.match(r'^ROCQ compile (\S+\.v)$', lines[i])
        if m:
            cur = m.group(1); i += 1; continue
        if lines[i].startswith('The proof of '):
            buf = lines[i][len('The proof of '):]
            j = i
            while 'should start with one of the following' not in buf and j + 1 < len(lines):
                j += 1; buf += ' ' + lines[j]
            name = buf.split('should start with one of the following')[0].strip()
            # A lone suggestion is printed on the SAME line as the header
            # ("...commands: Proof using Hn."), several one per line below it.
            head = buf.split('commands:', 1)[1].strip() if 'commands:' in buf else ''
            opts = [' '.join(head.split())] if head.startswith('Proof using') else []
            k = j + 1
            while k < len(lines) and lines[k].strip().startswith('Proof using'):
                opts.append(' '.join(lines[k].split())); k += 1
            if cur and name and opts:
                out[cur].append((name, opts[0]))
            i = k; continue
        i += 1
    return out


def is_generated(path):
    try:
        with open(path, encoding='utf-8', errors='replace') as f:
            return 'AUTO-GENERATED' in ''.join(f.readline() for _ in range(3))
    except OSError:
        return False


def proof_slots(src):
    """declaration name -> [line indices of its `Proof.`], in order."""
    slots = collections.defaultdict(list)
    for n, line in enumerate(src):
        d = DECL.match(line)
        if not d:
            continue
        for k in range(n + 1, min(n + 400, len(src))):
            if PROOF_USING.match(src[k]):
                break                      # already annotated
            if PROOF.match(src[k]):
                slots[d.group(1)].append(k); break
            if DECL.match(src[k]):
                break                      # next declaration, no `Proof.`
    return slots


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--log', required=True, help='build log made with Suggest Proof Using=yes')
    ap.add_argument('--iris', default='iris')
    ap.add_argument('--apply', action='store_true', help='write the files (default: report only)')
    args = ap.parse_args()

    sugg = parse_log(args.log)
    patched = skipped_gen = skipped_let = skipped_anon = unplaceable = 0
    unplaced = collections.Counter()

    for f, items in sorted(sugg.items()):
        path = os.path.join(args.iris, f)
        if not os.path.exists(path):
            continue
        if is_generated(path):
            skipped_gen += len(items); continue
        src = open(path, encoding='utf-8').read().split('\n')
        lets = {m.group(1) for line in src if (m := LET.match(line))}
        slots = proof_slots(src)
        used = collections.Counter()
        dirty = False
        for name, minimal in items:
            if name.startswith('Unnamed_thm'):
                skipped_anon += 1; continue      # an aborted `Goal`: defines nothing
            if name in lets:
                skipped_let += 1; continue
            cand = slots.get(name)
            if not cand or used[name] >= len(cand):
                unplaceable += 1; unplaced[f] += 1; continue
            ln = cand[used[name]]; used[name] += 1
            m = PROOF.match(src[ln])
            if not m:
                unplaceable += 1; unplaced[f] += 1; continue
            src[ln] = m.group(1) + minimal + m.group(2)
            patched += 1; dirty = True
        if dirty and args.apply:
            open(path, 'w', encoding='utf-8').write('\n'.join(src))

    print('annotated %d proof(s)%s' % (patched, '' if args.apply else ' (dry run)'))
    print('  skipped %d in AUTO-GENERATED files (their generators emit it)' % skipped_gen)
    print('  skipped %d `Let` (Rocq suggests an annotation it then rejects)' % skipped_let)
    print('  skipped %d anonymous `Goal` (aborted; defines nothing)' % skipped_anon)
    print('  could not place %d' % unplaceable)
    for f, c in unplaced.most_common(8):
        print('      %-32s %d' % (f, c))
    return 0


if __name__ == '__main__':
    sys.exit(main())
