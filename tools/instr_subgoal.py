#!/usr/bin/env python3
"""instr_subgoal.py -- convert a proof from POSING instruction facts to closing
them as subgoals.

The discipline (claude-notes/projects/instr-subgoal-sweep.md): a leaf lemma's
[instr pc rvc ast] premise never enters the Iris context.  Instead of

    iPoseProof (pai_02 with "Htext") as "Hi02".        (* ...40 lines earlier *)
    iApply (wp_csdsp_s_sconf ... with "Hcg Hpc Hi02 Hr40").

write

    iApply (wp_csdsp_s_sconf ... with "Hcg Hpc [] Hr40").
    { iApply (pai_02 with "Htext"). }

RULE ONE says the cost of a proofmode step is |Delta|, so deleting a block of
sixty persistent facts discounts every one of the file's ~1700 steps.  Measured
on ProofPipealloc.v: wall -46%, Qed -61%, proof term -69%.

The hypothesis-name -> lemma-name map is READ OFF THE POSE LINES, so no
per-file prefix has to be guessed.

Usage:
    tools/instr_subgoal.py --check iris/ProofBmap.v      # report, touch nothing
    tools/instr_subgoal.py        iris/ProofBmap.v       # convert in place

--check exits 0 if the file converts outright, 1 if some reference to a posed
name is not a conforming call site (those need hand work; the converter refuses
to run rather than delete a pose whose fact is still needed).
"""
import argparse
import re
import sys

# iPoseProof (<lemma> with "Htext") as "<hyp>".
POSE = re.compile(r'iPoseProof \((\w+) with "Htext"\) as "(\w+)"\.')
# a whole line that is nothing but one or more such poses
POSE_LINE = re.compile(r'^[ \t]*(?:iPoseProof \(\w+ with "Htext"\) as "\w+"\. ?)+\n',
                       re.M)
# a conforming call site: the instr hypothesis is the third thing handed to a
# leaf, and the sentence ends on this line
SITE = re.compile(r'^([ \t]*)(.*with "Hcg Hpc )(\w+)([^"]*")\)\.$', re.M)


def scan(src):
    """-> (site position -> lemma, conforming sites, {hyp: stray count})

    A hypothesis name is resolved per SITE, against the NEAREST PRECEDING pose
    of that name -- which is how the proof itself reads.  Proof-local scopes
    legitimately rebind a name to a different instruction (ProofIput binds
    [Hi3a] to [ipi_38] early and to [ipi_3a] 3000 lines later; ProofKwait binds
    [Hie0] to [kwi_e0] and then to [kwi_ee] in the next lemma), and a global
    last-pose-wins map silently closes the early sites with the wrong lemma.
    """
    poses = {}                       # hyp -> [(offset, lemma)], in file order
    for m in POSE.finditer(src):
        poses.setdefault(m.group(2), []).append((m.start(), m.group(1)))

    resolved, sites, unposed = {}, [], {}
    for m in SITE.finditer(src):
        hyp = m.group(3)
        if hyp not in poses:
            continue                 # not an instr hypothesis at all
        earlier = [l for off, l in poses[hyp] if off < m.start()]
        if not earlier:              # used before it is ever posed
            unposed[hyp] = unposed.get(hyp, 0) + 1
            continue
        resolved[m.start()] = earlier[-1]
        sites.append(m)

    accounted = {}
    for m in sites:
        accounted[m.group(3)] = accounted.get(m.group(3), 0) + 1
    stray = dict(unposed)
    for h in poses:
        n = len(re.findall(r'(?<![\w])' + re.escape(h) + r'(?![\w])', src))
        n -= len(poses[h])                        # the poses themselves
        n -= accounted.get(h, 0)
        if n:
            stray[h] = stray.get(h, 0) + n
    return resolved, sites, stray, poses


def convert(src):
    resolved, _, stray, _ = scan(src)
    if stray:
        raise ValueError('non-conforming references: '
                         + ', '.join('%s x%d' % kv for kv in sorted(stray.items())))

    nsite = [0]

    def repl(m):
        indent, pre, _hyp, post = m.groups()
        lemma = resolved.get(m.start())
        if lemma is None:
            return m.group(0)          # not an instr fact -- leave it alone
        nsite[0] += 1
        return (indent + pre + '[]' + post + ').\n'
                + indent + '{ iApply (' + lemma + ' with "Htext"). }')

    # Rewrite the SITES FIRST: `resolved` is keyed by offsets into `src`, so
    # deleting the pose lines beforehand would shift every key.
    out = SITE.sub(repl, src)
    out, npose = POSE_LINE.subn('', out)

    # The site regex sees the indent of the line the [with "..."] sits on, which
    # for a multi-line iApply is the continuation indent.  Re-indent each brace
    # to the indent of the iApply that opened the sentence.
    brace = re.compile(r'^(\s*)\{ iApply \(\w+ with "Htext"\)\. \}$')
    lines, fixed = out.split('\n'), []
    for line in lines:
        if brace.match(line):
            j = len(fixed) - 1
            while j >= 0 and not re.match(r'^\s*iApply \(', fixed[j]):
                j -= 1
            if j >= 0:
                line = re.match(r'^(\s*)', fixed[j]).group(1) + line.strip()
        fixed.append(line)
    out = '\n'.join(fixed)

    assert not POSE.search(out), 'poses survived'

    return out, npose, nsite[0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='+')
    ap.add_argument('--check', action='store_true',
                    help='report conformance and change nothing')
    args = ap.parse_args()

    rc = 0
    for f in args.files:
        src = open(f).read()
        resolved, sites, stray, poses = scan(src)
        if args.check:
            print('%-28s posed %3d/%3d  sites %3d  %s'
                  % (f, len(poses), sum(len(v) for v in poses.values()),
                     len(sites),
                     'CLEAN' if not stray else 'HAND WORK: '
                     + ', '.join('%s x%d' % kv for kv in sorted(stray.items()))))
            if stray:
                rc = 1
            continue
        try:
            out, npose, nsite = convert(src)
        except ValueError as e:
            print('%-28s SKIPPED -- %s' % (f, e), file=sys.stderr)
            rc = 1
            continue
        open(f, 'w').write(out)
        print('%-28s pose lines removed %3d  call sites rewritten %3d'
              % (f, npose, nsite))
    return rc


if __name__ == '__main__':
    sys.exit(main())
