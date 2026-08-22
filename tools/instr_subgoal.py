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
POSE = re.compile(r'iPoseProof \((\w+) with "Htext"\) as "([^"\s]+)"\.')
# a whole line that is nothing but one or more such poses
POSE_LINE = re.compile(r'^[ \t]*(?:iPoseProof \(\w+ with "Htext"\) as "[^"\s]+"\. ?)+\n',
                       re.M)
# a conforming call site: the instr hypothesis is the third thing handed to a
# leaf, and the sentence ends on this line
SITE = re.compile(r'^([ \t]*)(.*with "Hcg Hpc )([^"\s]+?)(?=[ "])([^"]*")\)\.$', re.M)
# [iClear "Ha Hb Hc".] -- the names may span a line break (ProofSysLink)
CLEAR = re.compile(r'([ \t]*)iClear "([^"]*)"\s*\.')
# every double-quoted string; an Iris hypothesis name only ever appears inside
# one, which is how a Coq hypothesis of the SAME name is told apart (see scan)
QUOTED = re.compile(r'"([^"]*)"', re.S)
# a pose inside a [tac ; iPoseProof ... ;] preamble: the converter cannot touch
# it (its use site ends in [;], not [).]), and POSE_LINE cannot delete it, so
# "posed 0" would otherwise read as "fully converted" on a file still carrying
# a whole chained block
CHAINED = re.compile(r'iPoseProof \(\w+ with "Htext"\) as "[^"]+";')


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

    # [iClear "Hi"] of a fact we are about to stop posing is DEAD once the pose
    # goes, so it is accounted for here and deleted by convert().  Files written
    # in the "pose late, clear early" style are made almost entirely of this
    # shape -- ProofVirtioDiskInit poses [Hi], uses it, clears it, 127 times.
    cleared = {}
    for m in CLEAR.finditer(src):
        for name in m.group(2).split():
            if name in poses:
                cleared[name] = cleared.get(name, 0) + 1

    # Count references only INSIDE double-quoted strings.  An Iris hypothesis is
    # always named in one; a Coq hypothesis that happens to share the name is
    # not (ProofVirtioDiskInit has [apply pa_range_elim in Hx as (i & Hi & ->)]
    # beside 127 Iris [Hi]s), and counting bare occurrences reported it as a
    # stray reference and refused the whole file.
    quoted = {}
    for m in QUOTED.finditer(src):
        for name in m.group(1).split():
            quoted[name] = quoted.get(name, 0) + 1

    stray = dict(unposed)
    for h in poses:
        n = quoted.get(h, 0)
        n -= len(poses[h])                        # the [as "h"] of each pose
        n -= accounted.get(h, 0)                  # the call sites
        n -= cleared.get(h, 0)                    # the iClears we will delete
        if n > 0:
            stray[h] = stray.get(h, 0) + n
    return resolved, sites, stray, poses, cleared


def convert(src):
    resolved, _, stray, poses, _ = scan(src)
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

    # Drop the now-dead [iClear "Hi"]s.  A clear may name several hypotheses,
    # only some of them ours, so the list is filtered rather than the sentence
    # deleted; a sentence whose list empties is replaced by a sentinel, and a
    # line left holding nothing but the sentinel goes away with it.  Only lines
    # the sentinel touches are rewritten -- an earlier version stripped trailing
    # whitespace file-wide and silently edited 39 untouched files.
    nclear = [0]
    SENTINEL = '\x00'

    def declear(m):
        lead, names = m.group(1), m.group(2).split()
        keep = [n for n in names if n not in poses]
        if len(keep) == len(names):
            return m.group(0)
        nclear[0] += len(names) - len(keep)
        if not keep:
            return SENTINEL
        return lead + 'iClear "' + ' '.join(keep) + '".'

    out = CLEAR.sub(declear, out)
    if SENTINEL in out:
        kept = []
        for line in out.split('\n'):
            if SENTINEL not in line:
                kept.append(line)
                continue
            line = line.replace(SENTINEL, '')
            if line.strip():
                kept.append(line.rstrip())
            # else: the line held only the dead iClear -- drop it
        out = '\n'.join(kept)

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

    return out, npose, nsite[0], nclear[0]


QED = re.compile(r'^\s*(?:Qed|Defined)\.', re.M)


def rank(files):
    """Rank candidates by expected payoff, best first.

    Measured over 111 conversions, the thing that predicts the win is how much
    of a PROOF sits under a live block -- not the file's pose count, not its
    length, and not the largest contiguous run of pose lines.  Two corrections
    the sweep had to make the hard way are built in here:

      * poses killed by a later [iClear] were never live alongside the next
        pose, so a "pose late, clear early" file has a live block of ~1 however
        many poses it has (ProofVirtioDiskInit: 127 poses, -7.5%);
      * the unit of Delta is the PROOF, not the file, so poses-per-Qed sorts a
        set that peak-block leaves uncorrelated (ProofVirtioDiskRwD: 12 poses
        over 84 lemmas, -4.8%).

    Both columns are printed; sort key is poses-per-Qed, with peak live block
    breaking ties.  Neither sizes the win to better than about +/-10 points --
    ProofSysLink has the largest block in the tree and returned -14% because
    most of its time is not proofmode work at all.
    """
    rows = []
    for f in files:
        src = open(f).read()
        poses = POSE.findall(src)
        if not poses:
            continue
        live, peak = 0, 0
        for m in re.finditer(r'iPoseProof \(\w+ with "Htext"\) as "([^"\s]+)"\.'
                             r'|iClear "([^"]*)"', src):
            if m.group(1) is not None:
                live += 1
                peak = max(peak, live)
            else:
                live = max(0, live - len(m.group(2).split()))
        qeds = max(1, len(QED.findall(src)))
        ppq = len(poses) / qeds
        # the score has to be small when EITHER correction bites: a clear-early
        # file has a tiny peak however many poses it has, and a file of many
        # small lemmas has a tiny poses-per-Qed however big one block is
        rows.append((min(peak, ppq), peak, ppq, len(poses), qeds, f))
    rows.sort(reverse=True)
    print('%-30s %6s %6s %6s %9s %6s'
          % ('file', 'poses', 'Qeds', 'peak', 'pose/Qed', 'score'))
    for score, peak, ppq, n, q, f in rows:
        print('%-30s %6d %6d %6d %9.1f %6.1f' % (f, n, q, peak, ppq, score))
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='+')
    ap.add_argument('--check', action='store_true',
                    help='report conformance and change nothing')
    ap.add_argument('--rank', action='store_true',
                    help='rank unconverted files by expected payoff, best first')
    args = ap.parse_args()

    if args.rank:
        return rank(args.files)

    rc = 0
    for f in args.files:
        src = open(f).read()
        resolved, sites, stray, poses, _ = scan(src)
        chained = len(CHAINED.findall(src))
        if args.check:
            state = ('CLEAN' if not stray else 'HAND WORK: '
                     + ', '.join('%s x%d' % kv for kv in sorted(stray.items())))
            if chained:
                state += '  [+%d ;-CHAINED pose(s) the tool cannot touch]' % chained
            print('%-28s posed %3d/%3d  sites %3d  %s'
                  % (f, len(poses), sum(len(v) for v in poses.values()),
                     len(sites), state))
            if stray:
                rc = 1
            continue
        try:
            out, npose, nsite, nclear = convert(src)
        except ValueError as e:
            print('%-28s SKIPPED -- %s' % (f, e), file=sys.stderr)
            rc = 1
            continue
        open(f, 'w').write(out)
        print('%-28s pose lines removed %3d  call sites rewritten %3d'
              '  dead iClears dropped %3d' % (f, npose, nsite, nclear))
    return rc


if __name__ == '__main__':
    sys.exit(main())
