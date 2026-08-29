#!/usr/bin/env python3
"""proof_timeline.py -- per-function spec/proof HARDNESS analysis from git history.

The question this answers: *which functions were hardest to SPEC, and which
hardest to PROVE?*  Git history is the only data; every number below is a
proxy, and the proxies are chosen so that the failure modes of the obvious
naive metrics (see "HAZARDS" below) are avoided or at least made visible.

------------------------------------------------------------------ units ----
A "unit" is one verified C function, named by its iris/Spec<F>.v file.
Files are attributed to a unit by LONGEST-PREFIX match on the role-stripped
basename, so companion files land on the right function:

    iris/Spec<F>.v, iris/<F>Budget.v          -> spec-side effort
    iris/Proof<F>.v, iris/Proof<F>Parts.v,
    iris/Proof<F>A.v ... iris/Proof<F>Tail.v  -> proof-side effort
    iris/Link<F>.v                            -> "proven" marker (the tree's
                                                  own convention: the Link
                                                  layer is what closes a cone)

Longest-prefix keeps ProofNameiparent.v off Namei and puts ProofNamexParts.v,
ProofKforkB1..B7, ProofKexecSeam.v on Namex / Kfork / Kexec.  An auxiliary
spec name (a spec file whose name extends another unit's name and which has
no proof or link file of its own -- SpecCreateFreshTy.v, SpecMemsetParts.v,
SpecInitlockWrapper.v) is MERGED into its parent unit and recorded in the
note column.

--------------------------------------------------------------- hazards ----
(1) Spec birth date under-measures.  Create's budget reasoning lived in
    CreateBudget.v and in claude-notes/ for weeks before SpecCreate.v was
    born.  So spec_start = min(first add of any spec-side file, first
    claude-notes/ commit that is substantially ABOUT the function).
    "Substantially about" = the function's name appears >= --notes-threshold
    times in the lines that commit ADDS to claude-notes/ (a single passing
    mention is not design work).  Both dates are kept separately so the
    reader can see the gap and distrust it where it looks like a homonym.

(2) Calendar elapsed conflates waiting with working.  So the effort columns
    are DISTINCT AUTHOR-DAYS: distinct (normalized author, author date)
    pairs on which a commit touched the unit's spec-side / proof-side files.

(3) Raw commit counts mix mechanical sweeps with real rework.  Every commit
    is classed by how many iris/*.v files it touches:
        focused  <= --focused-max (default 5)   -- real work on this proof
        sweep    >  --sweep-min   (default 20)  -- a bump/restyle/re-address
                                                   wave that swept this file
        mid      in between
    focused_rework (focused commits after the proof file was first added) is
    the proof-hardness signal; sweep is deliberately excluded from it.

(4) Churn and size.  churn = lines added+deleted over all history of the
    unit's files (git log --numstat, renames followed); lines = today's size.

(5) SPEC INSTABILITY.  focused commits touching a spec-side file AFTER the
    unit's first proof landed (Link add, else first proof-file add).  A spec
    that kept moving after it had been proven is a spec that was hard to get
    right -- this is the hardest-to-spec signal.

(6) REDOS.  COMMITS that deleted a proof-side file (git status D, with rename
    detection on so renames are not counted); the note column also shows the
    file count when one commit deleted several.  A thrown-away-and-rewritten
    proof is a strong, rare hardness signal -- but count commits, not files,
    or one campaign that retires an eight-file part chain (virtio_disk_rw)
    masquerades as eight separate rewrites.

Renames are followed by canonicalizing every historical path to its present
name using the R records in the log, so no --follow calls are needed: the
whole history is read in two `git log` passes plus one `-p` pass over
claude-notes/, which keeps the run to a couple of seconds.

------------------------------------------------------------- caveats -------
* Bespoke helper libraries that do not follow the Spec/Proof/Link/Budget
  naming convention (PathElems.v, InodeRegion.v, ...) are NOT attributed to
  any unit, so functions carrying such libraries are under-counted.
* Wp<F>Decode.v / Code<F>.v decode scaffolding is tracked but kept out of the
  headline metrics (it is largely mechanical); see the tsv dump.
* Author-days are a coarse effort proxy: parallel worktree agents can move
  several functions on one calendar day, and one commit can be an hour or a
  day of work.
* Notes-mention dates are noisy for units whose name is an ordinary English
  word (Create, Main, Sleep, Walk, User, Panic, Spin, Entry).  Such units are
  flagged "homonym?" in the note column.
* The Spec/Proof/Link convention only dates from the 2026-07-21 module
  migration (and the 2026-07-23 Wp<F>.v -> Proof<F>.v rename, which IS
  followed).  Design work older than that lived in iris/CLAUDE.md, which the
  notes scan covers, and in files whose names give no unit away, which it
  does not.
* A file renamed OUT of the convention (ProofIupdateParts.v -> DinodeSlot.v)
  takes its whole history with it, since paths are canonicalized to their
  present name -- the same semantics as `git log --follow`.

Usage:
    tools/proof_timeline.py --sort=hard-proof --top=15
    tools/proof_timeline.py --sort=instability --md
    tools/proof_timeline.py --tsv --top=0 > hardness.tsv
    tools/proof_timeline.py --only=Namex,Writei --top=0
"""

from __future__ import annotations

import argparse
import collections
import datetime
import os
import re
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Unit names that are also ordinary English words; their notes-mention date is
# unreliable (a note about "create" may not be about create()).
HOMONYMS = {
    'Create', 'Main', 'Sleep', 'Walk', 'User', 'Panic', 'Spin', 'Entry',
    'Wakeup', 'Killed', 'Flags2perm', 'Release', 'Acquire', 'Holding',
    'Sched', 'Yield', 'Readi', 'Writei',
}

# Two emails, one person.
AUTHOR_ALIASES = {
    'nickolai.zeldovich': 'nickolai',
    'nickolai': 'nickolai',
    'kaashoek': 'kaashoek',
}


# --------------------------------------------------------------- git I/O ---

def git(*args: str) -> str:
    return subprocess.run(['git', '-C', ROOT, *args],
                          capture_output=True, text=True, check=True).stdout


def norm_author(email: str) -> str:
    local = email.split('@')[0].lower()
    return AUTHOR_ALIASES.get(local, local)


class Commit:
    """One commit's parsed footprint."""
    __slots__ = ('sha', 'ts', 'day', 'author', 'stats', 'status', 'iris_files')

    def __init__(self, sha, ts, day, author):
        self.sha = sha
        self.ts = ts
        self.day = day
        self.author = author
        self.stats = {}        # canonical path -> (added, deleted)
        self.status = {}       # canonical path -> 'A' | 'D' | 'M' | 'R'
        self.iris_files = 0    # how many iris/*.v files this commit touched


def read_history():
    """Two -z log passes -> commits (newest first) and a rename canonicalizer.

    Returns (commits, canon) where canon maps any historical path to the path
    that file carries today.  Because the log is walked newest-first, a rename
    record old->new is seen only after `new` has already been canonicalized.
    """
    canon: dict[str, str] = {}

    def canonical(p: str) -> str:
        seen = set()
        while p in canon and p not in seen:
            seen.add(p)
            p = canon[p]
        return p

    # Pass 1: name-status, for A/D/R records (rename map + redo detection).
    commits: dict[str, Commit] = {}
    order: list[str] = []
    raw = git('log', '-M', '--name-status', '-z',
              '--format=%x01%H%x02%at%x02%ad%x02%ae', '--date=format:%Y-%m-%d')
    for chunk in raw.split('\x01'):
        if not chunk:
            continue
        head, _, rest = chunk.partition('\x00')
        sha, ts, day, email = head.split('\x02')
        c = Commit(sha, int(ts), day, norm_author(email))
        commits[sha] = c
        order.append(sha)
        # the header ends "...\0\n", so the first status carries a newline
        fields = [f.strip('\n') for f in rest.split('\x00') if f.strip('\n')]
        i = 0
        while i + 1 < len(fields):
            st = fields[i]
            if st.startswith('R') or st.startswith('C'):
                old, new = fields[i + 1], fields[i + 2]
                i += 3
                tgt = canonical(new)
                if old != tgt:
                    canon[old] = tgt
                c.status[tgt] = 'R'
            else:
                path = canonical(fields[i + 1])
                i += 2
                c.status[path] = st[0]

    # Pass 2: numstat, for churn.  Same commit order, same rename records.
    raw = git('log', '-M', '--numstat', '-z', '--format=%x01%H')
    for chunk in raw.split('\x01'):
        if not chunk:
            continue
        sha, _, rest = chunk.partition('\x00')
        sha = sha.strip()
        c = commits.get(sha)
        if c is None:
            continue
        fields = [f.strip('\n') for f in rest.split('\x00') if f.strip('\n')]
        i = 0
        while i < len(fields):
            f = fields[i]
            parts = f.split('\t')
            if len(parts) == 3 and parts[2] == '':
                # rename entry: "add\tdel\t" then old, new as separate fields
                add, dele = parts[0], parts[1]
                path = canonical(fields[i + 2])
                i += 3
            elif len(parts) == 3:
                add, dele, path = parts[0], parts[1], canonical(parts[2])
                i += 1
            else:
                i += 1
                continue
            a = int(add) if add.isdigit() else 0
            d = int(dele) if dele.isdigit() else 0
            pa, pd = c.stats.get(path, (0, 0))
            c.stats[path] = (pa + a, pd + d)

    for c in commits.values():
        touched = set(c.stats) | set(c.status)
        c.iris_files = sum(1 for p in touched
                           if p.startswith('iris/') and p.endswith('.v'))
    return [commits[s] for s in order], canon


# ------------------------------------------------------------ attribution ---

ROLE_PREFIX = [('Spec', 'spec'), ('Proof', 'proof'), ('Link', 'link'),
               ('Wp', 'code'), ('Code', 'code')]


def split_role(basename: str):
    """iris/ProofNamexParts.v -> ('proof', 'NamexParts'); Budget files -> spec."""
    if not basename.endswith('.v'):
        return None, None
    stem = basename[:-2]
    for pre, role in ROLE_PREFIX:
        if stem.startswith(pre) and len(stem) > len(pre) and stem[len(pre)].isupper():
            return role, stem[len(pre):]
    if stem.endswith('Budget'):
        return 'spec', stem[:-len('Budget')]
    return None, None


def build_units():
    """Current Spec*.v files define the units; aux spec names merge upward."""
    iris = os.path.join(ROOT, 'iris')
    names = sorted(f[4:-2] for f in os.listdir(iris)
                   if f.startswith('Spec') and f.endswith('.v'))
    have = lambda pre, n: os.path.exists(os.path.join(iris, f'{pre}{n}.v'))

    merged = {}   # aux name -> parent unit
    units = []
    for n in names:
        if have('Proof', n) or have('Link', n):
            units.append(n)
            continue
        parents = [p for p in names if p != n and n.startswith(p)]
        if parents:
            merged[n] = max(parents, key=len)
        else:
            units.append(n)
    # resolve chains, then keep only real units
    for k in list(merged):
        while merged[k] in merged:
            merged[k] = merged[merged[k]]
    unit_set = set(units)
    merged = {k: v for k, v in merged.items() if v in unit_set}
    for k in [k for k in merged if k in unit_set]:
        del merged[k]
    lookup = sorted(unit_set | set(merged), key=len, reverse=True)
    return units, merged, lookup


def attribute(path, lookup, merged, unit_set):
    """path -> (units, role); units is a tuple, empty when nothing matches.

    Normal case: the longest unit name that PREFIXES the role-stripped
    basename wins, so ProofNamexParts.v -> Namex and ProofNameiparent.v ->
    Nameiparent rather than Namei.

    Shared case: a file whose name is a PREFIX of several unit names is a
    genuinely multi-function file -- ProofEitherCopy.v carries both
    either_copyin and either_copyout -- and is credited to all of them.  That
    double-counts its churn across those units on purpose; the alternative is
    to credit it to nobody.  Such units are flagged in the note column.
    """
    if not path.startswith('iris/'):
        return (), None
    role, rest = split_role(os.path.basename(path))
    if role is None:
        return (), None
    for name in lookup:          # longest first
        if rest.startswith(name):
            u = merged.get(name, name)
            return ((u,) if u in unit_set else ()), role
    shared = tuple(u for u in unit_set if u.startswith(rest))
    return (shared if len(shared) > 1 else ()), role


# ---------------------------------------------------------- notes mentions --

def camel_variants(name: str):
    """Namex -> {namex}; SysClose -> {sysclose, sys_close}; BeginOp -> begin_op."""
    parts = re.findall(r'[A-Z][a-z0-9]*|\d+', name)
    concat = name.lower()
    snake = '_'.join(p.lower() for p in parts) if parts else concat
    return {concat, snake}


# Where design prose has lived over the project's life.  claude-notes/ was
# split out of iris/CLAUDE.md on 2026-07-20, so the older file has to be in
# the scan or every pre-07-20 function looks like it was specced cold.
NOTES_PATHS = ['claude-notes/', 'iris/CLAUDE.md', 'CLAUDE.md', 'MANUAL-NOTES.md']


def notes_first_mention(units, threshold):
    """First design-notes commit whose ADDED lines are substantially about F."""
    alias = {}
    for u in units:
        for v in camel_variants(u):
            alias.setdefault(v, []).append(u)
    tok_re = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')
    first = {}
    raw = git('log', '--reverse', '-p', '--format=%x01%at', '--', *NOTES_PATHS)
    for chunk in raw.split('\x01'):
        if not chunk:
            continue
        head, _, body = chunk.partition('\n')
        try:
            ts = int(head.strip())
        except ValueError:
            continue
        counts = collections.Counter()
        for line in body.split('\n'):
            if not line.startswith('+') or line.startswith('+++'):
                continue
            for tok in tok_re.findall(line.lower()):
                if tok in alias:
                    counts[tok] += 1
        for tok, n in counts.items():
            if n >= threshold:
                for u in alias[tok]:
                    first.setdefault(u, ts)
    return first


# ----------------------------------------------------------- fan-in note ----

def proof_fanin(units):
    """unit -> set of other units whose Proof files Require its Spec/Proof."""
    iris = os.path.join(ROOT, 'iris')
    unit_set = set(units)
    fanin = collections.defaultdict(set)
    req_re = re.compile(r'^\s*(?:From\s+\S+\s+)?Require\s+(?:Import|Export)?\s*(.*?)\.\s*$')
    for fn in os.listdir(iris):
        if not (fn.startswith('Proof') and fn.endswith('.v')):
            continue
        role, rest = split_role(fn)
        src = None
        for name in sorted(unit_set, key=len, reverse=True):
            if rest.startswith(name):
                src = name
                break
        if src is None:
            continue
        try:
            with open(os.path.join(iris, fn), encoding='utf-8', errors='replace') as fh:
                text = fh.read()
        except OSError:
            continue
        for line in text.split('\n'):
            m = req_re.match(line)
            if not m:
                continue
            for mod in m.group(1).split():
                r, rst = split_role(mod + '.v')
                if r not in ('spec', 'proof'):
                    continue
                for name in sorted(unit_set, key=len, reverse=True):
                    if rst.startswith(name):
                        if name != src:
                            fanin[name].add(src)
                        break
    return fanin


# --------------------------------------------------------------- analysis ---

class Row:
    def __init__(self, unit):
        self.unit = unit
        self.spec_first = None      # first add of a spec-side file
        self.notes_first = None     # first substantial claude-notes mention
        self.proof_first = None     # first add of a proof-side file
        self.link_first = None      # first add of a Link file
        self.spec_days = set()          # non-sweep commits only (real effort)
        self.proof_days = set()         # non-sweep commits only (real effort)
        self.spec_days_all = set()      # including mechanical sweeps
        self.proof_days_all = set()
        self.spec_churn = 0             # non-sweep churn
        self.proof_churn = 0            # non-sweep churn
        self.spec_churn_all = 0
        self.proof_churn_all = 0
        self.sweep_churn = 0            # proof-side churn from sweeps alone
        self.code_churn = 0
        self.focused_rework = 0
        self.sweeps = 0
        self.mid = 0
        self.instability = 0        # focused spec commits after the proof landed
        self.instab_churn = 0       # spec lines moved by those commits
        self.redo_commits = set()   # commits that deleted a proof-side file
        self.redo_files = 0         # files deleted by them
        self.proof_commits = 0
        self.spec_commits = 0
        self.notes = []

    @property
    def spec_start(self):
        cands = [t for t in (self.spec_first, self.notes_first) if t]
        return min(cands) if cands else None

    @property
    def proven(self):
        """When the cone actually closed.

        A Link<F>.v file can be created while F is still ASSUMED -- LinkIput.v
        was born on 2026-08-06 in the commit titled "... and iput assumed",
        four days before ProofIput.v existed.  So a unit counts as proven only
        once BOTH its Link file and a real proof file exist.
        """
        if self.link_first is None:
            return None
        if self.proof_first is None:
            return self.link_first
        return max(self.link_first, self.proof_first)

    @property
    def assumed_first(self):
        return (self.link_first is not None and self.proof_first is not None
                and self.link_first < self.proof_first)

    @property
    def landed(self):
        return self.proven or self.proof_first

    @property
    def elapsed(self):
        if self.spec_start and self.proven:
            return (self.proven - self.spec_start) / 86400.0
        return None

    @property
    def notes_lead(self):
        """Days by which design notes preceded the first spec file."""
        if self.notes_first and self.spec_first and self.notes_first < self.spec_first:
            return (self.spec_first - self.notes_first) / 86400.0
        return None


def analyze(args):
    units, merged, lookup = build_units()
    unit_set = set(units)
    commits, _canon = read_history()
    rows = {u: Row(u) for u in units}
    for u, parent in merged.items():
        rows[parent].notes.append(f'+{u}')

    # current sizes
    for r in rows.values():
        r.proof_lines = r.spec_lines = 0
    shared_with = collections.defaultdict(set)
    for fn in sorted(os.listdir(os.path.join(ROOT, 'iris'))):
        us, role = attribute('iris/' + fn, lookup, merged, unit_set)
        if not us or role not in ('spec', 'proof'):
            continue
        if len(us) > 1:
            for u in us:
                shared_with[u].update(x for x in us if x != u)
        try:
            n = sum(1 for _ in open(os.path.join(ROOT, 'iris', fn),
                                    encoding='utf-8', errors='replace'))
        except OSError:
            n = 0
        for u in us:
            if role == 'proof':
                rows[u].proof_lines += n
            else:
                rows[u].spec_lines += n

    for c in commits:                       # newest -> oldest
        sweep = c.iris_files > args.sweep_min
        hit_spec, hit_proof = set(), set()
        for path, (a, d) in c.stats.items():
            us, role = attribute(path, lookup, merged, unit_set)
            for u in us:
                r = rows[u]
                if role == 'spec':
                    r.spec_churn_all += a + d
                    if not sweep:
                        r.spec_churn += a + d
                    hit_spec.add(u)
                elif role == 'proof':
                    r.proof_churn_all += a + d
                    if sweep:
                        r.sweep_churn += a + d
                    else:
                        r.proof_churn += a + d
                    hit_proof.add(u)
                elif role == 'code':
                    r.code_churn += a + d
        for path, st in c.status.items():
            us, role = attribute(path, lookup, merged, unit_set)
            for u in us:
                r = rows[u]
                if role == 'spec':
                    hit_spec.add(u)
                    if st == 'A':
                        r.spec_first = c.ts if r.spec_first is None else min(r.spec_first, c.ts)
                elif role == 'proof':
                    hit_proof.add(u)
                    if st == 'A':
                        r.proof_first = c.ts if r.proof_first is None else min(r.proof_first, c.ts)
                    elif st == 'D':
                        r.redo_commits.add(c.sha)
                        r.redo_files += 1
                elif role == 'link' and st == 'A':
                    r.link_first = c.ts if r.link_first is None else min(r.link_first, c.ts)
        # Author-days are only counted for NON-SWEEP commits: a tree-wide
        # restyle that happened to rewrite ProofCpuid.v is not a day of work
        # on cpuid.  (Without this filter every leaf function inherits ~15
        # phantom author-days from the sweeps -- see the module docstring.)
        for u in hit_spec:
            rows[u].spec_days_all.add((c.author, c.day))
            rows[u].spec_commits += 1
            if not sweep:
                rows[u].spec_days.add((c.author, c.day))
        for u in hit_proof:
            rows[u].proof_days_all.add((c.author, c.day))
            rows[u].proof_commits += 1
            if not sweep:
                rows[u].proof_days.add((c.author, c.day))

    # second sweep: classify commits now that first-add / landed times are known
    for c in commits:
        focused = c.iris_files <= args.focused_max
        sweep = c.iris_files > args.sweep_min
        touched = set(c.stats) | set(c.status)
        us, up = set(), set()
        for path in touched:
            hits, role = attribute(path, lookup, merged, unit_set)
            if role == 'spec':
                us.update(hits)
            elif role == 'proof':
                up.update(hits)
        for u in up:
            r = rows[u]
            if sweep:
                r.sweeps += 1
            elif focused:
                if r.proof_first is not None and c.ts > r.proof_first:
                    r.focused_rework += 1
            else:
                r.mid += 1
        for u in us:
            r = rows[u]
            if focused and r.landed is not None and c.ts > r.landed:
                r.instability += 1
                for path, (a, d) in c.stats.items():
                    hits, role = attribute(path, lookup, merged, unit_set)
                    if role == 'spec' and u in hits:
                        r.instab_churn += a + d

    notes_first = notes_first_mention(units, args.notes_threshold)
    for u, ts in notes_first.items():
        if u in rows:
            rows[u].notes_first = ts

    # How much of the iris/ churn the naming convention actually captures.
    # Everything else is shared infrastructure and bespoke per-function helper
    # libraries (PathElems.v, InodeRegion.v, DirentEnc.v ...) that no unit can
    # claim -- the tool's principal blind spot, so it reports its own size.
    attributed = unattributed = 0
    for c in commits:
        for path, (a, d) in c.stats.items():
            if not (path.startswith('iris/') and path.endswith('.v')):
                continue
            hits, _ = attribute(path, lookup, merged, unit_set)
            if hits:
                attributed += a + d
            else:
                unattributed += a + d
    analyze.coverage = (attributed, unattributed, len(units), len(merged))

    fanin = proof_fanin(units)
    for u, r in rows.items():
        if u in HOMONYMS and r.notes_first and r.spec_first and r.notes_first < r.spec_first:
            r.notes.append('homonym?')
        if r.proven is None:
            r.notes.append('unlinked')
        if r.assumed_first:
            r.notes.append('assumed first')
        if shared_with.get(u):
            r.notes.append('shares files with ' +
                           ','.join(sorted(x.lower() for x in shared_with[u])))
        if r.redo_commits:
            n, f = len(r.redo_commits), r.redo_files
            r.notes.append(f'{n} redo' + (f'/{f} files' if f > n else ''))
        f = fanin.get(u, set())
        if len(f) >= 2:
            r.notes.append('reused by ' + ','.join(sorted(x.lower() for x in f)[:3]))
    return list(rows.values())


# ----------------------------------------------------------------- output ---

METRICS = {
    'focused': ('focused_rework', 'focused rework commits on the proof'),
    'churn': ('proof_churn_all', 'lines added+deleted in proof files, all commits'),
    'churn-nosweep': ('proof_churn', 'lines added+deleted in proof files, sweeps excluded'),
    'sweep-churn': ('sweep_churn', 'proof lines rewritten by mechanical sweeps'),
    'proof-days': ('proof_days_n', 'distinct author-days on proof files, sweeps excluded'),
    'proof-size': ('proof_lines', 'current proof size (lines)'),
    'instability': ('instability', 'focused spec edits after the proof landed'),
    'instab-churn': ('instab_churn', 'spec lines moved after the proof landed'),
    'spec-days': ('spec_days_n', 'distinct author-days on spec files, sweeps excluded'),
    'spec-churn': ('spec_churn', 'lines added+deleted in spec files, sweeps excluded'),
    'spec-size': ('spec_lines', 'current spec size (lines)'),
    'elapsed': ('elapsed', 'calendar days from spec start to Link'),
    'redos': ('redos', 'commits that deleted a proof file (rewritten from scratch)'),
    'sweeps': ('sweeps', 'mechanical sweep commits that swept the proof'),
    'hard-proof': ('proof_score', 'rank-sum of focused rework, churn, author-days, size'),
    'hard-spec': ('spec_score', 'rank-sum of instability, spec author-days, spec churn'),
}

# Rank-sum composites.  Each component is turned into a percentile (1.0 = the
# hardest unit on that component) and averaged, so no single component with a
# fat tail (churn) can dominate.  Composites are a convenience for "which was
# hardest overall"; the individual columns are the evidence.
PROOF_SCORE = ['focused_rework', 'proof_churn', 'proof_days_n', 'proof_lines']
SPEC_SCORE = ['instability', 'instab_churn', 'spec_days_n', 'spec_churn',
              'spec_lines']


def decorate(rows):
    for r in rows:
        r.proof_days_n = len(r.proof_days)
        r.spec_days_n = len(r.spec_days)
        r.proof_days_all_n = len(r.proof_days_all)
        r.redos = len(r.redo_commits)
        r.spec_days_all_n = len(r.spec_days_all)
    n = max(1, len(rows) - 1)
    for attr, out in (('proof_score', PROOF_SCORE), ('spec_score', SPEC_SCORE)):
        pct = {r.unit: 0.0 for r in rows}
        for comp in out:
            order = sorted(rows, key=lambda r: getattr(r, comp))
            for i, r in enumerate(order):
                pct[r.unit] += i / n
        for r in rows:
            setattr(r, attr, round(100.0 * pct[r.unit] / len(out), 1))
    return rows


def day(ts):
    return datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d') if ts else '-'


COLS = [
    ('function', lambda r: r.unit, '<20'),
    ('spec_start', lambda r: day(r.spec_start), '>10'),
    ('proven', lambda r: day(r.proven), '>10'),
    ('elapsed', lambda r: f'{r.elapsed:.0f}' if r.elapsed is not None else '-', '>7'),
    ('spec_days', lambda r: r.spec_days_n, '>9'),
    ('proof_days', lambda r: r.proof_days_n, '>10'),
    ('focused', lambda r: r.focused_rework, '>7'),
    ('sweeps', lambda r: r.sweeps, '>6'),
    ('instab', lambda r: r.instability, '>6'),
    ('churn_work', lambda r: r.proof_churn, '>10'),
    ('churn_all', lambda r: r.proof_churn_all, '>9'),
    ('proof_lines', lambda r: r.proof_lines, '>11'),
    ('spec_churn', lambda r: r.spec_churn, '>10'),
    ('notes', lambda r: '; '.join(r.notes), '<40'),
]


def render_table(rows, cols=COLS, md=False):
    out = []
    if md:
        out.append('| ' + ' | '.join(c[0] for c in cols) + ' |')
        out.append('|' + '|'.join('---' for _ in cols) + '|')
        for r in rows:
            out.append('| ' + ' | '.join(str(c[1](r)) for c in cols) + ' |')
    else:
        out.append(' '.join(f'{c[0]:{c[2]}}' for c in cols))
        for r in rows:
            out.append(' '.join(f'{str(c[1](r)):{c[2]}}' for c in cols))
    return '\n'.join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--sort', default='focused', choices=sorted(METRICS),
                    help='ranking metric (default: focused)')
    ap.add_argument('--top', type=int, default=15, help='rows to print (0 = all)')
    ap.add_argument('--md', action='store_true', help='markdown table output')
    ap.add_argument('--tsv', action='store_true', help='full TSV dump of every column')
    ap.add_argument('--focused-max', type=int, default=5,
                    help='<= this many iris files in a commit = focused work')
    ap.add_argument('--sweep-min', type=int, default=20,
                    help='> this many iris files in a commit = mechanical sweep')
    ap.add_argument('--notes-threshold', type=int, default=3,
                    help='mentions in one notes commit to count as design work')
    ap.add_argument('--only', help='comma-separated unit names to show')
    ap.add_argument('--coverage', action='store_true',
                    help='report how much of iris/ churn the units capture')
    args = ap.parse_args()

    rows = decorate(analyze(args))
    if args.only:
        want = {w.strip().lower() for w in args.only.split(',')}
        rows = [r for r in rows if r.unit.lower() in want]

    key = METRICS[args.sort][0]
    rows.sort(key=lambda r: (getattr(r, key) is None,
                             -(getattr(r, key) or 0), r.unit))

    if args.tsv:
        hdr = ['unit', 'spec_first', 'notes_first', 'spec_start', 'proof_first',
               'proven', 'elapsed', 'spec_days', 'proof_days', 'spec_days_all',
               'proof_days_all', 'focused_rework', 'sweeps', 'mid',
               'instability', 'instab_churn', 'notes_lead', 'redos', 'redo_files',
               'proof_churn', 'proof_churn_all', 'sweep_churn', 'proof_lines',
               'spec_churn', 'spec_lines', 'code_churn', 'proof_score',
               'spec_score', 'notes']
        print('\t'.join(hdr))
        for r in rows:
            print('\t'.join(str(x) for x in [
                r.unit, day(r.spec_first), day(r.notes_first), day(r.spec_start),
                day(r.proof_first), day(r.proven),
                f'{r.elapsed:.1f}' if r.elapsed is not None else '-',
                r.spec_days_n, r.proof_days_n, r.spec_days_all_n,
                r.proof_days_all_n, r.focused_rework, r.sweeps, r.mid,
                r.instability, r.instab_churn,
                f'{r.notes_lead:.0f}' if r.notes_lead is not None else '-',
                len(r.redo_commits), r.redo_files, r.proof_churn, r.proof_churn_all,
                r.sweep_churn, r.proof_lines, r.spec_churn, r.spec_lines,
                r.code_churn, r.proof_score, r.spec_score,
                '; '.join(r.notes)]))
        return

    shown = rows if args.top == 0 else rows[:args.top]
    print(f'# ranked by {args.sort}: {METRICS[args.sort][1]}\n')
    print(render_table(shown, md=args.md))

    if args.coverage:
        att, unatt, nunits, nmerged = analyze.coverage
        tot = att + unatt or 1
        print(f'\n# {nunits} units ({nmerged} auxiliary spec files merged in). '
              f'Spec/Proof/Link/Budget naming captures {att} of {tot} lines of '
              f'iris/*.v churn ({100.0*att/tot:.0f}%); the remaining '
              f'{100.0*unatt/tot:.0f}% is shared infrastructure and bespoke '
              f'per-function helper libraries, and is credited to nobody.')


if __name__ == '__main__':
    main()
