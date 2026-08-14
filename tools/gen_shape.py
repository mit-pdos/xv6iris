#!/usr/bin/env python3
"""gen_shape.py -- GENERATE the per-function SHAPE lemmas over the Sail model.

Stage C3 of [claude-notes/projects/weak-memory-premises.md].  Emits, from
model-xv6iris/rv64d.v alone, one lemma per monadic definition reachable from
[try_step]:

    Lemma gw_<f> : forall a0 .. an, gwalk None (@<f> a0 .. an).
    Proof. intros; cbv [<f>]; gw_solve. Qed.
    #[export] Hint Resolve gw_<f> : gshape.

in DEPENDENCY (topological) order, sharded across iris/WeakShapeGen*.v.  THE
HINT DATABASE IS THE DEPENDENCY MECHANISM: [gw_solve] closes a leaf
[gwalk None (g x y)] out of `gshape`, so emitting in topological order is all the
ordering that is needed, and each shard Requires the previous one.

  Regenerate with:   make gen-shape          (from the repo root)

A HAND-PATCHED SHARD IS SILENTLY REVERTED BY THE NEXT REGENERATION -- the
gen_code.py footgun, recorded in claude-notes/durable-notes.md.  Anything that
needs a hand proof belongs in iris/WeakShapeOverrides.v (the kit + the
hand-written sites) or in the SKIP set below, never in a shard.

WHAT IS *NOT* GENERATED, and why (the "override list"):

  * the two memory leaves [read_ram] / [write_ram] -- WeakShape.v §6 proves
    them, keyed on the read_kind/write_kind argument, because their shape
    DEPENDS on that argument (plain vs. exclusive);
  * everything in their up-cone (the 53 monadic functions from
    [checked_mem_read]/[checked_mem_write] up to [try_step]) -- those carry
    the semantic side conditions (0 < split_width, the misaligned loop's
    termination, the exclusive window) and, since stage C3's finding (O4),
    are where [sail_shaped] is FALSE;
  * the three OPAQUE MONADIC AXIOMS [load_reservation], [cancel_reservation],
    [plat_term_write] and their up-cone -- nothing about an axiom's shape is
    provable;
  * the three fuel [Fixpoint]s ([_rec_pt_walk], [_rec_hartSupports],
    [_rec_check_stateen_bit]) -- they need induction on the fuel, not [cbv];

The call graph is an identifier-occurrence closure with comments, string
literals and locally-bound names removed (without the last filter it reports
spurious cycles: Sail names local lets after global definitions).  It is
deliberately CONSERVATIVE upward -- an extra edge only moves a function out of
the generated set, it never produces an unsound lemma.
"""

import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MODEL = os.path.join(ROOT, 'model-xv6iris', 'rv64d.v')
OUTDIR = os.path.join(ROOT, 'iris')

ROOTFN = 'try_step'

# Leaves whose up-cone is excluded from the generated sweep (see the header).
IMPURE_LEAVES = [
    'read_ram', 'write_ram',                       # the memory leaves
    'load_reservation', 'cancel_reservation',      # opaque monadic axioms
    'plat_term_write',
]
# Textual markers that would make a definition unshaped; propagated up the
# call graph like the leaves.  There are NONE: [gwalk None] -- the sweep's
# predicate -- constrains only the two MEMORY nodes.  A Barrier, a [throw]
# (an ExtraOutcome with an empty continuation), an [exit]/[internal_error] and
# every [Choose] are all walkable, which is why the generated fragment is as
# large as it is.  The list is kept so the next model can name one.
IMPURE_TOKENS = []

# Never generated, whatever the call graph says -- AND NEITHER IS ANYTHING
# THAT CALLS THEM (the up-cone is removed too, exactly like the memory
# leaves').  This is the escape hatch for a function [gw_solve] cannot do:
# put its name here, regenerate, and the build stays green with the coverage
# number in `make gen-shape`'s report dropping to match.  Each entry is a
# recorded residue, not a silent omission.
SKIP = {
    # [check_leaf_pte] is generatable (its cone touches no memory leaf), but
    # it sits between [_rec_pt_walk] and the page-table cone, i.e. inside the
    # residue's own call chain, and it is proved BY HAND in
    # iris/WeakShapeOverrides2.v alongside [_rec_pt_walk] itself -- so it is
    # skipped here rather than emitted into a shard.  Removing this entry
    # renumbers the whole topological order and rebuilds all seven shards.
    'check_leaf_pte',
}

# HAND-WRITTEN PROOF OVERRIDES, kept HERE (not in a shard) so that a
# regeneration cannot revert them, and emitted at the group's TOPOLOGICAL
# position so the hint database still works as the dependency mechanism.
#
# The model's fuel recursions are the only functions [cbv]+[gw_solve] cannot
# do on its own: they need a [fix] on the [Acc] argument.  [_rec_pt_walk] is
# not here because it is in the memory cone (not generated at all).
STATEEN_GROUP = [
    '_rec_check_stateen_bit', '_rec_currentlyEnabled', '_rec_get_hstateen',
    '_rec_get_sstateen', '_rec_get_xLPE', '_rec_is_hstateen_accessible',
    '_rec_is_sstateen_accessible', '_rec_is_zfinx_enabled_by_stateen',
    '_rec_virtual_memory_supported',
]

# key -> (members, emitted text).  A key stands for the whole set of members
# in the call graph: edges into any member become edges into the key.
OVERRIDE_PROOFS = {
    '_rec_hartSupports': (['_rec_hartSupports'], """
(* FUEL RECURSION: [fix] on the [Acc] argument, not [cbv]. *)
Lemma gw__rec_hartSupports : forall a0 a1 a2, gwalk None (@_rec_hartSupports a0 a1 a2).
Proof.
  fix IH 3. intros a0 a1 a2. destruct a2 as [a2].
  cbv [_rec_hartSupports]. gw_solve.
Qed.
#[export] Hint Resolve gw__rec_hartSupports : gshape.
"""),
    '_rec_stateen_group': (STATEEN_GROUP, """
(* THE 9-WAY MUTUAL FUEL RECURSION.  One [fix] on the SHARED [Acc] argument
   proves all nine at once; the [K]s are the per-member instances of the
   induction hypothesis at the accessibility subterms, which is what
   [gw_solve]'s [eauto] needs (it cannot project a conjunction). *)
Lemma gw__rec_stateen_group :
  forall l acc,
    (forall p b s, gwalk None (_rec_check_stateen_bit p b s l acc)) /\\
    (forall e, gwalk None (_rec_currentlyEnabled e l acc)) /\\
    (forall i, gwalk None (_rec_get_hstateen i l acc)) /\\
    (forall i, gwalk None (_rec_get_sstateen i l acc)) /\\
    (forall p, gwalk None (_rec_get_xLPE p l acc)) /\\
    (forall u, gwalk None (_rec_is_hstateen_accessible u l acc)) /\\
    (forall u, gwalk None (_rec_is_sstateen_accessible u l acc)) /\\
    (forall u, gwalk None (_rec_is_zfinx_enabled_by_stateen u l acc)) /\\
    (forall u, gwalk None (_rec_virtual_memory_supported u l acc)).
Proof.
  fix IH 2. intros l acc. destruct acc as [acc].
  assert (K1 : forall y H p b s, gwalk None (_rec_check_stateen_bit p b s y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K2 : forall y H e, gwalk None (_rec_currentlyEnabled e y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K3 : forall y H i, gwalk None (_rec_get_hstateen i y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K4 : forall y H i, gwalk None (_rec_get_sstateen i y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K5 : forall y H p, gwalk None (_rec_get_xLPE p y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K6 : forall y H u, gwalk None (_rec_is_hstateen_accessible u y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K7 : forall y H u, gwalk None (_rec_is_sstateen_accessible u y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K8 : forall y H u, gwalk None (_rec_is_zfinx_enabled_by_stateen u y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  assert (K9 : forall y H u, gwalk None (_rec_virtual_memory_supported u y (acc y H)))
    by (intros y H; apply (IH y (acc y H))).
  clear IH.
  repeat apply conj.
  - intros p b s. cbv [_rec_check_stateen_bit]. gw_solve.
  - intros e. cbv [_rec_currentlyEnabled]. gw_solve.
  - intros i. cbv [_rec_get_hstateen]. gw_solve.
  - intros i. cbv [_rec_get_sstateen]. gw_solve.
  - intros p. cbv [_rec_get_xLPE]. gw_solve.
  - intros u. cbv [_rec_is_hstateen_accessible]. gw_solve.
  - intros u. cbv [_rec_is_sstateen_accessible]. gw_solve.
  - intros u. cbv [_rec_is_zfinx_enabled_by_stateen]. gw_solve.
  - intros u. cbv [_rec_virtual_memory_supported]. gw_solve.
Qed.

Lemma gw__rec_check_stateen_bit : forall p b s l acc,
  gwalk None (_rec_check_stateen_bit p b s l acc).
Proof. intros; apply gw__rec_stateen_group. Qed.
Lemma gw__rec_currentlyEnabled : forall e l acc,
  gwalk None (_rec_currentlyEnabled e l acc).
Proof. intros; apply gw__rec_stateen_group. Qed.
Lemma gw__rec_get_hstateen : forall i l acc,
  gwalk None (_rec_get_hstateen i l acc).
Proof. intros; apply gw__rec_stateen_group. Qed.
Lemma gw__rec_get_sstateen : forall i l acc,
  gwalk None (_rec_get_sstateen i l acc).
Proof. intros; apply gw__rec_stateen_group. Qed.
Lemma gw__rec_get_xLPE : forall p l acc,
  gwalk None (_rec_get_xLPE p l acc).
Proof. intros; apply gw__rec_stateen_group. Qed.
Lemma gw__rec_is_hstateen_accessible : forall u l acc,
  gwalk None (_rec_is_hstateen_accessible u l acc).
Proof. intros; apply gw__rec_stateen_group. Qed.
Lemma gw__rec_is_sstateen_accessible : forall u l acc,
  gwalk None (_rec_is_sstateen_accessible u l acc).
Proof. intros; apply gw__rec_stateen_group. Qed.
Lemma gw__rec_is_zfinx_enabled_by_stateen : forall u l acc,
  gwalk None (_rec_is_zfinx_enabled_by_stateen u l acc).
Proof. intros; apply gw__rec_stateen_group. Qed.
Lemma gw__rec_virtual_memory_supported : forall u l acc,
  gwalk None (_rec_virtual_memory_supported u l acc).
Proof. intros; apply gw__rec_stateen_group. Qed.
#[export] Hint Resolve
  gw__rec_check_stateen_bit gw__rec_currentlyEnabled gw__rec_get_hstateen
  gw__rec_get_sstateen gw__rec_get_xLPE gw__rec_is_hstateen_accessible
  gw__rec_is_sstateen_accessible gw__rec_is_zfinx_enabled_by_stateen
  gw__rec_virtual_memory_supported : gshape.
"""),
}

HEADER = """(* %(file)s -- AUTO-GENERATED by tools/gen_shape.py.  DO NOT EDIT BY HAND.

   Stage C3's per-function shape sweep over [Riscv.rv64d]: one
   [gwalk None (<f> args)] lemma per monadic definition reachable from
   [try_step] whose cone touches neither of the two memory leaves nor one of
   the model's three opaque monadic axioms.  [gwalk None] is
   [WeakSailLTS.sail_shaped] generalised to an arbitrary monad type
   ([WeakShape.gwalk_shaped]).

   Emitted in topological order; the `gshape` hint database is the
   dependency mechanism.  Shard %(idx)d.

   Regenerate with:  make gen-shape                                       *)
%(requires)s
Set Default Proof Using "Type".
"""


def strip_comments_and_strings(s):
    out = []
    i = 0
    depth = 0
    instr = False
    while i < len(s):
        if not instr and s.startswith('(*', i):
            depth += 1
            i += 2
            continue
        if not instr and s.startswith('*)', i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            if s[i] == '"':
                instr = not instr
                out.append(' ')
                i += 1
                continue
            out.append(' ' if instr else s[i])
        i += 1
    return ''.join(out)


DEFPAT = re.compile(r"(?m)^(Definition|Fixpoint|Axiom|with)\s+([A-Za-z_][A-Za-z0-9_']*)")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def parse_model(path):
    """-> (kind, span) per top-level name, over the comment/string-free text."""
    clean = strip_comments_and_strings(open(path).read())
    ms = list(DEFPAT.finditer(clean))
    out = {}
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(clean)
        out[m.group(2)] = (m.group(1), clean[m.end():end])
    return out


def local_names(body):
    """Names bound INSIDE a definition -- subtracted from its call set, or the
    graph acquires spurious cycles (Sail names local lets after globals)."""
    loc = set()
    loc |= set(re.findall(r"\(\s*([A-Za-z_][A-Za-z0-9_']*)\s*:", body))
    loc |= set(re.findall(r"let\s+'?\(?\s*([A-Za-z_][A-Za-z0-9_']*)", body))
    loc |= set(re.findall(r"fun\s+'?\(?\s*([A-Za-z_][A-Za-z0-9_']*)", body))
    for t in re.findall(r"'\(\(?([^)]*)\)", body):
        loc |= set(IDENT.findall(t))
    return loc


def binder_region(body):
    """The binder text of a definition: everything up to the depth-0 ':'."""
    depth = 0
    for i, c in enumerate(body):
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif c == ':' and depth == 0:
            return body[:i]
    return None


def binder_groups(b):
    """Split a binder region into groups.  Sail emits one name per group; a
    group is `(x : T)`, `{x : T}`, `'(pat)` or a bare name."""
    gs = []
    i = 0
    while i < len(b):
        c = b[i]
        if c.isspace():
            i += 1
            continue
        if c in "'({":
            start = i
            if c == "'":
                i += 1
            depth = 0
            while i < len(b):
                if b[i] in '({':
                    depth += 1
                elif b[i] in ')}':
                    depth -= 1
                    if depth == 0:
                        i += 1
                        break
                i += 1
            gs.append(b[start:i])
        else:
            j = i
            while j < len(b) and not b[j].isspace():
                j += 1
            gs.append(b[i:j])
            i = j
    return gs


def is_monadic(body):
    # THE RETURN TYPE MAY START A LINE.  Sail wraps a long signature so that
    # the `: M (...)` lands at column 0 on its own line; a bare ' M (' test
    # then MISSES the definition entirely -- it is neither generated nor
    # reported as residue, and the hole only shows up as a stuck leaf in a
    # hand proof of one of its callers (found in C5 at [check_leaf_pte]).
    # Normalising the whitespace is what makes the test line-shape-agnostic.
    head = ' ' + ' '.join(body.split(':=')[0].split())
    return ' M (' in head or ' MR (' in head or 'monad' in head or ': M ' in head


def build(model):
    calls = {}
    for n, (_kind, body) in model.items():
        ids = set(IDENT.findall(body)) - {n} - local_names(body)
        calls[n] = ids & set(model)
    # reachability from the root
    seen = set()
    stack = [ROOTFN]
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        stack.extend(calls[x])
    return calls, seen


def up_cone(calls, reach, targets):
    """Everything in [reach] that can reach one of [targets]."""
    rev = {}
    for k, vs in calls.items():
        for v in vs:
            rev.setdefault(v, set()).add(k)
    seen = set()
    stack = list(targets)
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        stack.extend(rev.get(x, ()))
    return seen & reach


def toposort(calls, nodes):
    """Dependencies first.  Iterative DFS; the graph is acyclic once local
    names are filtered out (asserted here, since a cycle would silently
    produce a shard whose lemmas cannot be proven in order)."""
    order = []
    state = {}
    for root in sorted(nodes):
        if state.get(root):
            continue
        stack = [(root, iter(sorted(calls[root] & nodes)))]
        state[root] = 1
        while stack:
            node, it = stack[-1]
            advanced = False
            for w in it:
                if state.get(w) == 1:
                    raise SystemExit('gen_shape: cycle through %s -> %s' % (node, w))
                if not state.get(w):
                    state[w] = 1
                    stack.append((w, iter(sorted(calls[w] & nodes))))
                    advanced = True
                    break
            if advanced:
                continue
            state[node] = 2
            order.append(node)
            stack.pop()
    return order


def split_shards(names, sizes):
    """Cut [names] into shards of the given sizes; the LAST size repeats.

    NOT a single uniform size, and the reason is the measured cost curve: a
    48-lemma shard near the bottom of the topological order costs ~7 minutes
    of `coqc`, the same size in the CSR/legalize band costs an HOUR, and a
    shard that is killed (build timeout, machine restart) loses ALL of its
    work because there is no partial `.vo`.  Small shards high up the order
    are how partial progress survives -- and the chain is serial, so nothing
    is lost by having more of them.  Keep the early sizes fixed when raising
    coverage: changing them rewrites shards that are already built."""
    out = []
    i = 0
    k = 0
    while i < len(names):
        n = sizes[min(k, len(sizes) - 1)]
        out.append(names[i:i + n])
        i += n
        k += 1
    return out


def emit(names, model, outdir, shard_sizes, dry_run=False):
    shards = split_shards(names, shard_sizes)
    written = []
    for idx, shard in enumerate(shards, start=1):
        fname = 'WeakShapeGen%02d.v' % idx
        reqs = ['From xv6iris Require Import WeakShape WeakShapeOverrides.']
        if idx > 1:
            # EVERY previous shard, not just the last one: the hints are
            # [#[export]], so they are activated by IMPORT and are NOT
            # re-exported transitively.  Requiring only shard n-1 silently
            # loses shard 1's hints at shard 3, and the symptom is a lemma
            # that fails on a callee proved two shards earlier.
            reqs.append('From xv6iris Require Import %s.'
                        % ' '.join('WeakShapeGen%02d' % j
                                   for j in range(1, idx)))
        reqs.append('Require Import Riscv.rv64d.')
        body = [HEADER % {'file': fname, 'idx': idx,
                          'requires': '\n'.join(reqs)}]
        for n in shard:
            if n in OVERRIDE_PROOFS:
                body.append(OVERRIDE_PROOFS[n][1])
                continue
            gs = binder_groups(binder_region(model[n][1]))
            arity = len(gs)
            args = ' '.join('a%d' % i for i in range(arity))
            if arity:
                stmt = 'forall %s, gwalk None (@%s %s)' % (args, n, args)
            else:
                stmt = 'gwalk None %s' % n
            # A PATTERN binder ('(...)) elaborates to a match, and with more
            # than one of them the body is a match APPLIED to the remaining
            # arguments -- which no [gwalk _ (match _ with _ end)] tactic rule
            # sees.  Destructing them up front is what the C1 calibration did
            # by hand ([destruct r. cbv [rX].]); here it comes off the binder
            # region, so it is never guessed.
            pats = ['a%d' % i for i, g in enumerate(gs) if g.startswith("'")]
            pre = ('destruct %s; ' % ', '.join(pats)) if pats else ''
            body.append('')
            body.append('Lemma gw_%s : %s.' % (n, stmt))
            body.append('Proof. intros; %scbv [%s]; gw_solve. Qed.' % (pre, n))
            body.append('#[export] Hint Resolve gw_%s : gshape.' % n)
        body.append('')
        text = '\n'.join(body)
        path = os.path.join(outdir, fname)
        # IDEMPOTENT ON DISK: only rewrite a shard whose text actually
        # changed, so that a `make gen-shape` on an unchanged model does not
        # touch mtimes and does not cost a ~10-minute recompile per shard.
        if not dry_run:
            old = None
            if os.path.exists(path):
                with open(path) as f:
                    old = f.read()
            if old != text:
                with open(path, 'w') as f:
                    f.write(text)
        written.append((fname, len(shard)))
    # STALE SHARDS ARE DELETED, not left behind: a re-shard (or a lowered
    # --limit) otherwise leaves a WeakShapeGen<nn>.v on disk that no longer
    # belongs to the sweep, and the next `make check-shape` cannot see the
    # difference between that and a hand-written file.
    if not dry_run:
        idx = len(shards)
        while True:
            idx += 1
            stale = os.path.join(outdir, 'WeakShapeGen%02d.v' % idx)
            if not os.path.exists(stale):
                break
            os.remove(stale)
    return written


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--model', default=MODEL)
    ap.add_argument('--outdir', default=OUTDIR)
    ap.add_argument('--shard-sizes', default='48,48,16',
                    help='comma-separated shard sizes; the LAST one repeats')
    # COMPILE-TIME BUDGET, not a correctness knob.  The topological order puts
    # dependencies first, so ANY PREFIX of it is self-contained: emitting the
    # first N is a smaller but complete sweep.  Measured on this tree, a
    # 48-lemma shard costs ~10 min of `coqc` (the extension-enum dispatches
    # dominate) and the cost grows up the order, so the whole 294 is a
    # multi-hour serial chain -- the shards form a Require chain and cannot be
    # built in parallel.  Raise this and regenerate when there is a build
    # budget for it; the functions beyond the cut are listed by --report.
    ap.add_argument('--limit', type=int, default=0,
                    help='emit only the first N of the topological order '
                         '(0 = the whole sweep)')
    ap.add_argument('--dry-run', action='store_true')
    ap.add_argument('--report', action='store_true')
    args = ap.parse_args()

    model = parse_model(args.model)
    calls, reach = build(model)

    # CONTRACT each hand-proved group to its key, so that the topological
    # order places the whole group at one point and the members' callers see
    # a single dependency.
    alias = {}
    for key, (members, _text) in OVERRIDE_PROOFS.items():
        for m in members:
            alias[m] = key
    def rn(x):
        return alias.get(x, x)
    ccalls = {}
    for n, vs in calls.items():
        ccalls.setdefault(rn(n), set()).update({rn(v) for v in vs} - {rn(n)})
    creach = {rn(x) for x in reach}
    mon = {rn(n) for n in reach if is_monadic(model[n][1])}

    impure = up_cone(ccalls, creach, [rn(x) for x in IMPURE_LEAVES])
    if IMPURE_TOKENS:
        tok = {rn(n) for n in reach
               if any(re.search(r'\b%s\b' % t, model[n][1]) for t in IMPURE_TOKENS)}
        impure |= up_cone(ccalls, creach, tok)

    impure |= up_cone(ccalls, creach, [rn(x) for x in SKIP if rn(x) in ccalls])
    gen = set(mon) - impure - SKIP
    order = [n for n in toposort(ccalls, gen) if n in gen]
    full = order
    if args.limit and args.limit < len(order):
        order = order[:args.limit]

    if args.report:
        print('reachable from %s: %d (monadic %d)' % (ROOTFN, len(creach), len(mon)))
        print('impure cone (memory leaves / opaque monadic axioms): %d monadic'
              % len(impure & mon))
        print('generatable: %d   emitted: %d (--limit) (%d hand-proved groups)'
              % (len(full), len(order),
                 len([n for n in order if n in OVERRIDE_PROOFS])))
        print('below the --limit cut, i.e. generatable but not emitted: %s'
              % ' '.join(sorted(set(full) - set(order))))
        print('residue (monadic, not generatable at all): %s'
              % ' '.join(sorted(mon - set(full))))

    sizes = [int(x) for x in args.shard_sizes.split(',')]
    written = emit(order, model, args.outdir, sizes, args.dry_run)
    for fname, n in written:
        print('%s  %d lemmas' % (fname, n))


if __name__ == '__main__':
    main()
