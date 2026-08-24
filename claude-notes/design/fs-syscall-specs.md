# fs-syscall-specs — directory-based specs for the fs syscalls, one history, two boundaries

STATUS: EXPLORATION, v2 (2026-08-24, Fable + owner).  A proposal, not a
design of record.  v1 (same day) presented each syscall's spec as "the
same delta read twice" — once at the logged view, once at the durable
view — with per-op durable tokens.  The owner asked for a design that
LIFTS the two-view burden off the spec's CONSUMER: no reasoning about
two states, no possibility of the two drifting apart.  v2 is that
design; the two-view machinery survives only INSIDE the framework, as
the proof obligation, never in a consumer-visible statement.

Prompted by the owner: once the durable-disk spike lands, we want specs
for the individual file system calls covering BOTH the in-memory and the
durable aspect, stated over a DIRECTORY-based abstraction (a set/map of
nodes with entry maps), NOT a file-system tree; specialized tree
specifications for a single user program come later, LAYERED on this.
External input: Lampson's 6.826 spec notes (`fs-butler-specs.pdf`) —
the history-based crash spec, directories as a graph of links, lookup
against the union of states it might see.  The consumer-facing shape of
v2 additionally matches DFSCQ's tree-sequence idea (crash = a recent
past state), specialized by the WAL's batch atomicity.

Related: [`fs-state.md`](fs-state.md) (design of record for the
two-view ghost state this layer rests on), [`fs-fragments.md`](fs-fragments.md)
(§1.1 inum-keyed store, §1.4 custody theorem),
[`fs-friendly.md`](fs-friendly.md) (the 2026-08-15 direction sketch),
`projects/namei-pinned-lookup.md` (the `dview` carrier and the
ghost-trace lookup spec), `projects/durable-disk.md` stage 3 (the mknod
spike whose end theorem is this layer's adequacy instance).

## 0. The one-sentence design

**There is ONE abstract state and one delta log; syscall specs are
logically-atomic deltas on the current state and say NOTHING about
durability; durability is three global principles a consumer applies
only at crash points — and because the durable view is DEFINED as a
prefix of the same delta log, there is no second state to drift.**

The three principles (stated precisely in §5):

1. **SNAPSHOT.**  Recovery yields a PAST current state — the state
   exactly as it was at some batch boundary.  Corollary, and the whole
   point: any property a consumer maintained continuously on the current
   view holds after recovery, with no crash-specific proof.
2. **BOUND.**  A persistent, monotone `flushed b` says batches ≤ b are
   on disk; the one synchronous source is `end_op`-was-last-in-group.
3. **PER-NODE PERSISTENCE.**  `i ↦ₐ a [≤b] ∗ flushed b ⊢ recovery
   preserves i at a` — the node-local reading of SNAPSHOT, and the only
   crash rule most consumers ever touch.  The version bound `[≤b]` rides
   the carrier the consumer already holds; it is not a second resource.

## 1. Why directory-based, and what that means precisely

`fs-state.md` §0 already rules it for the internal layer: *"There is no
tree.  The abstraction is a SET of inodes, some of which decode as
directories."*  This proposal keeps that rule AT THE SYSCALL BOUNDARY,
for three reasons:

1. **It is what the machine does.**  Every xv6 fs syscall is, at its
   linearization point, an operation on ONE or TWO inodes (a parent
   directory's entry map; a target node) under their locks.  No syscall
   reads or writes "the tree"; paths are resolved hop by hop against
   directories that can change between hops (SpecNamex's R8 ruling —
   there IS no path→inode function across instants).  A tree-shaped spec
   at this layer would be dishonest about lookup and unstatable for the
   in-flight states (`fs-fragments.md` §1.4: a whole-tree `fs_rep` is
   unholdable by any thread).
2. **It is what Lampson's notes do for directories.**  The graph-of-links
   spec (`G = set Link`, `Link = (from, to, name)`) deliberately avoids
   navigation/recursion; invariants like "dirs form a tree" are separate
   derived predicates, not the state's type.  Our inum-keyed node map
   with per-directory entry maps is the same state grouped by source
   node — the grouping matches the ghost state we own (`γtop` fragments
   and `dview` halves are per-inum).
3. **The tree layer stays honest AND cheap later.**  Reachability,
   acyclicity, and path-points-to are exactly the facts a SINGLE user
   program with exclusive ownership of its subtree can afford, and none
   of them survives concurrent sharing.  Layering them on top of
   per-directory specs (rather than baking them in) is what makes the
   lower layer true of the concurrent kernel while the upper layer is
   true of one program's world.

**The state.**

```coq
(* spec-level abstract node: the READING of FsNode.fs_node *)
Inductive absnode :=
| AFile (bs   : list (bv 8))            (* fn_file_bytes *)
| ADir  (ents : gmap fname Z)           (* dir_entries — INCLUDES "." and ".." *)
| ADev  (major minor : Z).

Record anode := { an_node : absnode ; an_nlink : nat }.

(* the spec state = fs-state's S, quotiented *)
Definition aview := gmap Z anode.       (* inum-keyed; ROOTINO distinguished *)
Definition abs_of : fs_node -> anode.   (* fn_file_bytes / dir_entries / fn_rec *)
```

Decisions folded in, each inherited from a landed ruling:

- **Inum-keyed, not path-keyed, not inductive** — `fs-fragments.md` §1.1
  (all four reasons apply verbatim; files are multi-parent, `".."` must
  be in `ents`, there is no rename so the only movers are edge
  insert/delete).
- **`ents` is `dir_view`'s first-match reading** (`fs-fragments.md`
  §1.2).  Uniqueness of names IS an invariant of reachable states
  (`dir_names_unique`, dirlink's guard under the lock) and may be carried
  as a pure conjunct; first-match is the definition.
- **`"."`/`".."` stay in the map.**  The syscall layer is honest about
  them (`unlink` refuses them by name; `isdirempty` reads them; mkdir's
  delta writes them).  The tree layer hides them later.
- **`nlink` is node-local data, not a derived edge count.**  The global
  "nlink = #in-edges" equation is exactly the whole-state fact
  `fs-state.md` §0 forbids; the spec exposes `nlink` as a field and the
  counting RA's one-directional law (#tokens ≤ nlink) does the safety
  work below the surface.  Lampson's `isDirTree` states the global
  version — for a QUIESCENT state seen by one observer, which is the
  tree layer's business, not this one's.
- **Orphans are IN the map.**  An unlinked-but-open file is a real
  state (`an_nlink = 0`, no entry names it); it leaves `aview` when the
  last fd closes (`iput`'s free).  Hiding it would make `sys_read` on an
  unlinked fd unspecifiable.

## 2. The client-facing resources

Three carriers, all per-inum, none whole-state:

```
i ↦ₐ{q} a [≤b]     (* fractional agreement: inum i's abstract node is a,
                      last modified in batch ≤ b.  The dview
                      generalization: the payload/escrow holds the other
                      half; a client half makes the node's value STABLE
                      against concurrent mutation.  The bound b is data
                      ON the same carrier (a nat beside the agreement
                      value), not a separate resource; it is monotone in
                      the obvious sense and consumers may weaken it. *)
i ↦ₐ a [≤b]        (* q = 1/2 shorthand; the client-held stability half *)
root_is r          (* persistent; r = ROOTINO *)
cwd ↦ i            (* per-process: the working directory ref (a held
                      reference, not a lock) *)
fd f ↦ (i, off, om) (* per-process file-table row: inum, offset, open mode.
                      pipes/devices have their own row forms *)
```

**Why fractional-agreement and not the `γtop` fragment itself.**  The
custody theorem (`fs-fragments.md` §1.4) stands: `γtop_L`'s fragment
rides in the checked-out payload (`ic_loaded`/`ipool_alloc`) and no
client can hold it.  The thing a client CAN hold is precisely what the
namei-pinned campaign built for directories (`dv_half`, ½-½
`dfrac_agree` on the entry map, living BESIDE the payload custody):
this proposal generalizes `dview` from `gmap fname Z` to `anode ×
batch-bound` — one per-inum ½-agreement whose payload half moves at
every retag (`ireg_top_retag` already moves `top_frag`; the same AU
moves this).  N-4's fraction-split plan is the same mechanism; call the
generalized carrier `nview` to keep `dview`'s name for the landed
directory case.

**Two spec strengths per syscall, and both are honest:**

- **AU form (always true).**  A logically-atomic triple in the
  Perennial/HOCAP style: at the linearization instant the spec opens the
  ambient state, observes the touched nodes' current values, applies the
  delta.  No client-held resources required; the postcondition relates
  RETURN VALUES to the values OBSERVED AT THE INSTANT (Lampson's "lookup
  sees some state in the interval", collapsed to one instant because
  xv6's dirops hold the parent's lock across the mutation).
- **Stable form (derived).**  The same triple with the client presenting
  `↦ₐ` halves for the nodes it cares about; agreement pins the observed
  values to the client's, and the AU's "some value" becomes "YOUR
  value".  This is the form the tree layer consumes, and it is a
  COROLLARY of the AU form + agreement, never a separate proof against
  the code.

## 3. Path arguments: the trace primitive and the functional corollary

Paths are NOT part of the abstract state and never become one.  The
primitive is the landed ghost-trace shape (namei-pinned, SpecNamex R8):

- `resolve_trace p tr` — the walk performed lookups `tr = [(d₀,n₀,i₁),
  (i₁,n₁,i₂), …]`, each hop atomic in ITS directory's then-current
  entry map (`dir_entries` first-match), dots and device boundaries per
  the kernel's rules.  This is Lampson's `cLookup`-against-`allLinks`
  made pointwise: instead of "some link present during the interval",
  each hop names its instant.  It is strictly stronger and it is what
  the landed `wp_namei_pinned` already provides.
- **Functional corollary**: if the client holds `↦ₐ` halves for every
  directory on the path for the duration (their values can't move), the
  trace collapses to `path_at aview d p = Some i` — the Perennial-style
  functional lookup.  One lemma, no new walk proof.

Each path-taking syscall therefore comes in the SAME two strengths: the
AU form quantifies over the trace; the stable form takes the halves and
speaks `path_at`.

## 4. The syscall surface — dirop deltas, in-memory ONLY

The delta vocabulary (pure functions on `aview`, one per operation kind;
these are the ONLY mutations — xv6 has no rename, no symlink, no
truncate syscall):

```
δ_create d name i ty   :  <[name:=i]> at d's ents  ∗  i fresh (AFile []/ADev/ADir with dots), nlink 1
                          (mkdir additionally: d.nlink+1 — fused, one delta)
δ_link   d name i      :  <[name:=i]> at d's ents  ∗  i.nlink+1        (files/devs only)
δ_unlink d name        :  delete name at d's ents  ∗  target.nlink−1
                          (dir arm: also d.nlink−1; child's ".." goes grey — the
                           child stays in aview as an orphan dir until iput)
δ_write  i off bs      :  AFile (splice off bs) — MAY GROW (size = max)
δ_free   i             :  delete i from aview     (iput at nlink 0, last ref)
```

Sketches of the AU forms (⟨·⟩ the atomic pre/post; failure arms elided
here, enumerated in §7).  **Note what is NOT here: no durable clause of
any kind.**  The only durability-adjacent artifact is the version bound
on the carriers the syscall returns or updates, and it is filled in
mechanically (the op's own batch):

```
mknod(p/name, ma, mi):
  ⟨av. state av ∗ ⌜av !! d = Some (ADir ents)⌝ ∗ ⌜ents !! name = None⌝⟩
    → ∃ i ∉ dom av, state (δ_create d name i (ADev ma mi) av) ∗ ret 0

link(old, new/name):
  two linearization instants (lookup old; mutate new's parent) — the AU
  is on the SECOND; the first contributes a trace hop and the iget ref
  that keeps i alive between them:
  ⟨av. state av ∗ ⌜av !! d = Some (ADir ents)⌝ ∗ ⌜av !! i = file/dev⌝
      ∗ ⌜ents !! name = None⌝⟩
    → state (δ_link d name i av) ∗ ret 0

read(fd):  fd f ↦ (i,off,O_RD) ∗ ⟨av. state av ∗ ⌜av!!i = AFile bs⌝⟩
    → ret (sub off cnt bs) ∗ fd f ↦ (i, off+r, _)   (* r = bytes read *)
```

**`sys_write` is honestly NON-atomic in memory, and ONLY in memory.**
`filewrite` splits a large write into MULTIPLE transactions (the
few-blocks-per-tx loop), unlocking the inode between chunks, so a
concurrent reader may observe any chunk boundary: the AU form is
per-chunk — a sequence of `δ_write` deltas, each with its own instant.
The friendly single-delta form is the STABLE corollary when the client
holds the file's `↦ₐ` half (nobody else observes the intermediates).
And that is the ENTIRE write spec: v1 additionally specified that a
crash may retain a prefix of the chunks, as write-specific durable
content.  Under v2 that sentence is not written anywhere, because it is
an instance of SNAPSHOT — each chunk boundary WAS a current state, so
"recovery = some past current state" already says exactly that a chunk
prefix (aligned to a batch boundary) may survive.  Lampson's
`Op`/`done`/`mix` machinery for non-atomic writes collapses into the
one global principle.

## 5. The durable aspect: one history, three principles, zero per-syscall content

This section replaces v1's per-op `logged δ b` tokens and its
batch-indexed second reading.  The redesign is driven by one question:
WHAT DOES A CONSUMER ACTUALLY HAVE TO PROVE, and what is the least it
must know to prove it?

**The model (internal — consumers never see it).**  The linearized op
deltas form one log, partitioned into BATCHES (the group-commit windows
between quiescences).  The WAL installs batches atomically and in order
(sector-atomic header, landed), so the on-disk state is always the fold
of a batch PREFIX.  Define:

```
S_cur  := fold of all deltas            (the state every §4 spec talks about)
S_dur  := fold of batches ≤ B_flushed   (DEFINED, never independently specified)
```

`S_dur` has no spec of its own, no deltas of its own, and no carrier a
consumer can hold.  **Drift between the views is not prevented by a
proof the consumer checks — it is impossible by construction, because
there is only one delta log and the durable view is a prefix fold of
it.**  The obligation that the MACHINE's disk state matches `S_dur` is
the framework's adequacy theorem (one theorem, proved once against
`Psi_dec`/`dur_stands_at_logged` — the mknod spike's end theorem is its
first instance), not a consumer-visible statement.

**The consumer-facing principles:**

1. **SNAPSHOT (crash = a recent past).**  After a crash and recovery,
   the current state is `S_cur`-as-of-some-batch-boundary in the past.
   Formally, recovery's post gives `state av' ∗ was_current av' ∗
   flushed-boundary av'` where `was_current` is minted at every batch
   boundary for the then-current view.
   *Consumer corollary, and the reason this design is lighter:* if a
   consumer maintains an invariant `I` of the current view continuously
   (which it does anyway, to reason about its own next syscall — every
   §4 delta preserves it), then `I` holds after any crash.  **Crash
   safety of invariants requires NO crash-specific proof and NO
   knowledge of batches.**  This is DFSCQ's tree-sequence guarantee,
   sharpened: the sequence is totally ordered and batch-aligned.
2. **BOUND (how far the past can reach back).**  `flushed b`:
   persistent, monotone — batches ≤ b are on disk, so SNAPSHOT's
   boundary is ≥ b.  Sources: `end_op`-was-last-in-group yields
   `flushed (my batch)` AT RETURN — the one synchronous durability xv6
   has; otherwise it arrives at a later quiescence.

   *`sys_sync` — IT EXISTS in this fork* (`SYS_sync = 22`,
   `xv6-riscv/kernel/log.c:247`; stock xv6-riscv has none) and it
   BLOCKS until the log has been flushed.  Its whole spec is "returns
   `flushed b` for `b` ≥ the batch current at invocation" — one token,
   no new durable state even here.  DOES IT MAKE THE IN-MEMORY STATE
   DURABLE?  Yes, in the sense a consumer can use: every carrier held
   across the call has bound ≤ b, so principle 3 makes each held node
   durable at its observed value, and SNAPSHOT's boundary moves past
   the sync point.  The honest refinement: the committed snapshot is a
   DESCENDANT of the invocation-instant state, not necessarily equal to
   it — the commit also sweeps in deltas other processes linearized
   between invocation and commit.  Monotone, so nothing a consumer
   concludes breaks; and it is what real sync means.

   THE CODE, and why its one-commit wait meets the spec.  `sys_sync`
   takes `log.lock`; if `!committing && outstanding == 0` it returns at
   once (the log is empty — the last `end_op` committed and cleared
   it); otherwise it waits until `log.ncommit` (a commit counter bumped
   after each `commit()`, log.c:180) advances by ONE.  One commit
   suffices by a case split at the lock: `committing` implies
   `outstanding == 0` (`begin_op` blocks while committing, so no op is
   open), hence the in-progress commit's batch already contains every
   delta linearized before the call; and with the group merely open,
   all older batches are committed and every remaining pre-sync delta
   sits in (or will join) the current group's log, which the next
   commit writes in full — the log only grows between commits.  So
   `ncommit + 1` IS "the commit covering the invocation-time batch".
   Note `sys_sync` never runs `begin_op` — it is not a transaction, it
   only watches the counter — which both sidesteps the naive
   `begin_op(); end_op()` shape (that pair commits NOTHING while other
   ops are open) and means sync does not delay the group it waits on.
   Caveat, safety vs liveness: with ops outstanding, quiescence needs
   `out = 0`, and `begin_op` admits new ops into the open group, so a
   continuous op stream defers the commit unboundedly.  The spec above
   is safety-only; termination of `sys_sync` would need a fairness
   assumption and is out of scope here.
3. **PER-NODE PERSISTENCE (the only rule most consumers use).**

   ```
   i ↦ₐ{q} a [≤b] ∗ flushed b  ⊢  recovery preserves i at a
   ```

   Read: this node last changed in a flushed batch, so every reachable
   snapshot contains it at `a`.  The bound comes from the carrier the
   consumer already holds (§2); a syscall that mutates `i` returns the
   carrier at `[≤ its own batch]`; untouched carriers keep their bound.
   A consumer that wants file `f` crash-safe checks exactly two local
   facts — its own carrier's bound and one `flushed` — and never
   mentions the view, the history, or any other node.

**What a consumer reasons about, in full:** the current state (via §4's
triples), plus — only if it cares about crashes — principle 3 for the
nodes it cares about, or principle 1 for an invariant.  It never holds
two states, never relates them, never checks that a durable delta
matches an in-memory one (there is no durable delta), and never reasons
about what OTHER processes' ops do to durability beyond the monotone
`flushed`.

**What was given up relative to v1, deliberately:**

- *Per-op durable receipts* (`logged δ b`).  Gone from the surface; the
  information survives as the carrier bound (`[≤b]` on whatever the op
  returned).  An op-granular receipt is derivable when someone needs it;
  none of the anticipated consumers (verified user programs) do.
- *Naming `S_dur` at all.*  A consumer wanting a cross-node durable
  fact ("after crash, the dirent AND the file it names are both there")
  states it as an invariant of past currents (principle 1) or as two
  bounded carriers + one `flushed` (principle 3, twice, same `b` — batch
  order gives the conjunction).  The dangerous middle — a free-floating
  durable state a spec could contradict — is unstatable BY DESIGN.

**Grounding in the ghost state under construction:**

- `flushed` = a mono-nat over the log's epoch counter (`LogInv.ln_ep`),
  minted persistent at each commit — the receipt shape ruling 4⅞
  decision 3 reserves, produced where `dur_stands_at_logged` concludes.
- The carrier bound = one nat beside the `nview` agreement value; the
  payload half's retag (already an AU at every mutation) stamps the
  current epoch.  No new invariant; one field on a ghost the namei
  campaign already routes.
- `was_current`/SNAPSHOT = the adequacy-level recovery theorem, i.e. the
  spike's end theorem generalized from "the durable view contains the
  device inode" to "the durable view IS the epoch-B fold".  It consumes
  the same `Psi_dec` bridge; nothing new below the spec layer.

## 6. Layering the tree spec on top (the later, single-program layer)

For ONE user program owning its world, the directory-based layer
composes upward mechanically; nothing below re-opens:

1. The program holds `↦ₐ` halves for every node of its subtree (obtained
   at spawn/open from a parent that owned them).  Agreement makes every
   value stable ⇒ every path form collapses to `path_at` (§3) ⇒
   FSCQ-style functional pre/posts over an `fstree` READING of the held
   fragment.
2. Acyclicity/reachability (`fs_dirs_acyclic`, root-reachability) are
   pure predicates of the held fragment, established at acquisition and
   preserved by the deltas (edge insert with fresh target, edge delete —
   the two lemmas are trivial precisely because there is no rename).
3. The dots are hidden by the reading (`fs-fragments.md` already prices
   this); `nlink` becomes the derived in-edge count WITHIN the owned
   fragment — the global equation is never needed because the fragment
   is closed by ownership.
4. **Durably, the tree layer inherits the three principles unchanged** —
   and principle 1 does the heavy lifting: "my subtree is well-formed"
   is an invariant the program maintains on the current view, so it
   holds after any crash with no additional proof; "my file survived" is
   principle 3.  The tree layer adds NO durable machinery of its own.

This is `fs-friendly.md`'s F4/F5 finish line, reached without ever
making the tree the KERNEL's abstraction.

## 7. Per-syscall inventory (the checklist for the eventual campaign)

Durable columns are GONE relative to v1 — that is the point.  The only
per-syscall durable artifact is the mechanical bound-stamp on returned
carriers, identical in shape for every mutator.

| syscall | deltas | instants | notable failure arms |
|---|---|---|---|
| `open` (no CREATE) | — | trace + iget | ENOENT-ish (ret −1), T_DIR w/ write mode |
| `open` (O_CREATE) | δ_create(AFile) | trace + create AU | exists→open-instead arm (xv6: returns existing FILE), parent gone |
| `mkdir` | δ_create(ADir+dots, d.nlink+1) | trace + AU | exists, parent gone |
| `mknod` | δ_create(ADev) | trace + AU | exists |
| `link` | δ_link | trace×2 + AU | target is dir, new exists, cross-of-life (target unlinked between instants — the two-instant shape makes this arm STATABLE) |
| `unlink` | δ_unlink (+dir arm) | trace + AU | ".": refused; dir non-empty; gone |
| `read` | — | per-chunk AU (readi) | off past size (ret 0) |
| `write` | δ_write per chunk | per-chunk AU | full disk mid-write (partial ret) |
| `close`/`iput` | δ_free when last | AU at iput | — |
| `chdir` | — | trace + cwd swap | not a dir |
| `fstat` | — | one AU (read i's meta) | — |
| `dup`,`pipe` | — | fd-table only | — |
| `exec` | — | trace + reads | (kexec cone; stage C of namei-pinned) |

Notes: `open(O_CREATE)` on an existing file is xv6's open-not-fail arm —
the delta is CONDITIONAL, which the AU form expresses as two arms, not
nondeterminism.  `unlink`'s dir arm leaves the child orphaned-in-map
(§1); `close`'s δ_free fires only at nlink 0 + last ref, i.e. the spec
of `iput`'s free path, reached from several syscalls.

## 8. What is inherited from the sources, and what is deliberately different

From Lampson's notes:
- **The history/`h` crash spec** (files, p.4–5): durability as "which
  recorded writes survive", `sync` collapsing the set.  Here `h` is
  batch-granular and the surviving set is always a PREFIX — the WAL's
  gift — so the nondeterminism shrinks to one number, and (v2) the
  history itself is demoted to framework-internal.
- **Directories as a link graph, invariants derived** (p.6): the state
  is the edges; `isDirTree` is a separate predicate consumed only where
  it holds.  Here: entry maps per inum; acyclicity is the tree layer's.
- **Non-atomic ops against a state interval** (p.8–10, `cLookup`/
  `allLinks`): here the per-hop ghost trace (strictly sharper — our
  hops are lock-atomic), and the same two-instant honesty for `link`.
- **"Keep the spec simple; show desired properties hold"**: v2 takes
  this further than v1 did — the durable spec is three principles
  total, and Lampson's own non-atomic-write machinery (`Op`/`done`/
  `mix`) becomes a corollary of SNAPSHOT rather than copied structure.

From DFSCQ (the consumer-facing shape): crash = a recent past state of
ONE evolving view, fsync-like operations only tighten the bound.  Ours
is sharper (totally ordered, batch-aligned) because the WAL's
atomicity is a theorem here, and — unlike DFSCQ — the principles are
node-local where consumers live (principle 3), because the carriers are
per-inum fragments rather than a whole tree.

Deliberately different from both:
- **No `choose`-nondeterminism in crash states** — batch prefixes only.
- **No symlinks, no rename** — xv6 doesn't have them; their absence is
  load-bearing simplicity.
- **`nlink` exposed, edge-count equation not stated** (§1).

## 9. Open questions for the owner

1. **Carrier scope for `nview` (§2).**  Generalizing `dview` to all
   nodes is new ghost machinery on the payload path (the same seam N-4
   already plans to touch).  Alternative: directories keep `dview`,
   FILES get their stability from the fd layer's refcount + inode lock
   instead (weaker: file values stable only while locked).  The
   fractional-agreement route is more uniform; the fd route is less new
   state.  Which?
2. **`aview` vs raw `fs_node` at the spec boundary.**  §1 quotients to
   `absnode` (friendly, hides blocks).  The alternative — expose
   `fs_node` and let the tree layer quotient — saves one reading but
   leaks `fn_blk` into every syscall post.  Proposal says quotient here.
3. **Where `state av` lives.**  The AU forms need an ambient authority
   for the quotient view.  Proposal: it is a READING of `γtop_L`'s
   authority (already in `ftop_inv`) — no new invariant, one
   `abs_of`-fmap.  Confirm nothing needs a separate `aviewN`.
4. **Batch identity.**  Is `b` the log's epoch counter (`ln_ep`)
   verbatim, or a spec-level counter tied to it by one ghost?  (`ln_ep`
   verbatim is cheaper; a spec counter insulates the spec from log
   refactors.)
5. **How SNAPSHOT is formalized without a crash-WP framework.**  The
   honest options: (a) an adequacy-level recovery theorem only (the
   spike's shape — cheapest, and enough for verified user programs whose
   crash story is stated at the whole-system theorem); (b) a
   `was_current` persistent snapshot token minted per batch, giving
   in-logic crash reasoning without Perennial-style crash conditions.
   Proposal: (a) first; (b) only when a consumer inside the logic needs
   it.
6. **Scope of the first increment.**  Suggest: mknod end-to-end (rides
   the spike's theorem), then unlink (hardest in-memory arm, exercises
   orphans), then write (exercises per-chunk deltas and shows SNAPSHOT
   subsuming write's crash story).  open/read/close/fstat/chdir after,
   mechanical.
