# fs-syscall-specs — directory-based specs for the fs syscalls, at two views

STATUS: EXPLORATION (2026-08-24, Fable + owner).  A proposal, not a design
of record: nothing here is staged work.  Prompted by the owner: once the
durable-disk spike lands, we want specs for the individual file system
calls that cover BOTH the in-memory and the durable aspect, stated over a
DIRECTORY-based abstraction (a set/map of nodes with entry maps), NOT a
file-system tree; specialized tree specifications for a single user
program come later, LAYERED on this.  External input: Lampson's 6.826
spec notes (`fs-butler-specs.pdf` in the repo root) — the history-based
crash spec for files, directories as a graph of links, and lookup
specified against the union of states it might see.

Related: [`fs-state.md`](fs-state.md) (design of record for the two-view
ghost state this layer SURFACES), [`fs-fragments.md`](fs-fragments.md)
(the ruled tree/fragment layer — §1.1's inum-keyed store, §1.4's custody
theorem), [`fs-friendly.md`](fs-friendly.md) (the 2026-08-15 direction
sketch this supersedes in part), `projects/namei-pinned-lookup.md` (the
`dview` carrier and the ghost-trace lookup spec),
`projects/durable-disk.md` stage 3 (the mknod spike whose end theorem is
this layer's first durable instance).

## 0. The one-sentence design

**A syscall's spec is a logically-atomic DELTA on an inum-keyed map of
abstract nodes, and the SAME delta read twice: applied to the logged
(in-memory) instance at the syscall's linearization point, and applied to
the durable instance at the commit of the batch that carries it.**  The
directory-based abstraction, the two instances, and the "same shape at
both views" principle are not new — they are `fs-state.md` §1–§4
(`Γ_L`/`Γ_D`, `γtop`, `fs_state`) — so this layer is a SURFACING of ghost
state the durable-disk campaign already builds, not a third abstraction.

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
i ↦ₐ{q} a          (* fractional agreement: inum i's abstract node is a.
                      The dview generalization: the payload/escrow holds
                      the other half; a client half makes the node's
                      value STABLE against concurrent mutation (no one
                      can move both halves without the client). *)
i ↦ₐ a             (* q = 1/2 shorthand; the client-held stability half *)
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
this proposal generalizes `dview` from `gmap fname Z` to `anode` — one
per-inum ½-agreement whose payload half moves at every retag
(`ireg_top_retag` already moves `top_frag`; the same AU moves this).
N-4's fraction-split plan is the same mechanism; call the generalized
carrier `nview` to keep `dview`'s name for the landed directory case.

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

## 4. The syscall surface — dirop deltas

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
here, enumerated in §7):

```
mknod(p/name, ma, mi):
  ⟨av. state av ∗ ⌜av !! d = Some (ADir ents)⌝ ∗ ⌜ents !! name = None⌝⟩
    → ∃ i ∉ dom av, state (δ_create d name i (ADev ma mi) av) ∗ ret 0
      ∗ logged (δ_create …) b                    (* §5: the durable half *)

link(old, new/name):
  two linearization instants (lookup old; mutate new's parent) — the AU
  is on the SECOND; the first contributes a trace hop and the iget ref
  that keeps i alive between them:
  ⟨av. state av ∗ ⌜av !! d = Some (ADir ents)⌝ ∗ ⌜av !! i = file/dev⌝
      ∗ ⌜ents !! name = None⌝⟩
    → state (δ_link d name i av) ∗ ret 0 ∗ logged (δ_link …) b

read(fd):  fd f ↦ (i,off,O_RD) ∗ ⟨av. state av ∗ ⌜av!!i = AFile bs⌝⟩
    → ret (sub off cnt bs) ∗ fd f ↦ (i, off+r, _)   (* r = bytes read *)
```

**`sys_write` is honestly NON-atomic, twice over, and the spec says so.**
`filewrite` splits a large write into MULTIPLE transactions (the
few-blocks-per-tx loop), unlocking the inode between chunks.  So:
in-memory, a concurrent reader may see any chunk boundary; durably, a
crash may leave a PREFIX of the chunks (each chunk has its own batch).
The AU form is therefore per-chunk — a sequence of `δ_write` deltas,
each with its own instant and its own `logged` token — and the
friendly single-delta form is the STABLE corollary when the client holds
the file's `↦ₐ` half (nobody else observes the intermediate states) —
in-memory only; durably a big write is never atomic and no spec should
pretend it is.  This is Lampson's non-atomic-write `h`-per-`Op` spec,
which is exactly the shape to copy; his `done(op)` is our chunk-batch
receipt.

## 5. The durable aspect: same deltas, batch-indexed

This is where the layer plugs into the durable-disk campaign rather than
inventing machinery.

**The model** (Lampson's history spec, collapsed by WAL atomicity).  The
spec-level history is the sequence of op deltas in linearization order,
grouped into BATCHES (the group-commit windows the log already has —
`begin_op..end_op` populations between quiescences).  Because the WAL
makes each batch's install atomic (sector-atomic header, landed), the
set of possible post-crash states is NOT Lampson's arbitrary
subset-of-writes — it is exactly the BATCH PREFIXES:

```
durable view after crash  =  fold δ over batches 1..B,   B = last committed batch
```

That one sentence is the whole crash story at this layer, and it is the
statement the spike's end theorem instantiates at mknod ("after mknod's
batch commits, the durable view contains the device inode").

**The client-facing tokens:**

```
logged δ b        (* persistent: my delta is carried by batch b —
                     minted at the op's linearization, inside its
                     begin_op..end_op window *)
committed_lb b    (* persistent, monotone: batch b has committed *)
durably P         (* := ∃ b, committed_lb b ∗ (all deltas ≤ b entail P) *)
```

- Each mutating syscall's post carries `logged δ b` for its delta(s).
- `end_op`'s was-last-in-group case yields `committed_lb b` AT RETURN —
  the one place xv6 gives synchronous durability.  (xv6 has no fsync; a
  client that needs a receipt realized can only quiesce.  If we ever add
  a `sys_sync`, its spec is precisely `∀ b logged. committed_lb b` — one
  new arm, no redesign.)
- The recovery theorem (adequacy-level, once, not per syscall): the
  post-recovery `aview` is the fold of batches ≤ B for some B with
  `committed_lb B` valid at the crash instant, and every `logged δ b`
  with `b ≤ B` is reflected.  Uncommitted batches vanish whole.

**How it grounds in the landed/in-flight ghost state.**  The durable
instance `Γ_D` lives in `P_wf` inside `crashN`; mortals hold no piece of
it (`fs-state.md` §4, ruling 1) — which is exactly why the client-facing
durable tokens are PERSISTENT RECEIPTS, the shape §4 and ruling 4⅞
decision 3 already reserve ("a deposit MAY hand back a persistent
'durable once this batch commits' receipt").  Under the current spike
direction (`P_wf_dec`/`Psi_dec`), the parked payload is pure+persistent
and the commit concludes `dur_stands_at_logged` — the durable view at
the batch's logged values — so `committed_lb`/`logged` are readings of
ghost state the spike already has to build, indexed by the epoch counter
the log already carries (`LogInv.ln_ep`).  No second durability
mechanism.

**What this deliberately does NOT state:** per-op durability ordering
beyond batch order, fsync-grade "this op is durable now" (xv6 cannot
promise it), or any coupling between the durable view and in-flight
in-memory state (the durable view lags by whole batches; that lag IS the
spec).

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
4. Durably: the program's tree-level crash statement is the batch-prefix
   theorem read through the same fold — "after a crash, my subtree is as
   of some batch boundary" — with `logged`/`committed_lb` unchanged.

This is `fs-friendly.md`'s F4/F5 finish line, reached without ever
making the tree the KERNEL's abstraction.

## 7. Per-syscall inventory (the checklist for the eventual campaign)

| syscall | deltas | instants | durable tokens | notable failure arms |
|---|---|---|---|---|
| `open` (no CREATE) | — | trace + iget | — | ENOENT-ish (ret −1), T_DIR w/ write mode |
| `open` (O_CREATE) | δ_create(AFile) | trace + create AU | logged×1 | exists→open-instead arm (xv6: returns existing FILE), parent gone |
| `mkdir` | δ_create(ADir+dots, d.nlink+1) | trace + AU | logged×1 | exists, parent gone |
| `mknod` | δ_create(ADev) | trace + AU | logged×1 | exists |
| `link` | δ_link | trace×2 + AU | logged×1 | target is dir, new exists, cross-of-life (target unlinked between instants — the spec's two-instant shape makes this arm STATABLE) |
| `unlink` | δ_unlink (+dir arm) | trace + AU | logged×1 | ".": refused; dir non-empty; gone |
| `read` | — | per-chunk AU (readi) | — | off past size (ret 0) |
| `write` | δ_write per chunk | per-chunk AU | logged×N | full disk mid-write (partial ret) |
| `close`/`iput` | δ_free when last | AU at iput | logged (free path) | — |
| `chdir` | — | trace + cwd swap | — | not a dir |
| `fstat` | — | one AU (read i's meta) | — | — |
| `dup`,`pipe` | — | fd-table only | — | — |
| `exec` | — | trace + reads | — | (kexec cone; stage C of namei-pinned) |

Notes: `open(O_CREATE)` on an existing file is xv6's open-not-fail arm —
the delta is CONDITIONAL, which the AU form expresses as two arms, not
nondeterminism.  `unlink`'s dir arm leaves the child orphaned-in-map
(§1); `close`'s δ_free fires only at nlink 0 + last ref, i.e. the spec
of `iput`'s free path, reached from several syscalls.

## 8. What is inherited from Lampson's notes, and what is deliberately different

Taken:
- **The history/`h` crash spec** (files page 4–5): durability as "which
  prefix of the recorded writes survives", with `sync` collapsing the
  set.  Here `h` is batch-granular and the subset is always a PREFIX —
  the WAL's gift — so the nondeterminism shrinks to one number `B`.
- **Directories as a link graph, invariants derived** (page 6): the
  state is the edges, `isDirTree` is a separate predicate consumed only
  where it holds.  Here: entry maps per inum; acyclicity is the tree
  layer's.
- **Non-atomic ops against a state interval** (pages 8–10, `cLookup`/
  `allLinks`): a lookup concurrent with mutation sees links from a RANGE
  of states.  Here: the per-hop ghost trace (strictly sharper, since our
  hops are lock-atomic), and the same two-instant honesty for `link`.
- **Non-atomic multi-part writes** (page 5, `Op`/`done`/`mix`): copied
  as §4's per-chunk write spec.
- **"Keep the spec simple; show desired properties hold"**: the AU form
  is small; everything path-shaped and tree-shaped is a corollary.

Different, and why:
- **No `choose`-nondeterminism in crash states** — the WAL's batch
  atomicity is proven, so the spec would be WEAKER than the theorem.
- **No symbolic links, no rename, no working-directory-relative subtle
  cases beyond cwd-as-ref** — xv6 doesn't have them; their absence is
  load-bearing simplicity (Lampson spends 3 of 10 pages on
  symlinks+rename).
- **`nlink` exposed, edge-count equation not stated** (§1): the global
  equation is the forbidden whole-state fact; the RA law carries safety.

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
5. **Scope of the first increment.**  Suggest: mknod end-to-end (rides
   the spike's theorem), then unlink (hardest in-memory arm, exercises
   orphans), then write (exercises per-chunk + multi-batch durability).
   open/read/close/fstat/chdir after, mechanical.
6. **Does the ghost-trace primitive need extending for `..` across the
   syscall layer**, or is the landed namei-pinned form already the
   needed shape?  (Believed: already the shape; verify at mknod.)
