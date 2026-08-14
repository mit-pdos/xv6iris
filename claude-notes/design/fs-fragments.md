# The fragment algebra and the tree layer — F1/F1.5 design of record

STATUS: VERIFIED DESIGN + RULINGS (2026-08-14).  This file is the output
of the approved parallel design-only stage ("let's do 1 in parallel"):
a report-only agent verified fs-friendly.md's F1/F1.5 sketch against the
landed tree (DirLinks, InodeRegion, IcacheRef, IcacheEscrow, the ialloc/
ilock/dirlink/iput specs, the namex trio, PathElems, DirView, DirentEnc)
and against the §20 graveyard in fs-icache.md.  §0 records the
coordinator's rulings; §1–§6 preserve the verification report.  NO BUILD
WORK is authorized from this file yet: execution is sequenced AFTER the
sysfile cone per the approved plan.  When the fragment campaign opens,
it starts here.

## 0. RULINGS (coordinator, 2026-08-14)

R1. **The tree type is adopted as reported** (§1.1): an inum-keyed node
    store `gmap Z fsnode` plus a distinguished root — NOT an inductive
    tree.  `".."` is recorded in `ents` provisionally (S7 may sharpen —
    §6).  `fs_dirs_acyclic` is a derived, separable pure conjunct, never
    a property of the type.  `fname` = `DirentEnc.bname 14`; paths add
    no new datatype (`PathElems.path_elems` is the vocabulary).

R2. **AMENDED (2026-08-14, user): name-uniqueness is carried as an
    INVARIANT, and `dir_view` keeps first-match only as its
    definition.**  The user's observation: xv6 cannot reach a
    duplicate-name state — every insertion goes through `dirlink`,
    which refuses a present name under the caller's directory lock
    (fs.c:613; create's own lookup is redundant protection — sys_link
    and mkdir's "."/".." rely on dirlink's guard alone).  The report's
    §1.2 trap is about the byte FORMAT and the current model (no landed
    invariant carries uniqueness; `dirlookup`'s proven semantics is
    first-match).  The amendment closed a real hole the first-match
    dodge left open — THE UNMASKING ARGUMENT: without the invariant,
    sys_unlink's friendly spec is FALSE, because zeroing the first
    record with a hidden duplicate behind it leaves `name` still
    mapped (to a different inum); the tree delta is not `delete name`.
    Uniqueness is load-bearing for F3's unlink triple, not cosmetic.
    It is also nearly free: `SpecDirlink` ALREADY exposes the
    maintenance fact on both arms (append: `dir_first data nrec s =
    None`, :653/:911; found: `<> None`), so re-establishment is
    caller-side with zero contract movement, unlink's zeroing preserves
    it trivially, and boot needs one computational image obligation for
    mkfs's initial image (`image_nlink_short`'s style).  Concretely:
    `dir_names_unique` is a pure predicate in FsTree.v (F1a) and a
    conjunct of `node_rep`'s NDir case, riding inside `fnode` (F1b);
    `dir_view` stays first-match AS A DEFINITION (total on all byte
    states, no definedness side conditions) with a lemma that under
    `dir_names_unique` it is the exact any-match map and commutes with
    record-zeroing.  §1.2's bytes→tree one-directionality stands.

R3. **No whole-tree authority, ever** (§1.3) — three §20.9 death
    certificates already cover every home one could have.  `fs_rep` is
    a derived predicate over client-held fragments, appearing only
    inside atomic-update accessors (§1.4 is a THEOREM of the landed
    lock placement, not a style choice).  Fragments-with-holes is the
    only consistent top-level shape (`fs_closed` is false in general).

R4. **Option (k)/(L5) is the design of record for the detached
    fragment** (§3.3): the clause lives on the BYTES
    (`c = Some (Excl ty) -> di_type d = ty /\ ty <> 0`), five of six
    movers free, `ireg_withdraw` owes NOTHING (verified against the
    landed proof).  §3.4's self-minting step (mintability direct from
    (L5) at a type-0 record, no free-side obligation) is NEW — not in
    §20.5/§20.16/§20.17 — and stands regardless of whether F1.5 lands.

R5. **STANDING CONSTRAINT — (L6) MUST NEVER BE STATED.**  The arm
    clause `c <> None -> inreg` discharges the free in two lines and
    collapses the whole design back into §20.16.3: the withdraw
    immediately owes it on every firing.  The free's discharge comes
    from the reference side or not at all.  Anyone touching
    InodeRegion's link_ok during the fragment campaign reads this first.

R6. **ilock's consumption is an option-indexed INPUT** (§3.7), the
    `filled` retrofit's exact mechanical precedent — eight of nine
    consumers instantiate `None`/`emp`.  It is not an obligation, which
    is why §20.16.5(e)'s death certificate does not apply.

R7. **Staging** (§5.3 adopted with one amendment): F1a, F1b, F1.5b are
    the unconditional slate — additive, reopen nothing — but they stay
    QUEUED BEHIND the sysfile cone; they are the fragment queue's first
    three items, in that order.  **F1.5c does not start until F1.5d's
    gate has a door**: `isdirempty`'s invariant (S7, unwritten), the
    root clause (owed, see R9), and SpecIget's licence enumeration (C′)
    — or fs-icache §20.17.7's kernel fix (ialloc's brelse-after-iget;
    NOTE the name collision: that is fs-icache's "F2", unrelated to the
    staging table's F2 row).

R8. **fs-friendly §4's F2 row is corrected** (§5.4): path resolution
    CANNOT be a re-derivation of namex's post (SpecNamex rules there is
    no path→inode functional statement — each dirlookup is atomic under
    its own lock).  F2 is a logically-atomic triple whose linearization
    point is a single dirlookup under one lock.  Amended in
    fs-friendly.md.

R9. **Owed items registered**, each with its home:
    - `node_rep_inj` — F1's one real proof obligation (fs_rep
      determinacy rests on it; `diblk_bytes_inj`'s precedent).
    - the edge-DELETE constructor (`dir_links_unlink` + its
      `dir_link_at` half) — F1.5b, zero consumers today, owed to S7 and
      can land ahead of it.  Today insert has a full resource story and
      delete has only the refcount half (`ireg_write_unlink` consumes
      an `ilink` and has NO CALLER).
    - the ROOT clause `di_nlink (ROOTINO) >= 1` in `ireg_body` — §20.4
      chartered it, never landed; licence (f)'s refutation needs it.
    - `isdirempty`'s invariant goes into S7's brief as a PREREQUISITE
      of create_fresh_ty's retirement, not a local convenience.
    - the `".."`-location fact (`ents ip !! ".." = Some dp`) is F1b's
      headline dividend — §20.17.4's owed fact, free as a conjunct of
      `fnode ip (NDir ents)`.

R10. **Byte-stability map accepted** (§5.1): the only moving seams in
     F1.5c are SpecIalloc (both forms) and SpecIlock (+9 callers, 8 at
     None); SpecIupdate moves only at F1.5d and is deferred with it.
     Everything else — dirlink, the namex trio, iput/iunlockput — stays
     byte-stable, caller-side, per §20.18 ruling 1.

R11. **Honesty markers kept**: licence (d) is §20.16.4's struck device
     REVIVED — founded for MINTING (new), unfounded for PRESERVATION
     (unchanged); the claim-vs-grey obligation is inherited UNDISCHARGED,
     not escaped; the adequacy clause hits M1's wall by a different
     mechanism (borrowed-at-iget, so not held at iput).  Do not
     overclaim any of the three.

R12. **Do not build on the current grey provenance** — today the only
     grey producer is the free mint (mint-from-nothing);
     `link_grey_of_link` has no caller until S7 lands and the dangling
     edge gains an evidence-bearing provenance.  And the LEDGER
     dimension (dl/crz credit) stays outside the algebra; only F3's
     syscall boundary can hide it.

---

What follows is the verification report, preserved verbatim (2026-08-14,
report-only agent; no files touched, no builds run).

## 1. THE TREE TYPE, AND THE GHOST SPLIT

### 1.1 The type: an inum-keyed node store with a distinguished root — NOT an inductive tree

```coq
Definition fname := list (bv 8).                    (* = DirentEnc.bname 14 f, DirentEnc.v:730 *)
Inductive fsnode :=
| NFile (bs : list (bv 8))
| NDir  (ents : gmap fname Z).                      (* name ↦ inum *)
Record fstree := MkTree { fs_nodes : gmap Z fsnode; fs_root : Z }.
```

Four reasons the shape is forced, each against the tree as it stands:

1. **Every landed inum-indexed resource is `Z`-keyed.**  `ireg_inG ::
   ghost_mapG Σ Z dinode` (InodeRegion.v:543-545), `dinode_at γi inum
   dn := bv_unsigned inum ↪[γi] dn` (:560-561), `linkUR := gmapUR Z
   (authR linkElemUR)` (IcacheRef.v:291), `icfg_iep : Z -> gname`
   (IcacheRef.v:430).  A path-keyed abstract state needs a coercion at
   every one of them.
2. **Files are multi-parent** (hard links), so an inductive `Tree` is
   wrong for leaves anyway; the DAG has to be a store plus a root.
3. **`".."` must be IN `ents`, not derived.**  §5 Q2 asks; the answer
   is forced.  `dir_link_at` is keyed by record *index* and is
   name-blind (DirLinks.v:433-438; §20.17.4(b) at fs-icache.md:5253-5258
   says the model has no invariant placing `".."` at index 1), and
   §20.16.5(g) (fs-icache.md:5058-5063) kills exempting `".."`
   outright: a `..` record with no fragment leaves `dirlookup(dp,"..")`
   with nothing to hand `iget`, so namex's parent step has no licence.
   FSCQ elides `".."`; we cannot.
4. **No rename ⇒ no tree surgery.**  The only shape movers are
   insert-edge and delete-edge, which is why §1's "mostly a reading"
   holds.

"Dirs form a tree" is then a **derived pure predicate**
`fs_dirs_acyclic t`, a separate conjunct, not a property of the type.
Nothing landed needs it; it becomes load-bearing only at S7 and F4.
Keep it separable so no mover has to re-establish it.

Paths: **add no new datatype.**  `PathElems.path_elems : list (bv 8) ->
list (list (bv 8))` (PathElems.v:368-369) and `nameiparent_of`
(:596-597) are already the name-sequence vocabulary, deliberately
iris-free, and `bname 14 f` (DirentEnc.v:730) is already the canonical
name.  `path_at : fstree -> Z -> list fname -> option Z` is one `foldl`.

### 1.2 THE ABSTRACTION RELATION'S ONE TRAP: duplicate names

xv6 does **not** forbid two live records with the same name; `dirlookup`
returns the first (`DirView.dir_first`, DirView.v:274).  A `gmap fname
Z` therefore **loses information the on-disk format permits**.  The
relation must be defined first-match-wins and used **one-directionally
only** (bytes → tree), never tree → bytes:

```coq
Definition dir_view (data : nat -> list (bv 8)) (nrec : nat) : gmap fname Z
  (* k-th live record contributes only if dir_first data nrec (dir_name data k) = Some k *)
```

Define it as a fold and F2 breaks against `dir_first` at the first
duplicate.  This is the kind of off-by-one the campaign stops catch; it
belongs in F1a's brief in bold.

[COORDINATOR AMENDMENT — superseded in part by R2: uniqueness IS an
invariant of xv6's reachable states (dirlink's guard under the lock)
and is carried as one (`dir_names_unique` inside `fnode`'s NDir case);
first-match survives only as `dir_view`'s definition.  See R2 for the
unmasking argument that made the invariant load-bearing.]

### 1.3 The auth/frag split: edges primitive, tree DERIVED, no new authority

The ruling, and it is forced three times over by §20.9's death
certificates:

- **Do NOT introduce a whole-tree authority.**  §20.9(c)
  (fs-icache.md:4551-4556) killed one global `auth (gmap Z nat)` inside
  `ireg_body` because with a global authority a mover can read the key
  only by opening and nothing lets the *caller* supply a fact about it.
  A `gmap_view Z fsnode` authority is that device verbatim.  §20.9(d)
  (:4558-4562) killed parking authority with the record.  §20.9(e)
  (:4564-4568) killed a new gname (it would enter `ireg_inv` AND
  `ipool_shape`, i.e. `ic_escrow`'s arity, i.e. every fs contract).
- **The edge multiset already exists and is already correctly homed.**
  `dir_links self dn data` (DirLinks.v:124-129) is one ledger unit per
  live non-self record, filed in the *directory's own payload* —
  `IcacheEscrow.ipool_alloc` (IcacheEscrow.v:437-444) and `ic_loaded`
  (:487-498).  Out-edges are owned by the source node.  That is exactly
  the fragment locality §3 wants, already paid for.
- **The node store already exists**: `ghost_map Z dinode` with
  `dinode_at` exclusive (InodeRegion.v:567) and `ghost_map_auth γi 1 m`
  inside `ireg_body` (:950-952).

So **`fs_rep` is a derived predicate over client-held fragments, not an
invariant.**  That answers §5 Q3 decisively — client-held — because a
global invariant needs an authority and both homes an authority could
have are already dead.

### 1.4 A HARD CONSEQUENCE WORTH RULING ON NOW

`fnode i n` requires `dinode_at γi i dn`, which lives in `ipool_alloc`
(behind the itable spinlock) or `ic_loaded` (behind the inode
sleeplock).  **A thread can hold `fnode i n` only while it holds `i`'s
inode locked.**  Therefore `fs_rep t` over a whole tree is unholdable by
any thread.  Consequence: **`fs_rep` can appear only inside
atomic-update/HOCAP accessors, never as a client-held whole-tree
assertion.**  This kills FSCQ-style whole-tree pre/posts outright and
independently confirms §2's choice of the Perennial style — but it
should be stated as a theorem of this tree, not as a stylistic
preference.

Second consequence, from §20.9(h)/(i) (fs-icache.md:4581-4593): the
edge ticket must keep the grey disjunct, so **an edge of `t` may point
at a node that is not in `t`.**  `fs_closed t` is false in general.
Fragments-with-holes is not a convenience in §6 — it is the only
consistent top-level shape.

## 2. THE FRAGMENT ALGEBRA'S SIGNATURES

All four reuse; the only new *resource* is (iii).

**(i) NODE — reuses `dinode_at` + `inode_blocks`, new nothing**
```coq
Definition fnode (γi : gname) (i : Z) (n : fsnode) : iProp Σ :=
  (∃ dn bm data, dinode_at γi (inum_of i) dn ∗ inode_blocks γfs bm data ∗
                 ⌜node_rep n dn data⌝)%I.
```
Composition: `fnode_excl` — one line from `dinode_at_excl`
(InodeRegion.v:567-573).  Determinacy: needs `node_rep_inj` (a pure
lemma, the analogue of `diblk_bytes_inj`, InodeRegion.v:45); this is
F1's one real proof obligation.

**(ii) EDGES — reuses `dir_links` verbatim; there is no separate edge
resource**

The landed ticket says *who is pointed at*, not who points:
`dir_link_at`'s payload is `ilink (dir_inum data k)` (DirLinks.v:77-85).
The `(source, name)` half is carried by the bytes, i.e. by
`fnode i (NDir ents)`.  So:
```coq
Definition fedges (i : Z) (dn : dinode) (data : _) : iProp Σ := dir_links i dn data.
```
and the **dangling edge is already formalized** as the grey disjunct
`igrey j ∗ ⌜di_nlink dn = 0⌝` (DirLinks.v:83-84, option (iii) landed at
B′).  Existing composition lemmas, all reusable as-is: insert
`dir_link_at_dirlink` (:322-331), self-insert
`dir_link_at_dirlink_self` (:360-370), frame `dir_links_dirlink`
(:234-254), no-op `dir_links_dirlink_nop` (:386-400), congruence
`dir_link_at_agree` (:193-197), and the open/close round trip
`dir_links_live` / `dir_links_of_ilink` (:459-466 / :502-508).

**Missing, and it is the algebra's inverse:** the delete constructor.
A zeroed slot's ticket collapses to `emp` and *releases* one `ilink`
(§20.6's sys_unlink row, fs-icache.md:4374).  No landed form exists.
See §6.

**(iii) DETACHED NODE — the one new resource**
```coq
Definition fdetached (i : Z) (ty : bv 16) : iProp Σ := iclaim_ty i ty.
```
built by widening the ledger's existing exclusive slot
`c : optionUR (exclR unitO)` (IcacheRef.v:288) to
`optionUR (exclR (leibnizO (bv 16)))`.  Exclusive by `iclaim_excl`
(IcacheRef.v:699-706); agreement by `link_claim_agree` (:681).
"`i ∉ t`" is then `fdetached i ty ⊢ ⌜indeg t i = 0⌝`, via
`link_claim_agree` + the new clause.  This is §7's "statable global
negative", and §3 works it in full.

**(iv) PATH SLICE and CLOSED COMPOSITION**
```coq
Definition fslice γi t i p j : iProp Σ :=
  (⌜path_at t i (path_elems p) = Some j⌝ ∗ [∗ list] (k,n) ∈ chain_of t i p, fnode γi k n)%I.
Definition fs_rep γi t : iProp Σ :=
  (([∗ map] i ↦ n ∈ fs_nodes t, fnode γi i n) ∗ ⌜fs_wf t⌝)%I.
```
The frame law `fs_rep (t1 ⊎ t2) ⊣⊢ fs_rep t1 ∗ fs_rep t2` on disjoint
node sets is `big_sepM_union` and costs nothing, because the node store
is a `gmap` and `dinode_at` is a `ghost_map` element.  **That is the CSL
dividend §3 promises, and it is genuinely free.**  Path-points-to (F4)
is `fslice` with a closed chain — §6's "closed-fragment special case",
confirmed.

**One arithmetic clause the relation must get right** (§20.9(g),
fs-icache.md:4576-4579): the ledger's `w i` is the count of live
**non-self** records naming `i`, so `w i = indeg_t i − (1 if i is a
directory, for its own ".")`, with `".."` records counted (they are
non-self and are paid for by mkdir's `dp->nlink++`).  `ents` includes
`"."`; the ledger does not.

## 3. THE ialloc → ilock SEAM

### 3.1 What the seam is today

| point | file:line | what crosses |
|---|---|---|
| the claim | InodeRegion.v:1442-1456 (`ireg_claim_au`) | **`True`** — literally, at :1456 |
| ialloc's post | SpecIalloc.v:280-292 | `inode_ref kslot q dev inum` + `log_op`, plus the **pure** `dn' = ialloc_fresh ty /\ di_type dn' = ty /\ fresh_shape dn'` — explicitly documentation-only, "says nothing about the region's state at RETURN time" (SpecIalloc.v:81-84) |
| ilock's post | SpecIlock.v:282, :325 | `filled : bool` + `⌜filled = true -> fresh_shape dn⌝`, out of `ireg_withdraw`'s own payout (InodeRegion.v:1715) |
| the gap | SpecCreateFreshTy.v:220-296 | `di_type dn = ty` (:269) and `filled := true`, assumed over the 4-instruction span +0xa4..+0xb0 |

### 3.2 What the claim already proves and throws away

`ireg_claim_au` derives, inside the invariant, at InodeRegion.v:1490-1491:
```coq
assert (Hw0 : wl = 0%nat) by exact (ireg_link_ok_free (ds !!! islot inum) wl Hlok Ht0).
```
**"No live directory record names the inum I am claiming" — i.e.
`inum ∉ t` — is already a theorem of the landed lemma.**  It is
discarded at :1537.  Recovering it is the tree's cheapest possible
dividend.

**But it cannot be recovered as a pure fact.**  `⌜w = 0⌝` at claim time
is a statement about the past the moment the fupd closes — §20.9(b)'s
death certificate verbatim (fs-icache.md:4543-4549: a persistent
per-inum allocatedness witness is dead on free-and-reclaim; the epoch
repair is §19.5(g)).  **Detachedness must be an exclusive resource or
nothing.**  This is the first sharp finding: there is **no cheap
intermediate increment** that pays out detachedness without the full
token.

### 3.3 The shape the token must take: §20.17.6's option (k), and the withdraw

The token must be exclusive — §20.9(j) (fs-icache.md:4595-4600): *"The
claim needs its own component, and it must be EXCLUSIVE (a counter would
let a second claim of the same inum through)."*  The algebra already has
the slot and all four moves (`link_mint_claim` IcacheRef.v:827,
`link_spend_claim` :838).

Adopt **option (k)** (fs-icache.md:5375-5390) — the clause on the BYTES,
not the arm:
```coq
(L5)  c = Some (Excl ty) -> di_type d = ty /\ bv_unsigned ty <> 0
```
and **do not state** §20.16.3's arm clause `c <> None -> inreg`.
Mover-by-mover, checked against the landed proofs:

| mover | file:line | (L5) survives? |
|---|---|---|
| `ireg_write_au` (ordinary flush) | InodeRegion.v:1312 | **free** — premise `di_type dn' <> 0` + `di_type_stable dn' dn` (:354-355) pins the type exactly |
| `ireg_write_link` | :1771-1779 | **free** — same two premises |
| `ireg_write_unlink` | :1904 | **free** — same shape |
| `ireg_claim_au` | :1442 | **free, and see §3.4** |
| **`ireg_withdraw`** | **:1703-1759** | **OWES NOTHING.**  Verified against the proof: the record is re-parked verbatim (:1744-1745, `list_insert_id`) and the ledger authority is re-parked at the *same* `wl gl cl rl` (:1755-1756).  The only thing it moves is the ARM, in-region → marker (:1740, :1757), and (L5) mentions no arm. |
| **`ireg_free_au`** | **:1578-1594** | **NO.  THE ONE WALL.**  It writes `di_type dn' = 0` (:1585), so (L5) demands `c = None` afterwards; setting an outstanding `Excl` to `None` is not frame-preserving without the fragment, and iput holds none. |

**Five of six movers are free.  The seam is one lemma wide.**  That is a
materially better position than §20.16 left, and it is the reason option
(k) is the right shape rather than §20.5's `(L2) c <> None →
fresh_shape d` (which is useless anyway: `fresh_shape` is *already*
ilock's payout at SpecIlock.v:325).

### 3.4 A NEW STEP: (L5) makes the claim SELF-MINTING, closing half of §20.5's circularity

§20.5 (fs-icache.md:4334-4343) derived the claim's mintability
(`c = None` at the claim instant) from (L3) *plus the free's new
obligation* — circular.  Under (L5) with its `ty <> 0` conjunct, it is
**direct**:

> `ireg_claim_au`'s own premise is `bv_unsigned (di_type (ds !!! islot
> inum)) = 0` (InodeRegion.v:1448).  Suppose `c = Some (Excl ty)`.
> (L5) gives `di_type d = ty` and `ty <> 0`, contradicting the premise.
> So `c = None` **at the authority**, no fragment is outstanding, and
> `link_mint_claim` (IcacheRef.v:827, `alloc_option_local_update`)
> applies.

No free-side obligation is needed to *mint*.  This is not in §20.5,
§20.16 or §20.17 and it is worth recording independently of whether
F1.5 lands.  It does **not** touch preservation.

### 3.5 The recycle / incarnation question, answered exactly

**A stale fragment from a previous life is not refuted — it is
unmintable, and the refutation lands at the free, not at the withdraw.**

Under (L5), suppose Q holds `fdetached i ty` from a claim, a stranger
frees `i` (type := 0), and a third thread re-claims at `ty'`.  The
re-claim needs `c = None`; Q's fragment forces `c = Some (Excl ty)`,
and (L5) at the freed record (`di_type = 0`) is already violated.  **So
no reachable state contains a stale fragment — provided the free
re-establishes the clause.**  Every burden of the design is therefore
concentrated at `ireg_free_au`, by construction.

Three substitutes are dead and must not be re-proposed:

- **A monotone generation/incarnation counter.**  §20.9(j): a counter
  lets a second claim through.  And a `mono_nat_lb` yields `n ≤ cur`,
  never `n = cur`, so the holder can never show its fragment is current
  — §19.5(g)/§20.9(b): *"the holder's proof that its epoch is current
  is exactly 'no free since', which is the goal."*
- **Reusing the existing generation `g`.**  It is keyed by itable
  **slot**, not inum (IcacheRef.v:236-237, :893-895), minted only by
  consuming the slot's whole unit (`live_gen_bump`, :994-1006), and
  **dropped at eviction** (`IcacheEscrow.ic_close_to_empty:1370`,
  comment :1392-1395).  It cannot key an inum's life.  `inode_ident` is
  explicitly disqualified for the same reason (IcacheRef.v:222-224).
- **Weakening (L5) to `di_type d = ty ∨ di_type d = 0`.**  Tempting (it
  makes the free free, and ilock's own `di_type <> 0` at
  InodeRegion.v:1711 would recover the equality).  It is **dead**: the
  re-claim then has to *change* an outstanding `Excl`, which is not
  frame-preserving — §19.5(f) case 1, and §19.7 (a resource may not
  forbid a machine-reachable step; a second `ialloc` is one).

### 3.6 The free's discharge — what the tree buys and where it stops

`ireg_free_au`'s caller is ProofIput's free path.  It must refute "the
inode I am freeing is somebody's claim box".  The record cannot do it:
§19.5(h)/§20.7 — **a truncated corpse IS `fresh_shape`**
(InodeRegion.v:322 vs iput's post-itrunc state).  So the discriminator
must be the reference.

The tree's contribution is to state the discriminator once, as `fs_rep`
adequacy: **every icache reference is justified by an edge of `t` or by
an owned detached fragment.**  Run §20.7's row-2 enumeration at a claim
box with licence (d) **now founded** by §3.4:

| licence | verdict at a claim box | evidence |
|---|---|---|
| (a) LINKED `ilink i` | **refuted** | `link_w_ge` (IcacheRef.v:665) ⇒ `w ≥ 1`; (L1) (InodeRegion.v:730) ⇒ `nlink ≥ 1`; the box has `nlink = 0` (`fresh_shape`, :326) |
| (c) HELD `dinode_at` | **refuted** | a claim box's fragment is IN the region (`ireg_in`, :652, left arm; re-parked at :1536); `dinode_at_excl` (:567) |
| (d) CLAIMED | **refuted** | `iclaim_excl` (IcacheRef.v:699) — create holds the unique token.  **Founded only under (L5).** |
| (e) BUFFERED | **refuted** | §20.7 row 2 — demands a type-nonzero read through the block ialloc's `log_write` just committed |
| (f) ROOT | **refuted** — *but the clause is not landed* | §20.4 charters `ireg_body` gaining `⌜di_nlink (m !!! ROOTINO) ≥ 1⌝` (fs-icache.md:4306-4307); `ireg_body` (InodeRegion.v:948-952) has no such conjunct.  **OWED.** |
| **(b) ORPHAN `igrey i`** | **THE RESIDUE** | `igrey` concludes nothing by construction: `link_mint_grey` is mint-from-nothing (IcacheRef.v:812), and §20.18 ruling 2 (fs-icache.md:5638-5643) accepts permanently that `g` can never again carry information |

Case (b) is closed only by §20.17.5's boxed enumeration
(fs-icache.md:5327-5329):

> *No reachable `iget` under a GREY licence reaches a WITHDRAW or a
> FREE via `namex`, `create` or `sys_link`.  The one residue is
> `sys_unlink`'s found arm, whose `ilock(ip)` IS a withdraw.*

— with namex's shelter already green at ProofNamex.v:3462, create's at
+0x2a/+0x2e, sys_link's by `valid = 0` (fs-icache.md:5319-5323), and
sys_unlink's by `isdirempty`, **which does not exist** (only
CodeSysUnlink.v; no SpecSysUnlink.v, no ProofSysUnlink.v).

**And here is where the tree stops.**  The enumeration is a fact about
*other threads' `iget`s*; §20.17.7 option (ii) (fs-icache.md:5448-5455)
established that nothing inside ProofCreate/ProofIput can see another
thread's `iget`, so *"the enumeration lives at SpecIget or nowhere"*.
But the licence is **borrowed and returned** at the `iget` (§20.4
:4281-4286; consuming it is §20.9(f), dead), so iput has no licence to
enumerate over.  §20.7's *"THE REFERENCE THAT OUTLIVES ITS LICENCE"*
(:4447-4451) is untouched by the tree.

**VERDICT (3).**  The tree layer:
- **founds licence (d)** (the token, mintable per §3.4) — real, new;
- **makes `inum ∉ t` statable** — real, and already proved inside
  `ireg_claim_au:1490`;
- **moves the obligation off the withdraw** (five of six movers free,
  §3.3) — real, and this is the escape from §20.16.3;
- **does NOT discharge `ireg_free_au`.**  What it changes is the
  residue's shape: from §20.16's "no carrier exists, stage E is dead"
  to **one premise, on one lemma, whose only unrefuted case is licence
  (b), whose closure is §20.17.5's already-verified enumeration plus
  one unwritten invariant (`isdirempty`) on an unwritten proof
  (`sys_unlink`), plus the unlanded root clause.**

### 3.7 The consumption shape at ilock — additive, and the precedent is landed

`ireg_withdraw` owing nothing (§3.3) is what makes this legal where
§20.16.5(e) was not.  Give SpecIlock an **option-indexed** input, not
an obligation:

```coq
(fr : option (bv 16)) ... (match fr with Some ty => fdetached inum ty | None => emp end) -∗
  ... post: ⌜fr = Some ty -> di_type dn = ty /\ filled = true⌝ ∗
            (match fr with Some ty => fdetached inum ty | None => emp end)
```

Eight of the nine `wp_ilock_sconf` consumers instantiate `None`/`emp`.
**§20.16.5(e) (fs-icache.md:5045-5048) killed an OBLIGATION the
withdraw owes on every firing; an option-indexed input is not one.**
The mechanical precedent is exact: `filled : bool` was retrofitted this
way in D₀ increment 1 (SpecIlock.v:118-135).

> **THE SINGLE MOST IMPORTANT DESIGN CONSTRAINT IN THIS REPORT:** if
> anyone adds the arm clause `c <> None → inreg` (L6) — which is
> tempting because it discharges the free in two lines from
> `dinode_at_excl` at InodeRegion.v:1618-1620 — **the withdraw
> immediately owes it back and the design collapses into §20.16.3
> verbatim.**  (L6) must never be stated.  The free's discharge has to
> come from the reference side, not the arm.

### 3.8 The axiom's deletion path

With F1.5c landed: LinkCreateFreshTy.v and SpecCreateFreshTy.v delete;
ProofCreate loses one functor hypothesis and gains four instructions
(+0xa4..+0xb0), exactly as SpecCreateFreshTy.v:85-86 predicts.  `ARM
C-OK-DIR`'s gate (`dirlink(ip,".")`'s `di_type dn = T_DIR` premise)
lifts at the same moment.  Nothing else in the axiom is load-bearing:
the two callee contracts are functor hypotheses
(SpecCreateFreshTy.v:193-219), so ProofIalloc/ProofIlock stay
load-bearing either way.

## 4. TWICE-INSTANTIATE AUDIT AND THE §20.16 GRAVEYARD CHECK

### 4.1 Twice-instantiate audit (the SpecCreateFreshTy.v:34-45 test)

The test's target is anything **assumed** — an `Axiom` or a module
`Parameter` — where two free variables are unrelated.  Instantiating a
*resource* at two values and deriving `False` is exclusivity, not
inconsistency.  Per proposed item:

| item | instantiate twice | verdict |
|---|---|---|
| `fnode γi i n` | `n₁ ≠ n₂` ⊢ `False` via `dinode_at_excl` (InodeRegion.v:567) | **correct** — an exclusive points-to, not an assumption. ✔ |
| `fedges` = `dir_links` | landed; nothing new assumed | ✔ |
| `fdetached i ty` | `ty₁ ≠ ty₂` ⊢ `False` via `iclaim_excl` (IcacheRef.v:699) | **correct and wanted** ✔ |
| **(L5) as a clause** | *cannot be instantiated by a client* — universally quantified inside `ireg_slot` over the single `c` the slot holds; `ty` is **determined by `c`**, not free | ✔ — **precisely the difference from the inconsistent form SpecCreateFreshTy.v:34-45 warns about**, where `ty` and `dn` were both free and unrelated.  The naive spelling of (L5) as a free-standing entailment `fdetached i ty -∗ ⌜di_type dn = ty⌝` **is** the inconsistent form. |
| `fs_rep γi t` | `t₁ ≠ t₂` must ⊢ `False`, else `fs_rep` is not a function of the resources | **owed**: needs `node_rep_inj`.  Provable the way `diblk_bytes_inj` (InodeRegion.v:45) is. ✔ once proved |
| `fslice` / path-points-to | derived, no new ghost | ✔ |
| `dir_view` (pure) | function of `data`, which is itself a function | ✔ — *but see §1.2's duplicate-name trap, a soundness bug of a different kind* |

**No proposed item introduces a new `Axiom` or `Parameter`.**  The
audit is clean.

### 4.2 The §20.16-graveyard check, device by device

**(a) Licence (d) CLAIMED** — struck at §20.16.4 (fs-icache.md:4991-4993)
because `ireg_claim_au` pays `True` and nothing mints an `iclaim`.
→ **The tree-founded version IS this device, revived.**  Being honest
about that is the point.  What is genuinely different: §20.5's
mintability argument was circular (needed `c = None` from the free's
obligation); under (L5)'s `ty <> 0` conjunct **mintability follows from
the clause itself at a type-0 record** (§3.4).  That is the only new
thing, and it is checkable.  **(d) is founded for MINTING and still
unfounded for PRESERVATION.  Do not overclaim.**

**(b) The claim token vs the grey colour** — §20.16.4's "you may have
either, not both" (:4979-4984) was downgraded by §20.17.6 (:5398-5403)
on the fixed binary: the obligation is **UNDISCHARGED, not FALSE**.  So
the tree version is not a proof of a false proposition — but it
inherits the undischarged obligation intact.  **It does not reduce to
the struck device, and it does not escape it either.**

**(c) Guarding the clauses by `g = 0`** (§20.16.5(d), :5039-5043) —
**FORECLOSED PERMANENTLY** by §20.18 ruling 2 (:5638-5643): the free
grey mint (`ireg_link_grey`, InodeRegion.v:2126; `link_mint_grey`,
IcacheRef.v:812) means `g` can never again carry information.
**Checked: the proposed design uses `g` as a discriminator nowhere.** ✔
It must stay that way.

**(d) (M1), the reference counter `r`** (§20.16.5(c), §20.17.8) — dead.
→ **The tree's adequacy clause does NOT reduce to M1's arithmetic**: M1
was an `auth nat` count coupled to the itable's `M` under the itable
lock; the tree's version is a per-reference *owned justification*, no
counting, no lock coupling.  **But it lands on the same wall for a
different reason**: the justification is borrowed at `iget` and
returned (§20.4 :4281-4286), so it is not held at `iput`.  Different
mechanism, same obstruction.  State both halves.

**(e) A licence premise on `ireg_withdraw`** (§20.16.5(e), :5045-5048)
— dead at the call site: namex `ilock`s the child *after*
`iunlockput(parent)`.
→ **The tree-founded version does NOT reduce to it**, and this is the
design's one clean escape.  §20.16.5(e) killed an **obligation the
withdraw owes on every firing**; under (L5) the withdraw owes nothing
(verified against InodeRegion.v:1740-1757), so create's fact arrives
through an **option-indexed input** that eight of nine callers
instantiate at `emp` (§3.7).  **Conditional on (L6) never being
stated** (§3.7's boxed constraint).

**(f) (M2), a generation bump at the free** (§20.16.5(b)) — dead.  Not
used; §3.5 records why every temporal/monotone carrier is dead
independently (§20.9(b), §19.5(g)).

**(g) `ireg_claim_au` paying out `dinode_at`** (§20.16.5(f),
:5050-5056) — dead on the marker's uniqueness (the marker for an
uncached inum is in the pool, behind the itable spinlock ialloc does
not hold).  Not used: `fdetached` is a ledger fragment, not the record.

**(h) §20.9(c)/(d)/(e)** — no new authority, no authority parked with
the record, no new gname. ✔ (L5) widens an existing component of
`linkElemUR` (IcacheRef.v:288).

**(i) §20.9(f)** — the licence stays borrowed. ✔

**(j) §20.9(h)/(i)** — the grey disjunct stays; `fs_rep`'s edge clause
is literally `dir_link_at`. ✔ (and see §1.4's consequence).

**(k) §20.18 ruling 1** (fs-icache.md:5630-5637) — stage C's read rows
are STRUCK from create's critical path; **SpecDirlink carries no
`dir_links` and MUST NOT gain one**.  Verified independently:
`ilink`/`igrey`/`dir_links`/`dir_link_at` appear in SpecDirlink.v only
in prose (:375-382); the contract is byte-level and the ledger move is
caller-side.  **The tree layer must state the algebra caller-side
too.** ✔ — also the single largest price saving (§5).

## 5. PRICE AND STAGING

### 5.1 The byte-stability constraint, and where it is achievable

Design constraint: the `_sconf` seals must stay byte-stable, per §3's
insulation argument and `wp_writei_sconf`'s precedent.  Verified per
seam:

| seam | moves? | why |
|---|---|---|
| `wp_dirlink_sconf` / `_gen` | **NO** | §20.18 ruling 1; deposit is caller-side via `dir_links_dirlink` |
| `wp_namex_*`, `wp_nameiparent_*`, `wp_dirlookup_*` | **NO** | same ruling; option (i)-lite was rejected at §20.17.7 (4 contracts, 3 landed proofs incl. ProofNamex) |
| `wp_iput_*`, `wp_iunlockput_*` | **NO** for F1a/F1b/F1.5b | they carry no ledger fragment at all (verified: no `ilink`/`igrey`/`dir_links` anywhere in either file) |
| `wp_ialloc_gen` / `_sconf` | **MOVES** at F1.5c | payout is unconditional on the success arm; the sconf twin is derived from the gen one (SpecIalloc.v:301-316), so both move.  5 consumer files, 3 of which are the axiom's own and delete. |
| `wp_ilock_sconf` | **MOVES** at F1.5c | new option parameter; 9 consumer files, 8 at `None`.  Same shape as the landed `filled` retrofit (SpecIlock.v:118-135). |
| `wp_iupdate_*` (3 bodies) | **MOVES** at F1.5d only | `ireg_free_au`'s premise ripples through SpecIupdate.v.  **Defer.** |

**Byte-stability is achievable at every seam except SpecIalloc and
SpecIlock, and at those two the move has a landed precedent.**  The
expensive seam (SpecIupdate) is entirely inside the gated increment.

### 5.2 File-by-file estimate (GR-style)

| file | change | lines | reopens? |
|---|---|---|---|
| **NEW FsTree.v** (pure, iris-free; DirView.v's precedent) | `fsnode`, `fstree`, `dir_view` (first-match), `node_rep`, `node_rep_inj`, `path_at`, `fs_wf` | ~400 | no |
| **NEW FsRep.v** (above DirLinks.v, requires InodeRegion + DirLinks) | `fnode`, `fedges`, `fslice`, `fs_rep`, the frame law, `fnode_excl` | ~350 | no |
| DirLinks.v | `dir_links_unlink` (the delete constructor) + its `dir_link_at` half | ~120 | no (zero consumers today) |
| IcacheRef.v | widen `c` to `optionUR (exclR (leibnizO (bv 16)))`; re-thread `lelem`, `link_auth`, `iclaim`→`iclaim_ty`, `link_claim_agree`, `iclaim_excl`, `link_mint_claim`, `link_spend_claim` | ~150 edited across :288-870 | **F1.5c** |
| InodeRegion.v | (L5) in `ireg_link_ok`; re-thread the `cl` existential through the 6 movers; mint at :1442; read at :1703 | ~200 | **F1.5c** |
| IcacheBoot.v | the IOU mints `c = None` per inum | ~30 | **F1.5c** |
| SpecIalloc.v | post gains `fdetached inum ty`; both forms | ~40 | **F1.5c** |
| SpecIlock.v + 9 callers | option-indexed premise/post; 8 callers at `None` | ~60 + 9×~5 | **F1.5c** |
| SpecCreateFreshTy.v, LinkCreateFreshTy.v | **DELETE** | −640 | **F1.5c** |
| ProofCreate.v | one hypothesis out, four instructions in | ~150 | **F1.5c** |
| SpecIget.v + 4 call sites, SpecIupdate.v (3 bodies), ProofIput.v | the adequacy clause + `ireg_free_au`'s premise | **unpriced** | **F1.5d — gated** |

`ireg_slot` is named in only four files (IcacheRef.v, IcacheBoot.v,
InodeRegion.v, SpecIalloc.v), which is why the (L5) sweep is bounded.

### 5.3 Staging table (§14.4's form), each increment independently gated

| stage | what lands | files | gate | independently correct? |
|---|---|---|---|---|
| **F1a** | the pure tree type, `dir_view` (first-match!), `node_rep`, `node_rep_inj`, `path_at` | FsTree.v (new) | none | **YES** |
| **F1b** | `fs_rep` as a reading over `dinode_at` + `dir_links`; the frame law | FsRep.v (new) | F1a | **YES** |
| **F1.5b** | the edge-DELETE constructor (the algebra's inverse) | DirLinks.v | none | **YES** — owed to S7, lands ahead of it, zero consumers today |
| **F1.5c** | (L5), `fdetached`, the mint, the option-indexed read at ilock, **the axiom deletes** | IcacheRef, InodeRegion, IcacheBoot, SpecIalloc, SpecIlock + 9, ProofCreate; 2 files deleted | **F1.5d** | **NO** |
| **F1.5d** | `ireg_free_au`'s `c = None` | SpecIget + 4 sites, SpecIupdate, ProofIput | §20.17.5's residue (`isdirempty`, needs S7) **+** the unlanded root clause **+** C′'s `iname`; **or** the fs-icache §20.17.7 kernel fix | **NO** |
| **F2** | path resolution as tree lookup | — | F1b, **and see §5.4** | conditionally |

**Recommendation: F1a, F1b, F1.5b are unconditional, additive, and
reopen nothing.  Do not start F1.5c until F1.5d's gate has a door.**
The two doors are unchanged from §20.17.7 (fs-icache.md:5517-5522):
the kernel fix (`ialloc`'s `brelse` after its `iget`), or a refutation
at the free.

### 5.4 A correction to fs-friendly's F2 row

§4's table says F2 is "the namex trio's specs re-derived as an `fs_rep`
lemma".  **That is not achievable as written.**  SpecNamex.v:113-124
rules explicitly that the postcondition is resource-shaped and there is
**no path → inode functional statement**, because each `dirlookup` is
atomic under its own lock and no stable global tree exists between
iterations.  F2 must therefore be a **logically-atomic triple whose
linearization point is a single `dirlookup` under one lock**, not a
re-derivation of namex's post.  §1.4's finding (`fs_rep` is unholdable
by any thread) says the same thing from the resource side.

## 6. WHAT sys_unlink TEACHES AND DEMANDS

sys_unlink **does not exist**: only CodeSysUnlink.v (decode).  No
SpecSysUnlink.v, no ProofSysUnlink.v.

**What it teaches — detachment is the algebra's inverse, and the region
half is already built and unused.**  `ireg_write_unlink`
(InodeRegion.v:1904-1934) is the only nlink-lowering region write and
it **CONSUMES one `ilink`** as it lowers, via `link_w_ge` then
`link_spend_link` (:1970, :1989; IcacheRef.v:762 is the only lowering
move in the algebra).  It has **no caller**.  The missing half is on
the DirLinks side: nothing releases the ticket out of a zeroed record.
**That asymmetry — insert has a full resource story, delete has only
the refcount half — is the single clearest statement of why F1.5b is
owed, and it can land ahead of S7.**

**What it demands of the tree design:**

1. **§20.17.4's owed fact, and the tree pays for it directly.**  S7
   cannot perform the grey conversion without knowing *which* `ilink
   dp` to convert; the only one is inside `ip`'s `dir_links` at `ip`'s
   `".."` index, and **the model has no fact placing it**
   (fs-icache.md:5270-5280: *"§20.6's preservation table quietly
   assumes it and nobody had noticed"*).  In the tree that fact is
   **free**: it is `ents ip !! ".." = Some dp`, a conjunct of
   `fnode ip (NDir ents)`.  **This is the clearest single place where
   the tree layer pays for itself, and it should be the headline of
   F1b's brief.**
2. **The `isdirempty` invariant** — an orphaned directory has no live
   record but `"."` and `".."`, and sys_unlink refuses both by
   `namecmp`.  This is simultaneously §20.6's itrunc-row obligation
   (fs-icache.md:4383-4390) and **the closure of §20.17.5's residue,
   i.e. F1.5d's gate.**  It goes into S7's brief as a *prerequisite of
   the axiom's retirement*, not a local convenience.
3. **C4** (§20.18 ruling 4): the SpecLogWrite AU wand for the
   nlink-lowering flush stays **PROBE-FIRST**.  Orthogonal to shape.

**What to leave open until it lands:**

- **Do not decide whether `t` records `".."` explicitly or derives
  it.**  §5 Q2's answer is forced by whichever fragment S7's conversion
  consumes, and S7 does not exist.  Record `".."` in `ents`
  provisionally (§1.1's reasons 3 and (g)-consistency), and mark the
  clause "S7 may sharpen".
- **`link_grey_of_link` (IcacheRef.v:777) has no caller.**  Today the
  only grey producer is the *free mint* (`link_mint_grey`, :812), so
  the tree's dangling edge currently arises only from nothing.  Once S7
  lands, the conversion path becomes live and the dangling-edge
  fragment gains a second, evidence-bearing provenance.  Do not build
  anything on the current provenance.
- **The ledger dimension stays outside the algebra.**  §6's honesty
  check is confirmed against the code: SpecDirlink's credit machinery
  (`dl_spend`/`dl_need`/`dl16_post`, SpecDirlink.v:241-325, :402-418)
  is byte-level accounting orthogonal to shape, and SpecIput's
  `crz`/`nlz_obs` group credit likewise.  **The fragment layer must not
  attempt to hide either; only F3's syscall boundary can.**

## One-line summary

F1 is a reading and should be built (F1a, F1b, F1.5b — all
unconditional).  F1.5's detached fragment is sound in shape, escapes
the `ireg_withdraw` graveyard cleanly via option (k) plus an
option-indexed premise, and is now self-minting (a new step) — but it
is **all-or-nothing with the type clause, and the type clause is gated
on `ireg_free_au`'s `c = None`**, whose only unrefuted case is licence
(b) grey and whose closure needs `isdirempty` (S7, unwritten), the root
clause (unlanded), and SpecIget's licence (C′) — or the §20.17.7 kernel
fix.  §7's "refactor, not campaign" is achieved for the shape half
only; the type half is one lemma wide — a much better position than
§20.16 left, but not free.
