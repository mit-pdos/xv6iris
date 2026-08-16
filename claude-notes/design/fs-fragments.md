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
    root clause (LANDED, see R9), and SpecIget's licence enumeration (C′)
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
    - ~~the ROOT clause~~ — **LANDED and RATIFIED** (coordinator,
      2026-08-15: the form and home moves are both forced — the
      chartered body-form is unpreservable at `ireg_write_unlink`, and
      strictness names `w`, which lives only at the slot; the
      claim/free REFUTATIONS falling out as theorems exceed the
      charter).  `ireg_slot` (not `ireg_body`) carries
      `ireg_root_ok z d w := z = ireg_root -> w < di_nlink d`, (L1) MADE
      STRICT at the root, with §20.4's `di_nlink ≥ 1` as its projection
      `ireg_root_ok_alive`.  The chartered form is unpreservable at
      `ireg_write_unlink` and strictness is what the root's structural
      slack of one (its `"."`/`".."` are self-records no `dir_links` unit
      is filed against) buys; see the campaign ledger for the mover table.
    - `isdirempty`'s invariant goes into S7's brief as a PREREQUISITE
      of create_fresh_ty's retirement, not a local convenience.
    - the `".."`-location fact (`ents ip !! ".." = Some dp`) is F1b's
      headline dividend — §20.17.4's owed fact, free as a conjunct of
      `fnode ip (NDir ents)`.

R13 (2026-08-15, C′ RULINGS — the C′ verification report is the design
     of record for the licence enumeration; **it is now TRANSCRIBED at
     §7.1 below**, together with the six other probes' death
     certificates (§7).  The former pointer — "find it in the
     coordinator session's task output and its content mirrored in
     fs-fragments-campaign.md's C′ entry" — was dangling: no such entry
     ever existed, and four probes' findings lived only in prompts.
     See §7's preface):
     (i) C′'s indexed form (ilic/iname, borrowed-and-returned at the
     SAME l, IgetLic.v leaf home, licence (e) as the fsblock half NOT
     bio_locked) is ADOPTED as designed.
     (ii) §20.18 ruling 1 is AMENDED: "no dir_links OBLIGATION at
     dirlink/dirlookup; a ticket list borrowed over the PRE-state and
     returned verbatim on both arms is admissible" — the re-park
     objection and the +0x128 ordering are untouched by a borrow.
     (iii) K-F2 (the ialloc brelse-after-iget kernel fix) is REJECTED
     (user, 2026-08-15: "roll back kernel change — one reason we are
     going for the tree representation is that we can see this inum
     isn't in the tree yet").  The invisibility licence for ialloc's
     window comes from the TREE (the §7 founding ruling: inum ∉ t /
     the detached fragment), not from a kernel reorder; the kernel is
     correct as-is and only bug fixes go upstream.  C′ therefore waits
     for the tree route to mature rather than landing behind a kernel
     edit; formerly-K-F2-parked — kernel changes are the user's; the writeup is ready
     (three lines, founds ialloc's iget, closes the ireclaim boot-only
     hazard structurally, enables the escort route). C′ EXECUTES ONLY
     AFTER K-F2 lands and its bump cycle completes.
     (iv) The ESCORT-PROBE (§6.4's route to ireg_free_au's discharge —
     the first non-dead candidate) is QUEUED as a design-only pass
     behind K-F2 + C′.
     (v) R7 STANDS: F1.5c does not start — the report's own finding is
     that the gate does not open when C′ lands; the door is the free,
     and the escort is its first honest key.
     (vi) The S7-PLANK (the strong isdirempty payload conjunct) is
     independently correct NOW (true of f60ff58) and is assigned to
     the in-flight payload-conjunct pass (same home, same movers as
     dir_dots_ix).

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

> **FALSE AS WRITTEN (corrected 2026-08-16, per TRACE G — §7.5.4).**
> The entailment `fdetached i ty ⊢ ⌜indeg t i = 0⌝` is **not sound**.
> The bridge runs through the arithmetic clause below, and that clause
> omits grey; `w` counts only *paid* records, while a grey edge raises
> `indeg` and not `w`.  In trace G, `indeg_t a ≥ 1` (the orphan `b`'s
> live `".."` record names `a`) while `w a = 0`, and `a` is then freed
> and re-`ialloc`'d as a claim box — so `fdetached a ty` holds with
> `indeg t a ≥ 1`.  What `fdetached` actually entails, and all it
> entails, is **`w i = 0`** — which is already a theorem at both ends
> (`Hw0` inside `ireg_claim_au` and inside `ireg_free_au`) and is
> therefore *not* the statable global negative §7 wanted.  The
> corrected form is
>
> ```coq
> fdetached i ty ⊢ ⌜w i = 0⌝              (* landed, both ends *)
> fdetached i ty ⊢ ⌜indeg_live t i = 0⌝   (* in-edges out of LIVE nodes only *)
> ```
>
> i.e. **no edge of `t` out of a live node names a claim box** — proved
> from the ledger (a live non-self record forces `ilink`, `link_w_ge` ⇒
> `w ≥ 1`, (L1) ⇒ `nlink ≥ 1`, and a claim box has `nlink = 0` by
> `fresh_shape`), never from `t`.  In-edges out of ORPHANS are exactly
> the residue, they are exactly the grey edges, and each orphan
> contributes exactly one (its `".."`).  **F1.5c depends on the
> uncorrected form; it must be re-derived against the corrected one.**

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

> **CORRECTED 2026-08-16 (§7.5.4, trace G): THAT EQUATION OMITS GREY,
> and the omission is what makes §2(iii)'s global negative false.**  A
> grey edge — an out-edge of an ORPHANED directory — contributes to
> `indeg_t` and contributes **nothing** to `w`, because
> `dir_link_at`'s grey disjunct files no `ilink` (`DirLinks.v:77-85`).
> The correct clause carries a second correction term, and under
> `dir_orphan_clean` (now landed in both payloads — §7.8) it has a
> closed form:
>
> ```
>   w i  =  indeg_t i
>           −  [ i ∈ dirs ]                                  (* i's own "." *)
>           −  #{ j : j is an ORPHANED directory of t with ".." → i }
> ```
>
> The second correction is bounded by **one edge per orphan**, because
> an orphan has no live records but its two dots (`dir_orphan_clean`),
> its `"."` is a self-record the ledger already exempts, and its `".."`
> always names its parent (§7.5.8's ORPHAN-SET vocabulary).  The
> `sys_unlink` `dp->nlink--` conversion (`link_grey_of_link`) is exactly
> the mover that transfers one unit from the first term to the second.
> **This is a defect in the design of record that F1.5c's `fdetached`
> depends on; correct it before F1.5c is re-opened.**

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
| (f) ROOT | **refuted**, and the clause is LANDED | `ireg_slot` carries `⌜ireg_root_ok z d w⌝` = (L1) strict at the root; a claim box has `di_nlink = 0` (`fresh_shape`), and `ireg_root_ok_ne` / `InodeRegion.ireg_root_ne` turn that into `z ≠ ROOTINO`.  The mover-level dividend is stronger than the row asks: `ireg_claim_au` and `ireg_free_au` REFUTE the root outright, so no claim box is ever at ROOTINO in the first place. |
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

---

## 7. THE DEATH CERTIFICATES

STATUS: transcribed 2026-08-16 from seven report-only probes of
`create_fresh_ty`'s retirement (the C′ design report, the first
retirement pass, the span-stability probe, the harmlessness probe, the
record-backed-greys/tree-leverage probe, the synthesis probe, and the
ownership-transfer probe).  Nothing below was built; no file was touched
and no build was run by any of the seven.

**Why this section exists.**  The fifth and sixth probes both opened
with the same ledger finding, and it is the reason for the transcription:
R13 above says C′'s content is "mirrored in fs-fragments-campaign.md's
C′ entry" — **there was no such entry**, and there was no record
anywhere in `claude-notes/` of the harmlessness, birth-certificate,
record-backed or escort probes.  Four probes' findings existed only in
prompts, and each successive probe re-derived them.  The notes' own
discipline ("death certificates so nobody re-proposes") was being
defeated by rulings that outlived their arguments.  **The map of walls
is the asset.**

**CORRECTION, standing, and it applies to every line reference in §§0–6
above as well as to the ones below: the notes' line numbers for
`InodeRegion.v` are STALE by ~140 lines throughout §16/§19/§20 of
fs-icache.md and in places here.**  Verified current homes:
`ireg_claim_au` at `InodeRegion.v:1586` (not `:751`/`:1442`),
`ireg_free_au` at `:1734`, `ireg_withdraw` at `:1869`, `ireg_slot` at
`:1049-1054`, `fresh_shape` at `:322`, `ireg_in` at `:781`,
`ireg_inv` at `:1094`.  **Do not trust a line number in these notes
without re-grepping.**  Where a probe below cites a line, it cited it
against the tree it read (`c105ad60` / `3e8d4c3e`); treat the *name* as
load-bearing and the *number* as a hint.

### 7.0 THE FIVE NAMED WALLS — index

Every route below terminates at one of five walls.  They are the
section's actual content; the per-probe subsections are the derivations.

| wall | one-line statement | first named by |
|---|---|---|
| **THE CLAIM'S HORIZON** | Every discharge of `c = None` at the free requires `ireg_claim_au` to re-verify the coupling that makes the discharge sound — i.e. to verify the ABSENCE of the freer's receipt.  The claim sees only its own region slot and the dinode block's bytes.  The record and the arm are inside the horizon and are dead ((L2)/(L6)+R5).  Everything that can discriminate a box — the licence, the reference, the entry, the occupancy, the marker — is outside it. | the synthesis probe (§7.6) |
| **THE CONSERVATION LAW** | The region holds exactly one of {fragment, marker} per inum; both tokens are minted once at boot (`IcacheBoot.v:570`, one `ghost_map_alloc (ireg_M0 dss nib ∪ ireg_MK nib)`) and thereafter only moved.  The claim has nothing to deposit, so the free has nothing to withdraw, and the fill has nothing to conclude. | the ownership-transfer probe (§7.7) |
| **THE CURRENCY GAP** | Between `ialloc`'s `brelse` and `ialloc`'s `iget` the claimant holds *nothing revocable* — no buffer fraction, no reference, no fragment, only a ghost token — and it can be preempted there arbitrarily long.  Any epoch/generation repair fails at the consumer, because currency needs a revocable, reference-tied resource. | the first retirement pass (§7.2) |
| **BORN BEFORE THE ENTRY** | The claim box is created *before* the cache entry exists (`iget` mints the generation afterwards), so no `g`-keyed, `k`-keyed or deposit-keyed proposition can be an invariant of the claim box; and a fixed per-inum keying dies at the opposite end (a one-shot cannot be re-shot at a second type). | the harmlessness probe (§7.4) |
| **TRACE G** | A live directory record naming a claim box is REACHABLE on the pinned binary: an orphaned directory pinned open by a third process keeps a live `".."` naming its parent, the parent is then rmdir'd, freed, and re-`ialloc`'d.  Record-backing removes the grey licence's *mintability*, not its *satisfiability at a claim box*. | the record-backed probe (§7.5) |

To which the earlier, already-recorded walls still apply unchanged:
§20.16.3/§20.16.5(e) at `ireg_withdraw` (R5's ban on (L6)), §19.7 (a
resource may not forbid a machine-reachable step), §20.9(b) (a
persistent per-inum allocatedness witness is dead on free-and-reclaim),
§16.5 (the packaging gap: `ci` lives in the itable spinlock's resource
and no fupd can open it).

---

### 7.1 C′ — the SpecIget licence enumeration (the design report)

Verified against `c105ad60` with `XV6_REV = f60ff58`.  **This is the
design of record R13 refers to.**  It is a *verification* report, not a
death certificate: C′ is buildable.  Its finding is that the gate does
not open when it lands.

#### 7.1.1 The enumeration's form — an INDEX, not an ∃

```coq
(* iris/IgetLic.v -- NEW; requires InodeRegion, IcacheRef, FsBlocks, DinodeEnc.
   Home chosen for IregLinkNz.v's reason: InodeRegion.v carries ~350
   dependents and an additive definition inside it costs that cone on every
   iteration.  Fold back at a milestone. *)

Inductive ilic := LinkedL | GreyL | HeldL | ClaimL | BufL | RootL.

Definition iname `{!riscvGS Σ, !iregG Σ, !icacheG Σ, !fsLogG Σ, !diskGhostG Σ}
    `{ICFG : icfg}
    (γi : gname) (γfs : fs_names) (inum : bv 32) (l : ilic) : iProp Σ :=
  match l with
  | LinkedL => ilink (bv_unsigned inum)                              (* a *)
  | GreyL   => igrey (bv_unsigned inum)                              (* b *)
  | HeldL   => (∃ d, dinode_at γi inum d ∗
                     ⌜bv_unsigned (di_type d) <> 0⌝)                 (* c *)
  | ClaimL  => iclaim (bv_unsigned inum)                             (* d *)
  | BufL    => (∃ ds : list dinode,                                  (* e *)
                  fsblock γfs (iblk_of (bv_unsigned inum)) (diblk_bytes ds) ∗
                  ⌜diblk_wf ds⌝ ∗
                  ⌜bv_unsigned (di_type (ds !!! islot inum)) <> 0⌝)
  | RootL   => ⌜bv_unsigned inum = ireg_root⌝                        (* f *)
  end%I.

Global Instance iname_timeless γi γfs inum l : Timeless (iname γi γfs inum l).
```

Three properties the index buys that the ∃ form does not: the case list
is closed at the type level (`destruct l` is exhaustive by
construction); every call site documents WHICH licence in its own
`iApply` line, checkable by `grep`; and §20.17.5's box becomes a
mechanically auditable proposition — *no site in the tree instantiates
`GreyL`* — which today is a paragraph and under C′ is a grep.

Keep **all six** constructors including `ClaimL`, even though nothing
can mint an `iclaim` until F1.5c: the constructor costs nothing, §20.4's
numbering survives, F1.5c becomes a pure "found (d)" step with no
signature move at SpecIget, and R11's honesty marker stays visible in
the source.

#### 7.1.2 The contract's shape — borrowed, returned, on both arms

```coq
Definition wp_iget_sconf_body … (γi : gname) … (dev inum : mword 32)
    (l : ilic)                                        (* <- NEW, one binder *)
    … :=
  …
  iref_slot -∗
  iname γi γfs inum l -∗                              (* <- NEW premise     *)
  wp_next b p (fun CID =>
    ∀ (mr : regfile) (k : nat) (q : Qp),
      … ⌜callee_saved m mr /\ (k < NINODE)%nat /\ mr !!! a0 = ientry k⌝ -∗
      inode_ref k q dev inum -∗
      iname γi γfs inum l -∗                          (* <- NEW, SAME l     *)
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).
```

Two load-bearing constraints: **the post must return the licence at the
SAME `l`** (a `∃ l'` post is sound but silently permits a licence swap
and destroys the per-site documentation the increment exists for); and
`ProofIget` spends it on nothing — one `iFrame` on each of the hit and
recycle arms, dropped on the diverging `panic("iget: no inodes")` arm.

#### 7.1.3 The one real improvement over §20.4's sketch: licence (e) is a `fsblock` half

§20.4 wrote (e) as `bio_locked`-on-IBLOCK.  **Do not.**  That drags
`BioInv` into `SpecIget`'s cone and forces two new binders.  The right
resource is one level down and is *stronger* evidence:
`FsBlocks.fsblock γ bno bs := bno ↪[fs_L γ]{#(1/2)} bs`.  The region's
invariant holds one half per block (`ireg_blk`); the buffer holder holds
the other and extracts it in one line with `ProofIupdate.iu_held_L`,
which returns a wand to put it back.  Because the element sits at ½+½, a
client holding one half means **no other client holds any** — so while
`ireclaim`/`ialloc` holds it, no `ireg_write_au` / `ireg_claim_au` /
`ireg_free_au` at *any* inum of that block can fire.  That is §16.2's
serialiser as a resource fact rather than a paragraph.

**Net: SpecIget gains one binder (`l`), one premise, one post conjunct,
and no new require beyond the tiny `IgetLic.v`.**  This is R13(i)'s
ruling, and it is the single largest price saving in the increment.

#### 7.1.4 The reading lemmas, and the shape they must NOT take

| reading | source | cost |
|---|---|---|
| `LinkedL` ⇒ allocated | `IregLinkNz.ireg_link_nz` / `InodeRegion.ireg_link_alloc` — landed | 0 |
| `HeldL` ⇒ allocated | definitional | 0 |
| `RootL` ⇒ allocated | `ireg_root_ok_alive` (the landed root clause) + (L3)'s contrapositive; first consumer of the root clause | ~10 lines |
| `BufL` ⇒ allocated | `ireg_read_blk`'s pattern + `diblk_bytes_inj` | ~40 lines, owed to F1.5d |
| `ClaimL` ⇒ allocated | needs (L5); not available at C′ | F1.5c |
| `GreyL` | concludes nothing, by construction (§20.18 ruling 2) | — |

**STANDING CONSTRAINT (the `SpecCreateFreshTy.v:34-45` test, applied
here).**  Every reading must be an **accessor over `ireg_inv`** that
names the record by opening the region — `ireg_link_nz`'s shape.  A
free-standing entailment `iname γi γfs inum l -∗ ⌜di_type dn <> 0⌝` with
`dn` free is the inconsistent form the axiom's own header warns about,
verbatim.  Write it in the accessor shape or not at all.

#### 7.1.5 THE CIRCULARITY, stated as a theorem

> **Theorem.**  Any region clause strong enough to found licence (d) is
> a clause `ireg_free_au` must re-establish.
>
> *Proof.*  To mint `iclaim z` the authority's slot must be `None`
> (`link_mint_claim`, `alloc_option_local_update`).  `ireg_claim_au`'s
> only handle on the record is its own premise
> `bv_unsigned (di_type (ds !!! islot inum)) = 0`, plus, through (L3),
> `di_nlink = 0`.  So the clause must have the form
> `di_type d = 0 -> c = None` (or the `nlink` twin).  `ireg_free_au`
> writes `di_type dn' = 0` — and, by `di_nlink_stable`,
> `di_nlink dn' = 0` — so it must re-establish exactly `c = None`, which
> it cannot do without consuming an `iclaim` it does not hold.  ∎

Corollary: **C′ with (d) instantiated ⟺ F1.5c ∧ F1.5d.**  They are one
increment, and it is the walled one.  C′ with (d) never instantiated is
separable, and (d)'s only would-be instantiation is `ProofIalloc`'s
`iget`.

#### 7.1.6 The residue after C′ — the ordering wall is untouched

At `ireg_free_au`, iput holds `dinode_at γi inum dn` (nlink 0),
`ic_loaded`, REF-1 on entry `k`, and (post step-4) the whole outstanding
sleeplock share of slot `k`.  It holds **no licence**: the licence was
borrowed and returned at an `iget` that happened in some other function,
possibly on another thread, arbitrarily long ago.  §20.9(f) forbids
consuming it; §20.17.7 option (ii) forbids seeing it from inside
`ProofCreate`/`ProofIput`.

> **DEATH CERTIFICATE (C′ as a discharge).**  *§20.7's "the reference
> that outlives its licence" is untouched: the licence is returned at
> the `iget` and iput holds none.  C′ is NECESSARY AND NOT SUFFICIENT.*

What C′ *does* change is that the enumeration exists, is closed, and is
minted from somewhere — and §20.17.7 option (ii) already proved there is
nowhere else to mint a carrier.  C′ is on the critical path of **every**
surviving route to F1.5d while discharging none of it.

#### 7.1.7 NEW FINDING — §20.17.5's box is too narrow: the licence-(e) route

§20.17.5 says *"No reachable `iget` under a GREY licence reaches a
WITHDRAW or a FREE."*  **The colour is not the only carrier of the
hazard.**  `ireclaim` igets exactly when `dip->type != 0 &&
dip->nlink == 0` — which is precisely a claim box (`ialloc_fresh ty`:
type ≠ 0, nlink 0).  The trace, every step stock code and landed
contract:

1. `ialloc` claims inum: `memset`, `dip->type = ty`, `log_write`,
   **`brelse`** — the claimant now holds nothing;
2. `ireclaim` breads the block, sees type ≠ 0 ∧ nlink = 0, `iget`s
   (fresh entry, ref 1, valid 0), `brelse`;
3. `begin_op(); ilock(ip)` — **this is an `ireg_withdraw` at the claim box**;
4. `iunlock; iput` at REF-1 with nlink = 0 — **this is `ireg_free_au`**,
   whose `c = None` is FALSE there.

Under (L5) the invariant is *unpreservable* on that trace, not merely
undischarged.  It is excluded only by reachability: `ireclaim` is called
only from `fsinit`, called only from `forkret`'s `first` branch, i.e.
before `kexec("/init")` and before any second process exists.  That is a
boot-order fact the model states nowhere.

**Consequences.** §20.17.5's box must be widened to *"no `iget` under a
GREY **or BUFFERED** licence reaches a withdraw or a free"*, and (e)'s
shelter named as the boot-only argument.  §20.7 row 2's (e) refutation
is *instant-relative* and does not cover a later read of the same block;
that row is corrected.

#### 7.1.8 Price (recorded, and it survives the probes that followed)

| file | change | lines | reopens |
|---|---|---|---|
| **NEW `iris/IgetLic.v`** | `ilic`, `iname`, timelessness, the three cheap readings | ~180 | no |
| `SpecIget.v` | one binder, one premise, one post conjunct, one require | ~15 | contract |
| `ProofIget.v` | frame the licence on both arms; drop on the panic arm | ~10 | no |
| `SpecDirlookup.v` | borrowed colourless ticket list + `dinode_at`, in and out | ~25 | contract |
| `ProofDirlookup.v` | matched-index `lookup_acc` + the self-record case split | ~120 | proof |
| `SpecDirlink.v` | borrowed **pre-state** ticket list, returned verbatim | ~25 | contract, and §20.18 ruling 1 → **amended by R13(ii)** |
| `ProofDirlink.v` | thread it to its `dirlookup` | ~60 | proof |
| `ProofNamex.v` | `dir_links_live` at the walk's `dirlookup`; `RootL` at `+0x4c` | ~40 | proof |
| `ProofCreate.v` | `dir_links_live` at `+0x38` and at its four `dirlink`s | ~60 | proof |
| `ProofSysLink.v` | supply at its `dirlink` | ~40 | proof |
| `ProofIreclaim.v` | `BufL` via `iu_held_L` | ~30 | proof |
| `ProofIalloc.v` | `BufL` — **only behind K-F2, which R13(iii) rejected** | ~250 | proof |

**What does NOT move, verified:** `SpecNamex`, `SpecCreate`,
`SpecSysLink`, `SpecIalloc`, `SpecIlock`, `SpecIput`, `SpecIupdate`,
`InodeRegion.v`, `IcacheRef.v`, `IcacheEscrow.v`, `IcacheBoot.v`,
`DirLinks.v`.  The licence is borrowed *within* one call, so no
syscall-level contract sees it; every supply comes out of `ic_loaded`,
which every caller already holds.

---

### 7.2 THE FIRST RETIREMENT PASS — routes A, B and C

Three routes at the free, all dead.  This is the probe that isolated the
currency gap.

| route | verdict | where it dies |
|---|---|---|
| **A — adequacy / reference provenance** | **DEAD** | the justification is *borrowed* at iget (§20.9(f) forbids consuming it); the two licences that do **not** imply "not a box" — (b) GREY and (e) BUFFERED — are closed by trace arguments, not resources.  **New**: M1's objection (ii) ("no absence from `auth nat`") is *repaired* by REF-1 + `ci`-injectivity, and the route still dies — on (iii), the lock, and on the gap |
| **B — entry-keyed birth certificate** | **DEAD, but the ghost is constructible** | the carrier is fine (a per-*generation* one-shot dodges §20.9(b) and (e) exactly as hoped).  It dies on the **issuer**: the only fact worth certifying is "this bundle is not an unconverted claim box", its only issuer is `ireg_withdraw`, and a foreign filler cannot issue it — §20.16.3's wall relocated, §19.7 |
| **C — fs_L escort without K-F2** | **DEAD as a route, ALIVE as two instruments** | phase 1 (claim→brelse) is refuted by the fs_L element, needs no K-F2, ~5 lines, provable today; phase 3 (post-iget) is refuted by REF-1 + `ci`-injectivity, but only under the itable lock at +0x50; **phase 2, the brelse→iget gap, is a CURRENCY gap and is unrefutable by any resource** |

#### 7.2.1 THE FREE'S BLINDNESS — the indistinguishability theorem

At `ireg_free_au`'s fupd (fired from `ProofIput`'s `wp_iupdate_credgen`)
iput holds exactly: `dinode_at γi z dn` at `dn = di_trunc dn₀`; the
whole checked-out `ic_loaded` cells, the entry sleeplock,
`ic_deposit … (DepRef q dev inum ga')`, `iref_frag k q`,
`live_gen k q ga'`, `ity_shot`; the dinode block's **bio half** of
`fs_L` (it is inside `log_write`, holding `bio_locked`) — and the AU
hands it the **region's half**, i.e. the *whole* element;
`di_nlink dn = 0`; and **NOT** `itable_half` — released at +0x5c.

> **THEOREM (the free's blindness).**  In every component the region can
> name, a *truncated corpse* and a *claim box* are identical.

| component | corpse | claim box |
|---|---|---|
| the record | `di_trunc dn` = type≠0, size 0, addrs 0, nlink 0 = **`fresh_shape`** | `ialloc_fresh ty` = the same shape |
| the arm (`ireg_slot`) | OUT (marker in region) since its fill | OUT since the withdraw |
| the ledger `w` | 0 (proved inside the free) | 0 (proved inside the claim) |
| `g` | unconstrained | unconstrained |
| the payload / generation / `ity_shot` | same shape, same type | same |
| the fs_L element | held whole | held whole |
| the reference | REF-1 | REF-1 |

Hence **no separating conjunction of iput's resources distinguishes the
two**, and `c = None` is underivable.  §19.5(h) is not a curiosity about
`fresh_shape`; it is the free's whole predicament, and it survives the
tree untouched.

The only distinguishing information in the system is (i) *which fill
route* produced iput's fragment (a withdraw = a box; `ipool_alloc` = not
a box), and (ii) *which licence* founded iput's reference.  Both are
facts about the past.

*A finding worth recording separately:* the free's record at the flush
is `di_trunc dn`, which keeps `di_major`/`di_minor`.  A corpse of a
`T_DEVICE` inode is therefore *distinguishable* from a box; a corpse of
an empty `T_FILE` is not.  The generic case is the indistinguishable one.

#### 7.2.2 Route A

1. **The tree's invisibility is already landed and is not the missing
   fact.**  `inum ∉ t` is `w = 0`, and it is a *theorem* at both ends
   already: `Hw0` inside `ireg_claim_au` and `Hw0` inside
   `ireg_free_au`.  R13(iii)'s ruling ("we can see this inum isn't part
   of the tree") is right and is *already proved*.  What it does not
   give is what the free needs, because **three of the six licences are
   not tree edges** — (b) GREY, (d) CLAIMED, (e) BUFFERED.  "Not in the
   tree" ⇏ "no reference".
2. **NEW — M1's objection (ii) is repaired, and the route still dies.**
   §20.15(ii)/§20.17.8 rule that no `nat`-counter authority yields
   `r ≤ 1` from the presence of one fragment.  True — but the *absence*
   fact exists elsewhere: `IcacheInv.iref_lookup` gives `n = 1 → q = qt`
   (REF-1), and `IcacheEscrow.ic_ci_wf`'s second conjunct gives
   `ci`-injectivity on inums with `dom ci = dom M`.  Together: **"no
   other icache reference to inum z exists anywhere" is a theorem at
   `ProofIput` +0x50**, with no ledger at all.  §20.15(ii) should be
   recorded as *repaired by the itable, not by the ledger*.
3. **And it is useless where it is needed.**  It holds under
   `itable.lock`; the free runs after the release (+0x50 REF-1 → +0x54
   `live_slot_regen` → +0x5c release → +0x62 itrunc → the free).
   Carrying it across the release is a temporal carrier, i.e. M2's
   shape.  And *even at +0x50* it refutes only a claimant that has
   **already run its iget** — the gap-phase claimant holds no reference
   at all, by construction.

> **DEATH CERTIFICATE (A).**  *The adequacy coupling needs "every
> reference to z is justified" plus "I hold them all".  The second half
> is now available (REF-1 + ci-injectivity) and the first half is not: a
> justification is borrowed at iget and returned (§20.9(f)); minting a
> persistent derivative is §20.9(b) verbatim; and the residual licences
> (b)/(e) are honest ones that a stranger really can hold at a box.*

#### 7.2.3 Route B — and three corrections to its framing

**The mechanism is constructible.**  Entry ghosts die at eviction
(`IcacheEscrow.ic_close_to_empty`, whose own comment reads "the
generation's one-shot dies here, unspent or spent"), so a slot-keyed
certificate is not a stale witness — §20.9(b) is genuinely dodged.  And
§20.9(e) is dodged too, because the certificate can ride at the
**per-generation gname that already exists**: `IcacheRef.ityR`,
`ic_payload`'s `ity_shot`/`ity_pending` polarity, minted at the recycle
by `live_slot_alloc`, retired by `live_slot_regen`.  *A second one-shot
at `g` costs no arity anywhere.*

Three corrections to the framing:

* **The read point is wrong.**  iput does *not* hold `itable.lock` at
  the free.  §17.6's landed home (+0x54) is under the lock; the free is
  three calls later, after `release` (+0x5c; the free runs +0x62..+0x74).
  A certificate homed in `itable_res2`, where `ci` lives, is
  **unreadable at the free**.
* **The only structures that span fill→free *and* are readable at the
  free** are the payload (`ic_loaded`/`ic_payload`, checked out in
  iput's hand) and the thread's own carried resources.
* **A payload conjunct is an obligation at the PARK *and* at the FILL**
  — "a payload conjunct is only as strong as the worst state any walk
  re-parks it in".

**What must it say?**  Only one thing is strong enough: **"this bundle's
record is not an unconverted claim box"** (equivalently `c z = None`).
Who can issue it?

| filler | site | can issue? |
|---|---|---|
| ordinary fill from `ipool_alloc` | `ProofIlock`'s left disjunct | **YES** — the pool never holds a box |
| the withdraw, by the claimant | create's `ilock` | **YES** — it holds the token |
| the withdraw, by a stranger | same lemma, `fr = None` (8 of 9 callers) | **NO** |

> **DEATH CERTIFICATE (B).**  *`ireg_withdraw`'s only reachable firing
> is at a claim box (`ireg_in d ∧ type ≠ 0 ⟹ fresh_shape d`).  A
> certificate the withdraw must issue is an obligation the withdraw owes
> on every firing — §20.16.5(e)'s death certificate verbatim, and R5's
> standing constraint.  Making it an option-indexed input does not help
> here, because unlike SpecIlock's `filled` this is an OUTPUT the caller
> must supply, not an input it may decline.  The certificate is (L6)
> wearing a payload's clothes; it relocates §20.16.3's wall and does not
> escape it.  §19.7 at the withdraw.*

Corollary: the C′ per-site table cannot save it — the sites that would
supply the certificate are ilock's callers, and §20.16.5(e) established
(and namex's code confirms: `ilock(next)` runs *after* `iunlockput(ip)`)
that they hold nothing at that instruction.

#### 7.2.4 Route C — the escort, phase by phase

**Phase 1 (claim → brelse): REFUTED, and it does not depend on K-F2.**

```coq
Lemma fsL_block_exclusive (γfs : fs_names) (b : Z) (bs bs' : list (bv 8)) (q : Qp) :
  b ↪[fs_L γfs]{#(1/2)} bs -∗ b ↪[fs_L γfs]{#(1/2)} bs' -∗
  b ↪[fs_L γfs]{#q} bs'' -∗ False.       (* 1/2 + 1/2 + q > 1 *)
```

At the free's fupd iput holds *both* halves (its own buffer's, plus the
region's through the AU).  At `ireg_withdraw` the same is already true
and already used (`ghost_map_elem_agree with "Hhalf Hfsb"`).  So **at
either of those two fupds, no other thread is inside a bread/brelse
window on that dinode block.**  This is the honest formal content of
"the buffer serialises the region" — the licence composes because it is
a *fraction*, not a handle.  **LANDED as `IregBox.fsL_block_exclusive`**,
generalised from the sketch's `q : Qp` to an arbitrary `dfrac`.

**Phase 3 (post-iget): REFUTED, but at +0x50 only.**  REF-1 +
`ci`-injectivity.  Genuine absence; genuinely stronger than §20.15
believed.  Available **only under `itable.lock`**, not at the free.

**Phase 2 (brelse → iget): UNREFUTABLE — and this is the whole problem.**

In the gap the claimant holds **nothing revocable**: no buffer fraction,
no reference, no fragment — only the ghost token.  And the gap is not
four instructions of *time*: the claimant can be preempted there for
arbitrarily long.  Two supporting facts, both new:

* **`c` is frozen while the fragment is out.**  `ireg_claim_au`
  destructs the arm and refutes the MARKER arm from its own type-0
  premise (`exact (Ht2 Ht0)`).  So while any thread holds
  `dinode_at γi z dn` with `di_type dn ≠ 0`, **no claim at z can fire**.
  iput holds that fragment continuously from its checkout (+0x3c) to the
  free.  So `c z` at the free = `c z` at iput's checkout.  The free's
  obligation is therefore *exactly* "was c = None when my entry was
  filled?" — and that is (L6), whose one broken mover is the withdraw.
* **The gap is a CURRENCY gap**, in §17.1(ii)/§19.5(g)'s exact sense.
  Any epoch/generation repair of (L5) (`c = Excl (ty,e) ∧ ep z = e →
  di_type d = ty`, with the free bumping `ep` instead of clearing `c` —
  which *is* frame-preserving and *does* free the free) fails at the
  consumer: create must prove its epoch current, and currency needs a
  **revocable, reference-tied** resource.  The claimant provably has one
  in phase 1 (the buffer half) and one in phase 3 (the reference) and
  provably none in phase 2.

> **DEATH CERTIFICATE (C).**  *The escort decomposes exactly as designed
> and each end is refutable by a resource iput already holds.  The
> middle is not, and no clause on the region, the payload, the entry or
> the ledger can reach it, because in that interval the claimant's token
> is backed by nothing at all.*

**K-F2 is precisely the deletion of phase 2.**  That is what "K-F2
enables the escort route" meant, and without it the escort has a hole no
invariant can cover, because the hole is a property of the instruction
order.

#### 7.2.5 The ireclaim boot-only hazard — closable, with a landed pattern

The boot-order fact the model needs, in the `KallocInv`/`ProcAvail`
two-regime shape (landed: an exclusive counted regime under which no
other thread can act at all, and a persistent sealed regime with no way
back):

```coq
(* a global one-shot at a fresh gname in [icfg]: pending = "no ialloc has ever run" *)
Definition ireg_boot  : iProp Σ := (* csum (Excl ()) (agree ()) at PENDING — EXCLUSIVE *)
Definition ireg_open  : iProp Σ := (* … at SHOT — PERSISTENT *)

(* the region's per-slot clause, a persistent conjunct of [ireg_slot]: *)
   c <> None -> ireg_open
```

`ireg_claim_au` gains the **persistent** premise `ireg_open` (threaded
like `ireg_inv`: `SpecIalloc` both forms + its 5 consumers, zero
linearity).  `ireclaim`/`fsinit` hold `ireg_boot`; holding the pending
refutes any `ireg_open`, hence `c z = None` everywhere for free at every
iput ireclaim performs.  The seal fires once, after `fsinit` returns.

| mover | clause `c ≠ None → ireg_open` |
|---|---|
| `ireg_claim_au` | establishes it from its new persistent premise |
| `ireg_write_au` / `_link` / `_unlink` / `ireg_withdraw` | **free** — none moves `c` |
| `ireg_free_au` | free (it is the *consumer*) |
| boot (`IcacheBoot`) | `c = None` per inum: vacuous |

**The one gap in the home.** `SpecForkret.v` — "the `first` branch is
assumed away, not proved" — so `fsinit`'s call site is not on a proven
path today, and the one-shot that would mint `ireg_boot` is the very
`first` one-shot SpecForkret's header names and discards.  **This closes
ireclaim; it does not close the general free** (the boot token is gone
by the time any user process runs), so it is a plank, not a door.

#### 7.2.6 THE THIRD DOOR (unaudited)

Delete the *axiom* by weakening what depends on it, rather than by
proving it.  `create_fresh_ty`'s content is consumed in exactly two
places: `SpecCreate`'s made-arm conjunct
`ty <> T_DIR -> dn = create_made ty major minor` and, through it,
`dirlink(ip,".")`'s `di_type dn = T_DIR` premise on ARM C-OK-DIR.
Dropping the conjunct costs sys_open/sys_mkdir/sys_mknod a spurious
failure arm each (live code, partial correctness — sound); ARM C-OK-DIR
is the real question, because with the type unknown ProofCreate's mkdir
arm must case-split and the non-`T_DIR` branch strands create's
`ilink dp` (affine, so sound, but it over-counts `dp`'s `w` and blocks
`dp`'s later free — a *liveness* cost inside the model, not a soundness
one).  **A probe, not a plan**: it removes the tree's last assumption at
the price of a weaker `SpecCreate`, and it is the only route that needs
no kernel change and no new resource.

#### 7.2.7 THE HONEST RESIDUE, named

> **No thread other than the claimant can hold an icache reference to an
> inum during the window between `ialloc`'s `brelse` and `ialloc`'s
> `iget`.**

It is *true* of the pinned binary `f60ff58`.  It is not a tree fact (the
tree's `inum ∉ t` is landed and proves `w = 0`, which is not it).  It is
not a resource fact (the claimant holds nothing revocable in that
window).  It is not a certificate fact (the only issuer is a foreign
withdraw).  It is a fact about the **instruction order inside `ialloc`**,
and the only sound imports of it are: move the `brelse` after the `iget`
(K-F2 — rejected by R13(iii)), or stop depending on it (§7.2.6).

---

### 7.3 THE SPAN-STABILITY PROBE — DEAD, and it dies twice before it reaches the withdraw

The route: issue the justification at the **iget** rather than at the
withdraw, founded on the negative *"no itable entry names `inum`"* over
the claim→fill span.

> **DEATH CERTIFICATE (span-stability).**  *The route's whole content is
> the negative "no itable entry names `inum`".  That negative is a fact
> about `ci`, which lives in the **itable spinlock's resource**, has **no
> ghost algebra, no gname and no authority at all**, and is therefore
> unreadable by a fupd.  The span's two readers are `ProofIalloc`'s
> claim (holds only the dinode buffer) and `ProofIlock`'s fill (holds
> only the entry's sleeplock).  Neither holds the itable lock.  This is
> §16.5's packaging gap verbatim, one design later.*

Second, independent death: **the birth obligation has no discharge at
ialloc's own `iget`**, where §19.2's "the claimant holds nothing" is
exact.  That is licence (d)'s hole reached by a new path, and it is
unchanged by moving the issuer from the withdraw to the iget.

Third: **the invariant is FALSE on a landed green proof.**  `ProofIput`
frees the record (`ireg_free_au`, after `release` at +0x5c) while its
own entry is still in `ci`; the entry is deleted only at the `ref--`
store.  §19.7.

#### 7.3.1 Three findings to keep whatever happens

**(1a) The span's *write* half is already a theorem of the region, and
nobody has written it down.**  All three ordinary movers carry **both**
`bv_unsigned (di_type dn') <> 0` **and** `di_type_stable dn' dn`
(`di_type_stable dn' dn := di_type dn' = 0 ∨ di_type dn' = di_type dn`).
The two premises together force `di_type dn' = di_type dn` exactly.  So:

> **Once a record is claimed, no ordinary write can change its type.
> The only type-changing movers in the whole region are `ireg_claim_au`
> (0 → ty, needs a buffer showing type 0) and `ireg_free_au` (ty → 0,
> needs `dinode_at`).**

The user's intuition is right about writes — and writes were never the
hazard.  Worth landing as a three-line lemma: zero contracts, zero
consumers reopened, and it documents that the residual hazard is **the
fill/free baton**, not writes.

**(1b) The real baton is the MARKER, not the tree.**  `ireg_slot` puts
**exactly one** of {fragment, marker} inside the invariant:

```coq
  ((⌜ireg_in d⌝ ∗ z ↪[γi] d)                         (* FREE or CLAIMED: fragment IN  *)
   ∨ (⌜bv_unsigned (di_type d) <> 0⌝ ∗ imark γi z))  (* OUT: marker IN                *)
```

For a claimed inum the fragment is **in** the region, so the only way to
obtain it is `ireg_withdraw`, whose premise is
`imark γi (bv_unsigned inum)`.  And `ireg_free_au` needs `dinode_at`.
Therefore:

> **`imark γi inum` in hand ⟹ nobody can fill and nobody can free
> `inum`.**  Two lines, via `imark_excl`.

That *is* span stability, as a resource, with no tree, no token, no
enumeration and no `fdetached`.  It is the sharpest formulation the
route could have — **and its death certificate is one sentence long: at
a free inum the marker is OUTSIDE the region — in the pool, behind the
itable spinlock ialloc does not hold** (§20.16.5(f)).  *Write that
sentence into `SpecCreateFreshTy.v`'s header the next time that file is
touched, so nobody re-derives the marker route a fourth time.*

**(1c) `dinode_at_excl` already refutes one whole class of interloper.**
For a claimed inum the region holds `dinode_at`, so **no entry can be
`ic_loaded` for it** (`ic_loaded` carries `dinode_at`).  Any entry that
exists during the window is necessarily **unloaded, holding the
marker**.  The hazard set is precisely one shape, not six.

#### 7.3.2 The clause, and its three homes — all dead

```coq
(* candidate, inside itable_res2 beside ⌜ic_ci_wf M ci nib dv⌝ *)
⌜forall k dev i, ci !! k = Some (dev, i) -> di_type (m !!! bv_unsigned i) <> 0⌝
```

- It names `m`, the region's `ghost_map`, which the lock does not own.
  Coupling it needs the region's authority under the lock — §20.9(c) and
  §20.13.
- Restated as owned justifications per entry: §20.9(f) — a consumed
  licence makes a second `dirlookup` of the same name unprovable,
  because the fragment belongs to `dp`'s payload and must return at
  `iunlock(dp)`, which happens while the entry is still alive.
- Restated as a persistent birth *tag*: §20.9(b) verbatim.  A tag
  concludes nothing in the present, and the present is where the claim
  reads.
- Moving `ci` into an invariant so a fupd could read it: `ci` is a bare
  `gmap` with no cmra; giving it one is a **new gname**, which enters
  `ireg_inv` *and* `ipool_shape`, i.e. `ic_escrow`'s arity, i.e. every
  fs contract — §20.9(e) / §16.5.

**The one coupling that does exist runs the other way, over the
complement** — `itable_res2`'s last conjunct
`ipool γfs γi cov logstart (region_inums nib ∖ ci_inums ci)`, with
`ipool_shape := ipool_alloc ∨ imark`.  So the lock owns, per *uncached*
inum, either its full bundle or its marker, and `dom ci = dom M` makes
"uncached" exact.  **"No entry names `inum`" is therefore equivalent to
"`inum`'s `ipool_shape` is in the lock" — a lock-held resource, which is
exactly why no fupd can see it.**

#### 7.3.3 The marker's custody chain

| edge | lemma | who holds the marker after | lock held |
|---|---|---|---|
| boot | `icache_boot` | the pool (`ci = ∅`) | — |
| **claim** (0 → ty) | `ireg_claim_au` | **unchanged** — the claim never touches it | buffer only |
| entry birth (recycle) | `ipool_acc` + `ic_open_empty_free` + `ic_mk_unloaded` + `ic_close_mid` | the new entry's `ic_unloaded` | **itable spinlock** |
| **fill** (claim-box arm) | `ireg_withdraw` | back **into** the region (OUT arm); fragment out | entry sleeplock + the block's `fs_L` half |
| ordinary write | `ireg_write_au/_link/_unlink` | region (OUT arm) | — |
| **free** (ty → 0) | `ireg_free_au` | pays the marker **out** to iput | none (runs after `release` at +0x5c) |
| re-park | — | the entry's `ic_unloaded` | itable spinlock |
| **eviction** | `ic_close_to_empty` | back to the pool | itable spinlock, at REF-1 |
| recycle-on-live-entry | **does not exist** | — | — |

#### 7.3.4 The route's own error, at step 3

"No write ⟹ the axiom" is **too weak**.  `filled = true` means exactly
"this call took §16.4's claim-box arm", and the fill's case split is on
the **entry's parked payload**, not on the record: `ipool_alloc` →
ordinary fill, `filled = false`; `imark` + type 0 → the live panic;
`imark` + type ≠ 0 → `ireg_withdraw`, `filled = true`.  So if any
foreign referrer's `ilock` reaches the withdraw first, create's `ilock`
takes the **cached** arm and reports `filled = false` — with
`di_type dn = ty` still true.  **The axiom's second conjunct is an
exclusion of foreign FILLS, which are read-shaped and available to any
referrer; write-stability does not touch it.**

*The §19.7(iii) repair, and why it self-destructs.*  §20.17.4(a)'s trick
("state the theorem over parked payloads and it is exactly true") has an
analogue here: restrict the clause to entries whose escrow arm is
PARKED, excluding HELD (iput's free window) and OUT (a checked-out
entry).  Preservation then survives.  **But the hazard the span must
exclude is precisely an OUT-arm entry** — a foreign `ilock` in flight.
The repair that saves the invariant deletes its only consumer.

---

### 7.4 THE HARMLESSNESS PROBE — T1, T2, and BORN BEFORE THE ENTRY

**The harmlessness route is DEAD.**  But it dies later than the two
previous routes and at a *different, sharper* wall: **the claim box is
born before the cache entry exists**, so no entry-keyed or
generation-keyed resource can witness it, and no *region*-keyed resource
can survive a re-claim (§19.7).

#### 7.4.1 T1 (CLAIM-BOX FREEZE — provable, region-internal, ~3 lines)

> While `ireg_slot γi z d` stands at its IN arm with `fresh_shape d`
> (the claim box), the region's record at `inum` cannot change, and no
> `dinode_at γi inum _` exists anywhere in the system.

Proof, from the landed code:

* `ireg_slot` is `(⌜ireg_in d⌝ ∗ z ↪[γi] d) ∨ (⌜type d ≠ 0⌝ ∗ imark γi z)`,
  and `ireg_in d := type d = 0 ∨ fresh_shape d` with `fresh_shape`
  *including* `type ≠ 0` — so the two IN sub-cases are disjoint and the
  claim box is the right one.
* `ireg_free_au`, `ireg_write_au`, `ireg_write_link`,
  `ireg_write_unlink` all take `dinode_at γi inum dn` and are refuted at
  the IN arm by `dinode_at_excl` (the pattern is written out in the free
  itself).
* `ireg_claim_au` is refuted by its own type-0 premise against the box's
  `type ≠ 0`, through `ireg_couple`.
* **Corollary (new and free):** `ipool_alloc` and `ic_loaded` each carry
  `dinode_at γi inum _`, so at a claim box **no pool bundle and no
  loaded entry anywhere names this inum** — every `ilock` at it must
  take the fill arm.  This is the fact §16.4 argued informally about the
  itable; it is a one-line ghost consequence and nothing in the tree
  states it.
* So the box is exited **only** by `ireg_withdraw`, whose sole gate is
  `imark γi (bv_unsigned inum)`, and the marker is unique (`imark_excl`).

**T2 (DELIVERY — not provable).**  The claimant's own `ilock` is *the*
withdraw of *its own* claim box.

**T1 is the whole harmlessness content that Iris can hold.  T2 is the
axiom.**

#### 7.4.2 The case analysis, as far as it goes

At `ireg_claim_au`'s instant the arm is IN, so the marker is out, held
by exactly one party.  Three homes:

**(A) UNCACHED — marker in `ipool`.**  ialloc's `iget` misses,
recycles, mints generation `g` + `ity_pending g` and parks
`ipool_shape`'s marker arm into `ic_unloaded`.  create's `ilock` finds
`valid = 0`, takes the withdraw.  ✔ delivery.

**(B) CACHED-UNLOADED entry.**  iget HITs; same fill. ✔

**(C) MID-FREE `iput` — the interesting one, and it checks out exactly
as conjectured.**  `ireg_free_au` pays the marker; the generation was
already bumped at +0x54, *inside* the itable lock, at the last instant
the whole liveness unit exists (`live_slot_regen`) — so **every
reference minted afterwards, including ialloc's, names the NEW
generation `ga'`, and every earlier one is refuted by REF-1**.  This is
resource-carried, not a trace argument.  The re-park at +0x74 deposits
`ic_payload … ga' false` = `inode_raw ∗ ipool_shape`(marker arm)
`∗ ity_pending ga'`.  The C source and the proof agree that the tail is
`ip->valid=0; releasesleep; acquire; ip->ref--; release` — **no second
`ilock`, no second withdraw, no second record write.**

So the conjecture "the only co-referrer is a past-free `iput` whose
remaining actions are ghost-only and harmless" is **factually correct on
the fixed binary**, and the freer's re-park does make the claimant's
withdraw the unique next fill *of generation `ga'`*.

**Where it stops.**  "The unique next fill of `ga'`" ≠ "my fill".
create holds `live_gen kslot (q/2) g` and its `ilock` reports
`ity_shot g (di_type dn)` — but on the `filled = false` arm that shot is
at *somebody else's* record.  create cannot refute `filled = false`,
because refuting it needs "no other thread `iget`ed this inum", which is
`SpecIget`'s licence, which needs licence (d), which is the circularity.

#### 7.4.3 The KEY HOPE — refuted in one line

> "the marker's location IS region-visible via `ireg_slot`'s two arms"

**False.**  The arms are `fragment-in / marker-in`.  At the claim the
region takes the IN arm, which says *only* "the marker is not here".
`imark γi z := ∃ d, imark_key z ↪[γi] d` is a bare exclusive token with
no identity payload and no holder name.  **The region is name-blind
about the marker's exterior**, and the one place the exterior is
enumerated — `ipool` — is behind the itable spinlock.  There is no
case-split to be had at the claim's fupd.

The marker's *value* slot (`d : dinode`, existential, "never updated —
only moved") is a genuine unused degree of freedom, and it is the only
one found.  It is unusable here: writing it needs auth **+** the
element, and the element is out of the region precisely when the claim
runs.

#### 7.4.4 THE GENERAL IMPOSSIBILITY (the new content)

Any create-side certificate `R` must survive from the claim to the fill
and must exclude "a foreign free-and-reclaim happened in between".

* `ireg_claim_au` must stay firable by any thread holding a type-0
  buffer read, at any inum, always (§19.7; `ProofIalloc` holds nothing
  else).  Therefore the claim's ghost step is frame-preserving against
  **every** frame, in particular against `R`.  Hence `R` is satisfied
  identically before and after a foreign re-claim and **cannot
  distinguish them**.
* The only escape is that `R` block the *free* (a re-claim needs a
  type-0 record, which only `ireg_free_au` writes).  create *does* hold
  such an `R` post-`iget` — its reference slice makes
  `live_slot_regen`/REF-1 unattainable — but that is a fact about the
  *other* thread's reachability, and create can only cash it through an
  **invariant clause** linking the region's record to the entry.
* **And no such clause can exist, for a structural reason nobody has
  written down: THE CLAIM BOX IS CREATED BEFORE THE ENTRY.**  In case
  (A) the generation `g` does not exist at claim time — `iget` mints it
  afterwards.  So no `g`-keyed, `k`-keyed or deposit-keyed proposition
  can be an invariant of the claim box.
* A *fixed* per-inum keying (ambient gname, §20.9(e)'s permitted dodge)
  fails at the opposite end: a one-shot cannot be re-shot at a second
  type (wedges `ireg_claim_au`), and a fractional/exclusive cell cannot
  be re-taken by the claim without reassembly, which is a premise on
  `ireg_withdraw` — §20.16.5(e)'s wall.

> **COROLLARY.**  *K-F2 is not "one of two doors"; it is the only
> proof-side door, because it is the only change that makes the claim
> and the entry-mint share a window (the buffer), giving the claim box
> something to be keyed on.*

#### 7.4.5 Death certificates for the named candidates

**(l) Region parks a half of the claim token, withdraw hands it back
unconditionally.**  DEAD at re-claim.  Whatever algebra: `ghost_map`
fractional elements cannot be updated at 1/2; `auth` fragments that the
claim may move are by definition monotone, hence episode-blind (§20.9(b)
verbatim).  The withdraw cannot restore full ownership without a premise
→ §20.16.5(e).

**(m) Claim pays out `z ↪[γi]{1/2} dn'` (half the region fragment
itself).**  DEAD, and worse than (l): `ireg_withdraw` must produce a
*whole* `dinode_at` for `ic_loaded` (named in 19 files), and it would
hold only 1/2.  `ProofIlock`'s fill arm — landed, green — becomes
unprovable at a machine-reachable step.  §19.7.  (Also: create holding
the half plus `ilock` returning the full is jointly invalid, i.e. the
design is self-refuting rather than merely stuck.)

**(n) Mint the type one-shot at ialloc's `iget` instead of at the
fill.**  DEAD twice.  `SpecIget` has no type argument (4 call sites),
and — fatally — `ic_payload`'s `false` polarity would become
`ity_pending g ∨ ity_shot g ty`, on which the fill's obligation
`ity_shot g (di_type dn)` is exactly `di_type dn = ty`: the goal,
circular.

**(o) Marker carries the claimed type.**  DEAD: the marker is out of the
region at claim time, so the claim holds the auth but not the element;
`ghost_map_update` is unavailable.  Only `ireg_free_au` could stamp it,
and the free does not know the future type.

**(p) `ireg_withdraw` premise / `ireg_free_au` premise (any shape,
including "optional").**  DEAD, §20.16.5(d)/(e) unchanged; an *optional*
premise is worse, because the fill arm must still close when the caller
passed `None` and the half is in a stranger's hand.

**(q) Enumerating the co-referrer's remaining steps.**  DEAD as *logic*,
not as *fact*: the facts in §7.4.2 are all correct, but "what the other
thread does next" is not an Iris proposition.  §20.17.7 option (ii) said
this at `SpecIget`; it applies verbatim at the withdraw.  §20.17.6(B)'s
formula — *"a guard prunes traces; it cannot hand a contract a
resource"* — is the whole obituary.

#### 7.4.6 What the probe yields (cheap, optional, ~30 lines)

1. `ireg_claim_box_freeze` — at the IN/`fresh_shape` arm, no mover but
   `ireg_withdraw` can fire.
2. `ireg_box_no_payload` — at a claim box, `ipool_alloc`/`ic_loaded` for
   that inum are refuted (`dinode_at_excl`).  This is §16.4's
   "exhaustiveness" argument discharged *without* the itable, one level
   stronger than the marker refutation already in `ireg_withdraw`.

Neither retires the axiom.  (2) would be the load-bearing lemma if K-F2
ever lands, because it makes "ialloc's `iget` finds either the pool's
marker or an unloaded entry's marker, and never a loaded record" a
theorem rather than a paragraph.

**Door 2 — "refute §20.17.6(B) at the withdraw" — is now closed too.**
The withdraw wall was previously stated as *a premise cannot be supplied
at the call site*.  This probe shows the payout direction (no premise at
all) fails independently, at `ireg_claim_au`'s re-mint.  So §20.17.7's
"those are the two doors" is corrected to **one**.

---

### 7.5 THE RECORD-BACKED-GREYS / TREE-LEVERAGE PROBE — G1, and TRACE G

#### 7.5.1 The reversal as stated is a NO-OP

The proposal was that the grey licence "demand the dangling RECORD (the
`dir_link_at` ticket at its grey disjunct, borrowed) rather than a bare
`igrey` token."  But:

```coq
Definition dir_link_at (self : Z) (dn : dinode) (data : nat -> list (bv 8)) (k : nat) : iProp Σ :=
  (if dir_liveb data k && negb (bool_decide (bv_unsigned (dir_inum data k) = self))
   then (ilink (bv_unsigned (dir_inum data k))
         ∨ (igrey (bv_unsigned (dir_inum data k)) ∗ ⌜bv_unsigned (di_nlink dn) = 0⌝))
   else emp)%I.
```

`self`, `dn`, `data`, `k` are **pure parameters**.  The grey disjunct is
`igrey z ∗ ⌜pure⌝` and owns nothing else.  A foreign thread that mints
`igrey z` from nothing (`link_mint_grey` / `ireg_link_grey`) picks any
`dn` with `di_nlink = 0`, any `data` with a live non-self record at `k`
naming `z`, and **has constructed `dir_link_at self dn data k` at its
grey disjunct.**  Wrapping `GreyL` in `dir_link_at` supplies exactly the
same licence with two extra existentials.

**The hole is not `igrey`'s mintability.  It is that a record ticket
carries no evidence that the record exists.**

#### 7.5.2 The producer/consumer table — and why grey is cheap to move

| # | site | role | what it needs |
|---|---|---|---|
| P1 | `link_mint_grey` (IcacheRef) — mint from nothing | producer (algebra) | nothing; `g` is constrained by no clause of `ireg_link_ok` |
| P2 | `ireg_link_grey` (InodeRegion) — the region-level free mint | producer (region) | `ireg_inv` + `inum < 16·nib`; reads nothing, takes no fragment |
| P3 | `link_grey_of_link` — the *conversion* | producer | one `ilink z`; **ZERO CALLERS** (owed to S7's `dp->nlink--`) |
| C1 | `dir_link_at`'s grey disjunct | **the only consumer of the resource, anywhere** | one `igrey z` + `⌜di_nlink dn = 0⌝` |
| C2 | `cr_grey_links` / `cr_grey_dir_links` (ProofCreate) | the only *caller* of P2 | rebuilds the failed mkdir child's whole `dir_links` big-op |
| C3 | the fail-arm re-park (ProofCreate) | **the single live consumer site in the tree** | one `cr_grey_dir_links` application |

Two facts follow.  *(1) `igrey` concludes nothing and is read by
nobody* — no lemma anywhere derives anything **from** an `igrey`, and
§20.18 ruling 2 already accepts permanently that `g` can never carry
information.  A CMRA component that carries no information and has no
reader is dead weight.  *(2) The entire grey machinery has exactly ONE
live consumer site.*

#### 7.5.3 The constructive form, and why it still does not close T2

```coq
(* the record-backed grey licence — GreyL′ *)
Definition GreyL (γi : gname) (γfs : fs_names) (z : Z) : iProp Σ :=
  (∃ (self : Z) (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) (k : nat),
     dinode_at γi (inum_of self) dn ∗ inode_blocks γfs bm data ∗   (* THE HOME, OWNED *)
     ⌜ bv_unsigned (di_type dn) = T_DIR_z ⌝ ∗
     ⌜ bv_unsigned (di_nlink dn) = 0 ⌝ ∗                            (* the home is an ORPHAN *)
     ⌜ (k < dir_nrec (bv_unsigned (di_size dn)))%nat ⌝ ∗
     ⌜ dir_live data k ⌝ ∗ ⌜ bv_unsigned (dir_inum data k) = z ⌝ ∗ ⌜ z <> self ⌝)%I
```

i.e. **`GreyL z` = "I own a directory node, it is orphaned, and one of
its live records names `z`"** — an out-edge of an orphaned node.  The
`igrey` token is not in it at all, because it adds nothing.

This **is** unmintable: `dinode_at` is a `ghost_map` element, exclusive
by `dinode_at_excl`, and no fupd over `ireg_inv` produces one.  **And it
is still SATISFIABLE at a claim box, on a trace the fixed binary
reaches.**

#### 7.5.4 TRACE G — reachable on `f60ff58`

```
  mkdir /a ; mkdir /a/b                    a.nlink=2  b.nlink=1, b has "."→b, ".."→a
  P: chdir("/a/b")                          b's ref pinned by P->cwd
  Q: rmdir("/a/b")   sysfile.c:237 zero b's record in a
                     :239  a->nlink--       ← the ilink a inside b's ".." is SPENT
                     :244  b->nlink-- → 0
                     :246  iunlockput(b) → iput: ref==2, NOT freed
        ⇒  b survives: T_DIR, nlink=0, live "." and "..", the ".." ticket now GREY
  Q: rmdir("/a")     isdirempty(a) holds (b's record was zeroed)
                     a->nlink-- → 0 ; iput(a): ref==1 ⇒ itrunc, a->type = 0   ← a is FREE
  Q: create(...)     ialloc may return a's inum         ← a CLAIM BOX
        ⇒  b's live ".." record names a claim box, and b is orphaned.
```

Three things follow:

1. **A live directory record naming a claim box is reachable.**  `GreyL′`
   is *true* there.  The record-backed licence is therefore not
   refutable at a claim box by any resource argument.
2. **What stops it is `namex`'s guard, and only that.**  P doing
   `chdir("..")` runs `namex`: `ilock(b)`, type is `T_DIR` ✔, then
   `fs.c:693` `if(ip->nlink == 0)` fires and returns 0 —
   `dirlookup(b,"..")` never runs, `a` is never `iget`ed.  **Note that
   `ilock(b)` happens BEFORE the guard**, so the licence is *held* and
   merely never *delivered* — which is precisely the delivery-gap shape,
   and why the enumeration must live at `SpecIget` (where delivery
   happens) and not at the payload.
3. **§2(iii)'s statable global negative is FALSE AS WRITTEN, and §2's
   arithmetic clause is why** — see the corrections applied to §2 above.

> **VERDICT (record-backed greys).**  *Record-backing removes the
> MINTABILITY of the grey licence but not its SATISFIABILITY at a claim
> box.  The refutation of licence (b) at a claim box remains a
> reachability argument (§20.17.5's shelters), not a resource argument.
> T2 does not fall, `create_fresh_ty` does not delete, and "no kernel
> change and no assumption" does not follow.*

What record-backing *does* buy, and it is not nothing: it converts
§20.17.5 from a fact about *which `iget`s the machine performs* — which
§20.17.7 option (ii) proved is unstatable anywhere inside
`ProofCreate`/`ProofIput` — into a fact about *who can hold the
licence*, which is a resource fact and therefore statable at
`SpecIget`.  Under `GreyL′`, **every grey licence names a `".."`
target**: combine `GreyL′`'s `di_nlink dn = 0` with
`DirView.dir_orphan_clean` and the record at `k` has name in
`{".", ".."}`; `"."` is self and excluded by `z ≠ self`; so `z` is the
home's parent.

#### 7.5.5 G1 — DELETE `igrey` AND THE `g` COMPONENT; make the grey disjunct pure

Since nothing reads `igrey`, the payload's grey disjunct can be:

```coq
     then (ilink (bv_unsigned (dir_inum data k)) ∨ ⌜bv_unsigned (di_nlink dn) = 0⌝)
```

Consequences, all favourable and all checked against the landed code:

- `linkElemUR` loses its `g` component; `lelem` goes from four fields to
  three; `link_agree`'s `prod_included` chain loses one layer;
  `link_mint_grey`, `link_grey_of_link`, `igrey`, `igrey_timeless`
  **delete** (`link_grey_of_link` has no caller, so it deletes free).
- `InodeRegion.ireg_link_grey` (~50 lines of invariant-opening)
  **deletes**.
- `ProofCreate.cr_grey_links` collapses from a `fupd`-carrying induction
  over `ireg_inv` to a **pure `big_sepL` introduction with no mask, no
  invariant and no `nib` bound** — its `dir_ok`/`dir_inums_ok` premise
  disappears with the mint.  **~40 lines DELETED, net.**
- `IcacheBoot`: unchanged.  Every `Spec*` file: **unchanged** —
  `dir_links`'s arity does not move.

**The one thing it costs:** `dir_link_at` at a grey record becomes
**duplicable**.  Sound — grey never contributed to `w`, and (L1)
`w ≤ nlink` is untouched — but the payload's per-record ticket is then
exclusive only at live records.  Nothing landed depends on grey
exclusivity (verified: no lemma consumes an `igrey`).  It also means
**the licence enumeration's row (b) has no resource to be** — which is
the point.

#### 7.5.6 The suppliable `SpecDirlookup` premise is a DISJUNCTION

With row (b) carrying nothing, `ProofDirlookup`'s `iget` must produce
`LinkedL` from the borrowed ticket at the matched index.
`dir_link_at_live` does it **from a home-live premise** — and a bare
home-live premise on `SpecDirlookup` is **unsuppliable at `sys_unlink`**,
which does `nameiparent` → `ilock(dp)` → `dirlookup(dp,name,&off)` with
**no `dp->nlink == 0` re-check**.  The suppliable premise:

```coq
  (* SpecDirlookup's new premise — supplied at every one of the six call sites *)
  bv_unsigned (di_nlink dn) <> 0  \/  (bname 14 s <> dot_name /\ bname 14 s <> dotdot_name)
```

with `⌜dir_orphan_clean dn data⌝` carried beside `dir_ok` in the
payload.  The right disjunct closes because under `dir_orphan_clean` an
orphaned home's live records are all dot records, so the *matched*
record — whose name is `s`, non-dot — is not live, the found arm is
vacuous, and the borrowed ticket is only ever cashed under a live home.

| dirlookup call site | disjunct | supplier |
|---|---|---|
| `namex` (guard, then `dirlookup(ip,name,0)`) | left | `ProofNamex`'s `Hnl0`, green |
| `create`'s `dirlookup(dp,name,0)` | left | `sysfile.c:269` guard (`create+0x2a/+0x2e`) |
| `create`'s `dirlink(ip,".")` inner lookup | left | `ip->nlink = 1`, flushed before |
| `create`'s `dirlink(ip,"..")` inner lookup | left | same |
| `create`'s / `sys_link`'s `dirlink(dp,name)` inner lookup | left | the `:269` / `:161` guards |
| **`sys_unlink`'s `dirlookup(dp,name,&off)`** | **right** | the two `namecmp` refusals at `sysfile.c:220-221` |

**The §20.17.7 (i)-lite price does not return.**  (i)-lite was rejected
because it was a *premise addition wearing a postcondition's clothes*
carrying a fact about the **past** ("was `ilink` at the read",
§20.9(b)).  This premise is about the **present** and is a pure `Prop`,
and R13(ii)'s borrowed-ticket-list amendment supplies the resource half.

#### 7.5.7 The `nlink`-lowering audit (§19.7's test applied to G1)

| site | order, and what the payload owes |
|---|---|
| `sys_link`'s `bad:` (`ip->nlink--`) | undoes the `++`; `ip` is not a directory (ARM E2's `T_DIR` refusal), so `dir_links ip = emp`.  **Nothing owed.** |
| `sys_unlink`, `T_DIR` arm (`dp->nlink--`) | **the conversion point.**  The record was zeroed FIRST, so `dp`'s own payload owes nothing.  What is spent is the `ilink dp` living in **`ip`'s** `".."` ticket.  `ip` stays LOCKED (`iunlockput(ip)` later), so its payload is in the walk's hands and is not re-parked until `ip->nlink--` has already made it 0.  **The window closes; by the lock, not by luck.** |
| `sys_unlink`, general (`ip->nlink--`) | `ip`'s own count; its records survive until `iput`'s `itrunc`.  Under `dir_orphan_clean` those are only the two dots. |
| `create`'s `fail:` (`ip->nlink = 0`) | the free mint's only consumer today.  Record-backed by substance already. |
| `iput`'s free (`itrunc; ip->type = 0`) | destroys the freed inode's own records. |

**Answer: no — every reachable grey has a real record behind it, so the
record-backed/pure form supplies all of them.**

#### 7.5.8 The tree-leverage half

**S2-0 — the tree layer has no supplier, and one pure conjunct is the
entire gap.**  `FsRep.fnode` requires `⌜node_rep n dn data⌝`, whose
`NDir` case demands `dir_names_unique data (dir_nrec (di_size dn))`.
**`dir_names_unique` occurs in exactly two files — `FsTree.v` and
`FsLookup.v` — and in no payload, no spec, and no walk.**  `ic_loaded`
carries every ingredient of `fdir` except uniqueness.  So:

> **No landed walk can construct an `fnode`, an `fdir`, an `fslice` or
> an `fs_rep`.  F1b and F2 are landed, green, `Print Assumptions`-clean
> — and unreachable from every proof in the tree.**

The clause, and it must be type-guarded exactly as `dir_ok` is
(unguarded it is **false** of a file — a large file's bytes read as
records will collide; the `dir_dots_ix` road-test lesson repeating):

```coq
(* DirView.v, beside dir_ok / dir_dots_ix / dir_orphan_clean *)
Definition dir_uniq (dn : dinode) (data : nat -> list (bv 8)) : Prop :=
  bv_unsigned (di_type dn) = T_DIR_z ->
  dir_names_unique data (dir_nrec (bv_unsigned (di_size dn))).
```

Five discharges, all existing: not-a-directory (`dir_ok_not_dir`'s
shape); free/`size = 0` (claim box, truncated corpse, `fresh_shape` —
`dir_nrec 0 = 0`, vacuous); every peel/re-park that moves nothing
(transfer, ~35 sites); **`dirlink`'s write** —
`FsLookup.dir_names_unique_write`, **LANDED**; **`sys_unlink`'s
zeroing** — `FsTree.dir_names_unique_zero`, **LANDED**; boot (one
computational image obligation in `ireg_alloc`'s existing ∀-slot).

**S2-1 — the tree-level "no path reaches a claim box" is FALSE.**
`FsTree.path_at` is `foldl (path_step t)`, and `path_step`/`tree_ent`
read `ents !! f` and return whatever inum the entry names — **whether or
not that inum is in `fs_nodes t`**.  That is deliberate ("a missing node
is an ordinary `None` and never an error"), and §1.4's second
consequence rules `fs_closed t` false in general.  What *is* provable:
**no edge of `t` out of a LIVE node names a claim box** (from the
ledger: a live non-self record forces `ilink`, `link_w_ge` ⇒ `w ≥ 1`,
(L1) ⇒ `nlink ≥ 1`, and a claim box has `nlink = 0` by `fresh_shape`);
and **every edge into a claim box is a `".."` out of an orphan**.  The
shelters themselves are *control-flow* facts, which no tree predicate
can state — **but they are subsumable at the CONTRACT rather than at the
tree** (§7.5.6).  *The unification lands on `SpecDirlookup`, not on
`fs_rep`.*

**S2-2 — the correct tree object is the ORPHAN SET.**  The mandate's
"record-backed grey = the hole's boundary edge" is wrong: `dir_link_at`'s
grey disjunct is guarded by `⌜di_nlink dn = 0⌝` — a condition on the
**home**.  Grey says *my source is orphaned*, not *my target is
missing*.  In trace G, at the instant `a->nlink--` fires, `a` is still
perfectly present in `t`; the edge is grey and its target is not a hole.

> `t` splits into the live tree reachable from `fs_root t` and a set of
> **orphaned nodes** (`di_nlink = 0`, still `T_DIR`, still holding
> bytes, pinned by an in-core reference).  **A grey edge is exactly an
> out-edge of an orphan.**  Under `dir_orphan_clean` an orphan's
> out-edges are exactly `{"." → self, ".." → parent}`, so each orphan
> contributes exactly **one** grey edge, and it always names its parent.

That sentence does four jobs: it is the grey correction term §2's
arithmetic clause was missing; it is the narrowing that makes `GreyL′`
say something; it makes `dir_orphan_clean` a **tree** statement
("orphans have out-degree ≤ 2, both dots") rather than a byte-level
record enumeration; and it identifies the F1.5 hole correctly —
**`fs_closed t` fails at ORPHANS, not at claim boxes.**

**S2-4 — three duplication candidates refuted, one confirmed.**
`dir_ok` vs `node_rep`: **REFUTED, no overlap** — `dir_ok` is a *range
bound*, `node_rep`'s `NDir` case is type + uniqueness + `ents =
dir_view data nrec`; they share the type guard and nothing else, by
design.  Do not merge them.  DirView's first-match lemmas vs FsLookup's:
**REFUTED, already unified** — `FsTree.dir_view` is defined over
`DirView.dir_first`, `dir_view_lookup` is the abstraction theorem, and
`FsLookup.node_lookup_first` is that same equation lifted; the tree
layer is a strict client of `DirView` with one equation as the seam.
`isdirempty`'s loop invariant as `dir_dots_only`: **CONFIRMED, and it is
the one to take** — `isdirempty` is inlined in `sys_unlink`, and its
loop is a `readi` scan whose natural invariant over the prefix is
precisely `DirView.dir_dots_only` restricted to `k < i`; the loop exit
yields `dir_orphan_clean` via `dir_orphan_clean_of_only` with no
conversion step, and the same walk's `ip->nlink--` needs
`dir_links_unlink`'s home-live premise, whose *only* supplier is that
very invariant.  A fourth, free: `FsTree.dir_view_zero` (the unlink
delta) and `FsLookup.dir_view_write` (the dirlink delta) are already the
matched pair, with `dir_first_after_write`/`_after_zero` as the
operational forms.  No action; noted so the pair is not rebuilt.

#### 7.5.9 Staging (the probe's own)

> **G1 — THE TOKEN DELETION.  Unconditional, additive-by-subtraction,
> one consumer site.**  Delete `igrey`/`g`; grey disjunct becomes pure.
> **Independently correct: YES.**  It is §20.18 ruling 2's own
> conclusion carried to its end: if `g` can never carry information, it
> should not be in the CMRA.
>
> **G2 — the payload conjunct `dir_orphan_clean`.**  (At the time of the
> probe: blocked on `ProofSysLinkTails`' `ip->nlink--`.  **SINCE
> LANDED** — see §7.8.)
>
> **G3 — the disjunctive `SpecDirlookup` premise + R13(ii)'s borrow; row
> (b) deletes from `iname`.**  Gated on G1 + G2.  This is the increment
> that makes the shelter enumeration a contract obligation instead of a
> paragraph.
>
> **G4 — the free.  Still not reached.**

---

### 7.6 THE SYNTHESIS PROBE — THE CLAIM'S HORIZON, and the AFFINITY finding

**The synthesis DIES, and it dies at a wall none of the four prior
probes named — but it dies *after* correcting two of their findings, and
it leaves one lemma worth landing.**

#### 7.6.1 T1 is real, landed, and FREE — better than claimed

It is not a new clause: it is the IN arm's own predicate.

```coq
(* InodeRegion.v *)  ireg_in d := bv_unsigned (di_type d) = 0 \/ fresh_shape d.
(* ireg_slot     *)  (⌜ireg_in d⌝ ∗ z ↪[γi] d) ∨ (⌜di_type d <> 0⌝ ∗ imark γi z)
```

While a box's fragment sits in the region, `ireg_in` at a nonzero type
**is** `fresh_shape`, hence `di_nlink = 0`, hence `w = 0` by (L1).  So
at a box, with *no new clause at all*:

- **LinkedL refuted** — `link_w_ge` gives `w ≥ 1` against `w = 0`;
- **HeldL refuted** — the region holds `z ↪[γi] d`, so `dinode_at_excl`
  kills any client copy;
- **RootL refuted** — `ireg_claim_au` proves `inum ≠ ireg_root`
  internally, so no box is ever at the root;
- **BufL, GreyL** — unchanged.

**Box-exclusion is CORRECT, and stronger than stated: it needs neither
C′'s licence enumeration nor a new invariant, only the arm.**

**Correction 1 (in the synthesis's favour): the delivery question is
moot.**  Under (L5), create does not need box exclusion at all.
`ireg_withdraw` pays out `⌜fresh_shape (ds !!! islot inum)⌝ ∗ dinode_at`
and moves neither `w` nor `c`, so with `fdetached` as ilock's
option-indexed input create reads `di_type dn = ty` by **one agreement
step** (`link_claim_agree`).  No fill-ticket, no entry-keyed mechanism,
no frame-rule composition.  **The born-before-entry wall never comes up
because the question it answers is not asked.**

**Correction 2 (against the synthesis, code-backed): create's fail arm
hands iput NOTHING, and does not need to.**  create's commit at +0xc4
mints the `ilink`; the fail arm's `sh zero,74(s3)` + `iupdate` at +0x14c
is `wp_iupdate_unlink` and it **CONSUMES that `ilink`**; the freeing
`iunlockput` at +0x152 receives `Hcload`, `Hcshot'`, `Hckp`, `Hcdiat`,
the escrow and the log set — **no ledger fragment of any kind.**  So
under F1.5c the commit at +0xc4 (an `ireg_write_link`) is where the
token would be spent, four instructions after the `ilock`, and by the
time any `iput` runs, `c = None` **already**.  A ClaimL-born *entry*
outlives its token by the entire life of the file.

#### 7.6.2 THE WALL: THE CONVERSE OF THE FREEZE

The freeze says: **box ⇒ (in-region ∧ fresh_shape ∧ w = 0)**.  Every
refutation runs off that implication.  What `ireg_free_au` needs is the
**converse**:

> `c ≠ None` ⇒ the record is in that arm at that shape.

That converse is `(L6) c ≠ None → inreg` conjoined with
`(L2) c ≠ None → fresh_shape d`.  And:

- **(L6) is R5's forbidden clause,** and R5's reason is exact and
  re-confirmed against the landed code: `ireg_withdraw` flips the arm on
  every firing, so it would owe `c = None` back, and `SpecIlock` takes
  no licence — §20.16.3, §20.16.5(e), §20.17.6(B).
- **(L2) is unpreservable at the two record-moving movers.**
  `ireg_write_au` carries `di_type_stable` and `di_nlink_stable` and
  nothing about `c`; `ireg_write_link` raises `nlink` and mints an
  `ilink`.  Given (L2) before and a write that breaks `fresh_shape`, the
  mover must produce `c = None` after, and it has no source.  Threading
  it as a premise ripples to `SpecIupdate` (3 bodies), `SpecWritei`,
  `SpecItrunc`, `SpecDirlink` — and the premise it needs *is the goal*.

**Without the converse, `c = Some` at iput's free is compatible with a
perfectly ordinary live record.**  §19.5(h) said the region cannot tell
a virgin box from a truncated corpse; the sharper statement is: **it
cannot tell a box from a file whose claimant never spent its token.**

#### 7.6.3 THE AFFINITY FINDING — new, and load-bearing

Nothing in option (k) forces the claimant to spend.  `fdetached` is an
affine Iris resource; `ireg_write_link` preserves (L5) *for free*
(`di_type_stable` pins the type), so the commit takes no token, and
create may simply frame the token away.  **After that drop,
`c = Some (Excl ty)` is pinned at the authority forever, and
`ireg_free_au`'s `c = None` becomes permanently underivable at an inum
the kernel frees on the most ordinary trace in the filesystem: `create`
then `unlink`.**  §19.7's rule — a resource may not forbid a
machine-reachable step — landing on the claim token itself.

Forcing the spend requires a mover to *demand* the token, i.e. an
option-indexed input on `ireg_write_link`/`ireg_write_au` whose `None`
branch must prove `c = None`.  Same wall, one mover further out.
**This is a price correction §5.2's table does not carry: F1.5c's real
cost includes the five-contract ripple, or F1.5d is false by leak.**

And in its general form:

> **`c = None` is an ABSENCE claim about an exclusive ghost fragment.
> An authority can only tell you a fragment is PRESENT (you show it
> one).  Absence is not observable.  So the free's premise is discharged
> either by holding the token — which only the claimant's own disposal
> can do, and create's disposal path proves the claimant never holds it
> that late — or by a region clause that manufactures absence from
> something the freer *does* hold.  The record cannot ((L2)); the arm
> cannot ((L6)/R5).**

That single sentence subsumes §20.16.5(a)–(f), §20.15(ii) and
§19.5(e)/(f).

#### 7.6.4 THE THIRD COUPLING, AND WHY IT DIES: THE CLAIM'S HORIZON

The certificate route couples `c` to neither the record nor the arm, but
to the **reference**.  Its temporal half is sound and is credited
precisely, because it is the first thing in five probes that escapes
§20.9(b):

- `iref_lookup` gives `n = 1 → q = qt` — genuine REF-1 **exclusivity**,
  not a counter, so §20.15's objection (ii) ("`auth nat` yields
  presence, the free needs absence") does **not** apply;
- a free ends the entry's occupancy (`ip->ref--` → eviction, §13.9), and
  the second generation bump fires **inside** the itable-lock window at
  +0x54, whose banner is explicit: *"every reference minted after it —
  including ialloc's — names the NEW generation, and every one that
  existed before is refuted by REF-1"*;
- therefore **within one occupancy no free of the inum precedes any
  other event**, so `c` cannot go `None → Some` inside it.  **That is
  real currency, from the cache, where §19.5(g)'s inum-keyed epochs had
  none.  This is the synthesis's one genuinely new gear.**

It dies on the mint side.  The soundness of a certificate meaning
"`c(z) = None`" must be re-established by **every mover that sets
`c := Some`, i.e. by `ireg_claim_au`** — which must show no certificate
for `z` is outstanding.  And:

```coq
(* InodeRegion.v -- ireg_claim_au takes NO caller resource *)
    ireg_inv γi γfs inodestart nib -∗ |={E, E∖↑iregN}=> ∃ bsl', fsblock … ∗ (… ={…}=∗ True)
```

**`ireg_claim_au` fires holding exactly the region invariant and the
dinode block's bytes.  That is its horizon.**  It holds no itable lock,
no entry, no marker, and `ProofIalloc`'s own spatial context at its
`iget` confirms it carries nothing per-inum at all.  The certificate
lives in the cache, outside the horizon.  So its absence is unverifiable,
and §19.5(f)'s trichotomy applies verbatim: a ticket the claim must
consume makes `ireg_claim_au` unprovable; one it ignores is
stale-indistinguishable; a persistent one can never be re-issued.

Binding the certificate *into* `inode_ref` fixes the enumeration (REF-1
exclusivity does it for free) but (i) needs an option index, because
iput must spend it at the free while keeping its reference through
+0x7a, and (ii) puts an arity on the single most-carried resource in the
fs tree — §16.5's packaging argument at maximum blast radius, worse than
a new gname.

> **THE FIFTH WALL, NAMED — THE CLAIM'S HORIZON.**  *Every discharge of
> `c = None` at the free requires `ireg_claim_au` to re-verify the
> coupling that makes the discharge sound — i.e. to verify the ABSENCE
> of the freer's receipt.  The claim sees only its own region slot and
> the dinode block's bytes.  The record and the arm are inside the
> horizon and are dead ((L2)/(L6)+R5).  Everything that can discriminate
> a box — the licence, the reference, the entry, the occupancy, the
> marker — is outside it.*

This also **explains** the graveyard rather than merely joining it:
§20.16.5(f) (the marker is behind the itable spinlock ialloc does not
hold), §19.5(e) (the marker's value is writable only by the fill and the
free), §20.7's (M1) — all three are the horizon argument in local
costume.  And it explains why **K-F2 was the unique cheap door**:
holding the dinode buffer across the `iget` is the one move that drags
the licence *inside* the claim's horizon.  R13(iii) closed that door by
policy.

#### 7.6.5 THE PINCER

| pole | obligation lands on | why it dies |
|---|---|---|
| **A** | `ireg_withdraw` (arm-coupled, (L6)) | needs a licence at `ilock`; `namex` ilocks the child *after* `iunlockput(parent)`, so the fragment is back in the parent's parked payload — §20.16.5(e) |
| **B** | `ireg_free_au` (record- or reference-coupled) | needs the ABSENCE of an exclusive fragment; only a clause the claim can maintain yields it, and the discriminating evidence is outside the claim's horizon |

(L5)'s achievement is real and stands: it **moves the obligation from A
to B**, which is the escape from §20.16.3 and is why five of six movers
are free.  The finding is that **B is now closed too**, and that A and B
are the same fact seen from two sides — §20.7's *"the reference that
outlives its licence"*, which each probe has hit from a different
direction.

#### 7.6.6 Point-by-point on the certificate design

| step | verdict |
|---|---|
| birth certificate, issuer = the iget | **shape sound, mint unsound.**  The corrected issuer is right (iget holds the licence, including on the recycle at +0x7c).  But the mint needs `ireg_inv` on `SpecIget` (absent today, cheap to add) *and* the licence→`c = None` implications, of which **LinkedL needs (L7) `c ≠ None → w = 0` and HeldL needs (L6)**.  (L7) has exactly one owing mover, `ireg_write_link`, and its discharge is the goal.  (L6) is R5. |
| no-reclaim-while-referenced | **the argument is CORRECT and the ingredients are landed.**  Better stated as *no free within one occupancy*.  Not enough: it makes the past fact current, but nothing makes it *mintable*. |
| certificate's home | **it can ride `ic_payload`, and `ic_payload` is the right home** — sole home of the `ity` family, named in 3 files, whereas `ic_loaded` is named in 19.  iput **can** read it there: at the free it holds the checked-out `ic_payload_at` from +0x3c, the entry sleeplock, and *not* the itable lock. |
| a ClaimL-born entry reaching a free | **the token dies at the +0xc4 commit; the `ilink` dies at the +0x14c unlink flush; the freeing iput at +0x152 gets neither.**  A ClaimL-born entry reaching a free is the *normal* case, and it must conclude `c = None` from the certificate, not from a token. |
| c-frozen-while-fragment-out | **holds, and it is a corollary of the occupancy currency, not a separate lemma.**  It lets the certificate speak about the fill instant only, and the fill instant is exactly where the licence→`c = None` implication is missing. |
| eviction/re-iget during iput's life | **correctly impossible** (entry pinned by the reference). |
| re-establishment at every entry-birth | **needs the mint on the HIT arm too**, not just the miss/recycle — a hit-joiner inherits nothing.  That makes the certificate per-holder, not per-entry, which is what pushes it into `inode_ref` and into the horizon. |

#### 7.6.7 The reachability partition (presentation layer, not load-bearing)

Stated as an invariant, "every reference is rooted in reachability or in
a carrier" is a **whole-tree** proposition, and all three homes an
authority could have are dead (§20.9(c)/(d)/(e); R3 forbids it
outright).  §1.4 says the same from the resource side and it is a
*theorem*: `fnode i n` is holdable only while `i` is locked, so
`fs_rep t` is unholdable by any thread and reachability is unstatable as
a client assertion.  But the licence disjunction **already is** the
partition, localised to one inum and made evidence-in-the-present:

| class | witnessing licence | carrier |
|---|---|---|
| 1 live-reachable | (a) LINKED, (c) HELD, (f) ROOT | an in-edge / the record / the root clause |
| 2 unreachable-but-carried | (d) CLAIMED, (b) ORPHAN | `fdetached` / **nothing** |
| 3 unreachable-uncarried | — no licence exists | — |

**Class 2's grey case is the member with no carrier, which is exactly
why `igrey` concludes nothing.**  Read as the partition, G1's deletion
of the grey row is not ad-hoc pruning — it is the partition's own rule:
*a class-2 member with no carrier cannot licence a reference.*  And it
predicts S7's obligation: `sys_unlink`'s directory arm, at the moment it
creates an orphan, must **mint a carrier**, not merely recolour an edge.

**Recommendation:** land `live_reachable` / `fs_reachable_from` as
*pure* predicates in `FsTree.v` beside `fs_dirs_acyclic` — iris-free,
separable, no mover re-establishes it, F1a's precedent exactly.  **Do
not let it into a resource, an invariant, or a licence.**

#### 7.6.8 Two count corrections

`IG.wp_iget_sconf` has **five** application sites, not four (the design's
table predates `ProofNamexRoot`): `ProofDirlookup`, `ProofIalloc`,
`ProofIreclaim`, `ProofNamex`, `ProofNamexRoot`.  `wp_ilock_sconf` has
**11** consumer files, not 9 (`ProofCreate` alone applies it three
times).  §5.2's "+9 callers, 8 at `None`" undercounts by two.

#### 7.6.9 The lemma worth landing

`ireg_box_excl` in `InodeRegion.v`: *if the slot's arm is IN and
`di_type d ≠ 0`, then `fresh_shape d`, `w = 0`, no `ilink z` exists, and
no client holds `dinode_at γi z d'`.*  Pure composition of `ireg_in`,
`ireg_link_ok`, `link_w_ge`, `dinode_at_excl` — additive, no clause, no
consumer required, and it is T1's formal content that every future
attempt re-derives by hand.

**The candidate space for the second door is now closed:** record (dead,
(L2)), arm (dead, R5/(L6)), reference/occupancy (dead, horizon), marker
(dead, horizon), log receipts (`logged_at` is *persistent* — §20.9(b)
with §19.5(g)'s currency gap, dead on arrival).

---

### 7.7 THE OWNERSHIP-TRANSFER PROBE — THE CONSERVATION LAW

**The reshape dies — and it dies further from the summit than the (L5)
design it would replace.**  The proposal: `ireg_claim_au` pays out
`dinode_at γi inum (ialloc_fresh ty)` — GoNFS/Perennial's
allocator-transfers-ownership idiom — so that type/shape stability
becomes a *frame* rather than a lemma.

#### 7.7.1 The custody map, verified from code

```coq
Definition ireg_slot γi z d :=
  ((∃ w g r c, link_auth z w g c r ∗ ⌜ireg_link_ok d w⌝ ∗ ⌜ireg_root_ok z d w⌝)
   ∗ ireg_ep z d
   ∗ ((⌜ireg_in d⌝ ∗ z ↪[γi] d)                       (* IN  *)
      ∨ (⌜bv_unsigned (di_type d) <> 0⌝ ∗ imark γi z))) (* OUT *)
```
with `ireg_in d := di_type d = 0 ∨ fresh_shape d` and
`imark γi z := ∃ d, imark_key z ↪[γi] d` at `imark_key z := -(z+1)`.

| inum state | region arm | fragment `z ↪[γi] d` | marker `imark γi z` |
|---|---|---|---|
| uncached FREE | IN (`type = 0`) | **in region** | `ipool_shape` free arm — itable spinlock |
| uncached CLAIMED | IN (`fresh_shape`) | **in region** | pool, same place — **unchanged by the claim** |
| uncached ALLOCATED | OUT | `ipool_alloc` | in region |
| cached-UNLOADED | IN or OUT per above | `ic_unloaded` ⊃ `ipool_shape` | ditto — the entry's sleeplock |
| cached-LOADED | OUT (forced: `inode_ok` ⇒ `type ≠ 0`) | `ic_loaded` | in region |
| holder in critical section | OUT | the holder's hand | in region |
| iput between free-flush and re-park | IN (`type = 0`) | absorbed by `ireg_free_au` | **iput's hand** (`ireg_out_free_inv`) |

> **THE CONSERVATION LAW, and it is a fact about the code, not a design
> preference.**  `IcacheBoot.v:570` allocates the record map and the
> marker map in ONE `ghost_map_alloc (ireg_M0 dss nib ∪ ireg_MK nib)`;
> `InodeRegion.v:653-654` states the consequence — *"no marker entry is
> ever updated -- only moved."*  A region-internal MINT of a second
> `imark γi z` is impossible twice over: the key is already occupied in
> the auth map (`ghost_map_insert` needs absence) and `imark_excl`
> refutes the pair directly.

#### 7.7.2 Where the chain snaps — three breaks

The claim pays out `dinode_at`, so the claimed slot must move to an arm
with the fragment **out**.  Both existing arms are unavailable: OUT
demands an `imark` the region does not have (it is in the pool) and
ialloc cannot supply.  So the reshape forces a **third arm holding
nothing**:

```coq
  ∨ (⌜fresh_shape d⌝ ∗ emp)        (* CLAIMED: fragment out to the claimant,
                                       marker ALSO out, in the pool *)
```

**Break 1 — `ireg_free_au` cannot pay.**  Its caller holds `dinode_at`;
arm IN is refuted by `dinode_at_excl`; arm OUT is today's case (marker
in, hand it out); **arm CLAIMED holds no marker and cannot be refuted**
— the freer holding a fragment while the region is at CLAIMED is exactly
"the claimant frees its own box", consistent in the logic.  `iput` needs
that marker to re-park.  *No premise fixes it:* the only thing that
refutes CLAIMED is a marker, and iput holds none until the lemma pays it.

**Break 2 — the repair that makes the arms disjoint is dead on a landed
certificate.**  Try `OUT := ⌜type ≠ 0 ∧ ¬fresh_shape d⌝ ∗ imark`.
§19.5(h) is verbatim fatal: *"a legitimately freed inode's record at
`ireg_free_au` is post-itrunc — type ≠ 0, size 0, addrs zero, nlink 0 —
which is LITERALLY `fresh_shape`.  The region cannot tell a virgin claim
box from a truncated corpse."*  Every ordinary iput of a truncated inode
would land in CLAIMED.  And it breaks one step earlier too:
`ireg_write_au` "keeps the arm where it is" — itrunc's flush turns a
real record into a `fresh_shape` one, so it would have to migrate
OUT→CLAIMED and drop a marker into the void.

**Break 3 — `ireg_withdraw` loses exhaustiveness, which is the entire
reason §16.5 built the marker.**  The filler holds the marker, refutes
OUT, and must then choose between IN (fragment there — today's payout)
and CLAIMED (fragment gone).  It cannot.  `ProofIlock`'s third fill
sub-arm is the live site, reached by **any** `wp_ilock_sconf` caller,
`fr = None` included.  Not hypothetical: §17.6.1/§19.9.1 step 3 certify
the trace against landed contracts — iput past its regen at +0x54 with
the lock released at +0x5c leaves a foreign referrer at REF-1 on the
claimed inum's entry; that referrer carves a share and `ilock`s, and
`ProofIlock`'s branch runs with no fragment in hand.  §19.9.1 records
this is a **model gap, not an object-code defect** — but a proof
obligation does not care.

#### 7.7.3 The statements, at Coq level

```coq
(* CLAIM — provable.  Premises unchanged (type-0 at the slot refutes both
   nonzero arms); (L1)/(L4)/root all re-established exactly as today. *)
Lemma ireg_claim_au … :
  … ={E∖↑iregN, E}=∗ dinode_at γi inum dn'.          (* was: True *)

(* FILL — the option-indexed input, R6's shape. *)
(fr : option dinode) …
  (match fr with Some dn0 => dinode_at γi inum dn0 | None => emp end) -∗
  post: ic_loaded … dn bm ∗ ⌜fr = Some dn0 -> dn = dn0⌝
(* fr = Some: create's own fragment IS ic_loaded's dinode_at; di_type dn = ty
   and fresh_shape read off the caller's frame.  THE AXIOM'S CONTENT IS FREE.
   fr = None at a CLAIMED slot: NO SOURCE.  ProofIlock wedges. *)

(* FREE — unchanged in statement, UNPROVABLE in body (Break 1). *)
Lemma ireg_free_au … dinode_at γi inum dn -∗ … ∗ imark γi (bv_unsigned inum).
```

**What the reshape genuinely proves, and it should be kept regardless of
its fate:** *ownership of the region fragment is a strictly stronger and
strictly cheaper carrier of the fresh-type fact than any ledger clause —
it makes stability a frame, not a lemma, and it kills the
recycle/incarnation question (§3.5) and the (L6) trap (R5) outright.*
No (L5), no `c` widening, no `iclaim`, no `IcacheRef` sweep, no
boot-mint change, no twice-instantiate exposure.  **The reshape's price
is genuinely lower than (L5)'s.  Only its wall is higher.**  (And it
confirms `c`/`iclaim`/`iref_lic` are dead weight: zero consumers outside
`IcacheRef.v`.)

#### 7.7.4 §19.7 at every reshaped step

- a second `ialloc` scan — **fine**, refuted purely on the buffer's
  nonzero type;
- a concurrent `iget` — **fine**: the fragment is a frame across
  brelse/iget, and the entry/pool still hold the marker on both MISS and
  HIT arms.  **The entry for a claimed inum holds the MARKER, and that
  survives the reshape unchanged** — which is exactly why the fill can
  still *reach* the broken branch;
- **the foreign FILL — BLOCKED.**  §19.7 violation, machine-reachable
  per §17.6.1;
- **the foreign FREE — BLOCKED, and this is the trap.**  Ownership kills
  §19.3(d)'s free-and-reclaim hazard outright (the thief's
  `ireg_free_au` needs the fragment create holds), which *looks* like
  the headline dividend.  It is §19.5(h) verbatim — *"block the thief's
  FREE instead of the thief's REFERENCE.  DEAD"* — and §19.7's
  generalisation: *"ANY blocker of a reachable step is dead, whether it
  blocks a fill or a free."*  The reshape does not make the hazard
  false; it makes the thief's proof stuck;
- the mid-free freer's re-park — **BLOCKED via Break 1**.

#### 7.7.5 GoNFS / Perennial, honestly reconstructed

Their allocator abstraction owns a free set plus the resources of the
free objects, and `alloc` atomically transfers one out.  Three
structural preconditions make that sound there and absent here:

1. **The allocator is the only namer.**  Free ⇒ unreachable is the
   allocator's own invariant.  Our analogue is §19.6's single
   proposition — *"no thread other than the claimant can name a
   just-claimed inum"* — which is true of xv6 and **unstatable in this
   development** (`SpecIget` takes an arbitrary inum; `dir_ok` gives
   range, never allocatedness).
2. **One serialiser.**  Their alloc and the object's lock are the same
   discipline; ours has two custodians — the buffer-serialised region
   (§16.2) and the itable-serialised icache — and the icache can
   independently name the claimed inum.
3. **One transaction.**  Their alloc-and-initialise is inside a single
   journal op, so no observation window exists.  xv6's window is
   claim(+0x9a) → brelse → iget → return → create's ilock, and the model
   must reason across it.

**Our region invariant IS that allocator, minus precondition 1.**  The
claim's payout shape is the easy half; the disjointness invariant is the
whole bill, and it is F1.5d's gate under another name.  **The
ownership-transferring claim is a CONSUMER of allocatedness, not an
alternative to it.**

#### 7.7.6 Re-open price (recorded for after allocatedness lands)

| contract / file | move | precedent |
|---|---|---|
| `SpecIalloc.v` (gen + sconf) | success arm gains `dinode_at γi inum dn'`; the three pure conjuncts become derivable | landed payout retrofits |
| `SpecIlock.v` + ~11 callers | option-indexed input, 10 at `None` | R6 / `filled` |
| `InodeRegion.v` | third arm; `ireg_slot_intro` arity; six movers re-case-split; `ireg_claim_au` payout | `ireg_slot` named in 4 files only |
| `ProofIlock.v` | third fill sub-arm splits `Some`/`None` | — |
| `ProofIalloc.v` | fragment framed across +0x9a…+0xaa (4 seams) | — |
| `ProofCreate.v` | one hypothesis out, four instructions in (+0xa4..+0xb0) | `SpecCreateFreshTy.v:85-86` |
| `SpecCreateFreshTy.v`, `LinkCreateFreshTy.v` | **DELETE** (−640) | — |
| `IcacheRef.v`, `IcacheBoot.v`, `IcacheEscrow.v`, `SpecIget.v`, `SpecIupdate.v` | **no move** | — |

Materially cheaper than F1.5c's (L5) sweep — and it *deletes*
`c`/`iclaim`/`iref_lic` as dead weight rather than reviving them.
**Worth keeping on file.  Not worth staging**, because every increment
reopens `ireg_withdraw`'s exhaustiveness on the first commit; there is
no additive prefix.

> **DEATH CERTIFICATE (ownership transfer), in the architecture's own
> terms.**  *THE CLAIM CANNOT PAY OUT THE FRAGMENT BECAUSE THE REGION
> WOULD BE LEFT HOLDING NEITHER TOKEN.  The {fragment, marker} pair is
> conserved from `IcacheBoot`'s single `ghost_map_alloc`; the claim has
> nothing to deposit, so the free has nothing to withdraw, and the fill
> has nothing to conclude.  §20.16.5(f) upheld, generalised from "cannot
> TAKE" to "cannot EXCHANGE".*

#### 7.7.7 THE ORDERING FINDING (the probe's own headline)

> The reshape's fill obligation and (L5)'s free obligation are **the
> same proposition** (§19.6's one sentence — "no thread but the claimant
> names a just-claimed inum", i.e. GoNFS's *the-allocator-is-the-only-namer*,
> i.e. **allocatedness**) arriving at two different lemmas.  (L5) puts
> it where the residue **has a route** (§20.17.5's enumeration +
> `isdirempty`, whose plank is landed, + the root clause, landed).  The
> reshape puts it where §20.16.5(e) certified it undischargeable at the
> call site.  **That ordering is the finding.**

**This sentence and §7.6.4's horizon are in apparent tension, and the
resolution is §7.9.**

---

### 7.8 WHAT HAS LANDED SINCE THE PROBES RAN

The probes read `c105ad60` / `3e8d4c3e`.  Verified at HEAD `e50a6508`:

- **`dir_dots_ix` AND `dir_orphan_clean` are BOTH in the payloads** —
  `IcacheEscrow.ic_loaded` and `ipool_alloc` each carry
  `⌜dir_dots_ix (bv_unsigned inum) dn data⌝` and
  `⌜dir_orphan_clean dn data⌝`, discharged across `IcacheBoot`,
  `ProofCreate`, `ProofIlock`, `ProofFilewrite`, `ProofSysLink`,
  `ProofSysLinkTails`, `ProofSysOpenParts`, `SpecKexecB2`.  **The
  record-backed probe's G2 blocker (`ProofSysLinkTails`' `ip->nlink--`)
  CLEARED.**  R13(vi)'s S7-plank is therefore no longer owed as a
  design step; it is landed machinery.
- **The root clause is landed and ratified** (R9): `ireg_root_ok` on
  `ireg_slot`, with `ireg_root_ok_alive` as the chartered projection.
- **`SpecSysUnlink.v` and `ProofSysUnlinkParts.v` now exist** (S7 is in
  flight; the T_DIR re-park has one missing premise, recorded at HEAD).
  `ProofSysUnlinkParts` is a new `igrey` consumer — **the grey
  conversion is becoming live**, which is R12's condition for building
  on grey provenance.
- **T1 IS LANDED.** `iris/IregBox.v` (a leaf, zero dependents, folded back
  into `InodeRegion.v`/`FsBlocks.v` at a milestone) carries
  `ireg_box_fresh`, `ireg_box_w0`, `ireg_box_excl`,
  `ireg_claim_box_freeze` and `ireg_box_no_payload`, plus the two flanks
  `fsL_block_exclusive` (§7.2.4 phase 1) and `iref_two_not_ref1` (§7.2.4
  phase 3, REF-1 as a refutation).  All seven are `Closed under the global
  context`.  `ireg_box_excl` is stated as a **dichotomy** rather than under
  an IN-arm hypothesis, because IN-ness is not nameable from outside the
  region (§7.4.3): at a nonzero-type slot either the region holds the
  MARKER (the record is checked out) or the slot is a box, and then
  `fresh_shape`, no `ilink_fl` of any flavour, and no client `dinode_at`.
- **C′ is still unlanded**: no `IgetLic.v`, no `ilic`, and `SpecIget`'s
  only resource premise is still `iref_slot`.

---

### 7.9 THE CONSOLIDATION — resolving §7.7.7 against §7.6.4

The seventh probe says (L5) puts allocatedness "where the residue has a
route"; the sixth says the route's terminus is the claim's horizon.
**Both are right, and they are not about the same obligation.**  The
route the seventh probe names discharges the *licence enumeration* at
`SpecIget` — the (b)-GREY residue §20.17.5 left open.  The horizon
closes the *`c = None` premise* at `ireg_free_au`.  Composing the landed
planks makes the first genuinely reachable and leaves the second exactly
where the sixth probe put it.

**What now composes (and this is more than any single probe had).**
With `dir_orphan_clean` landed in both payloads (§7.8), G1's token
deletion available unconditionally, and the root clause landed:

1. §7.5.6's disjunctive `SpecDirlookup` premise has **all six suppliers
   in the tree**, and the payload conjunct it needs is no longer owed.
2. Row (b) therefore deletes from `iname`; §20.17.5's shelter paragraph
   becomes a contract obligation, discharged once per site.
3. C′'s five rows reduce to four supplied plus (d), whose only
   instantiation is `ProofIalloc`'s `iget`, which R13(iii) foreclosed by
   rejecting K-F2.
4. §7.6.1's box-exclusion (`ireg_box_excl`) refutes LinkedL, HeldL and
   RootL at a box **for free, from the IN arm**, with no clause at all.

**What still does not compose.**  Steps 1–4 give a *complete, closed,
supplied* enumeration at the point of DELIVERY (`SpecIget`).  The free's
premise is owed at `ireg_free_au`, where iput holds no licence — §7.1.6,
§20.9(f), §20.7 — and where discharging it requires `ireg_claim_au` to
verify the absence of a receipt it cannot see (§7.6.4).  The three
missing pieces are, precisely:

- **the converse of the freeze** (§7.6.2): dead at the record ((L2)) and
  at the arm ((L6)/R5);
- **the affinity leak** (§7.6.3): even a perfect enumeration leaves the
  token droppable, so F1.5d is false by leak on `create; unlink` unless
  a mover *demands* the token — a five-contract ripple, and the premise
  it needs is the goal;
- **the currency gap** (§7.2.4 phase 2): the one interval in which the
  claimant holds nothing revocable, deleted only by K-F2.

**RULING (2026-08-16): `create_fresh_ty` is NOT retirable by the
composition.**  The landed planks retire §20.17.5's *paragraph*, not
§20.7's *wall*.  The axiom's justification is this section: it is the
single proposition §19.6 names — *no thread other than the claimant can
name a just-claimed inum* — which is true of `f60ff58`, is not a tree
fact, is not a resource fact, is not a certificate fact, and is a fact
about the instruction order inside `ialloc`.  The two remaining imports
are unchanged: **K-F2** (rejected by R13(iii); priced at three kernel
lines plus `ProofIalloc`'s re-walk) or **weakening `SpecCreate`'s made
arm** (§7.2.6's third door; unaudited, and it breaks ARM C-OK-DIR's
`dirlink(ip, ".")`).

**AMENDED, and this closes the record (§7.10, the seventh and FINAL
ghost-side route).**  The protocol-ghost probe upgrades the ruling from
an enumeration of dead candidates to an exhaustion argument: a
claim→fill protocol has exactly three stations (MINT, HAND-OFF, RESET)
plus a PAYOUT, every carrier of the episode pin kills exactly one of
them, and **the assignment space is exhausted** — bytes kill the RESET,
the arm kills the HAND-OFF, a client token kills the MINT (or leaks by
affinity), and pinning NOWHERE closes every station at the price of an
∃-typed payout that is byte-for-byte §19.9.2's already-landed ∃ty′.
The dichotomy is **LAW, not cost**.  So the standing conclusion is no
longer "no candidate has worked" but **"every ghost-only route is
excluded by law, and K-F2 is the unique door precisely because it is
the unique change that puts currency — the buffer half — into phase
2."**  Do not open an eighth ghost-side probe; the station-exhaustion
sentence and §7.3.1's marker sentence are now in
`SpecCreateFreshTy.v`'s header so the file itself says so.

---

### 7.10 THE PROTOCOL-GHOST ROUTE (probe 7) — station exhaustion, a LAW wall

Owicki–Gries in Iris: put the claim→fill handshake in an authority-side
*phase* rather than in a client-held token.  Read against the tree at
`90789dec` **plus the live uncommitted S7-unlink churn** — at the time of
the probe `ireg_slot` had become `link_auth z wl wd g c r` with
`ireg_dir_ok` as a third pure conjunct; **the arm structure, the `c` slot
and all six movers are unchanged in shape, so every argument below
survives the churn.**

> **VERDICT.  The protocol-ghost route is DEAD, and the certificate names
> a LAW wall — but it dies one wall LATER than all six predecessors, and
> the route's corpse is the most informative one yet: H1 is the first
> design in seven probes whose invariant is fully maintainable,
> §19.7-clean at every mover, and it dodges four of the five named walls
> outright.  It dies at the PAYOUT.**

#### 7.10.1 H1 worked out exactly, and it is BUILDABLE

The phase is a component of the slot's existential — authority-side
state, no client fragment:

```coq
Inductive iph := PhNone | PhClaimed (ty : mword 16) | PhFilled.

Definition ireg_slot (γi : gname) (z : Z) (d : dinode) : iProp Σ :=
  ((∃ (wl wd g r : nat) (c : option (excl unit)) (p : iph),
      link_auth z wl wd g c r
      ∗ ⌜ireg_link_ok d (wl + wd)⌝ ∗ ⌜ireg_root_ok z d (wl + wd)⌝ ∗ ⌜ireg_dir_ok d wd⌝
      ∗ ⌜iph_ok p d inreg⌝)                    (* THE PROTOCOL CLAUSE *)
   ∗ ireg_ep z d
   ∗ ((⌜ireg_in d⌝ ∗ z ↪[γi] d)                (* inreg = true  *)
      ∨ (⌜di_type d <> 0⌝ ∗ imark γi z)))%I.   (* inreg = false *)

Definition iph_ok (p : iph) (d : dinode) (inreg : bool) : Prop :=
  ∀ ty, p = PhClaimed ty ->
    inreg = true ∧ fresh_shape d ∧ di_type d = ty.     (* (P1) *)
```

(Mechanically, `inreg` is threaded by restating the arm disjunction with
the pure bit, or by putting `⌜∀ ty, p ≠ PhClaimed ty⌝` on the OUT arm —
same content.  `p` can even stay a bare existential rather than a CMRA:
since no fragment of it exists, "setting" it is choosing a different
witness at the close, which is the purest possible frame preservation.)

**Every mover's disposition, audited (§19.7 at each step):**

| mover | disposition | verdict |
|---|---|---|
| `ireg_claim_au` | sets `p := PhClaimed ty` at the type-0 slot.  Old phase: `PhClaimed` refuted purely ((P1) gives `fresh_shape` ⟹ type ≠ 0 against the buffer's 0, through `ireg_couple` — the same `exact (Ht2 Ht0)` pattern already landed); `PhNone`/`PhFilled` overwritten freely.  (P1) re-established from its own `fresh_shape dn'` premise and `di_type (ialloc_fresh ty) = ty`.  **Takes no caller resource, stays universally firable, frame-preserving against every frame** — §7.4.4's constraint is satisfied *by construction*, because there is no client copy to collide with | ✓ |
| `ireg_write_au` / `_link` / `_unlink` (all flavours) | each takes `dinode_at γi z dn` — so at `PhClaimed`, (P1)'s `inreg = true` puts the fragment in the region and `dinode_at_excl` refutes the phase before the write is even considered.  (P1) preserved **vacuously**; no premise travels to `SpecIupdate`/`SpecWritei`/`SpecItrunc`/`SpecDirlink`.  **This is T1's freeze doing the work, and it is the first design in which the freeze is load-bearing rather than decorative** | ✓ |
| `ireg_withdraw` | the hand-off.  Flips the arm, so it owes `p ≠ PhClaimed` after — **and it can pay, itself, region-internally: `p := PhFilled`.**  No `iclaim` consumed, no licence demanded, no option index, and the foreign marker-holder's fill (the §16.4 killing trace, §17.6.1's mid-free referrer) closes identically.  **R5's wall — §20.16.3/§20.16.5(e) — is DODGED**, because the obligation was only unpayable when the phase was a client fragment.  A fill at a *non*-claimed box cannot "hit Claimed wrongly": post-boot a box arises only via the claim (free exits to type-0/IN; ordinary writes run at the OUT arm; itrunc's fresh-shape-shaped corpse is OUT in the holder's hand and is absorbed by the free as type-0), and boot stamps any image box `PhClaimed (di_type d)` | ✓ |
| `ireg_free_au` | **the crux, answered:** the free holds `dinode_at γi inum dn` (its own signature).  (P1) says `PhClaimed → inreg = true`; the freer's fragment says the arm is OUT (`dinode_at_excl` — the *exact* two lines §20.16.3 wrote for `c ≠ None → inreg`, pattern already landed at the free's own arm-refutation).  **So `PhClaimed` at any free is REFUTED IN THE MODEL, unconditionally** — no reachability argument, no gamble, no block.  The free then sets `p := PhNone` ((P1) vacuous at the type-0 record).  And separately: free-at-mid-claim is machine-UNREACHABLE on `f60ff58` (a free needs a checked-out fragment; mid-claim it is in-region; extracting it needs a foreign withdraw, which needs a foreign namer of the just-claimed inum, which §7.2.7's honest residue excludes) — **but the proof never needs that fact** | ✓ |
| boot (`IcacheBoot.ireg_alloc`) | choose witnesses: `p := PhClaimed (di_type d)` at any in-region `fresh_shape` record, `PhNone` elsewhere.  **Zero image obligation** — (P1) holds definitionally | ✓ |
| eviction / re-park / `ireg_read` / obs lemmas | phase is per-inum, region-side: entry death (`ic_close_to_empty`) never touches it.  **BORN BEFORE THE ENTRY is dodged** — the phase exists before, during and after any entry, which no entry/generation-keyed candidate ever managed.  Openers re-close with the same witness | ✓ |

**And the conservation law is dodged too**: the claim deposits nothing
and the free withdraws nothing — the phase is not a token moved but
authority state rewritten; the {fragment, marker} conservation from
`IcacheBoot`'s single `ghost_map_alloc` is untouched.

So: consistent, frame-preserving, boot-cheap, no contract moves, no
§19.7 violation anywhere, and it steps past **four walls by name** — the
conservation law (§7.7), born-before-entry (§7.4), the converse of the
freeze (§7.6.2: H1 needs only `Claimed → box`, never `box → Claimed`),
and R5-at-the-withdraw (§20.16.3).  The affinity leak (§7.6.3) is dodged
trivially: nothing client-held exists to drop.  The claim's horizon
(§7.6.4) is dodged at the *mint*: this claim verifies no absence — it
overwrites.

#### 7.10.2 THE DEATH: the payout is ∃-typed — the episode-blindness theorem

What does create receive?  `SpecIalloc`'s post is pure and
claim-time-indexed (`dn' = ialloc_fresh ty` — "says nothing about the
region at RETURN time", its own header).  Under H1 it stays that way:
**the claim pays no resource, because there is none to pay.**  At
create's `ilock`, the withdraw reads the phase at its own fupd and can
pay at most:

```coq
∃ ty', ⌜p_pre = PhClaimed ty'⌝ ∗ ⌜di_type dn = ty'⌝ ∗ ⌜fresh_shape dn⌝ ∗ dinode_at γi inum dn
```

`ty'` is existentially bound.  **Create cannot pin `ty' = ty`, and this
is a theorem, not a gap:**

> **THEOREM (episode blindness).**  Let R be create's entire
> spatial+pure context at its `ilock`.  The interference sequence
> I = ⟨foreign `iget` of z (admissible: `SpecIget` takes only
> `iref_slot` today; under C′, licence (b)/(e) is honestly *satisfiable*
> at a claim box — TRACE G, §7.5.4); foreign `ilock` → `ireg_withdraw`
> (closes under H1 by design: `PhClaimed ty → PhFilled`); foreign `iput`
> at REF-1/nlink-0 → `ireg_free_au` at `PhFilled` (proceeds —
> `PhClaimed` is not there to refute it); third `ialloc` re-claims at
> ty₂ → `PhClaimed ty₂`⟩ consists entirely of frame-preserving updates
> fired by movers that are landed, green, and universally provable.
> Hence R is preserved verbatim across I.  After I the withdrawn record
> is `ialloc_fresh ty₂` with the phase a perfectly well-formed
> `PhClaimed ty₂`.  So R ∧ (everything derivable from R at the withdraw)
> is consistent with `di_type dn = ty₂ ≠ ty`, and `di_type dn = ty` is
> underivable.  ∎

This is §7.4.4's general impossibility, extended from client
certificates to authority-side registries: **the claim's universal
firability makes every episode reset invisible to every client frame.**
The phase can hold facts about the *box* (it does — (P1) is true and
maintained); "this box is MY episode's" is not a fact about the box, and
the claimant has no identity in the region's algebra.

Note the exact yield: `∃ty', di_type dn = ty' ∧ fresh_shape dn` — which
is **byte-for-byte §19.9.2's ∃ty′ weakening, already landed** via
`SpecIlock`'s `filled` indicator plus `ireg_withdraw`'s `fresh_shape`
payout.  **H1's marginal content over the landed tree is zero.  A
protocol nobody can be paid by is a diary, not an escrow.**

#### 7.10.3 The repair escalation — every rung lands on a named wall

- **(r1) per-inum exclusive receipt** (claim pays an `iclaim`-like token;
  phase clause mentions it): the re-claim must reset a slot whose token
  is in an absent (or *departed* — affinity) claimant's hand → wedges
  `ireg_claim_au` at a machine-reachable step (§19.7) — §19.5(f) case 1
  + the affinity leak §7.6.3, verbatim.
- **(r2) per-episode fresh gname** (claim allocates γ_e, pays a half;
  phase = `PhClaimed ty γ_e`): fresh allocation keeps the claim
  frame-preserving ✓ — and the abandoned half in create's hand after a
  reset is **stale-indistinguishable** (two distinct gnames coexist
  without contradiction; create cannot pin the phase's γ to its own).
  §19.5(f) case 2.
- **(r3) epochs/counters** (`PhClaimed ty e`, create remembers `e`
  purely): "my `e` is current" = "no free since my claim" — needs a
  revocable, reference-tied resource across the window, and in phase 2
  (brelse→iget) the claimant holds nothing revocable.  **THE CURRENCY
  GAP, §7.2.4, verbatim** — and it is a fact about the instruction order
  in `ialloc`, not about ghost state.
- **(r4) persistent receipt**: §20.9(b), dead on free-and-reclaim,
  unchanged.

**The debt is conserved: H1 escaped the horizon wall at the mint by
verifying nothing there — and the unverified absence reappears,
undiminished, at the payout.**

#### 7.10.4 H2 — the dedicated protocol invariant: collapses into H1

The §20.9(e) arity question, answered precisely: the registry's content
*must* couple to the region's arm ((P1)'s `inreg` conjunct is what
closes the free).  A separate invariant cannot state a clause about
another invariant's interior; it needs a shared coupling ghost whose
authority sits in `ireg_slot` — at which point the phase *is* in the
region and the second invariant is vestigial.  If built anyway: the
gname **can** ride ambient `icfg` (the `icfg_link` dodge, §20.2 — so no,
it need *not* enter `ic_escrow`'s arity; §20.9(e)'s catastrophe is
avoidable), and the persistent inv assertion would still tour
`SpecIalloc` (+5 consumers), `SpecIlock` (+11), `SpecIupdate`'s cred
form (+`ProofIput` chain), `SpecCreate` — additive but wide — **plus** a
two-invariant mask discipline at three movers that today open once.
Strictly dominated by H1 in every dimension (COST), and it dies at H1's
wall regardless (LAW).  **H2 is not a distinct route; it is H1 with
packaging debt.**

#### 7.10.5 H3 — the thread/hart registry, full Owicki–Gries

Registry `gmap hart_id (option (Z * mword 16))`; clause
`∀ h z ty, reg h = Some (z,ty) → z's slot: inreg ∧ fresh_shape ∧ di_type = ty`.
The hart-keyed pin genuinely **fixes delivery** (create holds hart h's
exclusive registry fragment; agreement pins its own entry —
twice-instantiate passes, the `ty` is resource-related to `dn`).  Two
claims at one z cannot coexist (second claim refuted purely by the box's
nonzero type through the coupling — the freeze again).  The free closes
(same two-line arm refutation).

**It dies at the hand-off:** a *foreign* `ireg_withdraw` at hart h's box
flips the arm and must clear `reg h` — which needs hart h's fragment,
which the foreign filler does not hold and `SpecIlock`'s 11 callers
cannot supply (option-indexed input, `fr = None`: the None branch at a
mid-claim box has **no source** — not expensive, *sourceless*).  That is
§20.16.5(e)/R5 landing on the registry exactly where it landed on `c` —
and moving the clause off the arm onto the bytes
(`reg h = Some (z,ty) → di_type = ty`, no `inreg`) frees the withdraw
and re-kills it at the free, which writes type 0 and cannot clear a
foreign hart's entry — §20.17.6's option (k) death, verbatim.  The
hart-token's affinity is a third, independent kill: a dropped hart
fragment wedges that hart's *next* `ialloc` forever (§19.7), and the
only cure is welding the fragment into the hart's permanent machine
bundle — a change to the execution-model resources, the maximal blast
radius in the tree — which still leaves the withdraw wall standing.
**Dead by law; the cost is merely astronomical on top.**

#### 7.10.6 THE CERTIFICATE — station exhaustion (a LAW wall)

> **DEATH CERTIFICATE (protocol ghost / Owicki–Gries, all homes).**  A
> claim→fill protocol has three stations — the MINT (`ireg_claim_au`),
> the HAND-OFF (`ireg_withdraw`), the RESET (`ireg_free_au`) — plus the
> PAYOUT (create's ilock).  Every possible carrier of the episode pin
> kills exactly one station, and the assignment space is exhausted:
>
> - pin on the **bytes** (`c = Excl ty → di_type = ty`; option (k)) →
>   the RESET cannot clear it (§20.17.6(k));
> - pin on the **arm** (`Claimed → inreg`; (L6)/H3's clause with a
>   client-held reflection) → the HAND-OFF cannot clear it (§20.16.3,
>   §20.16.5(e), R5);
> - pin on a **client token** → the MINT is blocked or the token is
>   stale or unreissuable (§19.5(f)'s trichotomy), and affinity makes
>   even the good case leak (§7.6.3);
> - pin **nowhere** (H1, authority-side phase) → every station closes
>   and the PAYOUT is ∃-typed: by frame preservation of frame-preserving
>   updates plus the mint's universal firability, episode resets are
>   invisible to every client frame, so the strongest payable fact is
>   §19.9.2's ∃ty′ — already landed.
>
> The dichotomy is LAW, not cost: (i) frame preservation is a property
> of the logic (a frame-preserving update is valid against *all* frames
> — no client resource can obstruct it); (ii) the stations' movers must
> remain provable because each fires on machine-reachable instantiations
> elsewhere (§19.7, and `ProofIlock`/`ProofIput`/`ProofIalloc` are one
> generic proof each); (iii) the mint's emptiness of hand is the
> machine's own instruction order (`brelse` before `iget` in `ialloc`).
> The six prior certificates each explored one assignment; the
> protocol-ghost frame shows **the assignments are the whole space**.
> **Owicki–Gries does not create currency; it relocates the debt around
> the protocol, and the only payer is a revocable resource in the
> claimant's hand across the window — which phase 2 of the window
> denies.  THE COST-RULE EXCLUSION IS HEREBY UPGRADED: the route the
> cost rule excluded (K-F2) is the unique door because it is the unique
> change that puts currency (the buffer half) into phase 2; EVERY
> GHOST-ONLY ROUTE, PROTOCOL GHOSTS INCLUDED, IS EXCLUDED BY LAW.**

Cost-rule waivers audited along the way: `SpecIlock`'s option-indexed
registry input — waivable at ~12 files, then sourceless at `None` (law);
H2's arity — waivable free via ambient `icfg` (collapses to H1); H3's
hart-bundle threading — waivable at execution-model blast radius, then
dead at the withdraw (law).  **Nowhere does a cost rule stand between
this route and life.**

#### 7.10.7 What the probe yields

- **Positive findings worth keeping:** (1) H1 is the first *consistent*
  protocol — it dodges the conservation law, born-before-entry, the
  freeze-converse, R5, and the affinity leak, and its free-side
  refutation (`PhClaimed → inreg` + `dinode_at_excl`, two lines)
  rehabilitates §20.16.3's "the free half closes" in a form where the
  withdraw closes too; (2) free-at-mid-claim is machine-unreachable on
  `f60ff58` **and** model-refutable — the model is stronger than
  reachability here, a rarity worth recording; (3) the
  station-exhaustion sentence belongs in `SpecCreateFreshTy.v`'s header
  beside §7.3.1's marker sentence, **so an eighth probe does not re-open
  OG** (both are now transcribed there).
- **Nothing new to build.**  H1's machinery (~100–150 lines,
  `InodeRegion.v` only, zero contract moves) is **buildable and
  worthless** — its entire payout is already landed as `filled` +
  `fresh_shape` + ∃ty′.  §7.6.9's `ireg_box_excl` was the one lemma still
  worth landing and it is now landed in `iris/IregBox.v` (§7.8).
