# fs-state — the file system as nested separation-logic predicates, at two views

DESIGN OF RECORD for the durable-disk project (ruled by the owner,
2026-08-23, over a review of what stages E–G of the previous worklist had
landed).  Worklist: [`../projects/durable-disk.md`](../projects/durable-disk.md).
The crash-side mechanics it sits on: [`crash.md`](crash.md).  The previous,
superseded approach (a byte-level committed view, pure whole-state
well-formedness, per-op preservation lemmas, an object-granular pending
ledger) is archived with its history in
[`../completed/durable-disk-byteview.md`](../completed/durable-disk-byteview.md);
nobody reads that for guidance.

## 0. The guiding rule: LOCAL reasoning

Every spec in this design must let a proof about one inode, one directory
or one block be done **without bringing the whole file system into the
proof context**.  Concretely:

- No predicate above `inode_owned` states a pure fact about more than one
  inode.  Whole-state pure predicates (`fs_durable_wf`, `fsimg_wf`-style
  sweeps, "every used block belongs to exactly one inode", "nlink equals
  the number of entries") DO NOT EXIST in this design.  Where such a fact
  is needed it is a consequence of ownership (the `∗`) or of a resource
  algebra's own law (a counting RA), never a maintained clause.
- Disjointness is never stated.  Exclusive ownership gives the frame rule,
  and the frame rule gives independence of concurrent operations.  The one
  exclusivity law ever invoked is `own x ∗ own x ⊢ False`, used exactly as
  `l ↦ _ ∗ l ↦ _ ⊢ False` is used everywhere in Iris — to learn that two
  owned things are different objects — never as an invariant.
- There is no "tree".  The abstraction is a SET of inodes, some of which
  decode as directories.  Reachability, acyclicity and the tree structure
  of directories are not part of this project and appear nowhere below.
- The log knows nothing about the file system.  It exposes bytes and two
  logically-atomic linearization points, and parks an opaque client
  payload.  Sector atomicity, pictures, write lists and install arithmetic
  never appear above `SpecLogWrite`/`SpecEndOp`.

## 1. The view record `Γ`, and the byte points-to

```
Γ := { Φ     : Z → bv 8 → iProp Σ   (* byte ownership, by BYTE ADDRESS *)
     ; γlink : gname                (* the link-counting family *)
     ; γtop  : gname }              (* the top-level abstract map *)
```

Every predicate below takes `Γ` explicitly (the standing rule: ghost names
are parameters, not a config-class dependency).  The file system is
instantiated TWICE with the same definitions:

- **`Γ_D`, the committed (durable) view.**  `Φ_D a v := a ↪[γD] v`, the
  FULL element of a fixed-layer byte-keyed `ghost_map Z (bv 8)` whose auth
  is the committed byte view `D` inside `P_disk` (`crash.md`).  `γlink_D`,
  `γtop_D` are fixed-layer gnames.  The whole instance lives inside
  `crashN` (`P_wf`, §4); no mortal ever holds a piece of it (ruling 1).
- **`Γ_L`, the logged (in-era) view.**  `Φ_L a v := a ↪[fs_L] v`, the FULL
  element of the era's byte-keyed logged view whose auth the log owns
  (§5).  `γlink_L`, `γtop_L` are era-minted and die with the era — correct,
  because the logged view (uncommitted writes, their link tokens, their
  abstract values) must vanish at a crash.

**Bytes, not blocks, on both sides.**  The durable disk is byte-addressed
already (`DiskImg.disk_img_bytes`).  `fs_L` is re-keyed from block to byte
so that an inode record can own ITS 64 bytes of an inode block.  A
`bread` is "a block's worth of bytes arrive, most of which the caller does
not own"; `log_write` is block-granular at the device and byte-granular in
the ghost update (§5).  Ownership is EXCLUSIVE (full elements) — this is
what lets `free_bitmap`'s argument in §2 run, and it is why the bio layer's
agreement share moves to a bio-side map (§5).

**Functoriality in `Γ`.**  Every non-`Φ` component of `Γ` is an
allocatable ghost, the ghost components live INSIDE the nested structure
(never in a side invariant), and there is ONE mint lemma

```
fs_state_mint : fs_state Γ_D S -∗ (footprint S at Φ_L) ==∗ fs_state Γ_D S ∗ fs_state Γ_L S
```

that walks the durable instance and allocates `Γ_L`'s ghosts to match
(for each directory, as many fresh link tokens as it holds entries with
tokens, drawn from freshly allocated `link_auth`s).  That lemma IS the
boot mint (stage H1 of the worklist); there is no image decoding at boot.

## 2. The nested predicates

```
fs_state   Γ S        := sb_owned Γ S.sb ∗ fs_inodes Γ S.inodes ∗ free_bitmap Γ S.free
fs_inodes  Γ I        := [∗ map] i ↦ n ∈ I, inode_owned Γ i n          (* the one ∗-iteration *)
inode_owned Γ i n     := rec_owned Γ i n.rec
                         ∗ [∗ k ∈ slots n] blk_owned Γ (addr n k) (blocks n k)
                         ∗ (ind_owned Γ n when the indirect block exists)
                         ∗ link_auth Γ i (nlink n.rec)
                         ∗ ⌜local clauses⌝
dir_owned  Γ d n      := inode_owned Γ d n ∗ (the entry reading, with tokens, below)
rec_owned  Γ i dn     := byte_range Γ (IBLOCK i) (64·slot i) (dinode_bytes dn)
blk_owned  Γ b bs     := byte_range Γ b 0 bs                   (length bs = BSIZE)
byte_range Γ b off bs := [∗ list] k ↦ v ∈ bs, Γ.Φ (b·BSIZE + off + k) v
free_bitmap Γ F       := blk_owned Γ bmapstart (bm_bytes F)
                         ∗ [∗ b ∈ free_set F] ∃ bs, blk_owned Γ b bs
```

- **The inode node** `n = { rec; blocks : slot → bytes }` ranges over EVERY
  nonzero `addrs` entry (direct and, via the owned indirect block,
  indirect), REGARDLESS of `rec.size`.  An inode may own blocks beyond
  its size (`itrunc` frees them all; `writei`'s partial-failure commit
  leaves one) — the F3 ruling, built into the representation.  The
  abstract byte-sequence is a READING, not the ownership:
  `file_bytes n := take rec.size (concat blocks)`;
  `dir_entries n := dir_view (file_bytes n)`.  The one local clause the
  reading needs to be total is `bm_covers` (every slot below
  `nblk rec.size` is allocated).  Distinctness of an inode's own blocks is
  the `∗`.
- **Local clauses of `inode_owned`**: `type ∈ {DIR, FILE, DEV}`;
  `size ≤ MAXFILE`; `bm_covers`; `type = 0 → nlink = 0`; `nlink ≤ 32767`.
  Of `dir_owned`: `16 ∣ size`; "." ↦ self and ".." present; names unique.
  Of `free_bitmap`: nothing beyond the encoding (the block's bytes are
  `bm_bytes F`).  There is NO clause at `fs_inodes` or `fs_state` level.
- **`free_bitmap`, CSL-style.**  It owns the bitmap block and, for every
  block whose bit reads FREE (xv6: bit = 0), the block itself.  `bfree`
  hands a block in: if its bit read free, `free_bitmap` would already own
  it — two owners of one block — so the bit reads allocated and the
  "freeing free block" panic arm is dead.  `balloc` flips a free bit and
  takes that block out of the `∗`.  Nobody carries a bit resource; there
  is no "used set" and no completeness clause (a block nobody owns is a
  lost resource, which is what a leaked block is).
- **Links are a counting RA, not an equation.**  `inode_owned Γ i n` holds
  `link_auth Γ i (nlink n.rec)`; every directory entry OTHER THAN "."
  inside `dir_owned` holds one `link_tok Γ target`.  The RA's law gives
  `#tokens ≤ nlink`, and that is the direction safety uses: at `nlink = 0`
  no entry points at the inode, so it may be freed.  The tokens move
  where the code moves the counts, with both inodes locked as the code
  has them: `create` mints `link_tok i` from `ip`'s auth into `dp`'s new
  entry; `link`/`unlink` move one between the two locked inodes; `mkdir`
  moves one from `dp`'s auth into the child's ".." entry; unlinking a
  directory returns that token to `dp` and leaves the child's ".." entry
  TOKENLESS — the orphan form, which is exactly this kernel's "grey"
  record (`fs-icache.md` §20).  `isdirempty` is a local check on the
  child's entries.  The `≥` direction (no over-count) would only rule out
  an unfreeable file — a leak, not a corruption — and is not stated.

## 3. In flight, not inconsistent

Mid-transaction states (a block taken by `balloc` that no inode points at
yet; an inode record written before its directory entry) are NOT
"inconsistent views" — in resource terms they are pieces CHECKED OUT of
`fs_state Γ_L` into the open operation's hand, exactly as a locked inode
is.  The logged view is always `fs_state Γ_L S_L` minus what open
operations and lock holders hold; each piece returns at its new value
when its holder releases it (the `log_write` AU / `iunlockput` — where the
holder actually owns it; at `end_op` an arm holds nothing, see the 2026-08-23
survey in the archived worklist).  At group quiescence (`out = 0`) every
operation has ended, nothing is in flight, and the view is whole.

Consequences: there is no "row (a)", no abstract target state `A`, no
pure well-formedness projection, and NO per-operation finalize obligation
at `end_op`.  An operation's entire contribution is the sequence of LOCAL
steps at its AUs.

## 4. The two views and the top

```
fs_view Γ := ∃ S, ghost_map_auth Γ.γtop 1 S ∗ fs_state Γ S
```

- **Durable**: `P_wf := fs_view Γ_D`, held WHOLE inside `crashN`.  `γtop_D`
  is the durable abstract state; mortals never hold its fragments.  What a
  mortal may hold about durability is a PERSISTENT receipt minted from
  `γtop_D` at commit (the contents layer's sync receipts, `crash.md`).
- **Logged**: `fs_view Γ_L`, whose body lives in the log's parked payload
  (§5) so that it is at hand at every `log_write` and at commit, MINUS the
  pieces currently checked out.  A holder of `inode_owned Γ_L i n` also
  holds the fragment `i ↪[γtop_L] n`, which is how it updates the top at
  its AU (auth in the payload + its own fragment).
- The shape is the same at both views; only where the body sits and the
  piecewise checkout differ.  That is what makes a later userspace layer
  compatible: a program owning file `f` holds `f ↪[γtop_L] n`, reached
  through syscall-level AUs whose linearization point is where the
  fragment moves — the same pattern as the inode holder's today.

**The debt** — the only place two objects ever meet, and only as
composition.  The payload holds `Dbt`, a stored basic update from the
durable instance at the last commit to the durable instance at the
current logged values:

```
Dbt : fs_view-body Γ_D (at S₀) ∗ γD_auth D₀ ==∗ fs_view-body Γ_D (at S_L) ∗ γD_auth D'
```

`iModIntro` at batch start; each `log_write` AU composes one per-object
`Γ_D` step — the SAME local lemma it just ran on its `Γ_L` resources,
instantiated at the other `Γ`, with the `Γ_D` resources supplied as the
debt's input (never owned by the writer).  Its intermediate resources are
`fs_state`-minus-in-flight ∗ in-flight, never required to be anything; at
`out = 0` the chain ends at the whole `fs_view Γ_D` at `S_L`.  If the era
dies, the chain dies in the payload and `P_wf` still holds the last
commit: uncommitted work vanishes, as it should.  The commit AU (§5) is
the debt plus the byte-level fact the log supplies.

## 5. The log's interface (FS-agnostic, logically atomic)

The log exposes, and knows, only this:

- **The logged byte view `fs_L`**, a byte-keyed `ghost_map`: the log holds
  the AUTH in `log_state`; clients hold FULL elements (`Φ_L`).  `L` cannot
  move without the log (freeze-by-auth during commit, as today).
- **Bio's agreement share moves out of `fs_L`.**  Today the client and the
  bio machinery each hold ½ of one block element so that `bread` can
  return `bytes = L(b)` by agreement without the log lock.  With the
  client owning the full element, bio holds halves of a bio-side cache
  map `γcache`, tied to `L` inside a log-layer INVARIANT
  `inv logN (auth L ∗ auth C ∗ ⌜C = L on cached blocks⌝)` that
  `log_write` opens under its lock and a `bread` client opens to turn
  `bytes = C(b)` into `bytes = L(b)`.  One-time re-plumb of `FsBlocks` and
  the bio `Ψ` instantiation; the price of exclusive ownership.
- **A parked client payload `Ψ D₀`** in `log_state`, Ψ-parametric exactly
  as `bio_view` is for bio: the log stores it, never reads it, and indexes
  it by the **committed view alone** — `D₀ = lm_committed M cov ls`, which
  the log knows by value once the era's mirror is born true (H2a).  It is
  parked in the log, not in a separate FS invariant, because whatever the
  committer needs at the commit instant must already be in the log's hands
  (the last-ending operation cannot know it is last), and `log.lock`
  already serializes every `log_write`.

  **The index is the committed view and NOT the logged one.**  The logged
  view needs no index: the payload's `Γ_L` content is pinned to `L` by the
  byte ELEMENTS it holds against the log's auth, and `fs_view Γ_L` binds
  its state existentially (§4).  An `L` index is not merely redundant, it
  is FATAL: it would make every `log_write`'s AU RE-INDEX the payload,
  which no client can do for an arbitrary `Ψ`, so no supplier could frame
  it and the interface could not be proven Ψ-parametrically at all.

  `Ψ` is packaged EXISTENTIALLY in the log's context — `log_ctx_at Ψ …` is
  the Ψ-named form and `log_ctx … := ∃ Ψ, log_ctx_at Ψ …` — so the 78 files
  that thread the log's context keep their arity and none of them ever
  names a file-system payload; a client that must name `Ψ` opens the
  existential in its own proof, and the BOOT picks the witness.
- **`log_write(b)`'s AU**:
  `fs_L-elements for the bytes that change ∗ (∀ D₀, Ψ D₀ ={E}=∗ Ψ D₀ ∗ Q)`.
  The payload goes in and comes back at the SAME index — a `log_write`
  writes no disk block, so the committed view does not move — and `D₀` is
  `∀`-bound because it is the log's own parked index, which no caller can
  name.  The client opens whatever it likes inside (its own invariants, the
  parked `fs_view Γ_L` body) to move its pieces, its top fragment and the
  debt.  Since the log learns the checked-out buffer's bytes equal `L(b)`
  on every byte (via `γcache`), and the writer's stores touched only its
  range, the update needs elements only for the bytes that differ —
  byte-range ownership works above a block-granular device.
- **The commit law, and the prepared step it RETURNS.**  The commit's own
  update is consumed by the log's permit at mask `∅`, so it must be a basic
  update the client prepared in advance (the debt).  What prepares it is the
  client's ONE persistent law, carried by `log_ctx_at`:

  ```
  log_psi_commit Ψ γfs cov ls :=
    □ (∀ M L Lb,
         (γL_auth Lb ∗ ⌜Lb is L's bytes on home⌝ ∗ Ψ (lm_committed M cov ls))
         ==∗
         (γL_auth Lb ∗ Ψ (lm_logged L cov ls)
          ∗ fs_dstep (lm_committed M cov ls) (lm_logged L cov ls)))
  ```

  where `fs_dstep D D' := ∀ g, γD_auth (bytes D) ∗ P_wf(g, bytes D) ==∗
  γD_auth (bytes D') ∗ P_wf(g, bytes D')`.

  **The law takes the log's byte-view AUTH as an input and gives it back**,
  and that is load-bearing.  A law of the naive shape
  `□ (∀ M L, Ψ (lm_committed M) ==∗ Ψ (lm_logged L))` is NOT provable for a
  real payload: quantified over an arbitrary `L` with nothing else in hand,
  the client cannot know that `L` is the view its own elements describe, and
  the debt it owes is specific to the ACTUAL logged view.  With the auth
  lent, the client agrees its elements against it and learns the real `L`.

  The permit LENDS `γD`'s auth AND `P_wf` to the returned step for the
  instant — the same move the machine layer makes when it lends `γdisk` to
  `P_fs` (`crash.md`, stage A3) — and that is forced: moving
  `ghost_map_auth γD 1 B` needs the ELEMENTS of `B`, and those may not be
  owned by anything mortal (crash.md principle 1), so they are `P_wf`'s.
  The log proves `D' = L|home` internally (row (b), `log_mirror_tie_body`).
  Today's `P_wf` is a bare byte map, so the trivial witness
  (`fs_dstep_rebase`) discharges the step and the boot's `Ψ := fun _ => emp`
  discharges the law; both are PARAMETERS of stage 1 and stop holding once
  `P_wf` becomes `fs_view Γ_D`.
- **`end_op`**: no FS-specific premise at all.

`FsCrash.end_op_pres`, `fs_commit_pres`, `LogInv.end_op_fin`, the
`∀ V Ws` / `∀ F L pend` shapes, the object ledger in `op_entry`, `FsObj*`,
`FsWfImg`, `log_row_a*` and `FsWf.fs_durable_wf` were REJECTED because
they leaked the log's internals upward and, being quantified over pictures
no caller can name, were not dischargeable by any arm (they were green
only as placeholders).  **They are all DELETED in the tree** — the last of
them by durable-disk 1d, which also deleted their 30 + 6 gate call sites;
`end_op` now takes no FS-facing premise at all.

The whole of §5 above is LANDED (durable-disk 1d/1d'); the one thing the
interface still names that stage 2 will move is the durable gname.
`fs_dstep`'s `∀ g` is not a generalisation anyone wanted: `γD` is
`FsCrash.fcn_view` of a record the crash predicate binds EXISTENTIALLY, so
no client can name it, and a step at an arbitrary gname is the strongest
thing statable today.  Hoisting `fcn_view` into `RiscvPtsto.riscvFixedGS`
— stage 2's job, and the same seam-equation move `riscv_swap_name` already
makes — turns that binder into a parameter and the step into the client's
debt at the real durable name.

## 6. What this supersedes in the tree

The stage-F/G pure layer (`FsWf.v`, `FsEff*.v`, `FsOp*.v`, `FsObj*.v`,
`FsWfImg.v`, ≈15k lines) proved whole-state preservation of whole-state
pure predicates, which this design never states.  What survives is the
ENCODING vocabulary each `*_owned` predicate uses for its own tie
(`dinode_bytes`/`fs_dinode`, `dirent`/`dir_view`, `bm_bytes`, the indirect
block, from `FsImg.v`/`DinodeEnc.v`/`BitmapEnc.v`/`FsTree.v`), and the
local facts (a dirent insert keeps names unique; a truncate frees every
owned block; …), which become lemmas beside the predicate that uses them.
The rest is deleted when the `Γ`-predicates replace their consumers, not
before.

## 7. As built — stage 2a (`FsState*.v`, 2026-08-23)

Five files, 1687 lines, all in `iris/_CoqProject` after `BitmapEnc.v`:

| file | lines | holds |
|---|---|---|
| `FsStateDefs.v` | 164 | the record `fs_view_names` (`fsΦ`/`γlink`/`γtop`), `byte_range`, `blk_owned`, `phi_excl`, `GTimeless` |
| `FsStateLink.v` | 327 | the link RA, its law, its two moves, the generic gather/scatter |
| `FsStateInode.v` | 713 | `fs_node`, `inode_local`, `rec_owned`, `ind_owned`, `inode_phi`, `ent_toks`, `inode_ghost`, `inode_owned`, `dir_owned`, the readings, the encode lemmas |
| `FsStateBitmap.v` | 172 | `free_pool`, `free_bitmap`, `bitmap_alloc`, `bitmap_free` |
| `FsState.v` | 311 | `sb_owned`, `fs_inodes`, `fs_state`, `fs_view`, `fs_footprint`, `fs_state_mint` |

Nothing is imported from any `Proof*`/`Spec*`/invariant file; the whole
stack sits on `FsImg`/`DinodeEnc`/`BitmapEnc`/`FsTree`/`BlockWords` plus
plain Iris.

**The RA.** `linkUR := gmapUR Z (authR natUR)` — one auth-of-nat per inum,
all inums in ONE ghost-map element at `γlink`.  `natUR`'s `op` is `+` and
its `≼` is `≤`, so the law IS `auth_both_valid_discrete` + `nat_included`;
`k` separate tokens compose because `◯ 1 ⋅ ◯ 1 = ◯ 2`.  One camera keyed by
inum (rather than one gname per inum) is what lets `fs_state_mint` allocate
every auth AND every token of the new instance in a single `own_alloc`.  No
existing class serves (the tree's unique `ghost_mapG Σ Z (bv 8)` is the byte
view's and must not be duplicated), so there are two new CAPACITY-ONLY
classes, `fsLinkG` and `fsTopG` (`ghost_mapG Σ Z fs_node`).  Neither is a
member of `Xv6G.xv6G`, so a file may bind both without a second instance
path; folding them into the bundle is 2b/2c's call.

Where the built shape differs from §2, and why:

- **The geometry is a parameter.**  `rec_owned Γ sb i dn`, `inode_owned Γ sb
  i n`, `fs_inodes Γ sb I` and `free_bitmap Γ sb u` take the superblock;
  §2's spelling elides it.  `IBLOCK`/`islot`/`sb_bmapstart`/`sb_size` are
  reused from `FsImg`, not duplicated.
- **A directory's tokens live INSIDE `inode_owned`**, not beside it.  §2
  writes `dir_owned Γ d n := inode_owned Γ d n ∗ (the entry reading, with
  tokens)`, but `fs_inodes` is the one `∗` over `inode_owned`, so tokens
  hung off `dir_owned` would sit outside `fs_state` entirely.  So
  `inode_owned` carries `ent_toks Γ n` (empty for a non-directory, since
  `dir_entries n = ∅` there) and the directory-local clauses, and
  `dir_owned Γ sb d n := inode_owned Γ sb d n ∗ ⌜fn_is_dir n = true⌝` is the
  READING.
- **`inode_owned` is factored as `inode_phi ∗ inode_ghost`** — the Φ-only
  half and the Φ-free half.  That factoring is what makes `fs_state_mint` a
  transport rather than a re-derivation: `fs_state_split` lifts it to
  `fs_state Γ S ⊣⊢ fs_footprint Γ S ∗ fs_ghost Γ S`, and `fs_ghost` splits
  again into `fs_links (γlink Γ) I ∗ fs_pure S` (persistent).
- **`fs_state_rec` carries the superblock's raw BYTES** (`fss_sbb`) beside
  the parsed `fs_sb`.  Two reasons: the tree has no superblock ENCODER (only
  `FsImg.fs_parse_sb`), and `fs_footprint` has to be a function of `S`
  alone, which an existential over the bytes would break.  `sb_owned`'s one
  local clause is `fs_parse_sb (λ _, bs) = Some sb`.
- **`free_bitmap Γ sb u` is indexed by the USED set**, matching
  `BitmapEnc.bm_bytes`' argument; §2's `F` is the free set.  The pool is a
  `big_sepL` over `seqZ 0 (sb_size sb)` whose element is `emp` at a set bit
  and `∃ bs, blk_owned Γ b bs` at a clear one, so "take a block out" and
  "hand a block in" are one `big_sepL_delete` plus one `big_sepL_proper`.
- **The readings are named [fn_*].**  `fn_file_bytes n` and `dir_entries n`
  are §2's `file_bytes`/`dir_entries`; the first is prefixed because
  `FsTree.file_bytes` is a different function (over a raw `data` map) that
  it is defined in terms of.  `dir_entries n` is `∅` for a non-directory,
  which is what makes `ent_toks` vacuous there.
- **The mint's gnames come out existentially.**  `own_alloc` cannot target a
  given gname, so
  `fs_state_mint ΓD ΓL S : fs_state ΓD S -∗ fs_footprint ΓL S ==∗ ∃ gl gt,
  fs_state ΓD S ∗ fs_state (MkFsView (fsΦ ΓL) gl gt) S` — `ΓL` carries only
  the target `fsΦ`, its gname fields being unread (`fs_footprint_gname`).
  `fs_view_mint` is the same with `γtop`'s auth allocated at `S`'s inode map
  and one `top_frag` handed back per inode (§4).
- **The link family's validity is READ OFF the durable instance.**
  `fs_links_valid : fs_links g I -∗ ⌜✓ link_elem I⌝` gathers the whole
  family into one `own` and applies `own_valid`.  That is the ONLY place the
  cross-inode fact "#tokens ≤ nlink everywhere" is ever produced, it is not
  a clause, and it is never maintained — the logged instance inherits it
  from the committed one, which inherits it from its own allocation.
- **`nlink` is counted at `nat`**: `fn_nlink n := Z.to_nat (bv_unsigned
  (di_nlink (fn_rec n)))`, since the RA's counter is `nat`.  The `≤ 32767`
  clause is stated at `Z` (a `nat` literal that large elaborates to an
  opaque `Nat.of_num_uint` — durable-notes).

- **BOTH dirent view deltas come out of `FsTree`, at the RECORD view, and
  neither is assumed here.**  An unlink is `dir_zeroed_at`, a dirlink is
  `dir_insert_at` — `dir_written_at` plus the two side conditions that make
  it an insert rather than an overwrite (the slot is not live below the old
  count; the records the count grew over are dead), with
  `dir_insert_reuse` / `dir_insert_append` as the two arms of dirlink's
  free-slot scan.  `dir_view_zero` and `dir_view_insert` are the equations;
  §2b's `dir_entries_zero` / `dir_entries_write` read them at `fs_node`, and
  `dir_entries_fresh` supplies the `big_sepM_insert` side condition.
  `ent_toks_insert` and `dir_owned_link` therefore take the record delta and
  dirlink's own guard (`dir_first data nrec s = None`, the WEAKEST
  precondition — equivalently `dir_view data nrec !! s = None`), never an
  entry-map equation.  `dir_view_insert` needs no `dir_names_unique`: an
  insert only has to reach the FRONT of the first-match scan, unlike the
  removal, which unmasks whatever was hiding behind it.  Uniqueness after
  the write is `dir_names_unique_insert`, a one-liner off
  `dir_names_unique_write`.

Left out, with the reason:

- **`inode_local` preservation lemmas** beyond the two readings
  (`inode_local_data_owned`, `inode_local_beyond_size`).  Each mover's pure
  side condition is `inode_local i n'` as a premise; which of them a given
  arm needs is stage 3's evidence, and writing them speculatively would be
  the near-duplicate family the guiding principle warns about.

Two things 2b should know before it starts:

- **Four names collide with live ones**, all at different types (so a
  mis-resolution is a type error, never silent): `byte_range` and `fs_view`
  with `FsBlocks`'s, `link_auth` with `IcacheRef`'s ten-argument ledger, and
  `free_pool` with `BitmapInv`'s — the last being exactly the thing
  `free_bitmap` replaces.  The design names are kept; a file that needs both
  spells one of them qualified.
- **The byte arithmetic lines up by conversion, not by name.**
  `FsStateDefs.byte_range` multiplies by `FsImg.BSIZE_z`, `FsBlocks.byte_range`
  by `FsBlocks.BSZ`; both delta-reduce to `1024`, so at `Φ_L a v := a ↪[gL] v`
  the two runs are convertible.  Nothing needs a bridge lemma, but do not
  expect a `rewrite` between them to fire.
