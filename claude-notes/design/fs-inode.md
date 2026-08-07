# Design: the inode layer — `struct inode`, the file block map, and the allocator seam

STATUS: DESIGN. Written for `bmap`, the first fs.c function above `iinit`;
stated so that `writei`/`readi` can be built on it without reshaping it.

Layers below: [`fs-log.md`](fs-log.md) (the logged view `fsblock`, the bio
handles, `log_write`) and [`../completed/bio.md`](../completed/bio.md). The
FS block range and its `fsblock` halves are minted per era by `FsBoot.v`.

## `struct inode`'s geometry — read off the code, not off the header

`bmap`'s own instructions pin the layout, so nothing here is inferred from a
C declaration:

| evidence in `bmap` | conclusion |
|---|---|
| `lw a0,0(a0)` (the `balloc(ip->dev)` argument) | `dev` at **+0** |
| `lw s1,80(s3)` with `s3 = ip + 4*bn` | `addrs` at **+80** |
| `lw s1,128(a0)` (`ip->addrs[NDIRECT]`) | `addrs[12]` at 80+48 ✓ |

Full layout, with the one subtlety that matters:

```
  +0    dev     uint          +64   valid   int
  +4    inum    uint          +68   type    short
  +8    ref     int           +70   major   short
  +16   lock    struct        +72   minor   short
        sleeplock (48 B)      +74   nlink   short
                              +76   size    uint
                              +80   addrs[13]  (NDIRECT+1, 52 B)
  sizeof = 132, aligned to 136
```

**`lock` starts at +16, not +12** — `ref` ends at +12 but `struct sleeplock`
contains a pointer and so is 8-aligned, leaving a 4-byte hole. Every field
after it is displaced by that hole, and `addrs@80` is the observable
consequence. Deriving the offsets from the struct text without the hole puts
`addrs` at 76 and every `lw` in the proof misses by four.

`addrs[j]` is at `+80 + 4*j`, which is what the `slli 0x20 / srli 0x1e` pair
computes: zero-extend `bn` to 64 bits, then `<< 2`. The same pair appears
again for the indirect entry at `bp->data + 4*(bn-12)` (`b_data` is +88 in
`struct buf`).

## The pure model: a file's block map

```coq
Record blkmap := MkBlkmap {
  bm_dir : list (bv 32);   (* length NDIRECT   = 12; 0 = unallocated *)
  bm_ind : bv 32;          (* the indirect block; 0 = none            *)
  bm_ent : list (bv 32);   (* length NINDIRECT = 256; meaningful iff bm_ind <> 0 *)
}.

blkmap_get bm i := if i <? 12 then bm_dir !!! i else bm_ent !!! (i - 12)
bm_slot    bm i := if i = MAXFILE then bm_ind bm else blkmap_get bm i
```

**Not `fmap`.** That name shadows stdpp's functor map in every importing
file, and this record will be imported by `ProofBmap`, `SpecWritei`,
`ProofWritei`, `SpecReadi`… Entries are `bv 32` (what the cells hold);
`bv_unsigned` converts at the `fsblock` seam, which is keyed by `Z`.

`bm_slot` indexes **every block the inode names** — the `MAXFILE` file
indices plus the indirect block at index `MAXFILE`. That is what collapses
the next two conjuncts from a data/indirect cross-product into one
quantified clause each.

`blkmap_wf cov logstart bm` carries five conjuncts, each load-bearing:

- the two lengths (12 / 256) — without them the `addrs` big-op and the
  indirect encoding do not line up with the cells;
- every nonzero slot is in `cov` and outside the log region — the premise
  `bread` and `log_write` both demand;
- **injectivity on the nonzero slots**, and
- `bm_ind = 0 -> bm_ent = replicate NINDIRECT 0`. Needed on the
  allocate-the-indirect-block arm: `balloc` hands over a ZEROED block, which
  forces the new entry list to be all-zero, so the postcondition's "agrees
  with `bm` at every index except `bn`" is only provable if the old entry
  list was all-zero too. Vacuous on the resulting `bm'` (its `bm_ind` is
  nonzero) and preserved everywhere else.

### Injectivity is NOT derivable from `fsblock` — the ownership token

The first draft of this document asserted that "`balloc`'s freshness
re-establishes injectivity at every insertion". **That was wrong, and it
blocked bmap's proof.** `fsblock γ b bs` is `b ↪[fs_L γ]{#(1/2)} bs` — a
HALF. Two owners each holding a half of one key is perfectly consistent:
they `iCombine` into a valid full element (machine-checked). The third half
that *would* contradict is the machinery half, and it lives inside
`bio_ctx`'s escrow — unreachable at a straight-line instruction step.
Adding `inode_blocks` does not rescue it either: aliasing then merely yields
`data i = replicate BSIZE 0`, which is not absurd.

So the layer needs an **exclusive** per-block ownership token, and it lives
in the block layer beside `γL` and `γdirty` (not bolted onto the inode
layer — "which owner holds block `b`" is FS-block-layer state, and it is
what the bitmap invariant will need when `balloc` is finally proved):

```coq
  fs_names gains  fs_own : gname          (* ghost_map Z unit *)
  blk_own γ b := b ↪[fs_own γ] tt          (* FULL fraction => exclusive *)
  blk_own_excl : blk_own γ b -∗ blk_own γ b -∗ False
  blk_own_ne   : blk_own γ b1 -∗ blk_own γ b2 -∗ ⌜b1 <> b2⌝
```

`blk_own_ne` is what every install site uses; injectivity then falls out in
two lines. The token's AUTH is not needed yet — only element exclusivity —
so it can be introduced before the bitmap invariant exists. `fs_alloc` mints
one per covered block and `FsBoot`'s bundle carries them until there is a
free pool to park them in.

## The two resources

Split deliberately in two, because `bmap` needs only the first and a
whole-file operation needs both.

**`inode_map γfs ip bm`** — the map itself:

- the 13 `addrs` cells, exclusive: `[∗ list] j ↦ a ∈ bm_dir ++ [bm_ind],
  i_addr ip j ↦₄ u32 a`;
- when `bm_ind ≠ 0`, the indirect block's own logical content, as an
  `fsblock` at the *encoding* of `bm_ent`, **plus its `blk_own` token**:
  `fsblock γfs (bm_ind bm) (ind_bytes (bm_ent bm)) ∗ blk_own γfs (bm_ind bm)`.
  Those two are SEPARATELY NAMED (`ind_res := ind_blk ∗ ind_tok`), and that
  split is load-bearing: bmap hands the content half to `log_write` and gets
  it back re-indexed, so between the two it still has to present the token to
  `inode_fresh`. A single fused conjunct would force the freshness step
  before the store, where the new entry list does not exist yet.

**`inode_blocks γfs bm data`** — the file's data, `data : nat → list (bv 8)`:

- `[∗ list] i ∈ allocated indices,
   fsblock γfs (blkmap_get bm i) (data i) ∗ blk_own γfs (blkmap_get bm i)`.

**`bmap` takes BOTH.** An earlier draft said it "never looks at
`inode_blocks`" while also saying the fresh half is deposited there — those
contradict, and the second is right. Without `inode_blocks` in the
contract, `balloc`'s `fsblock` for a freshly allocated *data* block is
silently discarded (affine, so the proof still goes through) and `writei`
could never touch the block bmap just allocated — the contract would be
useless to its only intended caller. It is also where the `blk_own` tokens
for data blocks have to live, which the injectivity argument needs.

`writei` uses a one-block accessor out of `inode_blocks`, the same shape as
`proc_pt_page_acc` in
[`../completed/copy-inout.md`](../completed/copy-inout.md);
`inode_blocks_acc` and `inode_blocks_insert` are already that pair.

`dev` rides separately as a fractional cell (`i_dev ip ↦₄{dq} dev`) — `bmap`
only reads it, and a fraction is what lets the caller keep its own copy.

### Why the fresh block is deposited, not returned

`bmap` allocating a data block gets that block's `fsblock` half from
`balloc` and must put it somewhere. Returning it would make the
postcondition asymmetric — a caller would receive an `fsblock` on the
allocating path and nothing on the hit path, and every caller would have to
case-split on which happened. So the fresh half is **deposited into the
bundle**: `inode_blocks` comes back at `data' = <[bn := zeros BSIZE]> data`,
uniformly on both paths. The allocating path is visible in the *map*
(`blkmap_get bm' bn ≠ 0` where it was 0), which is where a caller that cares
should look.

## Words inside a block — `BlockWords.v` (LANDED)

The indirect block is 256 little-endian `uint`s in 1024 bytes. `ByteBuf.v`
is byte-granular and does not cover this.

The vocabulary is *not* get/set over raw bytes. The block's content is
always in the image of `ind_bytes : list (bv 32) → list (bv 8)`, because
that is exactly what `inode_map` carries — so an update is `<[i:=v]>` on
the **entry list**, and the byte level only ever has to be read back:

```
ind_bytes_length        length (ind_bytes e) = 4 * length e
ind_bytes_lookup        i < length e -> j < 4 ->
                          ind_bytes e !! (4*i+j) = Some (nth_byte (e !!! i) j)
ind_bytes_insert_same   ind_bytes (<[i:=v]> e) !! (4*i+j) = Some (nth_byte v j)
ind_bytes_insert_other  k outside [4i, 4i+4) ->
                          ind_bytes (<[i:=v]> e) !! k = ind_bytes e !! k
```

Byte splitting reuses **`RiscvModelBytes.nth_byte`** — the same function
`RiscvPtsto.word4_pointsto` splits a `bv 32` with. Do not add a second one.
That file is iris-free, so `BlockWords.v` is proofmode- and ssreflect-free
and stays usable from the `Pt4kWalk`-style vanilla-rewrite files
(durable-notes' ssreflect rule).

## `balloc`'s contract — ASSUMED for now

`balloc` is stated as a `Module Type` and left unproven, the sanctioned
pattern already used for `myproc`/`panic`/`kerneltrap`. `bmap` linked
against it counts as proven-with-caveat in `proof_coverage.py`.

It sleeps (it `bread`s), so it threads the full running-process bundle.
Its two arms:

- **success** — returns `b ≠ 0` with `⌜b ∈ cov⌝`, `⌜b ∉ log_region⌝`,
  `fsblock γfs b (replicate BSIZE 0)` and **`blk_own γfs b`**: `bzero` has
  already logged the block as all-zero, so the caller receives a zeroed
  block, not an arbitrary one. Spends **two** budget units (the bitmap
  `log_write` plus `bzero`'s). The `blk_own` token IS the freshness claim —
  without it the caller cannot show the block differs from one it already
  owns, and no amount of `fsblock` reasoning substitutes (see "Injectivity
  is NOT derivable" above).
- **failure** — returns 0, spends nothing, gives nothing.

The arm-dependent budget costs nothing to state because the postcondition
is already a two-arm disjunction on the return value.

**The open question this defers**: where free blocks' `fsblock` halves live
while free. `FsBoot.v` mints one per covered block at boot, so they exist;
proving `balloc` means designing the bitmap invariant that holds them and
tying bit `b` of the bitmap to "block `b`'s half is in the pool". Stating
`balloc` does not need that, which is exactly why it is worth assuming
first — the shape of `bmap`'s proof is independent of it.

## `bmap`'s contract

```
uint bmap(struct inode *ip, uint bn)
```

Premises: `bn < MAXFILE` (= 268) — which kills the `panic("bmap: out of
range")` arm, in the same way both of `log_write`'s panics are dead;
`blkmap_wf cov logstart bm`; `log_geom_ok cov logstart` (the interior
`bread`s want `uint bno < 2^31` and `0 ∉ cov`, which `blkmap_wf`'s "∈ cov"
does not give — `SpecEndOp`/`SpecWriteHead` take it for the same reason);
the running-process bundle (it sleeps in `bread`); `log_ctx`, `bio_ctx`,
`i_dev ip ↦₄{dq} dev`, `bslots bn 3`, and the budget below.

### The budget is SPEND-AT-MOST, and that is forced

```
  premise  (5 <= n)
  pre      log_op γ n
  post     ∃ n', ⌜n - 5 <= n' <= n⌝ ∗ log_op γ n'
```

The obvious `log_op γ (5+u)` in / `log_op γ u` out is **unprovable**, and
the reason generalises to every function above the log that does not take
`log.lock`: `log_op` is a `ghost_map` element, its only mover is
`ghost_map_update` against the ledger auth inside `log_res`, and that auth
sits behind the log spinlock. `bmap` never acquires it. So on the
direct-hit path — no `balloc`, no `log_write` — bmap reaches its epilogue
still holding every unit it was given and **cannot burn the surplus**. A
spend-exactly postcondition would require minting the difference.

Five is the worst case: `balloc`(indirect) 2 + `balloc`(data) 2 + bmap's
own `log_write` 1. The upper bound `n' <= n` is free to prove and stops the
contract from being satisfiable by a bmap that mints budget.

State the premise as a lower bound on the caller's own counter (`5 <= n`),
not as a `5 + u` shape: a `writei` loop can then present its counter
directly and re-present what comes back, instead of rewriting it into
`5 + u` form at every iteration.

`balloc`'s budget needs none of this — its postcondition is already a
two-arm disjunction, it genuinely spends through `log_write` under the
lock on the success arm, and it refunds `2+u` unspent on failure because
no `log_write` ran.

Postcondition, one existential map `bm'` and a return value `r`, two arms:

- `r = 0` — allocation failed. `blkmap_get bm' bn = 0`. Note `bm'` is **not**
  `bm`: the indirect-path failure can already have allocated and installed
  the indirect block before failing on the data block, and the direct-path
  failure leaves `bm` alone. Pretending the map is unchanged would be
  false on the first of those.
- `r ≠ 0` — `blkmap_get bm' bn = r`, and `bm'` agrees with `bm` at every
  index except possibly `bn`.

Both arms return `inode_map γfs ip bm'` and `blkmap_wf bm'`.

The `s4` quirk: gcc saves `s4` **only on the indirect paths** (`sd s4,0(sp)`
at +0x058/+0x060, restored at +0x088); the direct path jumps to +0x08a and
never touches it. This turns out to cost almost nothing: ONE epilogue lemma
entered at +0x08a, parameterised by raw slot ownership (`∃ v, pa_stk sp0 6
↦₈ v`) plus the premise `M !!! s4 = m !!! s4`, is satisfied by both
families — the direct arm never writes s4 and keeps the push's existential
slot, and the indirect arm restores s4 at +0x088, one instruction before
the join. No per-arm `callee_saved` duplication beyond that premise.

### Confirmed by working the proof plan

`K_bmap = 56` (frame 6 slots + `K_balloc = 50`, which dominates `bread` 40,
`brelse` 26, `log_write` 18). `bslots bn 3` is **exactly tight** — the peak
is at the second `balloc`, where `bread`'s reference holds one while
`balloc` wants two. The spend-at-most bound of 5 is right: the reachable
spend profiles are exactly {0, 2, 4, 5}.

`inode_map_ind_acc`'s back-wand taking BOTH a new `w` and a new entry list
is the right shape and should be kept: +0x05a uses `(w := blk, e := zeros)`
and +0x0a6 uses `(w := bm_ind bm, e := <[q := blk]> (bm_ent bm))`, and in
the second case the `ind_res` it demands is literally what `log_write`
hands back — the `fsblock` re-indexed at the new bytes.

The buffer-entry read/write is `ByteBuf.bb_word4_acc` over `bio_hold0`'s
bytes, exactly `ProofWriteHead.v`'s `wh_hold_of`/`wh_hold_to` pattern —
that file (bread → word-store into `bp->data` → callee → brelse) is bmap's
indirect arm almost verbatim and is THE precedent to follow.

## `iupdate` — the flush, and `struct dinode`

126 bytes, 44 instructions, **completely straight-line**: no branches, no
arms, no panic. It is the in-memory-inode → logged-block flush.

### `struct dinode` (64 B, IPB = 16), read off iupdate's stores

| evidence | conclusion |
|---|---|
| `sh a4,0(a5)` after `lh a4,68(s1)` | `type` at **+0** (from inode +68) |
| `sh …,2(a5)` / `4` / `6` | `major` +2, `minor` +4, `nlink` +6 |
| `sw a4,8(a5)` after `lw a4,76(s1)` | `size` at **+8** |
| `addi a0,a5,12` / `li a2,52` / `addi a1,s1,80` | `addrs` at **+12**, 52 B |
| `andi a4,a4,15; slli a4,a4,0x6` | slot = `(inum & 15) * 64`, so IPB = 16 |

This is also an independent confirmation of the in-memory `struct inode`
layout derived from bmap — iupdate loads exactly +68/+70/+72/+74/+76/+80.

### The block, and the superblock field

`IBLOCK(inum, sb) = inum / IPB + sb.inodestart`, computed as
`srliw a5,a5,0x4` (unsigned divide by 16) then `addw`. `sb.inodestart` is
read from the global at **`sb + 24`** (`lw a1,1850(a1)` off an `auipc`,
i.e. `80020868 = sb+0x18`).

Take that field the way `SpecInitlog.v` already takes `sb + 20` for
`logstart`: a plain fractional cell `pa_add sb 24 ↦₄{dq} inodestart`,
threaded in and back out untouched. **Do not build a superblock
abstraction for one field** — there is a precedent and it is one line.

### What it needs that does not exist

- **A dinode-block encoding.** A block is 16 dinodes; the write targets
  slot `inum mod 16`. Same shape as `BlockWords.ind_bytes`: keep the
  block content in the image of an encoding function over a list of 16
  pure `dinode` records, so an update is an `<[k := d]>` on that list and
  the byte level is only ever read back.
- **An addrs-cells-as-byte-buffer bridge.** `memmove`'s source is the 13
  `i_addr` word cells viewed as 52 contiguous bytes. `ByteBuf.bb_word4_acc`
  goes the other way (borrow a word out of a byte buffer); this needs the
  converse. memmove's own contract is fine as-is — its non-overlap is
  carried by SEPARATION, and source (the inode) and destination (the
  buffer) are separate conjuncts.
- **`inode_meta`** — the five metadata cells at the values of a pure
  `dinode`. `InodeInv.v` already defines the accessors
  (`i_type`/`i_major`/`i_minor`/`i_nlink`/`i_size`); this bundles them.

### The budget: iupdate CAN promise spend-exactly

Unlike bmap, iupdate is straight-line and always executes its one
`log_write`, so `log_op γ (S u)` in / `log_op γ u` out is provable. The
spend-at-most form is forced only when a path can skip the spend — state
the exact form here and keep the weaker one for functions that branch.

`bslots bn 2`: bread's reference is held across `log_write`, which wants
one of its own; brelse returns it.

### Decision record: `inode_meta`'s phantom `di_addrs`

`inode_meta ip dn` is indexed by a whole `dinode` record but owns only the
FIVE SCALAR cells (`type`/`major`/`minor`/`nlink`/`size`); the thirteen
`addrs` cells belong to `inode_map`. So `di_addrs dn` is a phantom index —
nothing in the resource body constrains it — and the gap is closed by the
pure premise `di_addrs dn = bm_cells bm`.

This is SOUND: without that premise the postcondition would claim arbitrary
addrs had been written, so the tie is load-bearing and it is present.

The cleaner alternative is five explicit scalar arguments with the written
dinode assembled at the seam (`mk_dinode ty maj min nl sz (bm_cells bm)`) —
no phantom, no premise for callers. **Considered and deliberately not
taken** (2026-08-06): every caller that has `inode_meta` also has
`inode_map`, so the tie discharges from what it already holds and costs one
pure step. Revisit if a caller ever turns up that holds the scalars WITHOUT
the map — that is the case the phantom would actually hurt.

### Who owns an inode block

Deferred, like the bitmap. The block holds **16 different inodes'**
dinodes, so an icache/inode-table invariant will eventually have to
manage that sharing. iupdate's contract simply takes the whole block's
`fsblock` half and hands it back updated at one slot — correct, and it
does not prejudge the sharing design. No `blk_own` is needed: iupdate
establishes no injectivity.

## `writei` — the loop, and what a PARTIAL write may claim

256 bytes, 98 instructions. Structurally the hardest of the three: a loop
with two break conditions, three early exits, and five conditionally-saved
registers.

### The file-content view is the whole contract

`inode_blocks γfs bm data` is indexed by file BLOCK; writei is about a byte
RANGE that straddles blocks. Do not state the postcondition block by block
— define the flat view once,

```coq
  file_byte (data : nat -> list (bv 8)) (k : nat) : bv 8
    := data (k / BSIZE) !!! (k mod BSIZE)
```

and say exactly what a partial write achieves:

```
  ∀ k, file_byte data' k = if off <= k < off + tot
                           then <the source byte at k - off>
                           else file_byte data k
```

That one clause covers every arm — full write, short write, zero write —
and is what `filewrite` will actually consume. Stating it per block forces
the caller to reassemble the range and re-derive the straddle arithmetic.

### The return value is `tot`, and it may be less than `n`

Two breaks: `bmap` returning 0 (out of blocks) and `either_copyin`
returning −1 (bad user pointer). Both leave `tot < n` and are NORMAL
returns, not errors — only the three up-front checks return −1
(`off > size`, `off + n` overflow, `off + n > MAXFILE*BSIZE`; the constant
is `lui a4,0x43` = 274432 = 268 × 1024, confirmed against the image).

So the contract's return arm is `⌜r = -1 ∧ nothing changed⌝ ∨ ⌜0 <= tot <= n⌝ ∗ <the range clause>`.
A contract that promised `tot = n` would be unprovable, and one that
treated a short write as failure would be useless to `filewrite`, which
loops on exactly this.

### `ip->size` and the flush

`size' = max(size, off + tot)` — note the code compares against the
ADVANCED `off`. Then `iupdate` runs unconditionally, on every returning
path including `n = 0`. So writei needs everything `iupdate` needs on top
of its own: `i_inum`, `inode_meta`, the `sb + 24` field, and the inode
block's own `fsblock`.

### The user/kernel flag was designed for this

`either_copyin` already carries `user` as a ghost boolean, with `proc_priv`
required only on the user arm and the tighter length bound on the kernel
arm. writei THREADS that flag rather than passing a literal —
[`../completed/either-copy.md`](../completed/either-copy.md) says this
caller is exactly why the flag was made a ghost boolean. Thread it; do not
specialise writei to one arm.

### Budget: spend-at-most, with an iteration bound

Per iteration: `bmap` ≤ 5 + `log_write` 1 = **6**. Plus `iupdate`'s 1 at the
end. The iteration count is bounded by the blocks the range straddles,
`(off mod BSIZE + n + BSIZE - 1) / BSIZE`. So the premise is a lower bound
on the caller's counter of `6 * that + 1`, and the postcondition is
spend-at-most (writei branches, so spend-exactly is unavailable — see the
budget rule above).

### Five conditionally-saved registers, and why they are still free

`s3` is saved at +0x032 (before the `n = 0` test, so on every framed path);
`s1`, `s8`, `s9`, `s10`, `s11` at +0x038..+0x040 only when `n ≠ 0`, and
restored at +0x0c2 (normal) or +0x0ec (skip-size-update). The `n = 0` arm
at +0x0e8 jumps straight to +0x0cc and never restores them — correctly,
since it never saved them.

**bmap's lesson transfers exactly**: every restore happens BEFORE the join
at +0x0cc (the `iupdate` call), so all three paths reach that point with
`s1`/`s8`–`s11` already at their entry values. One join lemma taking the
full threading plus anonymous frame slots, as in `bm_epilogue`.

### The pre-frame exit is the one genuinely new shape

`+0x000..+0x002` tests `off > ip->size` and branches to `+0x0f8`, a bare
`li a0,-1; ret` — **before the prologue has run**. That path never pushes,
so it cannot be handled by the same epilogue lemma as everything else and
must not be given frame ownership. Nothing else in the inode layer has
this shape.

## Order of work

1. `BlockWords.v` — the `ind_*` vocabulary and its four laws.
2. `InodeInv.v` — geometry, `blkmap`, `blkmap_wf`, `inode_map`, `inode_blocks`,
   the one-block accessor.
3. `SpecBalloc.v` (assumed), `SpecBmap.v`.
4. `CodeBmap.v` — 69 instructions; check `KernelRvcDecode`/`KernelBaseDecode`
   first per the decode-dedup rule.
5. `ProofBmap.v` / `LinkBmap.v`.
6. Then `iupdate`, and `writei` on top of both.
