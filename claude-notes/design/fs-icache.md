# Design: the inode cache (`itable`, `iget`/`idup`/`iput`)

STATUS: DESIGN + a landed definitional layer (`iris/IcacheInv.v`, compiles,
axiom-free). No `Spec<F>.v` for `iget`/`idup`/`iput` exists yet and none is
written here — this note is what they will be stated over.

The icache is the chokepoint under `iput`, `idup`, `iget`, `namei` and most
of `sysfile.c`. Layers below: [`fs-inode.md`](fs-inode.md) (the inode
itself — `struct inode`'s geometry, `blkmap`, `inode_map`/`inode_blocks`,
`ilock`/`iunlock` and `InodeLock.v`'s seam), [`fs-bitmap.md`](fs-bitmap.md)
(the free pool `itrunc` hands blocks back to),
[`fs-log.md`](fs-log.md), [`file-table.md`](file-table.md) (the
reference-count algebra this reuses verbatim).

Read [`fs-inode.md`](fs-inode.md)'s "`ilock` / `iunlock` — the LOAD, and
the icache seam" first: the sleeplock-side of an entry is settled there and
is not restated here.

---

## 1. The `itable`'s geometry

```c
struct { struct spinlock lock; struct inode inode[NINODE]; } itable;   // NINODE = 50
```

Every number below is pinned by an instruction in the tracked image
(`kernel-rocq/KernelSyms.v` + `KernelInstrs.v`), never by transcribing the
C. `xv6-riscv/kernel/kernel.asm` is a stale local build and was not
consulted.

| evidence | conclusion |
|---|---|
| `iget+0x26`: `addi s1,s1,-1796 # 80020888 <itable+0x18>` — `s1 = &itable.inode[0]` | `lock` at **+0**, `inode[0]` at **+24** |
| `iget+0x3c`: `addi s1,s1,136` (the scan's stride) | `sizeof(struct inode)` = **136** |
| `iget+0x2e`: `addi a3,a3,900 # 80022318 <log>`, used as the scan's stop (`iget+0x40`: `beq s1,a3,…`) | `&inode[NINODE]` **is** the address of the next symbol |
| `iinit+0x26`: `addi s1,s1,-1950 # 80020898 <itable+0x28>` | `&inode[0].lock` = entry + 16 ✓ (`InodeInv.i_lock`) |
| `iinit+0x2e`: `addi s3,s3,746 # 80022328 <log+0x10>` | `&inode[NINODE].lock`, same stride from the other end |

`24` is `sizeof(struct spinlock)` (`uint locked` + 4 bytes of padding + two
pointers) and `136` is `sizeof(struct inode)` = 132 rounded up to the 8 the
embedded sleeplock forces — the same alignment hole that puts `addrs` at
+80 (`fs-inode.md`). Consistency check: `24 + 136*50 = 6824 = 0x1AA8`, and
`KernelSyms.log − KernelSyms.itable = 0x80022318 − 0x80020870 = 0x1AA8`. ✓

In `IcacheInv.v`:

```coq
Definition NINODE : nat := 50.
Definition itable_lock : mword 64 := mword_of_int KernelSyms.itable.
Definition ISLOTSZ : Z := 136.
Definition ientry (k : nat) : mword 64 :=
  mword_of_int (KernelSyms.itable + 24 + ISLOTSZ * Z.of_nat k).
```

with one arithmetic fact — `ientry_unsigned`, "in range, the address is its
literal offset and does not wrap" — and three corollaries: `ientry_inj`
(slot ↔ address, so a `struct inode *` determines its slot index and no
separate ghost mapping is needed), `ientry_step` (the scan's `addi 136`)
and `ientry_sentinel` (`ientry NINODE = KernelSyms.log`).

**`ientry_sentinel` is worth having as a lemma rather than a `vm_compute`
at the use site.** The loop bound the compiler emitted is literally the
address of the *next global*; if a future `XV6_REV` inserts a symbol
between `itable` and `log`, the scan's proof would silently be about the
wrong range, and this lemma is the thing that fails instead.

Per-entry field addresses are `InodeInv.i_dev`/`i_inum`/`i_ref`/`i_lock`/…
applied to `ientry k`; the icache adds no field vocabulary of its own.

---

## 2. What protects what — three disciplines, and one xv6 comment that is
not the whole truth

`fs.c`'s comment says:

> the `itable.lock` spin-lock protects the allocation of itable entries.
> Since `ip->ref` indicates whether an entry is free, and `ip->dev` and
> `ip->inum` indicate which i-node an entry holds, one must hold
> `itable.lock` while using any of those fields.
> An `ip->lock` sleep-lock protects all `ip->` fields other than `ref`,
> `dev`, and `inum`.

Both halves have exceptions that the model has to carry, and each exception
costs something:

1. **`dev`, `inum`** — written only by `iget` on a free entry, under
   `itable.lock`; read by any reference holder with no lock (`ilock` does
   `lw a0,0(a0)` / `lw a5,4(s1)` holding only the sleeplock). This is the
   ftable's discipline 2 exactly: *immutable while `ref > 0`*, hence
   **fractional**. No exception, and `SpecIlock`'s existing
   `i_dev ip ↦₄{dqd} dev` / `i_inum ip ↦₄{dqn} inum` premises fit it
   unchanged.

2. **`ref`** — read-modify-written under `itable.lock` by
   `iget`/`idup`/`iput`, but **read with no lock at all** by `ilock`
   (`ilock+0x0e`: `lw a5,8(a0)`, then `blez` — the `ip->ref < 1` guard) and
   by `iunlock`. One 4-byte load, so it is a single atomic step and an
   invariant can be opened around it. See §4: this is why the `ref` words
   cannot live in the lock's resource.

3. **`valid`, `nlink`** — written under the sleeplock (`ilock`, `iput`),
   and *read by `iput` under `itable.lock` only*
   (`iput+0x3c`: `lw a5,64(s1)` then `lh a5,74(s1)`). See §5: this is the
   real content of the "`ref == 1` means no other process can have `ip`
   locked" comment.

4. **`valid` again** — written by `iget` (`sw zero,64(s3)`) on a recycled
   entry under `itable.lock`, with no sleeplock. Same exception as 3.

Discipline 1 is free. Disciplines 2–4 are the whole design problem.

---

## 3. The ghost state, and how it composes with `InodeLock.v`

### The reference algebra: RustBelt's Arc, reused verbatim

```coq
Definition icacheUR : ucmra := authUR (gmapUR nat (prodR fracR positiveR)).
Definition iref_tok  γ k q := own γ (◯ {[ k := (q, 1%positive) ]}).
Definition itable_half γ M := own γ (●{#(1/2)} M).
```

`M !! k = Some (q, n)`: slot `k` is live, with `n` outstanding references
holding `q` of its identity between them. `k ∉ dom M`: the slot is free.
This is `FileInv.frefUR` with the payload and liveness components dropped
(the icache needs neither: its payload is the sleeplock's, and there is no
`off`-borrow), so the shape is already validated by the four proven
`file_*_step` lemmas and by `fileclose`. **Do not invent a second algebra
for it.**

`IcacheInv.v` ships `iref_alloc_step` / `iref_dup_step` /
`iref_close_step` / `iref_close_last_step` (algebra level, over the joined
authority) and `iref_lookup` (§5). The points-to side of each — the
`dev`/`inum` fractions moving between `islot` and a reference — is one
lemma per step and belongs with the contracts that consume it, not here.

Why the authority is **split in halves** (`itable_half`, with
`itable_half_op`/`_join`/`_split` as its laws): one half sits in the
`ref`-word invariant beside the cells so the counts and the words can never
disagree, and one half sits in `itable.lock`'s resource. Holding the lock's
half is what **pins** every count across the `lw; addiw; sw` the code
performs; holding a reference fragment alone is enough for a lock-free
reader to conclude its own slot's count is ≥ 1.

### What a reference IS

```coq
Definition inode_ident k dq dev inum := i_dev (ientry k) ↦₄{dq} dev ∗ i_inum (ientry k) ↦₄{dq} inum.
Definition inode_ref γ k q dev inum   := iref_tok γ k q ∗ inode_ident k (DfracOwn q) dev inum.
```

Note it takes no inode *pointer*: `ientry` determines the address from the
slot and `ientry_inj` determines the slot from the address, so the two are
interchangeable. `inode_ref_agree` — two references to one entry see the
same `dev`/`inum` — falls out of fractional points-to agreement with no
`agree` ghost, exactly as in the ftable.

**This is the predicate `FileInv.inode_ref v q` (today literally `emp`) and
`ProcInv.cwd_ref v = inode_ref v 1` are placeholders for.** Its signature
does not match theirs: it needs `γ` (and reads the slot off the address).
Two ways to close that, both recorded, neither taken here:
`inode_ref` gains a `γ` parameter (ripples into `FileInv`, `ProcInv`,
`SpecIput`, `SpecFileclose`, `kexit`), or `icacheG` carries the gname as a
class field so the predicate's arity is unchanged. The second is cheaper
and is what the ftable would have done if it had needed it.

### The lock's resource

```coq
Definition islot_rest k q := match (1-q)%Qp with
                            | Some q' => ∃ dev inum, inode_ident k (DfracOwn q') dev inum
                            | None    => emp end.
Definition islot M k := match M !! k with
                        | None        => ∃ dev inum, inode_ident k (DfracOwn 1) dev inum
                        | Some (q, _) => islot_rest k q end.
Definition itable_res γ := ∃ M, itable_half γ M ∗ ⌜icM_wf M⌝ ∗ [∗ list] k < NINODE, islot M k.
Definition is_itable γl γ := is_lock γl itable_lock "itable" (itable_res γ).
```

`icM_wf M` is two clauses: every live slot is in range, and every count is
`< 2^31`. The count bound is not bookkeeping — it is what makes the `lw` +
`sext.w` the code performs mean the count, and it is what kills `ilock`'s
and `iunlock`'s `ref < 1` panic (`iref_word_live`, feeding
`InodeLock.inode_ref_spos`).

The `Qp.sub`-shaped `islot_rest` is the price of letting a lone holder be
writable, and `islot_rest_join` is its payoff: a closer holding `q = qt`
plus whatever the table kept has fraction 1 of the identity, i.e. enough to
hand the slot back to `iget` as free.

### Composition with `InodeLock.v` — it does not duplicate the seam, and it
### does not yet compose with it either

`InodeLock.inode_parked` (the sleeplock's payload) and
`InodeLock.inode_key` (the `ghost_var` shadow that names the parked
`dn`/`bm`) are **not restated** here, and `IcacheInv.v` deliberately does
not mention them. Two things have to change in `InodeLock.v` before an
`itable_res` can carry them, and neither is a change this effort should
make unilaterally (`ProofIlock.v` is landed and proven):

**(C1) `inode_parked`'s unloaded arm must stop owning a block map.**
Today:

```coq
inode_parked γfs γi cov ls ip :=
  ∃ v dn bm data, ⌜inode_ok cov ls dn bm data⌝ ∗ inode_key γi v dn bm ∗
    i_valid ip ↦₄ valid_word v ∗ ind_res γfs bm ∗ inode_blocks γfs bm data ∗
    (if v then inode_meta ip dn ∗ inode_addrs ip (bm_cells bm) else inode_raw ip)
```

At `v = false` — an entry `iget` has just minted — the sleeplock still owns
`ind_res γfs bm` and `inode_blocks γfs bm data` for *some* `bm`. When
`iget` recycles the slot to a **different inum**, those are the *previous*
inode's blocks, and nothing can change them: the payload is inside a lock
`iget` does not acquire, and the caller-side `inode_key` half cannot be
retagged without the lock's half. `SpecIlock`'s premise
`vv = false → ds !!! islot inum = dn` then asks the disk block of the *new*
inum to hold the *old* `dn`, which is false. **As `InodeLock.v` stands, an
icache cannot recycle a slot to a different inode** — i.e. `iget`'s recycle
arm, which is most of `iget`, is unprovable.

The fix is the one that also matches how xv6 thinks: an *unloaded* entry
owns nothing. `inode_parked`'s `v = false` arm keeps only `inode_raw ip`
and `i_valid ip ↦₄ 0`; the shadow becomes two-state
(`Unloaded` / `Loaded dn bm`, i.e. `ghost_var … (option (dinode * blkmap))`);
and `ilock`'s uncached arm draws `ind_res`/`inode_blocks` from the FS-level
inode store (§7) by a fupd rather than from the lock, with
`ds !!! islot inum = dn` becoming an *output* instead of a matched input.
Cost: restate `inode_parked`/`inode_key`/`SpecIlock`, and re-prove the
`il_load` half of `ProofIlock.v` — the instruction-level work is untouched,
only where the block resources come from moves.

**(C2) `i_valid` must be reachable without the sleeplock** (see §5).

---

## 4. The `ref` words go in an invariant — and `SpecIlock`'s `i_ref`
## premise is unsatisfiable as written

`SpecIlock.v` and `SpecIunlock.v` both take

```coq
  i_ref ip ↦₄{dqr} refv  -∗  …          with   0 < bv_unsigned refv < 2 ^ 31
```

i.e. the caller owns a *fraction of the ref cell at a pinned value* for the
whole call. **No icache can supply that.** Owning any fraction of a cell
forbids every other thread from writing it, and `idup(ip)` / `iput(ip)` on
another core do write it — two processes holding references to one inode,
one of them `ilock`ing while the other `idup`s, is the ordinary case
(`sys_open` + `fork`). The premise is not merely awkward; it is
unimplementable, and the contract compiles only because nothing has ever
tried to discharge it.

The fix is structural: **the `ref` words live in a shared Iris invariant**,
not in `itable.lock`'s resource and not in any caller's hands.

```coq
Definition iref_cells M   := [∗ list] k < NINODE, i_ref (ientry k) ↦₄ iref_word M k.
Definition itable_body γ  := ∃ M, itable_half γ M ∗ ⌜icM_wf M⌝ ∗ iref_cells M.
Definition itable_inv γ   := inv icacheN (itable_body γ).      (* persistent *)
```

and `ilock`'s guard load becomes an atomic-update read:

```coq
Lemma iref_load_au Eo γ k q :
  ↑icacheN ⊆ Eo →
  itable_inv γ -∗ iref_tok γ k q -∗
  |={Eo, Eo ∖ ↑icacheN}=> ∃ v : mword 32, i_ref (ientry k) ↦₄ v ∗
     (i_ref (ientry k) ↦₄ v ={Eo ∖ ↑icacheN, Eo}=∗
        ⌜0 < bv_unsigned v < 2 ^ 31⌝ ∗ iref_tok γ k q)
```

which is exactly the shape `WpSconfMem.wp_load_s_sconf_au` takes at width
4, with `StartedInv.started_inv_load_au` as the worked precedent — the
`started` flag is the same situation (a plain global read lock-free by
several harts). The delivered bounds are precisely what
`InodeLock.inode_ref_spos` turns into "`bge x0,a5` falls through", so
`ilock`'s and `iunlock`'s first panic stays dead with no new bitvector
work. `iref_load_au` is proven in `IcacheInv.v`.

**Cost of the change**: `SpecIlock.v`/`SpecIunlock.v` swap one premise
(`i_ref ip ↦₄{dqr} refv` + the two bounds) for two (`itable_inv γic` +
`iref_tok γic k q`), and `ProofIlock.v`/`ProofIunlock.v` replace one
ordinary word-load leaf with `wp_load_s_sconf_au` at the guard. Everything
downstream of the guard is unchanged. It is a half-day, not a rewrite —
but it is a change to two landed, proven contracts, so it is recorded here
and left unmade.

Writes to `ref` (`iget`'s `sw a5,8(s1)` / `sw a5,8(s3)`, `idup`'s and
`iput`'s `addiw ±1` pairs) open the same invariant, join the lock's half
with the invariant's half into `own γ (● M)` (`itable_half_join`), run the
matching `iref_*_step`, and re-split. Holding the lock's half between the
`lw` and the `sw` is what makes the read-modify-write atomic *in the
proof*: no other thread can move `M`, because moving it needs both halves.

---

## 5. The load-bearing theorem: `ip->ref == 1` ⟹ nobody else has it

xv6 asserts, in a comment, that

> `ip->ref == 1` means no other process can have `ip` locked, so this
> `acquiresleep()` won't block (or deadlock).

That sentence is doing three different jobs, and only two of them are the
proof's business. Separating them is the point of this section.

### (a) The deadlock claim is a LIVENESS claim and this logic does not see it

`acquiresleep`'s spec in this tree (`completed/sleeplock.md`) is a partial
-correctness WP: an iLöb retry loop over `SLEEP` that says *if it returns,
you hold the lock and its resource*. Blocking forever is not unsound and
not expressible. So the "won't block" half of the comment needs **no**
theorem, and any design that spends effort proving it is spending it in the
wrong place. Say so explicitly, because the comment reads like a
proof obligation and it is not one.

### (b) REF-1 EXCLUSIVITY — the part that IS load-bearing, and is free

The safety-relevant statement is about *ownership*, not scheduling:

> **Theorem (REF-1).** If a thread holds `iref_tok γ k q`, holds
> `itable.lock` (hence `itable_half γ M`), and the invariant's `ref` word
> for slot `k` reads 1, then `M !! k = Some (q, 1)` — the thread's `q` is
> the entire outstanding share, so **no other reference to slot `k` exists
> anywhere in the system**, and the thread may take fraction 1 of the
> slot's identity and retire the entry.

Proof: `iref_lookup` (proven in `IcacheInv.v`). `Some (q,1) ≼ Some (qt,n)`
in `prodR fracR positiveR` splits into "equal" or "strictly below in both
components"; `positiveR` has no zero, so `n = 1` rules the second case out,
giving `q = qt`. The physical side is `iref_word`: the word is
`mword_of_int (Z.pos n)`, so reading 1 *is* `n = 1`.

**Cost: nothing beyond stating the algebra.** This is the same fact
`FileInv.fref_tok_lookup` already gives `fileclose`, and it is the whole
reason to reuse the Arc shape rather than a plain counter.

`iref_lookup` also gives the converse (`q = qt → n = 1`), which is what
tells a *non*-last closer that it is not the last one — needed so
`iref_close_step`'s `qt - q = Some qr` side condition is dischargeable.

### (c) The part that is NOT free: `iput` reads sleeplock-protected cells

`iput` reads `ip->valid` and `ip->nlink` **before** it calls
`acquiresleep`, holding only `itable.lock`:

```
+0x18  lw   a4,8(s1)        ; ref
+0x1c  beq  a4,a5,+0x3c     ; ref == 1 ?          <-- short-circuits
...
+0x3c  lw   a5,64(s1)       ; valid   (only reached when ref == 1)
+0x40  lh   a5,74(s1)       ; nlink
+0x48  addi a5,s1,16 ; +0x50 jal acquiresleep
```

The short-circuit is real and visible in the image: `valid` and `nlink` are
loaded only on the `ref == 1` arm. Both cells are inside
`InodeLock.inode_parked`, i.e. inside a sleeplock `iput` has not acquired.
`iget` has the same problem in the other direction (`sw zero,64(s3)` on a
recycled entry, no sleeplock).

REF-1 says nothing about this. Iris's lock spec makes `is_sleeplock`
*persistent* — any thread may attempt an acquire — so "no other thread
holds the lock" is not derivable from any ownership fact, and the
resource `iput` needs (the points-to for those two cells) is simply not
reachable from what it holds.

Three ways out were considered.

- **(i) Move `i_valid` (and `nlink`) out of the sleeplock into the
  reference tier, fractional.** Fails: `ilock` writes `valid = 1` and the
  five metadata cells while holding possibly *not* the sole reference (two
  processes can each hold a reference and one of them `ilock`s), so a
  write would need fraction 1 it does not have.

- **(ii) A second Iris invariant over `i_valid`, with the shadow held in
  thirds.** Fails for the same reason in ghost clothing: a caller-side
  third would pin `v`, and another reference holder's `ilock` legitimately
  changes it.

- **(iii) The bio escrow, and a reference share as the checkout token.**
  This is the one that works, and it is a shape this tree has already paid
  for (`completed/bio.md`: "a namespace invariant with a parked arm and a
  checked-out arm, over a sleeplock that protects only a checkout token").
  Per entry:

  * a namespace invariant with two arms — **parked** (the entry's cells and
    payload are inside) and **checked out** (a borrow marker is inside);
  * the sleeplock protects only the exclusive *checkout token*;
  * **the checked-out arm holds a slice of the entry's reference share.**
    `ilock` pays a fraction of its own `iref_tok`/`inode_ident` in when it
    checks the content out and takes it back at `iunlock`.

  Then `iput`, having established REF-1 (`q = qt`, count 1), opens the
  escrow invariant for its two loads: the checked-out arm would put a
  second, disjoint share of slot `k` in existence, contradicting `q = qt`
  via `iref_lookup`, so the escrow must be **parked** and the cells are
  readable. `iget`'s `valid = 0` store on a free entry is the same argument
  at `M !! k = None` (the escrow can hold no share of a slot the authority
  does not list).

  **This is where REF-1 is actually spent.** The Arc algebra alone proves
  the exclusivity; the escrow is what converts exclusivity into *access*,
  and without it xv6's comment has no formal counterpart at all.

**Cost of (iii), honestly:** it is the single most expensive item in the
icache. `InodeLock.inode_parked` becomes the escrow's parked arm rather
than the sleeplock's payload (change **C2**), `SpecIlock`/`SpecIunlock`
gain a reference-share premise and return it, and `ProofIlock.v`'s
acquire/release seam moves from "the lock hands me `R`" to "the lock hands
me a token, and the token opens the escrow". Estimate: comparable to the
bio escrow itself, which is why the plan in §8 does it *last* and only
because `iput` cannot be written without it.

**Cheaper alternative, if the escrow is too much for a first cut:** state
`iput`'s contract to take the sleeplock's payload as a *precondition*
supplied by the caller — i.e. `iput` on an inode the caller has already
`ilock`ed. That is wrong for `iunlockput` and for `kexit`'s `cwd`, so it is
not a real option; recorded only so the next reader does not rediscover it
as one.

---

## 6. HOW THE ICACHE DISCHARGES `itrunc`'S TWO OWED PREMISES

`SpecItrunc.v` takes two hypotheses the model cannot supply
(`fs-inode.md`, "OWED: an inode names only real block numbers"). They have
**different** answers, and one of them is not an icache question at all.

### (i) `∀ i ≤ MAXFILE, bm_slot bm i ≠ 0 → bv_unsigned (bm_slot bm i) < size`

`fs-inode.md` says this "wants to live in one of two places: in
`blkmap_wf`, which would have to take `size` … or in whatever invariant
`ilock` establishes", and picks the second. **Both are wrong, and neither
is needed.**

`blkmap_wf cov logstart bm` *already* says every block the inode names is
in `cov` (that is its fourth conjunct, the one `bread` and `log_write`
demand). What is missing is one **pure geometry fact relating `cov` to the
FS size**:

```coq
Definition cov_below (cov : gset Z) (size : Z) : Prop := ∀ z, z ∈ cov → z < size.
```

and then the owed premise is a two-line corollary — `IcacheInv.v`'s
`blkmap_slot_inrange`, with `blkmap_get_inrange` / `blkmap_ind_inrange` as
the two spellings a `bfree` caller actually has:

```coq
Lemma blkmap_slot_inrange cov logstart size bm :
  cov_ok cov → cov_below cov size → blkmap_wf cov logstart bm →
  ∀ i, (i ≤ MAXFILE)%nat → bv_unsigned (bm_slot bm i) ≠ 0 →
    0 < bv_unsigned (bm_slot bm i) < size.
```

The `0 <` half comes free from `cov_ok`, which every caller already holds
inside `log_geom_ok`. So `itrunc`'s premise (i) is replaced by a **pure
premise of exactly the same character as `log_geom_ok`**, supplied from the
same place, and *no invariant moves*: `blkmap_wf` does not change,
`inode_ok` does not change, `ilock` does not change, and `bmap`/`writei`/
`readi` are untouched.

It is dischargeable rather than assumed, which is the standard this project
holds a new premise to. `FsBoot.fs_cov_in cov ndisk` already says every
covered block lies inside the disk image
(`0 < b ∧ 1024*(b+1) ≤ ndisk`), and `sb.size` describes that same image, so

```coq
Lemma cov_below_of_image cov ndisk size :
  (∀ b, b ∈ cov → 0 < b ∧ 1024 * (b+1) ≤ Z.of_nat ndisk) →
  Z.of_nat ndisk ≤ 1024 * size → cov_below cov size.
```

closes it (proven in `IcacheInv.v`; the hypothesis is `fs_cov_in` spelled
out rather than imported, so the file stays under the boot layer).

**Where it goes in the contract**: `cov_below cov size` alongside
`log_geom_ok cov logstart` in `SpecItrunc.v` (LANDED, cycle C2), and
thereafter in `SpecIput` and every FS contract that reaches `bfree`.
(The §(ii) narrowing to `i < MAXFILE` was already in the landed
`SpecItrunc.v` — the paragraph below predates it.) The cleanest home is a single
`fs_geom_ok cov logstart size := log_geom_ok cov logstart ∧ cov_below cov
size` bundle, but that renames a premise in ~10 landed contracts, so it is
recorded and not done.

### (ii) `∀ i, length (data i) = BSIZE`

This one really is an inode-layer invariant, and it really does belong in
what `ilock` establishes — but not for the reason `fs-inode.md` gives.

`bfree` returns the freed block to `BitmapInv.free_blk`, whose conjunct
`⌜length bs = BSIZE⌝` is the obligation. Nothing above `fsblock` records a
length: `FsBlocks.fsblock γ b bs` is a bare `ghost_map` half, and its
authority is inside `log.lock`, so a caller cannot read a length fact out
of it without taking the log lock. So unlike (i), this is *not* derivable
from anything the model holds today.

It **is** inductive over the inode layer, which is what makes it carriable:

- `balloc` returns `fsblock γfs b (replicate BSIZE 0)` — sized;
- `bmap` deposits exactly that into `inode_blocks` — sized;
- `writei` replaces a block's bytes with a list of the same length;
- `itrunc` empties to `fun _ => replicate BSIZE 0` — sized;
- a hole is `replicate BSIZE 0` by `blk_holes_zero`, which is *already* an
  `inode_ok` conjunct.

So the home is **one more conjunct of `InodeLock.inode_ok`**, beside
`blk_holes_zero` — the pure record `ilock` mints and `inode_parked` holds,
and which every consumer of `inode_locked` already receives:

```coq
Definition inode_sized (data : nat → list (bv 8)) : Prop :=
  ∀ i, (i < MAXFILE)%nat → length (data i) = BSIZE.
```

`IcacheInv.v` ships it with the three laws its producers need —
`inode_sized_zero` (itrunc's and ialloc's output), `inode_sized_insert`
(bmap's deposit, writei's block update) and `inode_sized_of_alloc` (a hole
is sized for free, so a producer only reasons about allocated indices).
Adding the conjunct to `inode_ok` is a one-line change plus one line in
each of the ~6 places that build an `inode_ok`; it is left unmade because
`inode_ok` lives in `InodeLock.v`, which this effort must not touch.

**A necessary narrowing of the premise, which is a bug in
`SpecItrunc.v`'s statement.** It reads `∀ i : nat, length (data i) =
BSIZE` — *unbounded*. No holder of `inode_locked` can supply that: both
`inode_blocks` and `blk_holes_zero` stop at `MAXFILE`, and `data` is a
total function whose values above `MAXFILE` are unconstrained. The premise
has to be `∀ i, (i < MAXFILE)%nat → …`, which is all itrunc's loops touch.
As written, `iput` would inherit an undischargeable hypothesis.

**And the better home, recorded and not taken.** The length is a
*block-layer* truth, not an inode one — `BitmapInv.free_blk` already pairs
`fsblock` with `⌜length bs = BSIZE⌝` by hand, and every block minted at
boot is `fs_blocks dk b`, which is 1024 bytes by construction. Folding the
conjunct into `fsblock` itself

```coq
Definition fsblock γ bno bs := ⌜length bs = BSIZE⌝ ∗ bno ↪[fs_L γ]{#(1/2)} bs.
```

retires it from `free_blk`, from `inode_ok`, from `itrunc`'s premise and
from every future one at a stroke. The ripple is `FsBlocks.fsblock_update`
gaining a `length bs_new = BSIZE` premise (its only caller is `log_write`'s
ghost step, which writes a whole buffer) and `fs_alloc`'s per-block bundle
proving it once from `fs_blocks`'s length. That is a change to
`FsBlocks.v`, a file far below this one with many consumers, so it is
recorded here and left unmade — but it is the right answer and whoever
next touches `FsBlocks.v` should do it.

### Summary

| owed premise | home | cost |
|---|---|---|
| (i) blocks are in range | a **pure** `cov_below cov size` premise beside `log_geom_ok`; the per-slot fact is a corollary of the existing `blkmap_wf` | 1 new pure premise in `SpecItrunc`/`SpecIput`; **no invariant changes** |
| (ii) blocks are BSIZE bytes | a new `inode_sized` conjunct of `InodeLock.inode_ok` — *or*, better, folded into `FsBlocks.fsblock` and then nowhere | one line in `inode_ok` + ~6 producers; the `fsblock` variant is bigger but retires the fact permanently |

Neither is an icache *invariant*. That is the substantive correction to
`fs-inode.md`'s guess.

---

## 7. What the icache still needs that does not exist: the inode STORE

Falling out of (C1) in §3: when an entry is recycled, the previous inode's
`ind_res` and `inode_blocks` have to go **somewhere**, and when a
never-cached inode is `ilock`ed for the first time its blocks have to come
**from** somewhere. The `fsblock`/`blk_own` for every covered block are
minted at boot (`FsBoot.fs_alloc`) and today are partitioned between the
bitmap's free pool (`BitmapInv.free_pool`), the log's own storage, and
whatever the in-flight proofs hold. **The used data blocks of inodes that
are not in the icache have no owner in the model.**

**SUPERSEDED IN PART BY §10.** The shape guessed at below (two fupds, one
at ilock's uncached arm) is not implementable and is not what the bio escrow
does; read §10.1 first. What survives is the need for the object, and the
observation that `ireclaim` is the caller that can establish its contents.

That object — call it the inode store, an authoritative `inum ↦ (dinode,
blkmap, data)` map owning the blocks of every allocated inode — is a
separate piece of design from the icache, and `ialloc`, `ireclaim` and
`namei` will all want it. The icache's interface to it is exactly two
fupds, at `ilock`'s uncached arm (take) and at `iput`'s last close /
`iget`'s recycle (put). Do not try to build the icache without at least
fixing that interface, or (C1) comes back as an unprovable arm.

`ireclaim` is worth reading before designing it: it is `fsinit`'s
single-threaded orphan sweep, so it is the one caller that can establish
the store's initial contents.

---

## 8. Order of work

**Items 2 and 3 are superseded by §10**, which merges them: the escrow and
the pool are ONE edit, made at iget's recycle, and the escrow's design is now
fully determined. §10.5 records the piece that is NOT determined (the dinode
blocks' ownership), which has to be settled before item 4.


1. **`IcacheInv.v`** — done: geometry, algebra, the `ref` invariant, the
   lock resource, and §6's two pure layers.
2. **(C2 / §5(iii)) the per-entry escrow.** Everything else waits on it,
   because `iput`'s first two loads do. Model it on `BioInv.v`.
3. **(C1) `inode_parked`'s unloaded arm + the two-state shadow**, and the
   inode store's interface (§7) — one change, since the arm's resources go
   to the store.
4. **`SpecIlock`/`SpecIunlock`**: swap the `i_ref` premise for
   `itable_inv` + `iref_tok` (§4); add the escrow's reference share (§5);
   re-prove the two guard loads and the acquire/release seam.
5. **`inode_ok` gains `inode_sized`** (§6 (ii)), and `cov_below` enters
   `SpecItrunc`/`SpecIput` (§6 (i)). Narrow `SpecItrunc`'s length premise
   to `i < MAXFILE` at the same time.
6. **`SpecIdup` / `ProofIdup`** — the smallest of the three, 54 bytes,
   pure `acquire; ref++; release`, and the one that exercises
   `iref_dup_step` end to end. Retires `LinkIdup.v`'s axiom.
7. **`SpecIget` / `ProofIget`** — the scan (`ientry_step`,
   `ientry_sentinel`), `iref_alloc_step`, and the store hand-off.
8. **`SpecIput` / `ProofIput`** — REF-1, both close steps, and the whole
   truncate arm. Retires `LinkIput.v`'s axiom, and with it the last fs-side
   assumption in `kexit`'s cone.

---

## 9. Findings that contradict, or correct, existing notes

- **`SpecIlock.v` / `SpecIunlock.v`'s `i_ref ip ↦₄{dqr} refv` premise is
  unsatisfiable** by any icache (§4). Two landed, proven contracts are
  affected. This is the kind of thing `fs-inode.md` itself warns about
  ("the fourth time in this effort a contract was nearly written with a
  premise its only caller could not supply") — here it was written.
- **`fs-inode.md`'s guess about itrunc's premise (i) is wrong in both
  branches** (§6): it is neither a `blkmap_wf` conjunct nor an `ilock`
  invariant, but a pure `cov`-vs-`size` geometry premise, and the per-slot
  fact then follows from the `blkmap_wf` that already exists.
- **`SpecItrunc.v`'s second premise is stated unbounded** (`∀ i : nat`) and
  must be narrowed to `i < MAXFILE`; as written no holder of
  `inode_locked` can discharge it (§6 (ii)).
- **`InodeLock.inode_parked`'s unloaded arm blocks slot recycling** (§3
  C1) — i.e. it makes most of `iget` unprovable. This is the largest
  structural finding and it is invisible from `ilock`'s own proof, which
  never recycles anything.
- **xv6's own comment about `itable.lock` protecting `ref`/`dev`/`inum` is
  not the whole truth** (§2): `ilock`/`iunlock` read `ref` with no lock,
  and `iput`/`iget` touch `valid` and `nlink` with no sleeplock. Both
  exceptions are safe, and both cost real machinery.
- **The "`acquiresleep()` won't block (or deadlock)" half of `iput`'s
  comment needs no theorem** in this logic (§5 (a)). The load-bearing part
  of that comment is an ownership statement, not a scheduling one.
- **§11.4's "SETTLED" swap design was wrong** (§12): the checked-out arm
  has nothing it can hold, by conservation against `log_write`'s own
  footprint. The region is one-armed and `SpecLogWrite`'s `fsblock`
  premise generalizes to a fupd instead.

---

## 10. THE ESCROW AND THE POOL, worked out against `BioInv.v`

§7 posed the inode store as an object `ilock` would take from by a fupd, and
§8 ordered the escrow before it as two separate items. Reading the bio
escrow end to end says both were wrong, and in a way that makes the work
smaller rather than larger. This section supersedes §7 and §8's items 2-3.

### 10.1 `ilock` never touches the store

§7's shape is not implementable: `ilock` holds neither `itable.lock` nor the
authority -- only the entry's sleeplock -- and an Iris invariant cannot hold
resources across `ilock`'s `bread`/`brelse`.

bio does not do that. `bio_pool` lives inside **`bcache.lock`'s resource**
and the exchange fires in the RECYCLER, under that lock, at the single
instruction where cache membership moves. The recycler parks the arriving
block's bundle in the escrow's payload on its way past, and "whoever wins
the fill race finds it" (`BioInv.v:389-394`).

The icache does the same. The uncached inodes' bundles live in a pool inside
`itable_res`; the exchange fires at **`iget`'s recycle**, which holds
`itable.lock` and holds the authority at `M !! k = None`. `ilock` then finds
the arriving inode's bundle already parked in the escrow it opens anyway.
C1's fix and the store become the same edit, and §7's problem does not
arise.

### 10.2 THREE arms, not two -- and `iget` is why

`buf_escrow_body := buf_parked ∨ buf_chain ∨ buf_mid` (`BioInv.v:447`).
The third is the RECYCLE WINDOW: cells only, decoupled from any payload,
with the recycle token OUT in the recycler's hand (`BioInv.v:440`).

It is not optional here, and the reason is visible in the image. `iget`'s
recycle arm writes four fields at four separate instructions:

      +0x6e  sw s2,0(s3)      ip->dev   = dev
      +0x72  sw s4,4(s3)      ip->inum  = inum
      +0x78  sw a5,8(s3)      ip->ref   = 1
      +0x7c  sw zero,64(s3)   ip->valid = 0

Each is its own atomic-update opening, and between them the entry is in
NEITHER stable state. A two-arm escrow cannot get from `+0x6e` to `+0x72`.

bio refutes its mid arm with the **dev cell held FULL at the view's single
pinned device value** (`BioInv.v:434-439`), which works because there is one
device. xv6 is single-device too, so the trick carries -- but it breaks the
moment entries are keyed by `(dev, inum)` across devices. Recorded because
it is invisible until it fails.

### 10.3 The two refutations are DIFFERENT, and only one is ours

Do not conflate them; §5(iii) above does, slightly.

* The **sleeplock winner** (`ilock`) refutes the checked-out arm with
  `bown_exclusive` -- its own token against the arm's -- and the mid arm
  with any fraction of an identity cell against the mid arm's full one.
* The **authority-side opener** (`iget`, `iput`) holds no checkout token.
  It refutes the checked-out arm with the count fragment: at
  `M !! k = None` the arm's own `iref_tok` cannot exist. bio calls this
  `bref_tok_free_absurd` (`BioInv.v:482`); ours is `iref_lookup`.

It is the SECOND that `iget`'s `valid = 0` store needs, and it is the whole
reason the checked-out arm must carry the count fragment rather than just a
marker. The same fact does double duty in bio: `buf_pay_evict`
(`BioInv.v:619`) kills eviction of a DIRTY buffer because a dirty payload
parks a real reference. The inode analogue -- an inode with unflushed
changes is pinned -- carries over cleanly and is the most reusable idea in
the file.

### 10.4 What the sleeplock holds afterwards

Exactly one exclusive ghost token, and nothing else:

```coq
  is_sleeplock ... "buffer"%string (bown bn k)      (* BioInv.v:1030 *)
  Definition bown bn k := lock_tok_excl (bn_own bn k).
```

`InodeLock.inode_parked` stops being the sleeplock's payload and becomes the
escrow's parked arm. `inode_locked` -- which already carries
`i_valid ip ↦₄ 1` and both key halves -- is already, structurally, the
checked-out arm's complement; that is the one part of the restructuring the
current file gets right for free.

### 10.5 THE ONE THING STILL OPEN: who owns the dinode blocks

The pool settles `ind_res` and `inode_blocks`. It does NOT settle the tie
that makes `SpecIlock`'s

      vv = false -> ds !!! islot inum = dn

an OUTPUT rather than an assumed premise. Post-C1 the shadow is `Unloaded`
and carries no `dn`, so `ilock` reads `ds !!! islot inum` off the block and
must conclude that the pool entry it is about to take describes THAT dinode
-- in particular that the pool's `bm` is the one `di_addrs dn` names.

Nothing available says so. The pool entry would have to be tied to the
dinode block's content, and the dinode block is not the pool's to own: it
holds SIXTEEN inodes, and today the caller of `ilock` passes it in as
`fsblock gfs (IBLOCK inum inodestart) (diblk_bytes ds)` with `SpecIlock.v:175`
recording "who owns it is deferred exactly as it is for iupdate".

The icache is where that deferral comes due. The invariant IS maintainable
-- only `iupdate` writes a dinode, only on a LOCKED inode, and a locked
inode is not in the pool -- but stating it needs the inode region's blocks
to have an owner, which is a bigger object than the pool: something like an
`inode_region` owning every dinode block plus, per allocated inum, the
bundle the pool holds. `ialloc` and `ireclaim` will want the same object.

DO NOT start the escrow implementation expecting this to fall out. It is a
separate design step, it is the real remainder of §7, and the honest state
is that the escrow is now fully determined and the dinode-block ownership is
not.

### 10.6 Two corrections to the files this was read from

* `ProofBrelse.v:617-624` claims the escrow body is not timeless and strips
  the later by hand. `BioInv.v:456-478` DOES provide the instance (the view
  record carries `bv_clean_tl`/`bv_dirty_tl` precisely so every opener can
  strip it), and `ProofBread.v` uses `>Hbody` throughout. The comment is
  stale; model on the `>Hbody` form.
* §5(iii) of this note describes the checked-out arm as holding "a slice of
  the entry's reference share" and attributes the parked-arm argument to it
  generally. Accurate for the authority-side opener, wrong for the sleeplock
  winner -- see 10.3.

---

## 11. THE INODE REGION: refine the block half into per-inum fragments

§10.5 left one thing open: who owns the dinode blocks, so that `ilock` can
conclude the pool entry it takes describes the dinode the block actually
holds. This section answers it. The answer is not "a bigger pool" -- it is
a CHANGE OF GRANULARITY, and it makes an owed premise disappear rather than
be discharged.

### 11.1 The mismatch, stated exactly

`FsBlocks.fsblock γ b bs` is `b ↪[fs_L γ]{#(1/2)} bs` -- HALF a ghost_map
element, the other half riding in the bio handle. Two consequences the
whole problem follows from:

* it is the WRITE PERMISSION. `log_write` consumes `fsblock γfs bno bsl`
  and returns `fsblock γfs bno bs` at the new content (`SpecLogWrite.v:140,
  156`). An update needs the half; there is no writing without it.
* it is PER BLOCK, and a dinode block holds SIXTEEN inodes (`IPB = 16`).

But every inode-layer contract's EFFECT is already per-slot. `iupdate`
takes the block at `diblk_bytes ds` and returns it at
`diblk_bytes (<[islot inum := dn]> ds)` (`SpecIupdate.v:176, 203`) -- one
slot changed, fifteen untouched. The resource is coarser than the effect,
and that gap is the bug.

It is a real conflict, not a bookkeeping annoyance. Two locked inodes in
the same block both calling `iupdate` each need the half for their whole
call. Nothing serializes them: xv6 has NO lock over a dinode block except
the buffer's sleeplock, which is held only across `bread`..`brelse`. So a
contract that takes the half for the duration of the call is unsatisfiable
by two such callers, and threading it up to the caller (which is what every
contract does today, and what `SpecIlock.v:175` calls "deferred exactly as
it is for iupdate") only moves the unsatisfiability.

### 11.2 The fix: a per-inum dinode map, coupled to the block

Introduce a ghost map at the granularity the effects already have:

```coq
  Definition dinode_at (γi : gname) (inum : bv 32) (dn : dinode) : iProp Σ
    := inum ↪[γi] dn.            (* EXCLUSIVE, one per inum *)
```

and a per-block coupling that owns the coarse half and pins it to the
sixteen fragments:

```coq
  Definition iblk_body γfs γi (inodestart : Z) (b : Z) : iProp Σ :=
    (∃ ds : list dinode, ⌜diblk_wf ds⌝ ∗
       fsblock γfs b (diblk_bytes ds) ∗
       [∗ list] i ∈ seq 0 IPB, dinode_auth_frag γi (inum_of b i) (ds !!! i))%I.
```

The coarse half NEVER LEAVES the region. Sixteen callers coexist because
their fragments are disjoint. The coupling is what turns "slot `islot inum`
now holds `dn`" into "the block's bytes are `diblk_bytes (<[islot inum :=
dn]> ds)`" -- i.e. exactly `iupdate`'s existing postcondition, now derived
instead of assumed.

### 11.3 What this does to the contracts, and to the owed premise

`SpecIupdate`, `SpecIlock`, `SpecWritei`, `SpecItrunc` and `SpecFileread`
swap

      fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds)

for

      dinode_at γi inum dn

and `iupdate`'s postcondition collapses from `<[islot inum := dn]> ds` to
`dinode_at γi inum dn`. Five landed contracts, but each is strictly
simpler afterwards.

**And `SpecIlock`'s `vv = false -> ds !!! islot inum = dn` DISAPPEARS.** It
does not get discharged by a new invariant; it stops being expressible,
because the caller no longer supplies a block and a claim about its slot --
it supplies the inum's dinode directly, and the fragment IS the fact. That
is the test this design should be judged by: §10.5's question was "what
makes the premise derivable", and the right answer turned out to be "state
the resource at the granularity of the effect and there is no premise".

The pool of §10.4 then carries, per uncached inum, `dinode_at γi inum dn`
alongside the `ind_res`/`inode_blocks` bundle, with `inode_ok` tying them.
`iget`'s recycle moves the whole triple into the escrow; `ilock` finds it
parked. C1, the pool, and the region become one coherent object.

### 11.4 The borrow, and where it hangs -- SUPERSEDED BY §12

**This subsection's swap design is unimplementable and §12 replaces it.**
The checkout at +0x66 cannot state its checked-out arm: during the window
the thread's own log_write footprint holds every per-block exclusive
resource, so the arm has nothing to hold and a checkout can never refute
it. §12 has the conservation argument and the (smaller) fix. The
instruction observations below remain true and the ilock half survives in
simplified form; only the +0x66/+0x6c swap pair is dead.

The coupling must be OPENED to write: `iupdate` swaps the block's bytes at
its `log_write`. An invariant cannot be held open across a call, so the
swap has to be two GHOST OPERATIONS at two single instructions, with the
half travelling with the thread in between -- exactly `escrow_swap_checkout`
/ `escrow_swap_park`, and exactly why `ProofBrelse` hangs a swap on an
otherwise unrelated frame store (`ProofBrelse.v:605-638`).

The instructions exist, and they could not be more convenient. iupdate's
tail, read off the image:

      +0x62  jal  memmove
      +0x66  mv   a0,s2        <-- bp into a0 for the next call
      +0x68  jal  log_write
      +0x6c  mv   a0,s2        <-- bp into a0 again
      +0x6e  jal  brelse

Two plain register moves bracketing the `log_write`, each doing nothing but
reloading `bp`. So:

* at **+0x66**, swap the region's escrow for `IBLOCK inum` to CHECKED OUT,
  taking `fsblock γfs (IBLOCK inum inodestart) (diblk_bytes ds)` out;
* `log_write` at +0x68 consumes it at the old content and returns it at the
  new, with its contract COMPLETELY UNCHANGED;
* at **+0x6c**, swap back to PARKED at the new bytes and retag
  `dinode_at γi inum dn` in the same ghost step -- which is where the
  coupling `diblk_bytes ds` vs the sixteen fragments is re-established.

`SpecLogWrite` does not move. That was the thing worth checking before
starting, because it has many callers; the answer is that it is untouched.

The checkout is justified the way bio's is: the thread holds the BUFFER for
that block (from the `bread` at +0x20, still held at +0x66 and +0x6c), and
the buffer is exclusive, so no other thread can be mid-swap on the same
block. The region nests the bio protocol rather than duplicating it.

`ilock`'s read side has them too. Its `bread` is at +0x4a and its `brelse`
at +0x90, and between them:

      +0x4a  jal  bread
      +0x4e  mv   s2,a0        <-- bp saved
      ...    the dinode field reads and the addrs memmove
      +0x8e  mv   a0,s2        <-- bp into a0 for brelse
      +0x90  jal  brelse

so the OPEN hangs on +0x4e and the CLOSE on +0x8e. ilock only READS, so it
takes the half, learns the bytes by agreement against the handle's payload
half, and puts it back unchanged -- no `log_write`, no retag.

Both functions therefore have two plain register moves in exactly the right
places, and neither needs an instruction invented for it. That is the last
thing §10.5 was waiting on: the region is fully determined and the escrow
can be written.

*(The paragraph above was written before §12 found the checkout window
unstatable. The register moves are real; the swaps that were to hang on
them are not. Read §12.)*

---

## 12. §11.4'S CHECKOUT HAS NOTHING TO DEPOSIT: a conservation argument,
## and the smaller design that replaces it

Implementation (2026-08-09) hit a wall that re-derivation confirms is
structural, not a proof-skill problem. Recording it the way §10.6 records
bio's stale comment: so nobody re-settles §11.4 as written.

### 12.1 The hole

A §11.4-style escrow needs its CHECKED-OUT arm to contain something a
would-be second checker-outer can be refuted by (bio's `buf_chain` holds
`bown`; that is what makes `escrow_swap_checkout` provable). Whatever sits
in that arm must be deposited by the FIRST checker-outer at +0x66 and sit
there across its `log_write`. Now enumerate what the thread can spare
during that window:

* `SpecLogWrite`'s premise is `bio_held … bs bsl bsd d` PLUS the client
  half `fsblock γfs (uint bno) bsl`. `bio_held` contains `disk_block γd
  (uint bno) bsd` (full), and its `bio_pay` contains the machinery half
  `bno ↪[fs_L]{½}` and the machinery dirty half — on BOTH the clean and
  dirty arms.
* The `fs_L` entry's total fragment mass is client ½ + machinery ½ = 1;
  `disk_block` is a full exclusive element; the remaining dirty half and
  the `fs_L` auth live inside `log.lock`, which `log_write` itself takes.

So during the window **every per-block exclusive resource for that block
is in the thread's own `log_write` footprint**, and by conservation the
checked-out arm can hold none of it — not even a fraction. Nothing else
refutes: a per-inum deposit (`dinode_at`, the inode's sleeplock token)
does not clash with a checkout by a DIFFERENT inum of the same block, and
a fresh per-block token has no sound resting place — its holder between
windows would have to be "whoever holds the block's buffer", and there is
no hook in bio's interface to ride on. bio's own escrow escapes only
because `bown` is a resource its mid-window calls never need; the region
has no such spare. Variants tried and killed by the same argument: an
enter/exit pair bracketing the whole bread..brelse window (its mid state
is unrefutable at enter for exactly the same reason); `blk_own` as the
credential (no way to acquire it before the first opening); fractional
splits of `disk_block` or the halves (mass conservation).

### 12.2 The fix: no checked-out state, and log_write's fsblock premise
### becomes a fupd

The only moment the client half is actually NEEDED out of the region is
`log_write`'s own ghost step — `ProofLogWrite.v:2074`, a single `iMod` of
`fsblock_update` between two instruction dispatches, at mask ⊤, no
invariant open. So the withdrawal happens INSIDE that step:

* **The region is ONE-armed.** `ireg_inv` always holds, per inode block,
  `∃ ds, ⌜diblk_wf ds⌝ ∗ fsblock γfs b (diblk_bytes ds)`, plus (globally)
  `ghost_map_auth γi 1 m` with the pure coupling `m !! inum = Some (ds !!!
  islot inum)` for the sixteen inums of each block. Callers hold FULL
  fragments `dinode_at γi inum dn := uint inum ↪[γi] dn` (§11.2's shape,
  unchanged). No arms, no tokens, no swap lemmas.

* **`SpecLogWrite` generalizes its `fsblock` premise to an atomic-update
  form**: instead of `fsblock γfs (uint bno) bsl` in hand, the caller
  supplies

      |={⊤, E'}=> ∃ bsl', fsblock γfs (uint bno) bsl' ∗
         (⌜bsl' = bsl⌝ -∗ fsblock γfs (uint bno) bs ={E', ⊤}=∗ Φfsb)

  fired at the 2074 ghost step; `fsblock_update`'s own agreement against
  the handle's machinery half is what discharges `bsl' = bsl`, so the
  caller never has to know the region's content in advance. The OLD form
  is the trivial instance (a caller holding the fsblock wraps it in a
  no-op fupd), derived once in the spec file — **no existing caller
  moves, and `ProofLogWrite` changes at exactly one site.** Expose both
  as `Module Type` parameters so the sealed functor serves old and new
  consumers alike.

* **`iupdate`** discharges the fupd by opening the region there: withdraw
  the block's `fsblock` at `diblk_bytes ds`, let `fsblock_update` run,
  deposit it back at `diblk_bytes (<[islot inum := dn']> ds)` and retag
  `dinode_at γi inum dn'` against the auth in the same opening. Its
  contract's `fsblock`-in/`fsblock`-out pair collapses to `dinode_at γi
  inum dn -∗ … dinode_at γi inum dn'` exactly as §11.3 promised. The
  +0x66/+0x6c register moves are no longer load-bearing.

* **`ilock`** needs only a READ: one mask-preserving opening of `ireg_inv`
  at any instruction while it holds the buffer — its payload's machinery
  half agrees with the region's client half, pinning the bytes to
  `diblk_bytes ds`; `dinode_at` against the auth plus the coupling gives
  `ds !!! islot inum = dn`. Pure facts out, nothing withdrawn. This is
  §11.4's read side minus the checkout it never needed.

### 12.3 One new pure obligation: `diblk_bytes` is injective on wf lists

Between `iupdate`'s bread (where it learns the block's `ds`) and its
`log_write` (where the region's `∃ ds'` is opened again), nothing the
thread holds pins the region's LIST — only its bytes (via the machinery
half, which rides in the thread's payload the whole way). Concluding
`ds' = ds`, which the coupling's re-establishment at the other fifteen
slots needs, takes

    diblk_wf ds -> diblk_wf ds' ->
    diblk_bytes ds = diblk_bytes ds' -> ds = ds'

i.e. per-field injectivity of `dinode_bytes`. Provable from the
byte-extraction lemmas `DinodeSlot.v` already uses to read fields off a
block; it did not exist before because nothing decoded. It belongs in
`DinodeEnc.v`.

### 12.4 What this retires, and what stands

Retired: the three-state-per-block escrow of §11.4, `iblk_tok`, the
+0x66/+0x6c and +0x4e/+0x8e swap hangs. Standing, unchanged: §11.1–11.3
(the granularity argument, `dinode_at`, the disappearing premise), §10's
per-ENTRY escrow and pool (the itable entry's cells are a different object
with a real sleeplock credential — bio's shape fits THERE), and every
geometry/algebra layer in `IcacheInv.v`.

### 12.5 ...and §10.2's THIRD arm is probably unnecessary too

§10.2 argued the entry escrow needs bio's mid arm because iget's recycle
writes four fields at four separate instructions and "between them the
entry is in NEITHER stable state". That reasoning implicitly assumed the
escrow owns all four cells, the way `buf_parked` owns a buffer's. It does
not. In the landed architecture the four stores hit FOUR DIFFERENT
homes:

      +0x6e  sw s2,0(s3)      ip->dev    -- itable.lock's [islot] (held)
      +0x72  sw s4,4(s3)      ip->inum   -- itable.lock's [islot] (held)
      +0x78  sw a5,8(s3)      ip->ref    -- [itable_inv], one opening
      +0x7c  sw zero,64(s3)   ip->valid  -- the escrow, one opening

The identity cells are lock-carried (no instruction-level coupling: the
lock's resource is re-established at RELEASE, not per store), the ref
word's store and its `M` update share one `itable_inv` opening (§4), and
the escrow — which owns only `i_valid` and the sleeplock payload content
— sees exactly ONE store. Each object passes through no unstable window,
so the escrow is TWO-armed (parked / checked out), and §10.2's dev-pin
trick has nothing left to do. The checked-out arm still carries the
count fragment, and `iget`'s valid store still refutes it by
`iref_lookup` at `M !! k = None` — §10.3 stands verbatim.

VERIFIED (2026-08-09, against a full-generator scratch decode of iget —
170 bytes, `igi_` prefix): the only non-frame stores are the hit arm's
`sw a5,8(s1)` at +0x58 (ref++, one `itable_inv` opening) and the recycle
quad +0x6e/+0x72/+0x78/+0x7c. No escrow-owned cell is touched twice
between stable states. The escrow is TWO-armed — **SUPERSEDED: §13's
inum-cell tie makes the payload swap at +0x72 outrun the valid store at
+0x7c, and the mid arm resurrects with a different discriminator than
bio's; read §13.1c.** Three consequences the verification turned up
(all still true):

* **§10.3's refutation story is wrong at the `valid = 0` store.** By
  +0x7c the ref store at +0x78 has already run, so `M !! k` is
  `Some (q, 1)`, not `None`. The checked-out arm is refuted there by the
  recycler's own just-minted token against the arm's: two fragments'
  fraction components sum past 1, invalid with no authority in sight
  (`iref_tok_frac_excl`, to be added — fragment-only validity). The
  `M !! k = None` reading applies only to openings BEFORE +0x78.
* **`iref_alloc_step` mints at `q = 1`, and that cannot stand.** A full
  first fraction leaves `islot_rest` empty, and a later cache-HIT iget
  has no retained share to mint a new reference from (iget's hit arm has
  no caller token to split — `iref_dup_step` is idup's shape, not
  iget's). Alloc must mint at `q = 1/2` (table keeps 1/2), and the hit
  arm needs a `bio_incr_step` mirror (`iref_incr_step`: mint `qn` with
  `✓(qt + qn)` from the retained share, count++) plus its store_au
  wrapper. `BioInv.bio_incr_step` is the worked precedent.
* iget takes NO sleeplock (ilock does); its whole body runs under
  itable.lock, so every escrow opening it makes is authority-side.

---

## 13. THE ESCROW AND POOL, FULLY DETERMINED (C3's definitional layer)

Working §10.4 against the landed files forced three decisions §10 left
open. Recorded before the code, in the §12 discipline.

### 13.1 The shadow RETIRES — and ilock's "no type" panic stays LIVE

§11.3's promise holds fully: the parked content's record is pinned by
the arm's own `dinode_at` fragment, so `inode_key`/`ghost_var` has no
coupling job left. Its one remaining candidate job — letting a caller
refute ilock's "no type" panic on a never-loaded entry — turns out to
need NO ghost at all: **the panic arm simply stays live.** This is a
partial-correctness WP; a reachable panic diverges through
`panic_wp_any` and the postcondition then speaks only for successful
loads. A caller premise ("this inum is allocated") would be
undischargeable today anyway — allocatedness is directory-structure
knowledge (namei/ialloc, future work) — and v1's conditional premise
existed only because the lock's ∃-bound payload had no other tie to the
disk; the region IS that tie now. Consequences: `SpecIlock` v2 has NO
shadow premise, NO `ds`-slot premise, and one live panic arm (a first
for this tree — note it in the spec header; precedent for the pattern:
the contract still refutes the `ip == 0 || ip->ref < 1` panic, so only
the free-inode load diverges). `ilock`'s postcondition ∃-binds
`(dn, bm)`; readi/writei instantiate from it, exactly as they already
do from `inode_locked`'s existential `data`.

An ishadow ghost_var was drafted and rejected: with N reference holders
only two halves exist, so "the caller supplies the shadow half" is
unsatisfiable for the second holder — the same multi-holder trap as
§4's `i_ref` premise. Nothing that must be suppliable by EVERY
reference holder can be a ghost_var half.

### 13.1b The arm ties its dinode_at to the entry by an INUM-CELL
### fraction, and the identity mass is re-budgeted

The escrow is per-slot; its content's `dinode_at γi inum' dn0` must be
for THE inum the entry's identity cells name, or a winner cannot fire
`ireg_read` for its own inode. The tie is bio's (buf_parked holds
`b_dev ↦{½}`): **the escrow permanently owns HALF of the `i_inum` cell**
(the dev cell needs no arm tie — `dinode_at` is inum-keyed). The other
half is shared by the references and the table exactly as before, so
the reference algebra's identity fractions now range in `(0, ½]`:
`islot_rest k qt` becomes `(½ − qt)`-shaped, and `iref_alloc_step`'s
successor mints at `q = ¼`-style fractions (see §12.5's alloc note —
already forced to move off `q = 1` for the incr-step reason).
`IcacheInv.islot`/`islot_rest`/`islot_rest_join` change; nothing proven
consumes them yet except ProofIdup's pass-through frame.

### 13.2 The pool's domain is a pure slot→inum map in `itable_res`

"The pool holds every uncached inum" needs the cached set to be
speakable. `M : gmap nat (Qp * positive)` is slot-keyed and value-blind,
and the inum lives in identity CELLS. So `itable_res` gains a pure
`ci : gmap nat (mword 32 * mword 32)` (live slot → (dev, inum)) with
three wf clauses: `dom ci = dom M`; `ci` is INJECTIVE on inums (xv6's
own guarantee — iget recycles only after a full scan misses, and the
scan's loop invariant is what proves it); and each live slot's identity
cells sit at `ci !! k`'s values (i.e. `islot` takes its dev/inum from
`ci` instead of ∃-binding them). The pool is then

    ipool γfs γi P := [∗ set] z ∈ P, ipool_entry γfs γi z
    with  P = region_inums nib ∖ (uint ∘ snd <$> ci)

### 13.3 A pool entry has TWO shapes, because free inodes exist

`inode_ok` demands `di_type ≠ 0`, and the pool must also hold the
type-0 inums (a free inode owns no blocks — itrunc returned them):

    ipool_entry γfs γi z :=
        (∃ dn0 bm0 data0, ⌜inode_ok … dn0 bm0 data0 ∧ …⌝ ∗
           dinode_at γi z dn0 ∗ ind_res γfs bm0 ∗ inode_blocks γfs bm0 data0)
      ∨ (∃ dn0, ⌜bv_unsigned (di_type dn0) = 0⌝ ∗ dinode_at γi z dn0)

iget's recycle moves whichever shape the inum has into the escrow's
unloaded arm; §13.1's caller premise is what keeps ilock off the free
shape. ialloc (future) is the function that flips an entry free→allocated,
and it will do it through `dinode_at` + `wp_log_write_au` like iupdate;
nothing here prejudges it.

### 13.1c THE MID ARM RESURRECTS — with design-time evidence, and a
### different reason than §10.2 gave

§12.5's two-armed conclusion dies on the inum-cell tie of §13.1b.
Trace iget's recycle against the parked arm's coupling (valid word keys
the payload's shape; the arm's `dinode_at` is keyed by the inum cell):

    +0x6e  sw dev    — cells: table ½ only; no escrow coupling. Fine.
    +0x72  sw inum   — needs the arm's inum-cell ½ joined in, and the
                       arm's dinode_at must retag to the NEW inum: this
                       opening also swaps the payload (new inum's pool
                       bundle in, old bundle out to the pool). BUT the
                       valid cell may still read 1 — the arm's
                       valid↔shape coupling cannot be re-established.
    +0x7c  sw valid  — only here does the coupling hold again.

So the window `[+0x72, +0x7c)` is a real mid state after all: **valid
stale at 1, payload already the incoming unloaded bundle, recycle token
out in the recycler's hand.** §10.2's instinct was right; its REASON
(the dev store) was wrong — the dev store needs nothing, and it is the
inum-store-to-valid-store gap that cannot be bridged by two arms. The
arms are bio's exactly:

    PARKED : ∃ inum sh-payload, i_inum ↦₄{½} inum ∗
             i_valid ↦₄ (valid word keying the payload shape) ∗
             payload(inum) ∗ ic_mid k
    OUT    : ic_tok k ∗ (∃ q dev inum, inode_ref γic k q dev inum) ∗
             ic_mid k
    MID    : ∃ inum, i_inum ↦₄{½} inum ∗ i_valid ↦₄ (∃ stale word) ∗
             unloaded-payload(inum)      (token out with the recycler)

Refutations: a sleeplock winner refutes OUT by its own `ic_tok`
(lock_tok_excl) and MID by holding... the winner holds no valid-cell
fraction — MID is refuted authority-side only: the recycler holds
itable.lock, and a winner's checkout happens with no itable.lock, so
the winner refutes MID by `ic_mid`? No — the winner does not hold
`ic_mid`. The winner refutes MID the way bio's does: MID can only exist
while the recycler is between its two stores, and the recycler holds
the lock — but locks are not visible to the escrow. THE HONEST ANSWER:
the winner's checkout must present a resource MID excludes, and the
only candidate is the count fragment: MID exists only at a slot whose
`M`-entry the recycler has just minted at count 1 holding the whole
minted fraction, so a winner's OWN `iref_tok` at that slot makes the
outstanding count ≥ 2 against... `M` is not visible inside the escrow
either. RESOLUTION (bio's, verbatim): MID holds the i_valid cell FULL
(it does, see above) and so does PARKED — the winner cannot distinguish
them by cells; bio's winner refutes the mid arm by a fraction of an
identity cell against the mid arm's FULL one (`BioInv.buf_mid` holds
`b_dev` full). Mirror it: **MID holds the inum cell FULL** (the
recycler joins the table's ½ in at +0x72 and keeps it there through
+0x7c), so a winner — which always holds `inode_ident k q`, a real
inum-cell fraction, from its reference — refutes MID by fraction
overflow on the inum cell. PARKED keeps ½ so the winner's fraction
composes fine there. This is why the identity re-budget of §13.1b is
not optional bookkeeping: the ½/full split of the inum cell IS the
parked/mid discriminator.

### 13.1d Transcription findings (C3a, 2026-08-09): the whole-reference
### deposit, and PARKED-MEANS-FLUSHED

Two facts surfaced landing `IcacheEscrow.v`, both now normative:

* **A reference cannot be fraction-split without the authority**: two
  `iref_tok`s at `(q/2, 1)` compose to count 2, a different element —
  splitting the fraction splits the COUNT, which is `iref_dup_step`'s
  job and needs the lock. So the checkout deposits the winner's WHOLE
  `inode_ref` into the OUT arm and the park returns it whole (BioInv's
  shape exactly). iunlock's lock-free `ip->ref < 1` read, which happens
  INSIDE the critical section, borrows the deposited reference for one
  atomic update via `ic_open_out` (the winner's FULL valid cell refutes
  the other two arms). SpecIlock v2's postcondition returns the loaded
  BUNDLE and no reference; SpecIunlock v2 returns the reference whole.
* **PARKED-MEANS-FLUSHED**: the loaded arm's `dinode_at` is at the
  in-memory `dn` — no separate `dn0`. Without this, iget's eviction
  cannot conclude the pool's allocated shape (its `inode_ok` is about
  the on-disk record) from the loaded arm's (about the in-memory one).
  It is an honest invariant — every writer ends with iupdate (writei's
  and itrunc's tails), so a holder can always re-establish it at
  iunlock; the stale-record freedom lives only inside a critical
  section, where the checked-out bundle's `dinode_at` may lag until the
  holder's iupdate retags it. iunlock's contract carries the resulting
  obligation: park only with the region record retagged to the parked
  `dn'`.
* The +0x72/+0x7c ghost moves are open/close PAIRS, not combined swaps
  (bio's split): what an evicted payload becomes is iget's argument,
  made between the two, not the definitional layer's.

### 13.4 What breaks and what stays

`ProofIdup` consumes `is_itable`/`itable_res` and is proven — the `ci`
map and the pool ride through its critical section untouched (it moves
only the ref word and `M`), so its repair is re-framing, not re-proving.
`InodeLock.inode_parked`/`inode_key`/`inode_locked` retire once
`ProofIlock` is re-proven; `inode_ok`, `inode_raw`, `valid_word` and the
two guard lemmas survive unchanged. The escrow file is ADDITIVE
(`IcacheEscrow.v`), so the tree stays green until the SpecIlock flip.

