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
Definition inode_ref k q dev inum    := iref_tok k q ∗ inode_ident k (DfracOwn q) dev inum.
```

Note it takes no inode *pointer*: `ientry` determines the address from the
slot and `ientry_inj` determines the slot from the address, so the two are
interchangeable. `inode_ref_agree` — two references to one entry see the
same `dev`/`inum` — falls out of fractional points-to agreement with no
`agree` ghost, exactly as in the ftable.

**This is the predicate `FileInv.inode_ref v q` (once literally `emp`) and
`ProcInv.cwd_ref v` were placeholders for.** Its signature does not match
theirs: it needs a gname (and reads the slot off the address). Two ways to
close that were recorded; **C6b took the second, and generalised it**: a
class carries the gname as a field, so the predicate's arity is unchanged
(the alternative — an explicit `γ` parameter — ripples into `FileInv`,
`ProcInv`, `SpecIput`, `SpecFileclose`, `kexit`).

What landed (see projects/fs-icache.md's C6b entry for the whole story):

* the reference layer moved BELOW the file table, into a new
  `IcacheRef.v` — `IrefSlots.v` imports `FileInv.v`, so `FileInv.v`
  cannot import `IcacheInv.v`. `IcacheInv.v`/`InodeInv.v` re-export it,
  so no unqualified name moved;
* the class is `IcacheRef.icfg` — THREE fields, not one: the
  count-authority gname, THE device (§13.11's single-device pin makes
  that honest) and the inode region's block count (which is what bounds
  an inum). A reference is `inode_held v := ∃ k q inum, ⌜v = ientry k⌝ ∗
  ⌜k < NINODE⌝ ∗ ⌜uint inum < 16·nib⌝ ∗ inode_ref k q icfg_dev inum`, and `icfg` is a superclass field of `fileG`, so nothing that
  merely mentions `proc_priv` learns of it. and because the gname is CANONICAL rather than
  threaded, the algebra takes no explicit `γ` at all: `itable_half`,
  `iref_tok`, `inode_ref`, `itable_inv` and `IcacheEscrow.ic_names` all
  read it off `icfg`, and a cone that ALSO names the cache as an
  `ic_names` needs no `your-γ = my-γ` coherence premise to use two of
  these predicates together. (This is the same choice `IrefSlots` and
  `FdSlots` made for their own supplies. It arrived with the kfork
  merge, which had made it independently as `IcacheInv.irefNameG`;
  folding that class into `icfg` is what the merge did with it.)
  `IcacheRef.icfg_alloc` mints one, and `IcacheBoot.icache_boot` takes
  the authority `own icfg_iref (● ∅)` as a premise rather than allocating
  it — the ambient `icfg` the file table is stated over is the one the
  boot has to be about;
* `ProcInv.cwd_ref` is `inode_held` under a null test (`emp` at
  `p->cwd = 0`); `FileInv`'s payload is `inode_pay γx v q := cinv fileipN
  γx (inode_held v) ∗ cinv_own γx q`, because **`inode_held` does not
  split fractionally** — the fragment's count column is `1%positive`, so
  two shares are two references — and `file_payload_split` is a genuine
  ⊣⊢. The cancellable invariant is what makes fraction one, and only
  fraction one, produce the whole reference for `iput`.

**`FileInv.inode_ref v q`, the file layer's old `emp` placeholder, is
gone**: an FD_INODE file's payload is `inode_pay`, above, and `SpecIput`
takes the real reference. (The kfork line's `InodeRef.iref_at` /
`iref_shr_at` were a second spelling of the same idea over a `natR`
algebra with count-0 shares; `InodeRef.v` survives the merge as a thin
re-export of `IcacheRef`/`IrefSlots`, and the share vocabulary is
deferred to the T5 cycle — see projects/reconcile-fork-icache.md.)

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

### 13.1e §13.1b's dev-cell exemption was WRONG: the arm ties BOTH
### identity cells, symmetrically (C3b attempt 1, 2026-08-09)

"The dev cell needs no arm tie — `dinode_at` is inum-keyed" (§13.1b)
dies on two consumers, found by the first C3b attempt (which correctly
stopped without editing):

* **ilock's `bread(ip->dev, …)`** (+0x48 `c.lw a0,0(s1)`): the checkout
  deposits the caller's WHOLE reference (§13.1d) — the only `i_dev`
  fraction ilock ever holds — so after checkout nothing can read the
  dev cell or name its value for `SpecBread`'s `dev = bv_dev V`
  premise. Borrowing via `ic_open_out` re-existentialises it.
* **iunlock's returned reference** would sit at an ∃-bound device, so
  no caller could ever ilock the same inode twice.

The fix is bio verbatim (`buf_parked` holds `b_dev ↦₄{½}`;
`escrow_swap_checkout` pins and hands the half out;
`escrow_swap_park` returns the reference with dev/inum pinned, only
`q` existential): `ic_parked` gains `i_dev (ientry k) ↦₄{½} dev`
(∃-bound), the checkout returns it at the CALLER's dev by agreement,
the park takes it back and returns `∃ q, inode_ref … k q dev inum`,
`ic_mid_arm` carries the dev cell too (either polarity — inum stays
the sole parked/mid discriminator), and the §13.1b budget becomes
SYMMETRIC: both identity cells at `½ escrow + q refs + (½−q) table`,
so `islot_rest_at k q dev inum = inode_ident k (DfracOwn (½−q)) dev
inum` and `islot_free_at = inode_ident k (DfracOwn ½) dev inum` —
simpler than the lopsided version. iget's `sw dev` at +0x6e then
needs the escrow's half joined in, as its own open/close pair (NOT a
widening of the MID window — dev is not payload-coupled).

### 13.5 `inode_ok` gains the size cap

`SpecReadi`'s `bv_unsigned (di_size dn) <= MAXFILE * BSIZE` premise
(the fact that keeps bmap off its out-of-range panic) is suppliable
today only because fileread knows `dn`; under SpecIlock v2 `dn` is an
OUTPUT, so the fact must ride the bundle: one new `inode_ok` conjunct.
Producers all discharge it — itrunc truncates to size 0, writei
already caps `off+n`, ilock's uncached arm inherits it from the pool
shape, and the C7 boot stocking owes it (add to C7's list). No other
contract consumes `inode_ok` (checked). `IcacheEscrow` inherits it
textually with no edit.

### 13.6 The bundle's dinode_at ties to the SAME dn (correction to the
### first C3b worklist block)

A separate `dn0` existential in ilock's postcondition makes fileread
UNPROVABLE: readi never flushes, so iunlock's PARKED-MEANS-FLUSHED
obligation would be undischargeable. The strong form holds on both
arms (cached: the parked arm IS at its own dn; uncached: the loads
reconstruct exactly the `dn0` that `ireg_read` pinned, so `dn = dn0`).
ilock's postcondition hands back `ic_loaded γfs γi cov logstart k inum
dn bm` VERBATIM (∃-bound dn, bm), which is literally iunlock's
precondition and exactly what `ic_swap_park` consumes. The lag-window
freedom of §13.1d applies only to holders that EDIT (writei/itrunc
between their edit and their iupdate), and those flush before
unlocking.

### 13.7 §13.2's dom-tie is WRONG: ci tracks IDENTIFIED slots, and the
### parked arm needs a VIRGIN shape (found working C6 forward, while C5
### was in flight)

`dom ci = dom M` ties ci to slots with ref > 0. Two fatal consequences:

* **Boot is unsatisfiable.** At `M = ∅` the tie forces `ci = ∅`, the
  pool formula then owns EVERY inum's bundle — and each of the fifty
  escrows' parked arms demands `ipool_shape inum` for its ∃-bound inum,
  i.e. a `dinode_at` the pool already holds. `dinode_at_excl` says no
  state exists.
* **iput's last close has nowhere to put the entry.** xv6 keeps a
  ref-0 entry CACHED (its identity and payload stay; only iget's scan
  treats it as recyclable — the scan's hit test requires `ref > 0`).
  Under the tie, deleting `M !! k` forces deleting `ci !! k`, the pool
  formula immediately claims the inum, and the bundle sitting in the
  escrow becomes a second, contradictory copy.

The fix, three parts:

1. `ic_ci_wf`'s first clause becomes **`dom M ⊆ dom ci`** (a live slot
   is identified; an identified slot may have ref 0). Injectivity and
   the range clause stand.
2. `islot2` gains the **(None, Some) arm** — "cached, ref 0": dev cell
   FULL, inum cell at ½, both pinned at `ci !! k`; no `iref_slots`
   parked. (Some, None) stays `False`.
3. The parked payload gains a **VIRGIN alternative**: `inode_raw` +
   valid word 0 + NO bundle and NO dinode_at — the boot state of all
   fifty entries, before any identity has ever been written. The
   escrow's parked arm is then satisfiable with the pool full and
   `ci = ∅`. A virgin slot's cells are junk (∃-bound); iget's recycle
   from a virgin slot evicts nothing; from an identified ref-0 slot it
   evicts the old bundle to the pool and re-keys `ci`. iput's last
   close deletes `M !! k` ONLY — `ci`, the cells, the escrow bundle
   all stay; the entry parks as "cached, ref 0" with zero ghost work
   outside `itable_inv`.

Note what stays emergent rather than stated: global
no-two-`dinode_at`-for-one-inum consistency is maintained by the moves
(each pool extraction is paired with a `ci` insert and vice versa), not
asserted as an invariant — the pool formula over `ci` plus the arms'
shapes is all the proofs need.

### 13.8 The virgin state is a FOURTH ARM with the dev cell FULL, the
### `icn_id` agreement ghost, and `islot_rest_at`'s None arm is False
### (C5's two confirmed blockers, both fixed here)

§13.7's clause 3 (virgin as a payload disjunct) is UNREFUTABLE by an
ilock winner: same arm, same cells as the ordinary unloaded payload,
and the only distinguishing ghost (`M !! k = None`) is authority-side.
Confirmed empirically (ProofIlock:2162). The fix — and where §13.7's
"dev cell FULL" actually belonged:

* **VIRGIN is a fourth arm of `ic_escrow_body`**, not a payload shape:
  `∃ dev inum w, i_dev ↦₄ dev (FULL — the virgin discriminator) ∗
  i_inum ↦₄{½} inum ∗ i_valid ↦₄ w ∗ inode_raw ∗ ic_mid`. `islot2`'s
  never-identified (None, None) arm keeps ONLY the inum half — the
  virgin arm's full dev IS the table's missing share. The
  (None, Some) identified-ref-0 arm is `islot_free_at` (both cells at
  ½) — §13.7's asymmetric budget there was unsatisfiable against
  `ic_parked`'s permanent dev half.
* Refuters, each from what its opener already holds: ilock's checkout
  and iput's `ic_open_auth_ref` — the opener's reference carries a dev
  fraction vs virgin's full cell; park/`ic_open_out` — full valid vs
  full valid; +0x7c — `ic_mid` exclusivity.
* **The residual** (a recycler at `ci !! k = None` cannot tell virgin
  from an anomalous identified-parked state) closes with a per-slot
  two-state agreement ghost: `icn_id : nat -> gname` in `ic_names`,
  `ghost_var (icn_id cn k) (1/2) (b : bool)` — the escrow-side half
  rides the arms (virgin: false; parked/out/mid: true), the table-side
  half rides `islot2` ((None,None): false; the two identified arms:
  true). The lock holder proves identification state by agreement; the
  recycle-from-virgin flips both halves (it holds both at that
  opening). Identification is monotone in the code but the ghost does
  not need to know that.

And independently (C5's blocker B): **`islot_rest_at`'s `(1/2 − q) =
None` arm becomes `False`**, not `emp`. At `emp`, the state `qt = ½`
(all retained identity gone) is permitted though unreachable, and the
hit arm's mint — a positive identity fraction out of the retained
share — is unprovable there, as is any plain read of the identity
cells under the lock. With `False` the positivity is resource-carried
and re-established automatically at every split; `iref_alloc_step`'s
mint at ¼ (the worklist's choice) respects it, and IcacheInv's header
comment "(0, ½]" must be corrected to "(0, ½)".

### 13.9 §13.7's dom-⊆ was ALSO wrong: a non-live slot holds no payload,
### and iput's last close does the eviction (C5's blocker C)

xv6's scan hit-test requires `ref > 0`, and the recycle takes the FIRST
ref-0 slot — never consulting a ref-0 slot's identity. So under `dom M
⊆ dom ci` the state {slot 0: ref-0 cached B, recycle B into slot 1} is
reachable, ci-injectivity is FALSE, and two escrow arms would hold
inum B's bundle against `dinode_at_excl`. Confirmed by trace (C5's
report). The fix — enabled by §13.8's virgin arm, which removed §13.7's
boot motivation:

* `ic_ci_wf` REVERTS to `dom ci = dom M`. `islot2`'s (None, Some) arm
  dies as unreachable; `ic_open_parked_free`/`_dev` die.
* **iput's last close moves the parked bundle back to the pool and
  re-forms the arm as the EMPTY shape** — the mirror of the recycle's
  ghost flip, all lock-internal: the closer (REF-1, under the lock)
  holds table+own identity = ½ each cell; the arm's halves complete
  them; the empty arm takes dev FULL + inum ½ + ghost false; ci and M
  delete together; the pool insert is fresh (inum ∈ ci pre-delete).
  The EVICTION ARGUMENT (loaded shape → allocated pool shape, via
  PARKED-MEANS-FLUSHED §13.1d) is iput's, where the flush semantics
  actually hold — iget evicts NOTHING, ever.
* iget's recycle collapses to ONE variant (always from the empty arm),
  selected with no case split: the scan's empty-slot invariant `M !! j
  = None` gives `ci !! j = None` under the restored tie.
* RENAME virgin→EMPTY (`ic_empty_arm`), `ic_id` reads "live / has a
  payload", not "was ever identified" — identification is no longer
  monotone (a last close un-identifies), and the ghost + all four
  refuters are unchanged by the rename.
* The scan's live-slot invariant (∀ scanned live slot, identity ≠
  (dev, inum)) now IS `inum ∉ ci_inums` at the sentinel — exactly
  `ipool_acc`'s premise.

C6's SpecIput inherits: the last-close arm's postcondition is pure
(the reference is consumed, nothing comes back); the eviction is
internal. `K_iget` tightens to 16 (6-slot frame + the lock pair's 10)
while nothing consumes it.

### 13.10 The agreement ghost carries the IDENTITY, not just liveness
### (C5b's blocker: the recycle's values fall off the full cells)

A cell a recycler stores is ∃-bound in the arm it closes into, and
both discriminators (EMPTY's full dev, MID's full inum) forbid the
recycler a retainable fraction — so `dev` is unrecoverable across
[+0x6e, +0x72) and `inum` across [+0x72, +0x7c), and neither the
postcondition's `inode_ref … dev inum` nor the `ci`/pool rebuild can
name its values. bio dodges this only because its full mid-cell pins
to a VIEW CONSTANT (one device) with the other cell retainable at ½;
the icache has two per-call values and one retainable half, so one
always falls off. The fix (C5b's, adopted):

    ic_id cn k q (v : bool)  ⟶  ic_id cn k q (v : bool, dev inum : mword 32)

coupled to the arm's cells in all four arms and to `ci !! k` in
`islot2`'s live arm / to the cells in `islot_empty` (whose bare ∃inum
now ties to the tuple, and whose dev — which has no table cell — is
pinned by the ghost alone). The table half, held continuously by the
lock-holding recycler, pins EMPTY's full dev; the half kept across the
MID window pins MID's full inum; the +0x6e and +0x72 openings update
both halves (in hand at exactly those two points, as §13.8 argued for
the flip). Exported swap/open lemma SIGNATURES are unchanged;
ProofIdup frames the ghost through at its `ci !! k` values. The
`icacheG` class field widens to `ghost_varG Σ (bool * mword 32 *
mword 32)`.

Also from C5b's trace: +0x20/+0x76 are compressed `c.li`
(`wp_cli_s_sconf`, not the base-form `wp_li4_s_sconf`), and the three
recycle stores need AU store leaves against `icEscN` (a local
`wp_sw_au` restatement at `Em := ⊤ ∖ ↑minstretN ∖ ↑icEscN`) — the
cells live in an `inv`, not in the lock.

### 13.11 The table is SINGLE-DEVICE, said out loud (C5b's third gap —
### and §10.2's prophecy landing)

The scan's strongest invariant is pair-shaped (xv6's hit test
short-circuits on the device compare without loading the inum), but
`ipool_acc`'s membership premise is INUM-keyed — and a live slot
caching the same inum on a DIFFERENT device satisfies the former while
refuting the latter (and would break ci-injectivity and
`dinode_at_excl` besides). §10.2 recorded exactly this hazard when
borrowing bio's device pin ("breaks the moment entries are keyed by
(dev, inum) across devices... invisible until it fails"). The fix is
bio's, one token wide: `ic_ci_wf M ci nib dv` gains
`∀ k p, ci !! k = Some p -> fst p = dv`; `itable_res2`/`is_itable2`
gain a trailing `dv`; `SpecIget`/`SpecIdup` instantiate it at the
`dev` binder they already carry (no new premise — "no constraint on
dev" becomes "the table is this device's"). The scan's pair invariant
then collapses to `ii ≠ inum` at every live slot, membership follows,
and the recycle re-establishes the device clause by construction.
`SpecIlock`/`SpecIunlock` are untouched (they take `ic_escrow` and
`bio_ctx`, not the table). A future multi-device xv6 re-keys
`dinode_at` by (dev, inum) — recorded, not owed.

### 13.12 §5(a) is wrong at iput's call site: the nested acquiresleep's
### block IS a safety obligation — and §6(ii)'s conjunct comes due

**(a)** iput calls `acquiresleep(&ip->lock)` at +0x50 HOLDING
itable.lock (the only nested acquiresleep in the kernel; fs.c:348).
The sleep path runs sched's `noff != 1` check, i.e. blocking is
reached only through `panic("sched locks")` — a SAFETY arm, not the
liveness §5(a) waved away. xv6's "won't block (or deadlock)" comment
is asserting exactly this. The adopted route (C6's, Route B): take
the panic. Three lemmas in the sched/sleep stack, no definitional
change anywhere: (1) sched entered at noff ≥ 2 diverges (ProofSched's
walk already reads the check; this variant takes the branch it
refutes); (2) sleep at noff ≥ 2 diverges; (3)
`wp_acquiresleep_nested_sconf` at `cpu_own (S n)`: returns holding the
lock on the free branch (no park, so no `cpu_own 0`), diverges on the
locked branch. iput's REF-1 makes the divergence unreachable in
practice; we do not prove that, we permit it — the ilock/iget live
panics are the precedent. Route A (prove the lock free) was examined
and rejected: `sl_res`'s locked arm is a bare pure with no resource to
refute by, and giving it one reparameterizes `is_sleeplock` for every
user including bio.

**(b)** itrunc's `length (data i) = BSIZE` premise is unstateable by
iput — `data` is ∃-bound in the checked-out payload. §6(ii)'s designed
home lands: `inode_sized data` becomes an `inode_ok` conjunct
(IcacheInv shipped `inode_sized_zero`/`_insert`/`_of_alloc` for
exactly this in C1). iput then derives itrunc's premise from the
bundle's own `inode_ok` — NO contract changes anywhere; discharges at
the `inode_ok` producers (ProofIlock's uncached arm inherits from the
pool shape, ProofItrunc by `inode_sized_zero`, ProofWritei by
`inode_sized_insert`; C7's stocking owes it like the §13.5 cap). The
`fsblock`-fold alternative stays deferred.

### 13.13 iput needs a FIFTH arm: the HELD window (the valid-polarity
### observation cannot cross acquiresleep otherwise)

iput reads `valid == 1` at +0x3c through the read-only authority-side
open (`ic_open_auth_ref` re-seals with `v` ∃-bound), and its checkout
happens 20 bytes and one `acquiresleep` later — with a FRESH `v` and
nothing tying it to the one observed. The invariant genuinely permits
the flip (the escrow is a persistent `inv`; a hypothetical opener could
convert loaded→unloaded within one step), and no ghost can pin `v`
from the itable side: `valid`'s writers (ilock) hold no itable
credential, so a table-anchored half has no partner. Every alternative
was enumerated and dies (C6a-final's route table — widen `ic_id`,
close at MID/OUT/EMPTY, retain `dinode_at` fractions, handle
`v = false` in the truncate arm which is UNSOUND since the raw cells
are untied to the record).

The fix is the MID arm's own idea, replayed for iput: **`ic_held`, an
authority-side window arm** — the cells stay in the arm, the PAYLOAD at
its concrete polarity leaves with the holder (so nothing is re-bound
and nothing needs stability). LANDED, and two details the compile
settled differently from this note's first draft:

* **NO NEW TOKEN.** A fresh `ic_hld` family would have had to sit in
  the four other arms, which means in `ic_mid_arm` — and that is
  ProofIget's inline arm construction at +0x72 and its destructuring at
  +0x7c, so it would have broken the "no proof file moves" rule for a
  refutation already available. `ic_open_held`'s credential is **REF-1
  plus the payload**: `iref_tok_two_lookup` kills OUT (and makes the
  credential exclusive — no second thread holds a reference at all),
  the carried payload's `dinode_at` kills PARKED and MID by
  `dinode_at_excl` (the inum pinned first by `ic_id_agree`), and the
  table's `ic_id` half at `true` kills EMPTY. REF-1 rather than
  `ic_tok` is FORCED: iput must also UNDO the window at +0x44, where
  `ip->nlink ≠ 0` and no `acquiresleep` has run.
* **The valid cell is SPLIT ½/½,** not left whole in the arm. The undo
  closes back at PARKED and needs the cell AT THE PAYLOAD'S POLARITY;
  a cell the arm owned whole hands its value back existentially bound —
  §13.13's own failure one level down. The holder's half pins it by
  `word4_pointsto_agree`, and a half still dies to `ic_word4_excl`
  against the FULL cell the parker and `ic_open_out` carry.

So the arm is `dev ↦{½} ∗ inum ↦ (FULL, the discriminator) ∗
valid ↦{½} ∗ ic_mid ∗ ic_id{½} true`, entered at +0x3c off
`ic_open_auth_ref` and closed with `ic_close_held`, exited by
`ic_open_held` (then `ic_close_out` at the checkout, or a rebuilt
`ic_parked` at the nlink undo), where the full inum cell re-splits into
arm-½ + the deposited reference's q + the table's (½−q). Refutations
for the new disjunct are one existing line each: checkout/auth_ref by
`ic_word4_excl` against the full inum cell, park/out by the same
against the valid half, mid by `ic_mid` exclusivity, empty by
`ic_id_agree`. No exported signature changes, no `ic_names` change, no
C7 obligation; ProofIget/ProofIlock/ProofIunlock rebuilt untouched
(verified: 0 errors, 913 .vo, none of the three recompiled by hand).

Also settled by the same trace: the `iref_slot` give-back needs no new
IrefSlots lemma (Pos2Nat.inj_succ + iref_slots_split on the non-last
arm; `iref_slot` IS `iref_slots 1` definitionally on the last), and
the truncate arm's park shape is exactly `ipool_shape`'s free disjunct
after iupdate retags to the type-0 record — `ic_swap_park` at
`v = false` consumes it with `inode_raw` rebuilt from the truncated
cells.

### 13.4 What breaks and what stays

`ProofIdup` consumes `is_itable`/`itable_res` and is proven — the `ci`
map and the pool ride through its critical section untouched (it moves
only the ref word and `M`), so its repair is re-framing, not re-proving.
`InodeLock.inode_parked`/`inode_key`/`inode_locked` retire once
`ProofIlock` is re-proven; `inode_ok`, `inode_raw`, `valid_word` and the
two guard lemmas survive unchanged. The escrow file is ADDITIVE
(`IcacheEscrow.v`), so the tree stays green until the SpecIlock flip.


---

## 14. T5's GATE: the whole-outstanding-share witness (DESIGN IN
## PROGRESS, 2026-08-10)

Under `natR` count-0 shares, `iref_lookup` loses `n = 1 -> q = qt`, and
`ProofIput.v`'s two eviction derivations (:924, :1387) stand exactly on
it. The surviving direction (`q = qt -> n = 1`) is only usable if
`q = qt` is SUPPLIED — and no resource on either line supplies it. The
counterexample that kills the naive plans: a second reference to the
same inode (p->cwd beside an open file) means iput's caller cannot know
it is last, so "the caller gathered its shares" is not "no shares
exist". The premise `∃ q, iref_at ip q` (origin's step-3 target) is
insufficient; so is any caller-local bookkeeping alone.

### 14.1 The load-bearing observation: every share use is BRACKET-SHAPED

Both consumers that exist or are designed carve a share and return it
WITHIN one contract's execution, while the parent reference is held or
parked somewhere that survives the bracket:

- kfork (d69678b3): `inode_ref_shed` before the `ld`, upgraded back to
  a reference at idup's return — the share never crosses kfork's
  boundary.
- C8's future ilock/fileread share: carved from the file payload's
  parked reference at fileread's entry, returned before its exit.
- fileclose's gather (origin's design): by construction complete at
  fraction 1, before iput.

If shares NEVER cross a contract boundary — a discipline the tree can
enforce by simply never stating a share in a Spec's pre/postcondition,
except as a within-call bracket pair — then at every iput call, shares
outstanding belong to brackets of OTHER live references' holders. At
`ip->ref == 1` the caller's reference is the only live one, so no
bracket is open, so share mass is zero. The DISCIPLINE makes the
invariant true; the question is its RESOURCE encoding, because iput's
proof needs it inside the escrow/authority opening, not as prose.

### 14.2 Candidate encodings, with their failure modes

(a) **Share column in the authority**: value becomes
`(Qp × nat-refs × nat-shares)`; `n_shares` moves at carve/gather; iput
at `(qt, 1, 0)` derives `q = qt` (sum over one fragment). FAILS as
stated: `n_shares = 0` at the eviction must come from somewhere, and
the caller cannot attest an authority-side count it never sees; the
eviction branch at `n_shares > 0` would be unprovable-not-refutable.
Needs (c)'s tie to become dischargeable.

(b) **Per-slot share-free token** (`ishr_zero k`, taken by the first
carver, returned by the last gather): a counter problem disguised as a
token — multiple concurrent carvers from different references need a
counted pool, at which point it IS (a)'s column as a ledger. Same
discharge problem.

(c) **Bracket receipts tied to the REFERENCE (the promising one)**:
carving from a reference yields `share ∗ receipt`, and the receipt is
lodged where the PARENT reference's own transfer is blocked until
gather — concretely, redefine

    inode_ref' k q dev inum n_open :=
      iref_tok k (q, 1) ∗ inode_ident q ∗ shed_ledger k n_open

with `SpecIput` (and every contract that consumes a reference) taking
`inode_ref' … 0` — a reference with NO open brackets. `shed_ledger` is
per-reference ghost state... and references are anonymous, so the
ledger must ride the fragment itself. THE SHAPE THAT WORKS WITHOUT NEW
GHOSTS: carve by SPLITTING THE FRACTION — `(q,1) ⇝ (q−s,1) ∗ (s,0)` —
so the parent's own recorded fraction DROPS while its share is out,
and gather restores it. Then "no open brackets" is `⌜the reference is
at its full allotted fraction⌝ — which only the holder knows, and
which is EXACTLY the accounting origin's `fp_iq` constant makes
arithmetical for file payloads (allotment = q·fp_iq) and trivial for
cwd (allotment = the mint fraction, never carved across a boundary).
The remaining gap: at ip->ref == 1, `qt = q_caller + Σ shares`, and
shares from OTHER references are impossible only by the bracket
discipline — whose resource form is precisely that a contract-crossing
reference is at full allotment, so a live-but-bracketless second
reference contributes no shares. This closes IF every share's
(s,0) fragment is unreachable outside brackets — i.e. if no Spec
mentions a bare share. That is checkable by grep and enforceable by
convention, but it is a META-theorem about the spec set, not a
resource; the honest formal statement is per-slot:

    ishr_mass k = qt − Σ (live references' fractions)

held as an authority-side invariant clause `ishr_mass k = 0 ∨ (some
reference's bracket is open)` — and "bracket open" IS representable:
the bracket pair mints an exclusive `bracket_tok k` at carve and
consumes it at gather, with the invariant clause `n_shares k > 0 →
bracket_tok k is OUT`. iput's eviction holds the lock; if it can also
hold/witness `bracket_tok k` IN (i.e., in the invariant), then
n_shares = 0 follows. Multiple concurrent brackets per slot: the tok
becomes a count — but now it is a count the INVARIANT owns and the
BRACKETS borrow, so the discharge is: iput at ref==1 opens the
invariant and finds the bracket count intact BECAUSE any open bracket
belongs to a live reference's holder, and REF-1 says the caller is the
only one, and the caller (per its contract, `inode_ref'` at zero
brackets) has none open. THAT is the witness: REF-1 + the caller's
zero-bracket reference + the invariant clause tying open brackets to
live references.

### 14.3 What remains to nail down (next design session)

- The invariant clause's exact form: "every open bracket is tagged
  with a live reference" needs the tag — a bracket_tok minted AGAINST
  a specific fragment, which anonymous fragments complicate. Candidate:
  key brackets by SLOT and count them in the authority's third column,
  with the CLAUSE `n_shares k ≤ Σ over fragments of (their open
  brackets)` — made inductive by carve/gather moving both sides.
- Whether `inode_ref'`'s bracket count can stay OUT of the fragment
  (keeping origin's `(Qp × nat)` value) by putting the per-slot bracket
  count in `islot2`/the escrow instead — the arms already carry per-slot
  state, and iput's eviction already opens both.
- The retype inventory is already scoped (reconcile round 1/2 notes):
  origin's b4902e13 is the template; escrow + ProofIget retype
  mechanically; ProofIdup/SpecIdup/ProofKforkB4 take origin's versions
  ported to dev/icfg_dev; ProofIput's two sites rework on the witness.

### 14.4 THE OPEN RULING (pending, 2026-08-10): natR convergence vs the
### separate share ghost

Two viable shapes for T5, DELIBERATELY LEFT UNDECIDED pending
coordination between the two working lines:

- **Path A — adopt origin's natR** (`prodR fracR natR`, count-0 shares
  in the same map): converges the algebra with the kfork line; takes
  their idup/ProofKforkB4 improvements as written; COSTS the full
  retype (IcacheRef/IcacheInv/escrow/ProofIget — mechanical, their
  b4902e13 is the template) PLUS reworking ProofIput's two REF-1 sites
  against §14.2(c)'s bracket machinery — and the bracket count must be
  invariant-side, because natR fragment splits are free (⋅-valid) and
  CANNOT be forced through a carve lemma: the ledger would bound
  nothing it doesn't own.
- **Path B — keep positiveR, add a SEPARATE authority-guarded share
  ghost** (per-slot share-mass + bracket count inside itable_inv;
  carve/gather/upgrade lemmas are the only mints because the ghost is
  auth'd there): REF-1 and therefore ProofIput/ProofIget/the escrow
  survive UNTOUCHED; purely additive; the witness clause
  ("share-mass > 0 → an open bracket against a live reference") is
  owned by the invariant rather than assumed as discipline. COSTS:
  origin's line must port its idup-over-shares/kfork-B4 onto it (the
  upgrade step maps directly: ghost-mass → fragment under the lock),
  and the two lines must agree or the next pull re-collides on the
  algebra a third time.

Either path then reaches C8 (SpecIlock/SpecFileread over shares) with
the same bracket vocabulary. The trade is: A pays in re-proof and a
weaker (discipline-shaped) ledger; B pays in cross-line coordination.

### 14.5 Path A sharpened to an impossibility: under natR, carving a
### share is a NON-EVENT (2026-08-10, exploring "how hard is A")

> **Read §14.6 first.** Its RECOMMENDATION paragraph below still speaks of
> a "ledger" and of `fp_iq` as "the ledger's proportional accounting".
> §14.6 removes the ledger entirely — iput needs no witness — so that
> phrase names a structure the plan no longer has. `fp_iq` survives, but
> for the FILE layer's own reason (the payload's shares need definite
> proportional masses or the last closer's gather cannot restore the
> parent reference to canonical pairing), not for iput's.

The decisive algebraic fact: at `prodR fracR natR`,

    (q, 1) = (q − s, 1) ⋅ (s, 0)

is ⋅-DECOMPOSITION, not an update. Owning a reference definitionally IS
owning a smaller reference beside a share; nothing fires, no invariant
opens, no ghost moves. So no ledger — invariant-side, authority-side,
or otherwise — can count shares, because a ledger counts EVENTS and
share-creation is not one. Every witness clause of §14.2/§14.3 is
therefore only ASSUMABLE under natR, never OWNABLE, and iput's eviction
needs it owned. Under `positiveR` the same decomposition does not exist
(no zero in the count), so carving REQUIRES a real update against some
other ghost — which is precisely the event Path B's auth-guarded ledger
counts. The algebra choice is not a cost trade-off: it decides whether
"share" is a countable event.

Consequently Plan A has exactly three completions, none of which is
"adopt natR and rework iput":
1. iput stays unprovable (regression; rejected);
2. A+B — natR retype PLUS Path B's separate share ghost, with the
   count-0 elements never used by any contract: sound, but the retype
   buys only textual compatibility with origin's two share commits,
   and the unused free-split capability is a standing hazard (any
   future proof that uses it silently divorces the ledger from the
   truth it is supposed to bound);
3. a third RA where share-creation is auth-mediated inside the same
   map — a redesign, i.e. Path B in different clothes.

RECOMMENDATION SHARPENED: the A-vs-B question as posed in §14.4
dissolves — B (or an A+B hybrid where natR is adopted knowingly as
compatibility-only) are the only sound endpoints. What origin's line
loses under B: the two share commits' proofs port (idup's share form
becomes a ledger-carve + upgrade against the new ghost — same shape,
one extra fupd) and fp_iq survives verbatim as the ledger's
proportional accounting. What B must add that A never had to state:
nothing — the ledger was needed either way; B just makes it sound.

### 14.6 Plan B simplifies: iput needs NO witness at all — mass
### conservation IS the witness (2026-08-10, sizing B)

Keep `inode_ref k q dev inum := iref_tok k q ∗ inode_ident k q`
CANONICALLY PAIRED (tok fraction = ident fraction — what every
contract already states). Then:
- a share = ident fraction carved from a reference, so its parent's
  holder is short on ident and CANNOT meet any contract that spends
  the reference — shares cannot outlive their parent;
- at REF-1 the caller's canonical q + the table's (½−q) + the escrow
  arm's ½ sum to the whole ident mass, so no share exists ANYWHERE, as
  a corollary of `word4` fraction arithmetic, not a premise. The
  eviction assembles full cells exactly as today. ProofIput:924/:1387
  are UNTOUCHED (positiveR's REF-1 intact).
- Free ident splits without the carve lemma are harmless: they make a
  pair of fractions the holder keeps, not a share (no liveness), and
  the holder's own contract obligations force the mass back.

What the new ghost is actually FOR — not iput, but the SHARE's own
liveness: a share-holder must refute ilock's `ref < 1` panic without a
tok. One per-slot fractional liveness ghost (`γlive`, auth in
`itable_body` beside the ref words, clause tying its support to
`dom M`), minted/consumed ONLY by the carve/gather lemmas (the
auth-guarded EVENT positiveR forces, per §14.5), retired whole by the
last close inside the same invariant opening. So:
`inode_shr k s dev inum := inode_ident k s ∗ live_frac k s`.

C8's recorded escrow blocker ALSO dissolves: a share-holding ilock
deposits `inode_shr` in a share-shaped OUT alternative, and iput's
authority-side opener refutes that arm at REF-1 by the same ident-mass
overflow (caller q + table (½−q) + arm's ½-resident + the share's s
exceeds 1). No tok needed in the arm for that refutation.

SIZING (in this project's demonstrated agent-run currency):
- B1: γlive + carve/gather/upgrade + itable_body's extra conjunct
  re-framed through the six store-AU lemmas + iput's last close
  retiring the pool — one C3a-scale run.
- B2: C8 contracts (SpecIlock/SpecIunlock/SpecFileread over
  `inode_shr`) + the share-shaped OUT arm + ProofIlock's re-proof +
  fileread/iunlock repairs — one to two C3b/c-scale runs (the bulk).
- B3: port origin's two share commits (idup = carve+upgrade,
  ProofKforkB4's shorter block, fp_iq's payload arm) — one run,
  partly deferrable.
Total ≈ 3–4 agent runs + one design pass: comparable to cycle C3
alone, and far below §14.4's estimate, which budgeted ledger machinery
for iput that B turns out not to need.

### 14.7 B1's three corrections to §14.6 (landed, green)

1. **Liveness rides INSIDE `iref_tok`** (`iref_tok k q := iref_frag k q
   ∗ live_frac k q`; three equal fractions in `inode_ref`), not in a
   free-standing pool: a support clause counts only what the invariant
   owns, and the shares are exactly what it does not — the retirement
   at last close works ONLY by conservation, which needs the closer's
   tok to carry pool mass proportional to qt. Every consumer statement
   survives because iref_tok is opaque to all of them.
2. **Carve/gather are `⊣⊢`, not events.** §14.5's demand for
   auth-guarded events was aimed at the LEDGER; §14.6's conservation
   argument deleted the ledger, and with it the need: `inode_ref_carve`
   is a pure RA split (no fupd, no mask), which B2's fileread/ilock
   exploit directly. The free slot's whole live unit in the invariant
   is what makes a share imply `M !! k = Some _` (`iref_live_load_au`).
3. **No share→reference upgrade exists under positiveR** — the identity
   budget cannot line up (the share's s is already the hole in its
   parent's slice). idup-over-shares instead mints from the table's
   retained share (iget's hit shape, `iref_upgrade_store_au` =
   incr-with-the-share-carried) and RETURNS the share beside the new
   reference; kfork's parent gathers it back. B3 adjusts accordingly.

### 14.8 B2 WAS BLOCKED (repaired by §14.9): the OUT arm cannot carry two
### deposit shapes, because the two parkers are resource-indistinguishable

B2's plan is "`ic_out` gains a share-shaped alternative beside the
reference-shaped one". Worked through against the code, that does not
close, and the obstruction is not local to any one lemma. Two findings,
the first repairable, the second not without new ghost state.

**(a) §14.6's REF-1 refutation is stated over resources iput does not
hold — but the task's LIVE-mass replacement works, at the cost of making
`ic_open_auth_ref` a fupd.** §14.6 says the share arm is refuted at REF-1
by "caller q + table (½−q) + arm's ½-resident + the share's s exceeds 1".
The `½-resident` is wrong: in the OUT state the parked arm's ½ of `i_dev`
/ `i_inum` is in the CHECKED-OUT THREAD's hand (SpecIlock's postcondition
hands it out; SpecIunlock consumes it), not in the arm. So the arm holds
only the share's `s` of each cell, iput holds `q + (½−q) = ½`, and
`½ + s ≤ 1`: no overflow, no refutation.

The LIVE-mass form does work: at REF-1 the caller's `iref_tok k q` carries
`live_frac k q` with `q = qt` (both `ProofIput` call sites already
instantiate the lemma that way), the arm's share carries `live_frac k s`,
and `live_slot M k` carries `1 − qt`; the three sum past one. But
`live_slot` lives inside `itable_inv`, and `ic_open_auth_ref` is a pure
wand. It has to become

    Lemma ic_open_auth_ref ... (Eo : coPset) (M) (q qi) (dev inum) :
      ↑icacheN ⊆ Eo -> M !! k = Some (q, 1%positive) ->
      itable_inv -∗ ic_escrow_body ... -∗ itable_half M -∗
      iref_tok k q -∗ inode_ident k (DfracOwn qi) dev inum -∗
      |={Eo}=> (... as today ...)

i.e. fupd + `itable_inv` + the tok's fraction FORCED to be the map's `qt`.
Checked at both call sites: `ProofIput:857` is inside `fupd_wp`/`iInv
"Hesc"` at mask `⊤ ∖ ↑icEscN`, `ProofIput:1368` inside the `lw` AU at
`⊤ ∖ ↑minstretN ∖ ↑icEscN`; `↑icacheN` is free in both, and both already
pass `q = qt = qi`. So (a) costs two `iDestruct`→`iMod` edits and a
`solve_ndisj`. Repairable.

**(b) THE BLOCKER: `ic_swap_park` cannot be made deterministic.** With two
OUT alternatives, every parker faces both, and the two parkers hold
IDENTICAL resources:

- iunlock parks with `½ i_dev`, `½ i_inum`, the FULL `i_valid`, the
  payload, `sleeplocked gisl`, and no reference (§13.1d's deposit);
- iput's window exit parks with exactly the same four (ProofIput:1979:
  `Hidv`, `Hinh`, `Hvld`, `Hpayf`), having released `itable.lock` at
  +0x5c — so it holds NO `itable_half`, NO `islot_rest`, NO
  `iref_tok`, NO `live_frac`, and no `ic_tok`/`ic_mid` (both deposited).

Inventory of every candidate discriminator, all dead:
- `ic_tok` must be in BOTH OUT arms (it is the sleeplock's sealed resource
  and the arm is what records "somebody is inside"; drop it from either arm
  and `ic_swap_checkout` loses its refutation of that arm);
- `ic_mid` must be in both (drop it from either and `ic_open_mid`, iget's
  re-open at +0x7c, loses its refutation);
- `ic_id`'s two halves are the arm's and `islot2`'s — a parker holds
  neither;
- cell fractions: the arm holds `q` (reference) or `s` (share) of each
  identity cell, both `≤ ½`, against the parker's `½`; never past 1;
- `dinode_at` is in the parker's payload and in NEITHER arm;
- `itable_inv` is persistent and available, but the pool gives only
  `s ≤ qt`, and the parker knows no `qt`.

So a share-parker cannot refute the reference arm, and a reference-parker
cannot refute the share arm. `ic_swap_park` can only return the
DISJUNCTION — and iput cannot absorb it: a share has no count fragment, so
its `ip->ref--` (`iref_close_store_au`, needing `iref_tok k q'` with the
liveness and the count fragment at the SAME fraction) is unprovable on the
share branch.

**And iput cannot switch to depositing a share either**, which is what
would make OUT uniform and delete the problem. Keeping `iref_frag k q` and
depositing `inode_shr k q` fails at the gather: `ic_swap_park` returns the
arm's share at an EXISTENTIAL fraction `s`, and re-pairing it with the
retained fragment needs `s = q`. Only `s ≤ q` is derivable (identity: arm
½ + table (½−q) + iput s ≤ 1; liveness: pool (1−q) + s ≤ 1). Equality is
exactly the un-ownable conservation fact §14.6 was built to avoid needing.
Note the fraction being existential is otherwise harmless — `ic_swap_park`
is existential in it TODAY and `fileread_fs_out` already returns
`∃ q'` — the problem is the KIND, not the fraction.

Three requirements, pairwise fine and jointly impossible with the present
ghost state:
  (R1) the share must sit IN the arm, or iput's REF-1 opener cannot see
       its mass (this is what forces (a)'s shape too);
  (R2) each parker must recover its own deposit;
  (R3) the two deposits differ in kind, because §14.7(3) says a share
       cannot become a reference and the gather above cannot re-form one.

**THE MINIMAL REPAIR (recommended): turn `ic_tok` into a deposit
descriptor.** `ic_tok cn k` is today `lock_tok_excl (icn_esc cn k)`, i.e.
`lock_frag (icn_esc cn k) None`. Make it a `ghost_var` instead:

    Inductive ic_dep := DepNone | DepRef (q : Qp) (dev inum : mword 32)
                                 | DepShr (s : Qp) (dev inum : mword 32).
    ic_tok cn k     := ghost_var (icn_esc cn k) 1 DepNone.
    ic_deposit cn k d := ghost_var (icn_esc cn k) (1/2) d.

`ic_tok` keeps its role verbatim — it is exclusive at fraction 1, so
`ic_tok_exclusive` survives, and `is_sleeplock ... (ic_tok cn k)` needs no
change. At checkout the winner updates the whole var to its deposit and
splits: ½ into the arm, ½ kept. At the park the two halves meet,
`ghost_var_agree` PINS the shape, the fraction and the identity, they
rejoin, and the var goes back to `DepNone` for releasesleep. Consequences:
- `ic_swap_checkout`'s refutation of both OUT arms becomes ghost_var
  1-vs-½ invalidity (same one line);
- both parkers select their arm by agreement, deterministically;
- BOTH postcondition existentials disappear — `ic_swap_park` returns the
  deposit at its EXACT fraction, so SpecIunlock's `∃ q` and
  `fileread_fs_out`'s `∃ q'` can be tightened (B3's `fp_iq` accounting
  wants exactly this);
- `ic_open_out` can select its arm the same way, or simply return the
  common `live_frac k _` both arms carry, which is all
  `iref_live_load_au` needs.
- (a)'s fupd is STILL required: at REF-1 iput holds no descriptor half.

COST, honestly: `ic_tok`'s definition, `ic_tok_fun_alloc` /
`ic_names_alloc` (the esc family becomes a `ghost_var` family, `ic_id`'s
allocator is the template), `IcacheBoot`, all five arms, all eleven escrow
swap/open lemmas, `ProofIput` (three sites), `ProofIlock`, `ProofIunlock`.
That is a token-layer rework of the escrow, not "one line per arm" — call
it its own stage (B2a) ahead of the contract work (B2b).

Rejected alternatives, for the record: (i) asymmetric cell budgets, so that
each arm holds a `½`-resident the OTHER parker's `½` overflows — it does
close the two refutations, but it then denies each parker a fraction of the
cell it must PIN (`ic_parked` ties the ½ `i_inum` to the payload's inum),
and patching that back needs an epsilon-sliver whose side condition
(`½ < r + q`) has to be written into the arm; a house of cards.
(ii) `ic_swap_park` returning the disjunction and pushing the case split to
the callers — dead at iput, as above. (iii) a fourth `ic_names` token
family — strictly worse than (b)'s repair: it needs a home in EVERY arm at
boot, whereas the descriptor reuses a gname that already exists and already
has exactly the right lifetime.

### 14.9 B2a/B2b LANDED (2026-08-11): §14.8's repair as built

§14.8's design went in unchanged — no correction, no alternative — so read
it as the WHY and this as the WHAT. Tree green (937 .vo); ilock, iunlock,
fileread, iget, idup, iput all still PROVEN; assumption sets unchanged.

**The descriptor.** `IcacheRef.ic_dep` (`DepNone | DepRef q dev inum |
DepShr s dev inum`) with `ghost_varG Σ ic_dep` as a fourth `icacheG` field.
`IcacheEscrow.ic_tok cn k := ghost_var (icn_esc cn k) 1 DepNone` and
`ic_deposit cn k d := ghost_var (icn_esc cn k) (1/2) d`. The OUT arm is
`∃ d dev inum, ic_deposit cn k d ∗ ic_dep_res k d dev inum ∗ ic_mid cn k ∗
ic_id cn k (1/2) true dev inum`, where `ic_dep_res` is `False` at `DepNone`,
`inode_ref` at `DepRef` and `inode_shr` at `DepShr`, each tying the
descriptor's own dev/inum to the arm's.

**What the shapes have in common is what every lemma actually uses**, and
that is the reason the rework stayed small. Two accessors carry the whole
generic part: `ic_dep_res_ident` (both shapes hold an identity FRACTION —
which is every checkout-side refutation's ammunition, so `ic_swap_checkout`
is ONE lemma generic in `d`, not one per kind) and `ic_dep_res_live` (both
hold a LIVENESS slice — which is all a lock-free `ip->ref` guard needs, so
`ic_open_out` borrows kind-independently and needs no descriptor half).

**The REF-1 refutation that replaces §14.6's.** `IcacheInv.
live_whole_share_absurd`: a holder whose `q` IS the map's `qt` carries the
slot's whole outstanding liveness, the invariant's arm is the exact
complement, so any further slice is over budget. The COUNT is a parameter
the lemma never reads — REF-1 is only how the caller comes to know
`q = qt`. This is what forces `ic_open_auth_ref` AND `ic_open_held` (§14.8
named only the first) to be fupds over `itable_inv`; all four ProofIput call
sites sit at masks where `↑icacheN` is free and already pass `q = qt`.

**The contracts.** SpecIlock v3 takes `inode_shr k s dev inum` wholly (its
one caller is ProofFileread) and its guard read goes through
`iref_live_load_au`; SpecIunlock v3 takes the bundle plus
`ic_deposit cn k (DepShr s dev inum)` and returns the share AT `s`.
SpecFileread v3's `frn_q` becomes `frn_s` and `fileread_fs_out` returns the
same share. Both postcondition existentials are gone, which is exactly what
B3's `fp_iq` gather needs: a gather must re-form the fraction that was
carved.

**The one cost §14.8 did not price:** the descriptor's other half TRAVELS
with the checked-out thread, so it appears in ilock's postcondition and
iunlock's precondition, `ProofIlock`'s `il_cont`/`il_epilogue`/`il_load`
gained `(cn, s)` plus one premise, and `ProofIput` threads it by hand from
+0x54 to +0x70. No statement in `ProofIput` moved; that stretch is one
proof and the spec applications there name their arguments.

`IcacheInv.iref_load_au` is now consumer-less (both guard reads went to the
liveness twin). Kept deliberately as the reference-side form.

### 14.10 B3 LANDED (2026-08-11): PLAN B IS COMPLETE — the payload's share,
### idup's mint, and the one thing a short parent cannot do

Tree green (937 `.vo`), coverage unchanged, assumption sets unchanged.
`projects/reconcile-fork-icache.md`'s "What B3 actually landed" is the WHAT;
this is the design half.

**§14.6's third shape, as built.** The FD_INODE payload is
`cinv fileipN γx (inode_held_short v Q) ∗ cinv_own γx q ∗
inode_shr_held v (q·Q)`, with `Q = fp_iq pn` a per-slot CONSTANT in
`FileInv.fpnames`. The share cannot be carved from the parked reference on
demand, because a `cinv`'s content is unreachable without cancelling it —
so it is carved once, at publication, and **the invariant parks the parent
SHORT**. That is sound for the reason `inode_ref_short` exists at all: a
short parent is unspendable, the cinv is its only holder, and the gather
that restores canonical pairing is the last closer's move, inside
`inode_pay_cancel`, before iput ever sees the reference. Conservation is
untouched — `1·Q` out, `Q` back.

The arm being PROPORTIONAL rather than existential is what makes
`file_payload_split` distributivity, and it is what makes B2b's retirement
of `fileread_fs_out`'s `∃ q'` pay off: a gather needs the fraction that was
carved, and now both ends name it.

**§14.7(3) at the call site.** idup takes the share, hands it back
UNTOUCHED, and mints the child's reference from the table's retained
`1/2 − qt` — iget's cache-hit arm, not an upgrade. The postcondition's
fraction is therefore existential (a slice of a `qt` no caller can name)
while the share's is the caller's own. Consequence at kfork: the parent's
cwd fraction stops halving on every `fork`, which the `natR` shape this was
ported from could not achieve either (there the parent kept a reference but
still split it).

**THE ONE THING THAT DID NOT PORT, and the general law behind it.** The
staged plan had kfork close the parent's `proc_priv` block BEFORE the idup
call, on the strength of "the reference never leaves". Under canonical
pairing it cannot: `ProcInv.cwd_ref` is `inode_held`, i.e. a CANONICAL
`inode_ref`, and a parent with a share out has `iref_frag` at `q+s` against
identity and liveness at `q`. Re-canonicalising it downwards would mean
SHRINKING the count fragment — handing back authority mass that §14.6's
conservation argument requires to come home — and no such lemma may exist.

State it as the law it is: **a carve is a BRACKET, and the bracket cannot
be escaped by re-forming a smaller reference; it can only be closed by the
gather.** §14.1 observed that every share use is bracket-shaped; §14.6 made
the bracket a resource; this is the price, and it is the same fact that
makes shares unable to outlive their parent. Any future caller that wants
to lend a share across a call must keep the parent's block OPEN across it.

## 15. THE DIRECTORY-WF QUESTION (N4's gate, 2026-08-11): what survives
## a disk-full dirlink, and where each surviving fact lives

namex locks a DIFFERENT, unknown directory each iteration, so
SpecDirlookup's two image premises — `16 | di_size` and
`dir_inums_ok data nrec nib` — cannot be supplied by namex as pure
premises (ilock's dn/data are existential in its postcondition). They
would have to be system INVARIANTS riding in the escrow payloads. Are
they? THIS kernel's balloc RETURNS 0 when dry (stock xv6 panics —
SpecBalloc.v's header records the difference), so writei genuinely
short-writes and dirlink's third arm (N3a finding 3, proven live in
N3d) can write a PREFIX of a 16-byte record. The two facts part ways:

**(a) dir_inums_ok IS an invariant.** Enumerate the directory-data
writers: dirlink (both arms), sys_unlink's record-zeroing writei
(zeros — wf), itrunc on a dir (size 0 — vacuous), iupdate (no data),
filewrite (unreachable for T_DIR — sys_open refuses writable dirs;
recorded for the sysfile campaign, whose filewrite spec will need the
fd-type history). dirlink's short arm: it writes only at a FREE slot
(free records are all-zero — unlink zeroes whole records, holes are
zero), so the old high byte under the window is 0 and a tot=1 prefix
stores the halfword `inum mod 256` — which is < 16*nib whether
16*nib ≥ 256 (mod < 256 ≤ bound) or < 256 (premise makes mod the
identity). tot ≥ 2 stores the full in-range inum (SpecDirlink already
carries `bv_unsigned dinum < 16*nib`); tot = 0 leaves the record
free. A truncated-NAME record (tot ≥ 2, name prefix + old zeros) is
semantically a VALID record with a different name — no wf impact.
So: **strengthen `ic_loaded` and `ipool_shape`'s allocated arm with
one conjunct** `dir_ok nib dn data := bv_unsigned (di_type dn) =
T_DIR_z -> dir_inums_ok data (nrec-of dn) nib` (nib enters as the
section/ambient parameter the escrow already sees; if it does not,
thread it — capacity, no resource). Re-establishment sites, each by
the holder at its re-park, all short: ProofIlock's fill (from the
pool's strengthened arm — rides), ProofIget's eviction re-park
(same data — rides), ProofFileread's iunlock (data unchanged —
rides), ProofIput's itrunc path (data zeroed — vacuous by
dir_inum-of-zeros = 0), ProofIupdate/writers via callers (dirlink:
the analysis above; unlink when it comes: zeros). The BOOT mint
(ireclaim/fsinit, N5) gains the conjunct as one more clause of the
EXISTING image-wf IOU — mkfs images satisfy it.

**(b) granularity is NOT an invariant** — the short APPEND leaves
`size = 16*nrec + tot`, permanently non-granular, and the next scan
of that directory really does die: readi returns tot < 16 and the
code calls panic("dirlookup read"). That is panic-SHAPED, which is
the whole answer: **drop the `16 | size` premise from SpecDirlookup
and SpecDirlink and make the short-readi branch a live panic arm**
discharged by panic_wp_any, exactly like ilock's "no type" and the
Route-B family. No postcondition arm is added — panic never returns,
so the found/notfound arms simply carry an implicit "…and every
readi in the scan returned 16" history, which is what rd_clamp gives
under granularity and what the panic arm gives without it. namex
then needs NO granularity fact at all. (The alternative — a poison
ghost — founders on "not poisoned" being locally unknowable: any
per-inum flag a holder can re-establish freely tells a later reader
nothing, and one it cannot is exactly the invariant that is false.)

**What does NOT work, for the record:** iget over a garbage inum
(the reason dir_inums_ok cannot also become a panic arm — an
out-of-range inum does NOT panic; it would quietly claim a cache slot
whose inum has no pool bundle, breaking the pool's complement
accounting — totalising THAT is an escrow redesign, and (a) makes it
unnecessary); threading dir-wf as a universally-quantified premise
over inode_ok-admissible states (false in general — undischargeable);
extending inode_ok itself (its signature has no nib and its users are
legion — the parallel conjunct in the two escrow payloads is the
minimal home).

Execution: N4a = (a)'s retrofit + (b)'s two spec/proof reworks;
N4b = namex + wrappers on top. Recorded consumers: sysfile's create
must handle dirlink's short arm (a corrupt directory is a real
post-state); filewrite's future spec owes the fd-type fact.

### 15.1 Corrections from N4a's execution (the stage that landed §15)

Three of §15's claims were wrong in the details; the conclusions
survive but the record should not mislead the next reader.

**(i) The short-write analysis ignored writei's disturbed region.**
SpecWritei's range clause is THREE-way (kernel defect D1): new bytes
below tot, then up to a BLOCK of UNSPECIFIED bytes above it, then old
bytes. So §15's "new prefix + old zeros" picture is wrong. The APPEND
arm is fine — cheaper than §15 argued (the fragment sits at index
nrec, out of range at the unchanged nrec; no mod-256 argument exists
in the landed proof at all). But the MIDDLE-SLOT arm (filling an
interior free record) can clobber up to 64 FOLLOWING records with
arbitrary bytes — dir_ok is NOT derivable from dirlink's contract as
frozen. This does not affect N4a (dirlink parks no escrow bundle in
this tree — the holder does, and today's only holder-after-dirlink is
future sysfile code); the honest fix, owed to sysfile's create: on
the KERNEL arm either_copyin cannot fail, so dist = 0 — strengthen
SpecWritei's kernel arm and the middle-slot analysis becomes the
append one. Also: the LINKED inum (the mword 16 argument) has no
range premise in SpecDirlink — the writer-side dir_ok proof adds it.

**(ii) The panic arm is not per-iteration.** For i < nrec, floor
division alone gives 16*i + 16 <= size — granularity was never needed
below the boundary. The arm is reachable at exactly ONE index,
i = nrec with a non-granular tail (including i = 0 for 0 < size < 16).
The landed proofs restructure the loop invariant around the loop's own
test (off < size) instead of i < nrec.

**(iii) nib is icfg_nib, forced.** A nib parameter on ic_loaded would
cascade through SpecIunlock into every caller; the ambient class is
already how inode_held names the same bound. Consumers with their own
nib parameter take nib = icfg_nib (ProofKexit's existing premise).

### 15.2 (i) IS DISCHARGED — the dist=0 retrofit (fs-sysfile S2, 2026-08-11)

The three items §15.1(i) owed to sysfile are landed, and the verdict
on the design ruling is: **CONFIRMED, with no mechanism disturbing
kernel-arm bytes.** SpecEitherCopyin's post is
`⌜r = 0 ∨ r = -1⌝ ∗ …` on the user arm but a bare `⌜r = 0⌝` on the
kernel arm, so writei's `either_copyin == -1` break at +0xb0 is DEAD
for `user = false`. It is the ONLY site in ProofWritei that
instantiates `dist` nonzero (every other exit passes the literal
`0%nat`), which is why the whole retrofit is one extra postcondition
clause and one extra conjunct in the proof:

1. **SpecWritei** gains `⌜user = false -> dist = 0%nat⌝` as its own
   clause, next to the existing `tot = n -> dist = 0`. Stated
   separately rather than by case-splitting the range clause: user-arm
   consumers are untouched, and a kernel-arm consumer rewrites `dist`
   to 0 and reads the two-way clause off the same line. ProofWritei's
   internal chain (wi_cont / wi_ret / wi_join / wi_size) takes one more
   hypothesis; the copy-failure normalisation `Hnorm` now carries
   `user = true` on its −1 disjunct, and that conjunct IS the proof.
2. **SpecDirlink** drops `dist` and `dstb` from its postcondition
   binder entirely — dirlink writes from its own stack record, so
   `dist = 0` is immediate and the range clause is TWO-way. The short
   arm (`tot < 16`) now differs from the old file in exactly the `tot`
   bytes it wrote.
3. **The linked-inum premise** `bv_unsigned inum < 16 * nib` is in
   SpecDirlink and is deliberately UNUSED by dirlink's own proof
   (`clear Hcinb` right after the intros, with a comment). Nothing in
   the tree calls dirlink, so it broke no caller.
4. **`DirView.dir_ok_dirlink`** is the derivation §15.1(i) said was
   unavailable, and it goes through — *Closed under the global
   context*, zero assumptions. Its shape:

   - every record but `k0` keeps both inum bytes (windows are
     16-aligned and `tot ≤ 16`), so `dir_inums_ok` rides;
   - the count grows by at most one, and only when `k0 = nrec` **and**
     `tot = 16` — which is the full-write case;
   - at `k0` itself: `tot = 0` is pointwise-equal data; `tot ≥ 2` makes
     the inum halfword wholly new, bounded by the new premise; `tot = 1`
     is §15(a)'s **mod-256 argument, and this is its home** — the slot
     is free (`dir_slot_free`) so the old high byte is 0 and the stored
     halfword is `inum mod 256 ≤ inum`. §15.1(i) was right that the
     argument had no place in the APPEND analysis; it belongs here.

   Supporting additions in DirView: `dir_nrec_range` (the two floor
   bounds in one shape), `dir_inum_unsigned` (the halfword's value from
   its two bytes) and `dir_inum_of_two` (`dir_record_inum` needing only
   the first two bytes).

Print Assumptions after the retrofit: `Writei.wp_writei_sconf` and
`Dirlink.wp_dirlink_sconf` are each exactly the 5 platform axioms +
funext, unchanged. Full gate EXIT=0, 1021 vo.

## 16. `ialloc` CANNOT BE STATED OVER §13.3'S POOL — the free arm's
## authority is filed under the wrong lock (OPEN, raised 2026-08-11 by
## fs-namei N5a)

§13.3 left ialloc open ("nothing here prejudges it"). Working the decode
against the landed layer closes it, negatively: **ialloc's claim step has
no ghost authority it can reach, and no contract shape fixes that without
moving where the free arm lives.**

### 16.1 The argument

ialloc's `log_write` (+0x9a) must run `InodeRegion.ireg_write_au`, whose
first resource premise is the exclusive `dinode_at γi inum dn`. Retagging
the region's map at that key is `ghost_map_update`, which cannot fire
without the element, and `ireg_body` holds only the authority plus the
block halves. So the fragment must come from outside.

A type-0 inum's fragment lives in exactly two places, both lock-protected:
`IcacheEscrow.ipool` — a conjunct of `itable_res2`, i.e. **inside the
itable spinlock** — and `ic_unloaded` inside `ic_payload` inside
`ic_escrow_body`, i.e. **behind that entry's sleeplock**. It cannot be in
a LOADED entry: `ic_loaded` carries `inode_ok`, which demands
`di_type ≠ 0`.

Between its `bread` (+0x3c) and its `brelse` (+0xa0) ialloc acquires
nothing but the buffer; its only `iget` (+0xaa) takes the itable lock
internally, *after* the claim is committed. So it holds neither lock at
the claim.

Pushing the obligation to the caller (a `∀ inum, …` loan, or an
AU family indexed by the discovered inum) is expressible and would let
ialloc's own proof go through — but its only possible discharger is a
caller owning the whole pool, and `create` holds the itable lock at no
point. That moves the hole up a level and hides it.

### 16.2 Why: the model files the free arm under the wrong serialiser

What actually serialises two concurrent `ialloc`s in xv6 is **the buffer**,
not the itable: `bread` returns the dinode block under its sleeplock, and
the loser's `bread` returns the cached buffer with the type already set.
§13.3 files the free inums' authority under the itable lock instead,
which is a lock ialloc never touches.

### 16.3 The proposed fix: the free arm's fragment moves INTO the region

`ireg_blk` gains, per block, a conjunct

    [∗ list] i ∈ seq 0 16,
      if decide (bv_unsigned (di_type (ds !!! i)) = 0)
      then (16 * bi + i)%Z ↪[γi] (ds !!! i) else True

— re-establishable everywhere, because `ireg_couple` already says the
map's value at every key IS the parked record. Consequences:

- `ipool_shape` becomes ONE-armed (allocated only) and the pool's domain
  shrinks to the allocated inums. iget's recycle of a free inum parks
  nothing; ilock on it still panics ("ilock: no type", already live);
  iput's last close returns nothing.
- **NEW `ireg_claim_au`** — the mirror of `ireg_write_au`, with the
  fragment sourced FROM the invariant rather than supplied to it. Given
  the block's decoded `ds` and `di_type (ds !!! islot inum) = 0`, it
  produces exactly `SpecLogWrite.wp_log_write_au_body`'s fupd and pays the
  retagged `dinode_at γi inum dn'` OUT (legal: `dn'` has type ≠ 0). This
  is ialloc's whole ghost step, and it is guarded by the buffer the
  caller holds — the right serialiser.
- **DUAL `ireg_free_au`** for iput's `ip->type = 0; iupdate(ip)`: absorb
  the fragment back. This makes `ireg_write_au`'s unconditional payout
  wrong for a type-0 `dn'`, so it gains a `di_type dn' ≠ 0` premise —
  free for iupdate's ordinary callers (`inode_ok` gives it), and iput's
  free path uses the dual instead.
- `IcacheBoot.ipool_shape_free` and `ipool_alloc_all_free` RETIRE;
  `ireg_alloc` sorts the image's fragments (free stay in, allocated go to
  the pool). **The boot mint gets strictly cheaper**: an all-free mkfs
  image then needs no pool contents at all.

Blast radius: `InodeRegion.v` (invariant + two lemmas + one premise),
`IcacheEscrow.ipool_shape` (one arm), `IcacheBoot.v` (three lemmas), and
the re-park sites in `ProofIget` / `ProofIput` / `ProofIlock`.

**Not blocked by this ruling:** ireclaim and fsinit. ireclaim only READS
dinodes — its `lh` of type and nlink need no fragment, only
`InodeRegion.ireg_read_blk` (landed by N5a) — and then composes six
already-proven contracts.

### 16.4 THE RULING (coordinator, 2026-08-11): §16.3's direction is
### right, its payout target is wrong; the claim-box completes it

**§16.3's core move stands**: free inums' `dinode_at` fragments live in
the region invariant (the type-0 conditional conjunct), the claim is
`ireg_claim_au` guarded by the buffer — the machine's real serialiser —
and `ireg_write_au` gains `di_type dn' ≠ 0` with `ireg_free_au` as the
dual. The boot mint gets cheaper exactly as argued.

**But the fragment must NOT pay out to ialloc's caller.** The killing
interleaving: (1) sys_unlink zeroes a directory record, and a racing
dirlookup that read the record just before takes its inum; (2) the
unlinker's iput frees the inode — the fragment returns to the region;
(3) dirlookup's iget finds the inum uncached and (per the slimmed pool,
below) parks a MARKER — a stale entry, valid = 0, refs > 0; (4) ialloc
claims the same inum through its buffer; (5) the stale entry's holder
calls ilock BEFORE create does. That fill reads type ≠ 0 from the
buffer, holds a marker, and the fragment is in create's pocket —
`ic_loaded` cannot be built and the WP wedges. Real xv6 sails through
(the filler just reads the claimed bytes), so the model must too.

**The claim-box.** A new small invariant (one ghost_map, auth inside):
per inum, `(∃ dn', inum ↪cb dn' ∗ ⌜fresh_shape dn'⌝) ∨ empty`, where
`fresh_shape` = zero addrs, zero size, type ≠ 0 (exactly what ialloc's
memset+stores leave). Lifecycle:
- `ireg_claim_au` moves the fragment region → box (retagged at dn').
  A claim against a FULL box slot is refuted by coupling: a full slot
  means the record's bytes have type ≠ 0, and the claim's premise is a
  buffer showing type 0.
- The FIRST fill withdraws box → `ic_loaded`. While boxed, the bytes
  cannot move: every writer needs the fragment and it is in the box.
  So the fill's buffer read EQUALS the boxed dn', and `fresh_shape`
  makes `inode_ok` constructible from nothing (`bm_empty`: ind_res and
  every blk_res collapse; `inode_sized_zero`; `dir_ok_size_zero`).
- iput's free path absorbs the holder's fragment box-lessly back into
  the region conjunct via `ireg_free_au` (type-0 retag).

**The pool stays TOTAL — iget does not reopen.** Keep
`dom(pool) = in-range ∖ cached` (both sides lock-stable; "allocated" is
NOT lock-stable once claims bypass the itable, so §16.3's shrunken
domain is unmaintainable). `ipool_shape` stays two-armed but its free
arm slims to the marker (no record — the region has it). iget parks
whichever arm rides in, unchanged. ilock's FILL gains one sub-arm:
- bundle parked → today's fill, unchanged;
- marker parked, buffer type = 0 → panic("ilock: no type"), already live;
- marker parked, buffer type ≠ 0 → box withdrawal (the new arm) — and
  this case analysis is EXHAUSTIVE: type ≠ 0 means the fragment is out
  of the region, and out-of-region ∧ not-in-any-ic_loaded (this entry is
  unloaded; entries are unique per (dev,inum)) forces the box.

**Blast radius (one retrofit cycle, then ialloc, then the boot half):**
`InodeRegion.v` (conjunct + two AUs + one premise), new `IcacheClaim.v`
(the box), `IcacheEscrow.v` (the free arm slims), `SpecIlock.v` +
`ProofIlock.v` (the fill sub-arm), `ProofIput.v` (free path re-parks the
marker arm + uses the dual), `IcacheBoot.v` (mint simplifies; free mint
needs no pool contents), `ProofIget.v` (audit — expected to ride).
ireclaim/fsinit compose only contract SHAPES that survive, but fsinit's
postcondition is pool-shaped, so the boot half is sequenced AFTER the
retrofit: N5b (retrofit) → N5c (ialloc) → N5d (ireclaim + fsinit).

### 16.5 §16.4 AS BUILT (N5b, 2026-08-11): the box is NOT a second
### invariant — it is the region's own arm, and the marker is a real token

§16.4's *content* is landed exactly as ruled: free inums' fragments live in
the region, the claim is buffer-serialised, `ireg_write_au` gains
`di_type dn' ≠ 0`, `ireg_free_au` is its dual, the pool stays TOTAL with a
slimmed free arm, ilock's fill gains one sub-arm, and the boot mint gets
cheaper.  Its *packaging* changed, for one reason that is a genuine gap in
the ruling and is worth stating precisely.

**THE GAP: §16.4's exhaustiveness argument is not a proof.** The ruling
says the fill's third case is forced because "type ≠ 0 means the fragment
is out of the region, and out-of-region ∧ not-in-any-`ic_loaded` (this
entry is unloaded; entries are unique per `(dev,inum)`) forces the box."
That is a **uniqueness claim about the whole itable** — it needs
`ic_ci_wf`'s injectivity and `dom(pool) = in-range ∖ cached`, both of which
live under the **itable spinlock**, and ilock's fill holds only its entry's
sleeplock.  So `icb_withdraw` as ruled has no discharge: with a
content-free marker, "box full" and "box empty" are indistinguishable from
inside the fill, and the empty case cannot be refuted.

**THE REPAIR: the marker becomes a per-inum EXCLUSIVE TOKEN**, and then the
box collapses into the region invariant.  `InodeRegion.imark γi z` is a
ghost_map element of the region's OWN map at a key no inum can occupy
(`imark_key z := -(z+1)`; inums are `bv_unsigned`s, hence ≥ 0).  The
region's per-slot arm is

    ireg_slot γi z d :=
        (⌜di_type d = 0 ∨ fresh_shape d⌝ ∗ z ↪[γi] d)   (* FREE or CLAIMED *)
      ∨ (⌜di_type d ≠ 0⌝ ∗ imark γi z)                   (* OUT *)

so **exactly one of {fragment, marker} is inside the invariant and the
other is outside**, and the claim box is precisely the first arm taken at a
`type ≠ 0` record.  The fill holds the marker (it is the slimmed free arm),
which refutes the OUT arm by `imark_excl` in one line — no itable lock, no
entry-uniqueness argument, no second invariant, and **no two-invariant mask
discipline to design** (the risk §16.4 flagged evaporates).

Consequences that differ from the ruling's blast-radius list:

- **No `IcacheClaim.v`.** A separate box invariant needs its own gname, and
  that gname would have to appear in `ireg_inv` *and* in `ipool_shape` —
  i.e. in `ic_escrow`'s arity, i.e. in every fs contract in the tree.
  Filing the token in the region's existing map keeps **`ireg_inv`'s and
  `ic_escrow`'s signatures byte-identical**, which is why SpecIlock did not
  change at all.
- **`ireg_claim_au` pays out nothing** (`True`), not a boxed fragment: the
  retagged fragment simply stays in the region's first arm.  ialloc's whole
  ghost step is one premise-free AU.  N5c's signatures are in the N5b
  ledger.
- **`icb_withdraw` is `InodeRegion.ireg_withdraw`**, a mask-preserving
  opening in `ireg_read`'s shape: marker + machinery half in, `fresh_shape`
  + fragment out, map unchanged.
- **iupdate's contract had to change** — the ruling's "ProofIput's free path
  switches its region step to `ireg_free_au`" is not reachable from iput,
  which touches the region only *through* iupdate.  The fix is one
  conditional payout, `InodeRegion.ireg_out γi inum dn` = `dinode_at` when
  `di_type dn ≠ 0` and `imark` when it is 0, so iupdate keeps ONE contract
  and picks the arm move itself.  `SpecWritei` and `SpecItrunc` then need
  `di_type dn ≠ 0` as a premise (they flush type-preserving records);
  dirlink has it from `di_type dn = T_DIR` and iput from `inode_ok`.
- **`ic_payload_dinode` retires.** It pulled a `dinode_at` out of any
  payload to refute a rival escrow arm; the slimmed free arm has none.  Its
  replacement `ic_payload_excl` refutes on the entry's `inode_meta` CELLS,
  which every payload holds on both polarities — strictly better, because
  the cells are slot-keyed and the refutation no longer needs `ic_id_agree`
  to pin the two arms' inums first.
- **The boot mint** allocates the record map and the marker map in one
  `ghost_map_alloc` and pays out `ireg_out` per inum; `ireg_alloc` needs a
  flat-inum → (block, slot) re-index (`IcacheBoot.seq16_flatten`) that did
  not exist before, because the block conjunct now holds ghost elements.

## 17. THE FD-TYPE WITNESS (S3's gate, 2026-08-11): how "this open file
## is not a directory" crosses from sys_open to filewrite's re-park

filewrite's FD_INODE arm must rebuild `ic_loaded` after writei, whose
`dir_ok` conjunct constrains a DIRECTORY's data bytes. A user write
into a directory breaks `dir_inums_ok`; writei cannot change
`di_type`; and `dn` is ilock's OUTPUT, so "not a directory" cannot be
a premise about a caller-held record. The real xv6 invariant is
upstream: sys_open refuses writable directory fds. Importing it needs
a resource, and the analysis of the alternatives is short:

- A pure payload fact `⌜di_type ≠ T_DIR⌝` is unusable — connecting it
  to ilock's existential dn needs type-stability-under-references as
  a MECHANISM, not a remark.
- Fractional type ghosts on references break at the freeing iput
  (it cannot collect other holders' fractions) or force a SpecIput
  contract change.
- What IS true and cheap: **no writer retypes a live inode** (0→ty
  needs an unallocated slot; ty→0 happens only at the last-reference
  iput's free path; ty→ty' does not exist in this kernel). So a
  PERSISTENT witness minted per slot-GENERATION is sound — stale
  witnesses of dead generations never collide because the key
  includes the generation.

**The design:**
- New ghost: `ityp γt (k, g) ty` — a persistent fragment of an auth
  gmap keyed by (slot, generation), where g is the slot's ic_id
  descriptor generation (the identity ghost the recycler already
  bumps; if ic_id's descriptor is not yet generation-shaped, extend
  it with a monotone counter — capacity, no statement changes).
- MINT at the fill: ilock's fill knows dn; it mints
  `ityp (k, g) (di_type dn)` (persistent, duplicable). The escrow's
  LOADED arm gains the agreement clause: record's type = the current
  generation's witness (re-established freely by every writer since
  none retypes; the free path exits the generation before retagging,
  via the pool arm which carries no record clause).
- `SpecIlock`'s postcondition EXPOSES the witness (∃ ty, ityp (k,g) ty
  ∗ ⌜di_type dn = ty⌝) — additive; existing callers ignore it.
- `FileInv.inode_pay`'s FD_INODE payload gains the witness plus
  `⌜writable = true -> ty ≠ T_DIR⌝` (NOT unconditional — O_RDONLY
  directory fds are legal and fileread never needs the fact).
  sys_open establishes it at file creation: on the T_DIR path it
  forces O_RDONLY; on the create path the type is T_FILE by
  construction (ialloc_fresh).
- filewrite's re-park: ilock's post gives dn and the witness
  agreement; the payload gives writable → ty ≠ T_DIR; filewrite's
  contract carries writable = true; dir_ok(new data) is vacuous. ∎

Blast radius: IcacheEscrow (the agreement clause + generation
plumbing), ProofIlock (the mint — inside the existing fill), possibly
IcacheRef/ic_id (generation counter), FileInvDefs/FileInv (payload),
SpecIlock (additive post) + its callers' iDestruct patterns
(mechanical), sys_open's obligation recorded for S6. fileread/
fileclose/filedup carry the payload opaquely — audit, expected to
ride. The boot mint: unloaded slots mint nothing; first fill mints.

### 17.1 §17 DOES NOT CLOSE AS RULED (fs-sysfile S3b, 2026-08-11) —
### STOP-AND-REPORT, with the repair worked out

Four findings, in the order they bite.  Nothing below was built; S3b
stopped here and spent its budget on filestat instead.

**(i) `ic_id` IS NOT THE RIGHT HOME, AND MAKING IT GENERATION-SHAPED
DOES NOT HELP.** `ic_id cn k q (v, dev, inum)` is a `ghost_var` whose
two halves live in the escrow's arm and in `IcacheInv.islot2`.  Both
homes sit behind the itable lock or inside the escrow, and **the
consumer §17 was written for holds neither**: filewrite reaches the
fact through `FileInv.inode_pay`, whose only icache-side resource is
`IcacheRef.inode_shr_held` — the two identity CELLS at a fraction plus
a `live_frac` slice.  A counter bolted onto `ic_id` is unreadable from
there, so the generation cannot be plumbed that way at any price.

**(ii) A PERSISTENT WITNESS CANNOT SAY "THIS GENERATION IS THE CURRENT
ONE", AND THAT IS THE WHOLE OBLIGATION.**  The re-park needs
`di_type dn = ty` for the payload's recorded `ty`.  With a persistent
`ityp (k,g) ty`, the payload's `g` and ilock's `g` must be shown
EQUAL, i.e. somebody must assert that `g` is slot `k`'s live
generation — and a persistent fragment is by construction not
revocable, so it would survive the recycler's bump and keep asserting
a dead generation.  Currency is therefore a REVOCABLE, reference-tied
fact; persistence is exactly the property that forbids it.

**(iii) SO THE GENERATION MUST RIDE THE LIVENESS POOL, AND THAT MUCH
IS CAPACITY.**  The only reference-tied fractional resources in the
tree are `inode_ident` (the dev/inum cells) and `live_frac` (§14.6's
pool).  The cells pin IDENTITY, which is reused across a free +
realloc, so they cannot key a type.  The pool can:

    iliveUR := gmapUR nat (prodR fracR (agreeR (leibnizO gname)))
    live_gen k s g := own icfg_live {[ k := (s, to_agree g) ]}
    live_frac k s  := ∃ g, live_gen k s g          (* ARITY UNCHANGED *)

The existential keeps `live_frac`'s arity, so `iref_tok`, `inode_ref`,
`inode_shr`, `inode_ref_short`, `inode_held*` and every Spec over them
are textually unchanged.  A bump needs the WHOLE unit at the slot,
which exists in exactly one place — `IcacheInv.live_slot`'s `None`
(free) arm, under the itable lock, which is precisely iget's recycle.
That is the right side condition: a bump is impossible while any
reference exists.

The agree must carry a per-generation **gname**, not the type: at
recycle the type is UNKNOWN (iget writes `valid = 0`; the type is not
read until ilock's `bread`), and after the recycle nobody holds the
whole unit again until the last iput — so a "set the type at recycle"
scheme is unsatisfiable.  The type attaches later through a ONE-SHOT
at that gname: iget allocates it and parks the pending token in
`ic_unloaded`; ilock's fill spends it and mints the persistent
`own g (Cinr (to_agree (di_type dn)))`.  §17 left this two-level
structure implicit and it is forced.

**(iv) THE REMAINING GAP IS THE ARM SIDE: `ic_loaded` TRAVELS.**
ilock hands `ic_loaded` to its caller, so the agreement clause has to
be self-contained — "di_type dn is the CURRENT generation's type" —
with no access to the arm it came from.  Two shapes, and both cost
more than §17 budgets:

- a persistent WAND
  `□ (∀ s g, live_gen k s g -∗ live_gen k s g ∗ ityp_wit g (di_type dn))`
  is provable (the fill borrows the OUT arm's slice through
  `ic_dep_res_live`, mints at the borrowed generation, and closes by
  pool agreement) — but **it is not TIMELESS**, and
  `ic_loaded_timeless` / `ic_payload_timeless` are load-bearing:
  IcacheEscrow's own header records that every opener is inside a
  store's or a load's atomic update with no step left to absorb a ▷.
  So this shape breaks the escrow outright.
- `ic_loaded` carrying a POOL SLICE OF ITS OWN is timeless and
  self-contained (the slice names `g`; the one-shot witness rides
  beside it), and every transition still balances — split the unit at
  a LIVE slot as ½ (payload) + qt (holders) + (½ − qt) (itable), leave
  a FREE slot's whole unit in `itable_body` so `iref_live_load_au` and
  `live_slot_live` are untouched, hand the ½ out with the new payload
  at iget's recycle, and take it back at iput's REF-1 close, which
  holds the payload already (§13.13's HELD arm).  But it MOVES §14.6's
  mass conservation, which these notes call load-bearing, and it
  touches `IcacheInv.live_slot`'s four update lemmas, IcacheBoot,
  ProofIget, ProofIput, and every construct/destruct of `ic_loaded`
  (IcacheEscrow ×5, ProofIlock ×5, ProofIunlock ×1, ProofFileread ×6,
  ProofNamex ×6).

**RECOMMENDATION.** Rule on (iv)'s second shape as §17′ and give it a
stage of its own; it is a coordinator-level change to §14.6, not a
retrofit an implementing agent may take.  Until then filewrite's
FD_INODE arm stays blocked exactly as fs-sysfile S3a left it, and
`SpecFilewrite.v` stays unwritten.

### 17.2 THE RULING ON §17′ (coordinator, 2026-08-11): adopt §17.1's
### liveness-generation design, including the ic_loaded slice

§17's persistent witness is DEAD — §17.1's currency argument is
decisive and joins §16.4's claim-box in the corrected-by-execution
column. The repair is RATIFIED as proposed, all four pieces:

1. `iliveUR := gmapUR nat (prodR fracR (agreeR (leibnizO gname)))`,
   `live_frac k s := ∃ g, live_gen k s g` — arity-preserving; no Spec
   over iref_tok/inode_ref/inode_shr/inode_held changes text.
2. The generation bump happens where the whole unit exists: the
   free arm under the itable lock — iget's recycle, the right side
   condition by construction.
3. Per-generation ONE-SHOT at the agree-carried gname: minted pending
   at recycle (parked in ic_unloaded), spent by the fill against
   `di_type dn`. The type enters at the only instruction that knows
   it.
4. `ic_loaded` owns a ½ liveness slice (payload half; holders qt;
   itable (½−qt) at live slots; free slots keep the whole unit in
   itable_body). **§14.6's mass-conservation witness is RESTATED, not
   patched**: the conserved quantity becomes "1 per live slot, split
   payload-half / holders / itable-rest; 1 per free slot, whole in
   the table" — write the new ledger as a definition and prove the
   old lemmas as corollaries where they still hold; where they do
   not (live_slot's four update lemmas), the new statements replace
   them with the §17.1 balance sheet as the guide.

Consequences accepted: IcacheBoot's mint distributes the slices;
ProofIget hands the ½ out at entry mint and reclaims at recycle;
ProofIput's REF-1 close collects via §13.13's HELD arm; the ~23
ic_loaded sites across IcacheEscrow/ProofIlock/ProofIunlock/
ProofFileread/ProofNamex gain the slice mechanically. `inode_pay`
then carries the generation gname + the one-shot + ⌜fc_wbool C →
ty ≠ T_DIR⌝ (keyed on the WRITABLE bool — FD_DEVICE selects
inode_pay too and never reaches writei). sys_open's discharge
obligations are exactly S3b's report (a)–(c), recorded for S6.

Sequencing: S3c = this retrofit, full-gated. S3d = SpecFilewrite +
Proof + Link on top. sys_fstat/sys_read are NOT blocked and may be
folded into S4 whenever the pipeline has room; only sys_write waits.

### 17.3 §17.2 PIECES 2 AND 3 DO NOT CLOSE AS RULED (fs-sysfile S3c,
### 2026-08-12) — piece 1 LANDED and full-gated; the repair, checked
### against the code, is below

Piece 1 went in exactly as ruled and the tree is green at 1025 `.vo`
with all eight cones' assumption sets unchanged.  Pieces 2 and 3 were
then worked forward against the code and each hit a wall.  Both walls
are sharp, both have a repair, and both repairs are things §17's own
PROSE already said — §17.2's MECHANISM just did not carry them.

**(A) THE ½ MAY NOT TRAVEL WITH THE PAYLOAD: `ic_open_auth_ref`'s
REF-1 refutation of the OUT arm dies.**  §17.2 piece 3 puts the slice
inside `ic_loaded`, i.e. inside `ic_payload`, i.e. it LEAVES the escrow
with the checked-out thread.  `IcacheInv.live_whole_share_absurd` is
the REF-1 refutation §14.9 built to replace §14.6's identity-mass one,
and it works today because the invariant's arm is the EXACT complement
of the caller's `qt`.  Under the new ledger it is not: at
`IcacheEscrow.ic_open_auth_ref`, branch OUT / `DepShr s dv nu`, the
goal is `|={Eo}=> False` from

    Hinv  : itable_inv                    (so live_slot M k, i.e. 1/2 - q)
    Hhalf : itable_half M                 (HMk : M !! k = Some (q, 1))
    Htok  : iref_tok k q                  (carries live_frac k q)
    Hid   : inode_ident k (DfracOwn qi) dev inum
    Hres  : inode_shr k s dev' inum'      (carries live_frac k s)

and the live mass available is `q + (1/2 - q) + s = 1/2 + s ≤ 1`,
satisfiable for every `s ≤ 1/2`.  Today it is `q + (1 - q) + s`, which
is `1 + s` and absurd.  §14.8's inventory of alternative
discriminators is exhaustive and already recorded dead: `ic_tok` and
`ic_mid` are in both arms by construction, `ic_id` is `true` in both,
OUT holds no memory cell at all, and the identity mass is
`qi + (1/2 - q) + s ≤ 1`.  Note `ic_open_held` is NOT affected — it
takes `ic_payload` as a premise, so under §17.2's placement iput holds
the ½ there and the sum is `1 + s` again.  It is `ic_open_auth_ref`
alone, and it is the opener that has no payload BY DESIGN (§13.13: the
payload is what it is going in to fetch).

*The repair:* **the ½ stays in the ARM.**  `ic_parked`, `ic_mid_arm`
and `ic_held` gain `live_gen k (1/2) g`; `ic_dep_res` carries the
arm's ½ beside the deposit, at the descriptor's generation, so
`ic_out`'s text does not move.  Then EVERY live arm holds the exact
complement, including OUT, and `live_whole_share_absurd` merely gains
a `live_frac k (1/2)` premise that both openers supply from the arm
they have just destructed.  `live_slot`'s live case is `1/2 - qt` —
§17.2's restated ledger VERBATIM; only the slice's home moves.

*What that costs, and what it saves.*  `ic_loaded` then cannot be
self-contained, so the generation must be a PARAMETER rather than an
existential — but it belongs on `ic_payload`, not on `ic_loaded`:

    ic_payload γfs γi cov logstart k inum g v :=
      if v then ∃ dn bm, ic_loaded γfs γi cov logstart k inum dn bm ∗
                         ity_shot g (di_type dn)
           else ic_unloaded γfs γi cov logstart k inum g

**`ic_loaded` is then UNTOUCHED**, which retires §17.2's "~23
`ic_loaded` sites gain the slice" line entirely.  Measured at
4dc4a8c9: `ic_loaded` is named in 19 files (ProofFileread ×6,
ProofNamex ×6, ProofIlock ×5, SpecStati ×5, ProofFilestat, SpecIput,
SpecDirlookup, SpecDirlink, …) and `ic_payload` in THREE
(IcacheEscrow ×28, ProofIput ×9, ProofIlock ×1), `ic_unloaded` in
three (IcacheEscrow ×15, InodeLock, ProofIput).  The
type witness is exposed ADDITIVELY out of the payload at v=true, which
is the shape §17.2 piece 4 asked for anyway.

Two consequences to rule on with it:

  (A1) `ic_dep` (§14.9's deposit descriptor) gains a `gname` field.
       §14.8's two-parkers inventory is explicit that a PARKER holds no
       `live_frac` at all — so `ghost_var_agree` on the descriptor is
       the only handle by which `ic_swap_park` can pin the returning
       payload's generation to the arm's.  §14.9 already has the
       descriptor pinning kind, fraction and identity; generation is
       the fourth, and it costs nothing new.
  (A2) `live_slot_close_last` gains the same `live_frac k (1/2)`
       premise (the eviction's arm comes home through `ic_open_held`,
       which iput already calls).  `live_slot_alloc` becomes a fupd
       (it mints the fresh generation and the pending token) and its
       side condition tightens from `q ≤ 1/2` to `q < 1/2`, matching
       `islot_rest_at`'s identity budget exactly — the two ledgers
       become the SAME shape, which is the real endorsement of the
       restated conservation law.

**(B) THE ONE-SHOT MAY NOT BE KEYED ON `v = false`: iput's free path
performs a shot→pending transition, and no one-shot admits one.**
§17.2 piece 2 parks the pending token in `ic_unloaded`, i.e. on the
`v = false` polarity.  But iput's free path (§13.13's truncate arm)
RETYPES IN PLACE and re-parks UNLOADED **inside the same generation** —
a bump needs the free arm's whole unit and the slot is still live
here.  `ProofIput.v:1965-1990`:

    (* +0x70 sw zero, valid *)   Hsv70 : trunc32 … = valid_word false
    iAssert (ic_payload gfs gi cov logstart k inum false) …
    iMod (ic_swap_park cn … k (DepRef q dev inum) false dev inum …)

and the payload it is rebuilding was LOADED a moment earlier on iput's
own path (`ProofIput.v:1670` builds `ic_payload … true`), so ilock's
fill has already SPENT that generation's one-shot.  The goal at 1981
would be `… ⊢ ity_pending g` with `ity_shot g ty` outstanding, and
`own g (Cinr _) ~~> own g (Cinl (Excl ()))` is not a frame-preserving
update at any mask.

*The repair, and it is §17's own sentence:* **park the pending token
with `ipool_shape`'s ALLOCATED disjunct inside `ic_unloaded`, not with
the valid polarity.**  §17 wrote "the free path exits the generation
before retagging, VIA THE POOL ARM WHICH CARRIES NO RECORD CLAUSE",
and that is literally what the code does — `ProofIput.v:1989` is
`rewrite /ipool_shape. iRight.`, the `imark` marker.  So:

    ic_pool_gen γfs γi cov logstart inum g :=
      (ipool_alloc γfs γi cov logstart inum ∗ ity_pending g)
      ∨ imark γi (bv_unsigned inum)
    ic_unloaded γfs γi cov logstart k inum g :=
      inode_raw (ientry k) ∗ ic_pool_gen γfs γi cov logstart inum g

(`ipool_alloc` is `ipool_shape`'s existing left disjunct, named; the
POOL's own `ipool_shape` is untouched — a pooled inum has no
generation and must not acquire one).  Then: iget's recycle takes the
bundle from the pool and mints the pending on the allocated branch
only; ilock's fill MUST take the allocated branch (it is where
`dinode_at` lives), so it always finds a pending to spend; and iput's
free-path park takes the marker branch and owes nothing.  No new
ghost, no re-check, and `ProofIput.v:1989`'s `iRight` still typechecks.

*The route NOT taken, recorded so nobody re-derives it:* bumping the
generation at the retype instead.  It needs the slot's whole unit —
the parker's `qt`, the arm's ½ and the table's `1/2 - qt` — and iput
has released the itable lock at +0x5c, so it holds no `itable_half`
and cannot know the map's `qt` is still its own `q` (a concurrent
`iget` cache-hit on the same (dev,inum) would have moved it).  It
would need a REF-1 RE-CHECK at +0x70 that xv6 does not perform.  Dead.

**WHAT S3C LANDED.** Piece 1, whole, full-gated: `iliveUR` carries the
agreed gname, `live_gen` / `live_gen_agree` / `live_gen_split` are the
mechanism the rest of §17' runs on, `live_frac k s := ∃ g, live_gen k
s g` preserved every arity as promised (the ripple was ZERO files —
`IcacheRef.v` alone), and the one-shot's vocabulary (`ityR`,
`ity_pending`, `ity_shot`, `ity_shoot`, `ity_shot_agree`) is in beside
it, modelled on `KptGhost.v`'s.  Pieces 2-4 wait on the ruling above.

### 17.4 RATIFIED (coordinator, 2026-08-12): §17.3's two repairs are
### the design; §17.2's piece-3 slice-in-ic_loaded is dead

Both S3c findings were verified against code and their repairs are
adopted verbatim: (A) the ½ liveness slice lives in the ESCROW ARMS
(parked/mid/held gain live_gen k (1/2) g; ic_dep gains the gname
field; live_slot's live case is 1/2−qt exactly as the restated
ledger says; live_slot_alloc becomes a fupd at q<1/2, unifying the
live and identity ledgers' shapes) and the generation + type witness
ride ic_payload — ic_loaded does not move, and ic_open_auth_ref's
REF-1 refutation keeps its full unit. (B) the per-generation
one-shot parks with ipool_shape's ALLOCATED disjunct inside
ic_unloaded — minted at iget's recycle on that branch, spent by the
fill where dinode_at lives; iput's in-generation free re-park owes
nothing. The discarded routes (§17.2's travelling slice; bumping at
the retype, dead because iput holds no itable_half at +0x5c) stay
recorded in §17.3.

Execution: S3d = pieces 2–4 per §17.3 (the arm slices, the one-shot
parking, SpecIlock's additive post, inode_pay's witness), full-gated;
then SpecFilewrite/Proof/Link in the same stage if budget allows.

### 17.5 §17.3(A) LANDED; §17.3(B) DOES NOT CLOSE EITHER — §16.4's
### CLAIM BOX puts a second fill inside one generation (fs-sysfile S3d,
### 2026-08-12)

Piece (A) went in exactly as ratified and the tree is green.  Piece (B)
— the one-shot's parking — was worked forward against `ProofIlock` and
died on a branch §17.3 did not know about.  The finding is sharp, the
counterexample is in the code, and the repair needs a coordinator
ruling, so `ic_payload`'s witness conjunct is NOT in and `SpecIlock`'s
additive post is NOT in.  Everything they will need IS.

**WHAT (A) LANDED, and the one place it is smaller than the ruling.**
`live_slot`'s live case is `1/2 − qt`, which is `islot_rest_at`'s shape
character for character — the liveness ledger and the identity ledger
are now the SAME ledger, which is the endorsement §17.3 predicted.
`ic_parked` gains `∃ g, live_gen k (1/2) g` bound with its payload;
`ic_dep_res` splits into `ic_dep_own` (the depositor's reference or
share, generation-NAMED so `live_gen_agree` can pin the arm's half to
it) and `ic_dep_half` (the arm's ½ at the descriptor's generation), so
`ic_out`'s text does not move; `ic_dep` gains the gname field and
`ic_dep_gname` is the pure side condition the two swap lemmas carry.
`live_slot_alloc` is a fupd at `q < 1/2` that mints the fresh
generation AND its pending token; `live_slot_close_last`,
`iref_close_last_step`, `iref_close_last_store_au` and
`live_whole_share_absurd` each gain a `live_frac k (1/2)` premise;
`live_slot_incr` (hence `iref_incr_store_au` and
`iref_upgrade_store_au`) tightens to `qt + qn < 1/2`.
`ic_open_auth_ref`'s REF-1 refutation of OUT/`DepShr` is back to
`qt + (1/2 − qt) + 1/2 + s > 1`, and `ic_open_held`'s with it.

**THE ONE DEVIATION, and it is forced by the instruction stream.**
§17.3 says parked/mid/held all gain the ½.  MID and HELD do NOT, and
cannot:

  * MID is built at iget's `sw inum` (+0x72) and sealed into the escrow
    there, but the slot does not enter `M` until the `sw 1` to
    `ip->ref` at +0x78 — so at +0x72 no unit has been split and there
    is no ½ in existence to put in the arm.  The recycler carries the
    ½ (and the pending token) by hand from +0x78 to the reclose at
    +0x7c, where `ic_close_mid_to_parked` deposits both.
  * HELD is entered at iput's +0x3c off `ic_open_auth_ref`, which hands
    the parked arm's ½ out with the payload; iput carries it across
    `acquiresleep` exactly as it carries the payload, and puts it into
    `ic_dep_half` at the +0x54 checkout or back into PARKED at the
    +0x44 nlink undo.

  Neither costs anything: both arms are windows ONE thread holds
  exclusively between two stores, the mass ledger balances at every
  instant (the ½ is in that thread's hand), and no opener's refutation
  of either arm uses liveness — both are refuted by their FULL `i_inum`
  cell.  The operative claim of §17.3 (A) — "every live arm an opener
  can MEET holds the exact complement" — is true of PARKED and OUT,
  which are the only two an opener ever meets.

**(B) IS REFUTED BY §16.4.**  §17.3 (B) parks the pending one-shot with
`ipool_shape`'s ALLOCATED disjunct, on the argument that *"ilock's fill
MUST take the allocated branch (it is where `dinode_at` lives), so it
always finds a pending to spend"*.  That is false in this tree.
`ProofIlock`'s `il_load` splits the pool shape THREE ways (§16.4's own
sentence): the allocated bundle; a MARKER over a type-0 record, which
is the free inode ilock panics on; and **a MARKER over a NONZERO type,
which is ialloc's claim box** — `InodeRegion.ireg_withdraw` takes the
fragment out of the region, delivers `fresh_shape`, and the fill
COMPLETES on that branch.  So the fill reaches its mint holding only a
marker, and there is no pending token there.

Parking the pending on BOTH pool disjuncts is the obvious fix and is
exactly what §17.3 (B) refuted from the other side: `ProofIput.v:1981`
re-parks UNLOADED at the MARKER **inside the same generation**, after
the fill has already SHOT it.  So:

    fill needs   a pending on the marker disjunct
    iput needs   NO obligation on the marker disjunct

and for a per-generation one-shot these are jointly unsatisfiable.
Nothing weaker works either, and the reason is structural: the witness
must be IMMUTABLE per generation (that is what makes it agree with the
file payload's copy), so a generation that is filled TWICE is
unprovable — and iget's recycle plus iput's free path give a generation
exactly two fills.

**WHY THE OBVIOUS ESCAPES ARE DEAD** (so nobody re-derives them):

  * *Let the marker disjunct carry `ity_pending g ∨ ∃ ty, ity_shot g ty`
    and make the fill discharge the second case.*  On that branch the
    fill must prove `di_type dn = ty` for the record it just withdrew.
    That is TRUE — iput's free path leaves the region record at type 0,
    so the second fill would take ilock's `ip->type == 0` panic — but it
    is not DERIVABLE: `imark γi z` is `∃ d, imark_key z ↪[γi] d`, an
    exclusive token carrying no type at all (§16.4 slimmed the free arm
    to exactly this), and ialloc's claim can retag the inum between the
    two.  Making it derivable is an `InodeRegion` change: the marker
    would have to name its record's type, or a new region-side fact
    ("this inum's parked record is type 0") would have to travel with
    iput's re-park.
  * *Bump the generation at iput's re-park.*  §17.3 already killed this:
    the bump needs the slot's whole unit and iput released the itable
    lock at +0x5c, so it holds no `itable_half` and cannot know the
    map's `qt` is still its own `q`.  Note the ½ is no obstacle under
    (A) — `ic_swap_park` could hand it back — but the table's `1/2 − qt`
    still is.
  * *Let the payload's generation differ from the arm's slice
    generation.*  Impossible by construction: `iliveUR`'s `agree` is
    per-KEY, so ALL slices of slot `k` name one generation at every
    instant.  That is what makes `live_gen_agree` unconditional, and it
    is what makes the descriptor's gname field cost nothing — but it
    also means "re-park at a fresh generation" is not a local move.
  * *A fractional/authoritative type ghost instead of a one-shot.*
    §17.1 (ii) already ruled: currency is revocable, and a second
    setter must collect every outstanding fragment — which the file
    payload's persistent copy forbids.

**WHAT A FIFTH RULING HAS TO CHOOSE BETWEEN.**  Three candidates, each
priced against the code:

  (a) **Type the marker.**  `InodeRegion.imark` becomes
      `imark_at γi z ty` (or gains a duplicable "the parked record's
      type is `ty`" companion), `ireg_free_au` delivers it at 0,
      `ireg_claim_au` retags it, and `ic_pool_gen`'s marker disjunct
      becomes `imark_at … ty ∗ (ity_pending g ∨ ∃ ty', ity_shot g ty' ∗
      ⌜ty = 0⌝)`.  The fill then discharges the shot case by taking the
      panic branch.  Blast radius: `InodeRegion` (the marker, three
      lemmas, the invariant's per-slot arm), `ProofIlock`'s fill,
      `ProofIput`'s free path, `ProofIalloc`'s claim, `IcacheBoot`.
      This is the only candidate that is faithful to what is TRUE.
  (b) **Give iput's free path a fresh generation by re-checking REF-1
      at +0x70.**  xv6 does not perform that read, so this is a
      no-go without changing the kernel — recorded only to close it.
  (c) **Move the witness off the generation entirely** and key it on
      (slot, inum, type) with the file payload holding a persistent
      fragment plus a REVOCATION guarded by the pool — i.e. redo §17.1
      (ii) with the generation as the revocation key rather than the
      witness key.  Unexplored; probably (a) in different clothes.

Until one of those is ruled, `ic_payload`'s `g` is a live but
unconstrained parameter and the witness is a ONE-LINE addition to that
definition plus one line in `SpecIlock`'s postcondition.  filewrite
stays blocked exactly where S3a left it.

### 17.6 THE RULING ON §17.5 (fs-sysfile S3e, 2026-08-12): BOTH CANDIDATES
### DIE; the mechanism is a SECOND GENERATION BUMP, taken by iput's free
### path at +0x54 where it still holds the itable lock and REF-1

§17.5's two live candidates were worked to a mechanism against the code.
(a) is dead twice over and (c) is dead once; both certificates are in
§17.6.5.  The design that closes is neither: it keeps §17's ORIGINAL
per-generation witness — which §17.5 refuted only because *"a generation
admits exactly two fills"* — and removes the refutation at its root by
giving the second fill its own generation.  The bump has a home the four
previous iterations never looked at, and the reason it was never looked at
is that §17.3 and §17.5 both killed the bump AT THE RE-PARK (+0x70, no
`itable_half`) and neither went back twenty-six bytes to +0x54, where iput
has not yet let go of the lock.

**THE CENTRAL LEMMA IS PROVED.**  `live_slot_regen` (statement in
§17.6.3 (2)) compiled clean against the tree at `b538f806` as a scratch
probe on the mirror, first try, `DONE = 0` — the arithmetic, the invariant
round trip and the re-split are not conjecture.  Scratch deleted; mirror
`git status` clean at 1032 `.vo`.

#### 17.6.1 THE KILLER SEQUENCE IS REACHABLE, AND EVERY STEP IS PROVEN CODE

Worked against the instruction streams rather than argued:

1. `ProofIget.v:1226` recycles slot `k` at generation `g`
   (`iref_alloc_step` → `live_slot_alloc`, `IcacheInv.v:493`), which mints
   `g` AND `ity_pending g`; the re-close at `ProofIget.v:1278`
   (`ic_close_mid_to_parked`) parks the entry UNLOADED.
2. `ProofIlock.v:974` fills from the pool bundle's `dinode_at`, at type
   `ty₁`.
3. sys_open publishes an fd; the payload's share is
   `IcacheRef.inode_shr_held_gen … g` (`IcacheRef.v:954`).  The fd is
   closed later; a persistent `ity_shot g ty₁` survives in whatever
   context copied it.
4. iput's last close takes the free path: `ProofIput.v:1366`
   (`ic_open_auth_ref`, +0x3c) at REF-1, +0x44 falls through
   (`ProofIput.v:1538`), the truncate / `ip->type = 0` / iupdate stretch
   returns the region fragment and pays out the MARKER
   (`ireg_out_free_inv`, `ProofIput.v:1960`), +0x70 clears valid and
   `ProofIput.v:2013` re-parks UNLOADED at the marker — **still generation
   `g`**.
5. **The window is real and xv6 walks into it deliberately.**  Between
   iput's `release(&itable.lock)` at +0x5c and its `ip->ref--`, the entry
   is still CACHED with `ref = 1`, so `iget`'s hit test
   (`ip->ref > 0 && dev && inum`) matches.  `ProofIalloc.v:1454` claims the
   very same inum through `ireg_claim_au` — buffer-serialised, no cache
   lock (§16.1) — retagging the region record to `fresh_shape ty₂`, and
   `ProofIalloc.v:1625` then calls `iget`, which takes the CACHED entry and
   bumps `ref` to 2.  iput's decrement leaves 1.  The slot never goes free,
   so no recycle intervenes.
6. `create`'s `ilock` finds `valid = 0` and fills a SECOND time, on the
   third branch of `ProofIlock.v:974`'s split — marker parked, nonzero
   type, `InodeRegion.ireg_withdraw` — producing `ty₂` at generation `g`.

So a generation genuinely sees two fills at two types, and §17.5's
structural sentence is confirmed: any fact keyed on `g` ALONE is dead.

#### 17.6.2 THE FD-LIVENESS OBSERVATION, WORKED HONESTLY: it excludes the
#### second fill, it IS a resource, and it is the ENABLING condition — not
#### a proof that stale witnesses are unusable

The task's hypothesis is **confirmed, and then some**, but its intended use
does not work and the reason is worth recording.

*What is true.*  Step 4 needs `M !! k = Some (q, 1%positive)` — that is
literally `ic_open_auth_ref`'s second premise (`IcacheEscrow.v:1096`), and
`positiveR` has no zero (§14.5), so a count of 1 forces the caller's `q` to
BE the map's `qt`.  Then `IcacheInv.live_whole_share_absurd`
(`IcacheInv.v:1345`) says any further `live_frac k s` is over budget:
`qt + (1/2 − qt) + 1/2 + s > 1`.  A live fd's payload holds
`inode_shr_held (q·Q)`, which carries exactly such a slice.  **So no fd of
slot `k` is alive when the free path is taken**, and the resource that
carries the exclusion is the liveness pool's mass ledger — the lemma is
`live_whole_share_absurd`, and it is already landed.

*Why that alone does NOT rescue a per-generation one-shot.*  The
obstruction was never soundness — nobody could ever USE a stale
`ity_shot g ty₁` to conclude a falsehood, because using it needs agreement
with the payload's copy and the payload has only one.  The obstruction is
PROVABILITY at the second fill: `ity_shot` is PERSISTENT
(`IcacheRef.v:439`), so a stale copy survives the death of every share, and
`own g (Cinr _) ~~> own g (Cinl (Excl ()))` is not an update at any mask.
Fill₂ is stuck, and a stuck WP is as fatal as an unsound one.  "All
ty₁-holders are dead" is therefore not a fact the model needs; it is a fact
the model cannot even use.

*What the exclusion is actually good for, and this is the whole ruling.*
Read `live_whole_share_absurd` in the positive direction.  The three
summands it adds to a contradiction are, at that same instant, an
ASSEMBLY: the closer's `qt`, the escrow arm's `1/2` (handed to it with the
payload at `ProofIput.v:1376–1388`, since `ic_held` holds no slice —
§17.5's forced deviation), and the table's `1/2 − qt` inside `itable_inv`.
They sum to `1`.  **Holding the whole unit is precisely what licenses
`live_gen_bump` (`IcacheRef.v:597`), and `live_gen_bump` mints both a fresh
generation and a fresh `ity_pending`.**  The exclusion is not evidence
about stale witnesses; it is the PERMISSION SLIP for revocation, and it is
expressible as a resource because it already is one.

*The serialisation that makes it airtight.*  A concurrent `iget` cannot
slip a reference in before the bump: `iget`'s hit path takes the ITABLE
LOCK, which iput holds continuously from its `acquire` through +0x5c, and
the bump sits inside that window.  So every reference minted after the free
path commits — including step 5's, the one that keeps the slot alive — is
minted at the NEW generation.  Every reference that existed before it is
refuted by REF-1.  There is no interleaving in between; the lock is the
whole argument, and it is the same lock §16.2 calls the wrong serialiser
for ialloc and the right one for the cache.

**VERDICT: the killer sequence is REACHABLE, but never with a ty₁-witness
holder LIVE, and that exclusion — as an assembly, not as an absence — is
exactly the resource that retires generation `g` before fill₂ runs.**  So
agreement never crosses a re-type, for the reason the task guessed, by a
mechanism it did not.

#### 17.6.3 THE MECHANISM

**RA: NOTHING NEW.**  `ityR` (`IcacheRef.v:256`), `ity_pending` /
`ity_shot` / `ity_shoot` / `ity_shot_agree` (`IcacheRef.v:434–457`) and
`iliveUR`'s agreed gname are S3c's, unchanged; `live_gen_bump` is S3d's,
unchanged.  §17.6 adds no algebra at all.  What moves is WHERE the pending
lives and WHO bumps.

**(1) The pending rides `ic_payload`'s FALSE polarity — not `ic_unloaded`,
and not a pool disjunct.**

    ic_payload γfs γi cov logstart k inum g v :=
      if v then ∃ dn bm, ic_loaded γfs γi cov logstart k inum dn bm ∗
                         ity_shot g (di_type dn)
           else ic_unloaded γfs γi cov logstart k inum ∗ ity_pending g

`ic_loaded` does not move (still nineteen files, still untouched) and
**`ic_unloaded` does not move either** — which matters, because
`ic_mid_arm` (`IcacheEscrow.v:724`) holds `ic_unloaded` DIRECTLY, not
`ic_payload`, and it is sealed at iget's +0x72 (`ic_mk_unloaded`,
`ProofIget.v:1167`) six instructions before the unit is split at +0x78.
Putting the pending inside `ic_unloaded` would demand a token that does not
exist yet — §17.5's MID deviation, one level down.  On the FALSE polarity
of `ic_payload` the obligation lands exactly at +0x7c
(`ic_close_mid_to_parked`, `ProofIget.v:1278`), where `Hpend` is ALREADY in
the recycler's hand and is today simply dropped (`ProofIget.v:1205` carries
`∃ g, live_gen e (1/2) g ∗ ity_pending g` by hand from +0x78 to +0x7c).
Both conjuncts are TIMELESS (S3c made them so), so `ic_payload_timeless`
survives verbatim — §17.1 (iv) respected.  §17.3 (B)'s pool-disjunct
placement is RETIRED: the fill's three branches all get their pending from
the same place, and `ipool_shape` / `ipool_alloc` / `imark` are NOT
TOUCHED — which is what keeps `InodeRegion` and ialloc out of this
entirely (§16's constraint, respected by construction rather than by
argument).

**(2) `live_slot_regen` — the second bump.  PROVED (probe).**

    Lemma live_slot_regen (Eo : coPset) (M : gmap nat (Qp * positive))
        (k : nat) (qt : Qp) (n : positive) :
      ↑icacheN ⊆ Eo -> M !! k = Some (qt, n) ->
      itable_inv -∗ itable_half M -∗ live_frac k qt -∗ live_frac k (1/2)%Qp
      ={Eo}=∗ ∃ g' : gname,
         itable_half M ∗ live_gen k qt g' ∗ live_gen k (1/2)%Qp g' ∗
         ity_pending g'.

It is `live_whole_share_absurd` with the contradiction replaced by
`live_frac_bump` and a close: open `itable_inv`, `itable_half_agree`,
`live_pool_acc_upd`, `live_slot_some_inv` for `c` with `1/2 = qt + c`, join
`qt + c + 1/2 = 1`, bump, re-split, put `c` back through the accessor —
`live_slot`'s text does not change, because it is stated over `live_frac`
whose generation is existential.  **The COUNT `n` is a parameter the lemma
never reads**, exactly as in `live_whole_share_absurd`: REF-1 is only how
the caller comes to know `q = qt`.  Home: `IcacheInv.v`, beside
`live_whole_share_absurd`.

**(3) Who does what, at which instruction.**

| where | file:line | move |
|---|---|---|
| recycle, +0x78 | `ProofIget.v:1226` | `live_slot_alloc` mints `g` + `ity_pending g` (LANDED, unchanged) |
| recycle, +0x7c | `ProofIget.v:1278` | `ic_close_mid_to_parked` now CONSUMES `Hpend` instead of dropping it |
| the fill | `ProofIlock.v:940–1012` | inside the existing `fupd_wp`, `ity_shoot g (di_type dn)` — one `iMod`, on both payload-building branches of the three-way split; the panic branch builds none |
| iput +0x3c | `ProofIput.v:1366` | unchanged; the LOADED branch already hands out the arm's `1/2` and the payload |
| iput +0x44 taken (nlink ≠ 0) | `ProofIput.v:1506` | unchanged — no bump; the loaded payload and its shot go straight back |
| **iput +0x54, before `ic_open_held`** | **`ProofIput.v:1688`** | **`iMod (live_slot_regen …) as (ga') "…"`.**  Every premise is in hand at that line: `Hhalf : itable_half Mt` with `HMk : Mt !! k = Some (q, 1)`, `Hrtok : iref_tok k q`, `Hlvh : live_gen k (1/2) ga`, `#Hinv : itable_inv`; the mask is `⊤ ∖ ↑icEscN` and `↑icacheN` is free there |
| iput +0x54, checkout | `ProofIput.v:1714–1722` | the descriptor becomes `DepRef q dev inum ga'`; `ic_dep_own` / `ic_dep_half` at `ga'` |
| iput +0x74 | `ProofIput.v:2004–2013` | `ic_swap_park` at `ga'`; the FALSE payload is raw cells + marker + the fresh `ity_pending ga'` |
| ialloc | `ProofIalloc.v:1454, 1625` | **nothing.**  No token, no witness, no region change |

Note the shape of the last row against §16: the claim and its `iget` are
the two instructions that MAKE the killer sequence, and they acquire no
obligation whatsoever — the cache retires the generation on its own side,
under its own lock, before either of them can run.

**(4) The ONE generalisation the placement forces, and it is free.**
`ic_open_held` (`IcacheEscrow.v:1552`) today takes `live_gen k (1/2) g` and
`ic_payload … g v` at ONE `g`.  After the bump iput's arm-half is at `ga'`
while the payload in its hand is still the LOADED one at `ga` (with
`ity_shot ga ty₁`) — and it must stay there, because restating it at `ga'`
would mean shooting the fresh pending, which the +0x74 park needs.  So the
lemma takes two gnames.  This costs nothing: the payload is threaded
through untouched, its only use is refuting PARKED via `ic_payload_excl`,
and `ic_payload_excl` (`IcacheEscrow.v:1514`) is ALREADY generic in `g1`,
`g2`; the OUT and MID refutations use REF-1, the live mass and the cells,
never the payload's generation.  The stale loaded payload is destroyed on
iput's own path (itrunc + `ip->type = 0` turn `ic_loaded` into raw cells
and a marker), so `ity_shot ga ty₁` dies with the generation that named it.

**(5) The consumer end.**  `SpecIlock`'s postcondition gains one line, at
the site its own comment already reserves (`SpecIlock.v:262–268`):
`ity_shot g (di_type dn)`, at the CALLER'S `g` — SpecIlock v4 already takes
the share generation-named, and `live_gen_agree` inside ilock pins the
arm's generation to the caller's **with no itable fact anywhere**, which is
§17.1's currency requirement discharged.  `SpecIunlock`
(`SpecIunlock.v:148`) and `SpecIunlockput` gain the same conjunct as a
PREcondition, since `ic_payload`'s TRUE polarity is what they rebuild; the
five existing consumers (fileread, filestat, namex, ireclaim, iunlockput)
thread one resource each and none of them changes `di_type`.
`FileInvDefs.inode_pay` (`FileInvDefs.v:592`) becomes

    inode_pay γx Q v q := cinv fileipN γx (inode_held_short v Q) ∗
                          cinv_own γx q ∗ inode_shr_held_gen v (q*Q) g ∗
                          (∃ ty, ity_shot g ty ∗
                                 ⌜fc_wbool C = true -> ty ≠ T_DIR⌝)

with `g` a field of `fpnames` beside `fp_iq` — a per-slot CONSTANT, exactly
`fp_iq`'s status.  `ity_shot` is persistent, so `inode_pay_split`'s
distributivity is untouched.  filewrite then closes: ilock's post gives
`ity_shot g (di_type dn)`, the payload gives `ity_shot g ty` with
`ty ≠ T_DIR`, `ity_shot_agree` (`IcacheRef.v:457`) joins them, and `dir_ok`
is vacuous.  **Constraint 8 (filewrite's re-park) closes for free:**
`SpecWritei.v:263` defines `wi_dinode dn bm' off tot :=
MkDinode (di_type dn) …`, so the flushed record's type is DEFINITIONALLY
the fill's and filewrite re-parks with the same shot it was handed.

**(6) The boot story: ZERO.**  `IcacheBoot.v:855` starts all fifty slots at
`ic_empty_arm`, and an empty arm holds no payload — so no slot carries a
pending at boot, and `live_boot_map`'s single gname for all fifty (S3c) is
still right.  The first `live_slot_alloc` per slot mints that slot's first
real generation and its first pending.  `IcacheBoot.v` does not change.

**(7) Where a generation ends.**  At the last close the slot leaves `M`,
`live_slot_close_last` (`IcacheInv.v:562`) reassembles the whole unit into
the free arm, and the eviction turns `ic_payload` into `ipool_shape`,
DROPPING an unspent pending (or a spent shot).  Both are harmless: a free
slot carries no obligation, and the next recycle bumps again.  Every
generation therefore sees AT MOST ONE FILL — the invariant §17.5 proved was
necessary and could not get.

#### 17.6.4 BLAST RADIUS, priced per file

- **`IcacheInv.v`** — ONE new lemma, `live_slot_regen`, PROVED (22 lines).
  Nothing else moves: `live_slot`, `live_pool`, `live_slot_alloc`,
  `live_slot_close_last`, `live_whole_share_absurd` and all four update
  lemmas are text-identical.
- **`IcacheEscrow.v`** — `ic_payload`'s two arms gain one conjunct each (a
  three-line edit at `:520`); `ic_open_held` (`:1552`) takes a second
  gname; `ic_close_mid_to_parked` (`:1381`) gains an `ity_pending g`
  premise.  `ic_unloaded`, `ic_loaded`, `ic_mid_arm`, `ic_parked`,
  `ic_out`, `ic_held`, `ipool_shape`, `ic_swap_checkout`, `ic_swap_park`,
  `ic_open_auth_ref`, `ic_payload_excl`, `ic_payload_timeless` — **all
  unchanged**.  Of the 28 `ic_payload` mentions most thread it opaquely;
  expect ≈6 construct/destruct sites to need one `iFrame` each.
- **`ProofIget.v`** — ONE LINE: `Hpend` moves from the drop list into
  `ic_close_mid_to_parked`'s arguments at `:1278`.
- **`ProofIlock.v`** — one `iMod (ity_shoot …)` inside the existing
  `fupd_wp` at `:940`, discharged on both payload-building branches of the
  `:974` split; `il_load` (`:617`) gains one premise (`ity_pending g`, and
  `g` is ALREADY one of its parameters) and the caller at `:2220` splits it
  out of the payload alongside the `inode_raw`/`ipool_shape` pair it
  already splits.
- **`ProofIput.v`** — one `iMod (live_slot_regen …)` at `:1688` plus a
  `ga → ga'` rename over the free-path stretch `:1688–2013` (§14.9 records
  that this stretch is one proof whose spec applications name their
  arguments, so the rename is mechanical); `:2013` supplies the fresh
  pending; `:1684`'s payload rebuild and `:1506`'s undo carry the shot they
  already hold.
- **`SpecIlock.v`** (+1 line, additive), **`SpecIunlock.v`** /
  **`SpecIunlockput.v`** (+1 premise each), and their five consumers
  (**ProofFileread, ProofFilestat, ProofNamex, ProofIreclaim,
  ProofIunlockput**) one line each — the same shape S3d's
  `inode_shr_gen_intro` retrofit had.
- **`FileInvDefs.v` / `FileInv.v`** — `fpnames` gains a gname field,
  `inode_pay` gains the witness conjunct, `inode_pay_split` /
  `inode_pay_alloc` / `inode_pay_cancel` re-prove with `ity_shot`
  persistent (distributivity unaffected).
- **`IcacheBoot.v`, `InodeRegion.v`, `ProofIalloc.v`, `IcacheRef.v`,
  `ProofIunlock.v`, `SpecIget` / `SpecIput`, and every `ic_loaded`
  consumer** — **UNTOUCHED.**

Sequencing: **S3f** = (1)+(2)+(3)+(4), full-gated — escrow, iget, ilock,
iput, i.e. the icache half, with no contract flip beyond SpecIlock's
additive line.  **S3g** = (5) + `SpecFilewrite` + Proof + Link.  Splitting
there keeps the tree green at a point where nothing above the icache has
moved.

#### 17.6.5 DEATH CERTIFICATES

**(a) TYPE THE MARKER — DEAD TWICE, and §17.5's own parenthetical holds the
first counterexample.**  §17.5 proposed `imark_at γi z ty` with
*"`ireg_free_au` delivers it at 0, `ireg_claim_au` retags it"*.
  * *Not maintainable.*  `imark γi z` is `∃ d, imark_key z ↪[γi] d`
    (`InodeRegion.v:355`) — a ghost_map ELEMENT — and `ireg_slot`
    (`InodeRegion.v:416`) puts exactly one of {fragment, marker} inside the
    invariant.  At a type-0 or `fresh_shape` record the FRAGMENT is in and
    **the MARKER IS OUT**, in the pool or in a checked-out entry's
    `ic_unloaded`.  `ireg_claim_au` (`InodeRegion.v:751`) is the arm that
    retypes 0 → `ty₂`, and it runs with no cache lock and no marker in hand
    (§16.1 — the whole reason §16.3/§16.4 exist).  A ghost_map element is
    updatable only by its holder.  **So the claim cannot retag the marker**,
    and a marker naming its record's type is false the instant ialloc runs.
  * *Not true either.*  §17.5 justified the shot-case discharge with *"iput's
    free path leaves the region record at type 0, so the second fill would
    take ilock's `ip->type == 0` panic"* — and wrote, four lines earlier,
    *"ialloc's claim can retag the inum between the two"*.  §17.6.1 IS that
    retag, in proven code (`ProofIalloc.v:1454` then `:1625`).  On the
    killer sequence the second fill reads `ty₂ ≠ 0` and COMPLETES; the panic
    never happens.  Either the invariant is unmaintainable or the fill
    derives `False`.
  * And it breaks §16's standing constraint head-on: the type-knowledge
    ialloc must update would have to live in something ialloc holds, and
    ialloc holds only the buffer.

**(c) THE WITNESS KEYED ON (slot, inum, type) WITH A POOL-GUARDED
REVOCATION — DEAD AS STATED, and its live half is what §17.6 builds.**  The
revocation INSTRUMENT is right; the KEY is wrong, and the arithmetic says so
in one line.  A revocable per-slot fact is a fractional-agree over the slot,
and re-setting one needs the whole unit.  The whole unit exists in exactly
three assemblies:
  * at a FREE slot, in `itable_body` — that is the recycle, i.e. §17's
    generation, i.e. exactly what (c) proposed to abandon;
  * at iput's `[+0x3c, +0x54)` window — §17.6's bump;
  * nowhere else.  At the FILL the filler holds the payload, the sleeplock
    deposit and its own share — the arm's `1/2` is in `ic_dep_half` and the
    table's `1/2 − qt` is behind the itable lock, so **a filler can never
    re-set a slot-keyed agreed value**.  At iput's +0x70 the table's
    `1/2 − qt` is gone (§17.3's dead escape 2, still dead).
So (c)'s "persistent fragment + revocation guarded by the pool" has no
instant at which the revocation can fire other than the two the generation
already marks — which makes (c) exactly §17's generation witness, and the
only question left is whether the SECOND of those instants is used.  §17.5
did not ask it.  §17.6 uses it.

**(b) RE-CHECK REF-1 AT +0x70** — unchanged, dead: xv6 performs no such
read.  Recorded in §17.5, not revisited.

**Also dead, enumerated so a seventh iteration does not re-derive them:**
  * *Put the pending in `ic_unloaded` rather than on `ic_payload`'s FALSE
    polarity.*  `ic_mid_arm` (`IcacheEscrow.v:724`) holds `ic_unloaded`
    directly and is sealed at `ProofIget.v:1167` (+0x72), six instructions
    before `live_slot_alloc` mints anything.  There is no pending in
    existence to put there — §17.5's MID deviation, replayed one level down.
  * *Bump at +0x3c instead of +0x54.*  It works on the nlink-undo path and
    destroys the free path: restating the LOADED payload at the new
    generation spends the fresh pending, and the +0x74 UNLOADED park then
    has none.  Bumping twice does not help — the second bump separates the
    arm's half from the payload again.  The bump must sit AFTER the free
    path commits (`ProofIput.v:1538`, +0x44 fall-through) and BEFORE the
    arm's half leaves iput's hand (`ProofIput.v:1714`'s `ic_close_out`
    deposit); `:1688` is the natural line and every premise is already
    named there.
  * *Bump at iput's `ip->ref--` (+0x7c), where the itable lock is back.*  By
    then the killer sequence's `iget` has run: `qt' = q + qn > q`, the
    assembly is `q + 1/2 + (1/2 − qt') = 1 − qn < 1`, and `live_gen_bump`'s
    premise fails.  **The +0x54 window is the last instant at which REF-1 is
    still knowledge.**
  * *Carry the type witness at the holders' own fractions, so the fd's copy
    dies with its share.*  Two ledgers then have to agree, and the pool
    cannot supply a fragment to `iget`'s cache-hit — the hit mints its
    reference out of the table's `1/2 − qt` while the payload (the only
    place a type could live) is in another thread's hand.  A leaked fragment
    wedges the next free path, and a `dfrac` discard makes the authority
    unreassemblable forever.
  * *A `□`-wand from liveness to the type.*  Still not timeless; still
    breaks the escrow outright (§17.1 (iv), unchanged).

#### 17.6.6 WHAT THIS RULING ASSERTS, AND THE ONE THING IT DOES NOT

Asserted and code-checked: the reachability of §17.6.1 (every step a proven
proof at a cited line); the resources in hand at `ProofIput.v:1688`; the
arm's half being in iput's hand and not in `ic_held`; `ic_mid_arm` holding
`ic_unloaded` directly; `ic_payload_excl`'s genericity in both gnames;
`wi_dinode`'s type preservation; `ic_empty_arm` at boot — and
`live_slot_regen` itself, COMPILED.

NOT checked by compilation, and the only step an implementing stage should
be ready to find different: `ic_open_held`'s two-gname generalisation
(argued from its proof text at `IcacheEscrow.v:1552`, which threads the
payload and refutes on cells, REF-1 and live mass).  If it turns out to
need the two equal, the fallback is to split it — an `ic_open_held_out`
used only at +0x54, with the +0x44 undo caller keeping today's single-gname
form — at the cost of one duplicated lemma and no design change.

### 17.7 RATIFIED (coordinator, 2026-08-12): §17.6 is the design

The second bump at iput's free window is adopted verbatim — the
pending/shot on ic_payload's polarities, live_slot_regen at
ProofIput's +0x54 checkout, the two-gname ic_open_held (fallback: one
duplicated lemma, pre-approved), SpecIlock's additive post and the
generation-premised iunlock family. The §17.6.6 unprobed step is
authorized to resolve either way. Execution: one stage, icache half
full-gated before inode_pay + SpecFilewrite/Proof/Link proceed.

### 17.8 §17.6 IS BUILT (fs-sysfile S3f, 2026-08-12): the whole ruling
### landed as written, and the ONE unprobed step resolved the easy way

Five iterations of design, and the implementation found nothing to argue
with.  Every mechanism in §17.6 (1)–(7) is in the tree and full-gated at
1033 `.vo`; the eight cones' assumption sets are unchanged.  What follows
is only what an implementer could not have read off §17.6.

**§17.6.6's UNPROBED STEP RESOLVED IN FAVOUR OF THE GENERALISATION.**
`ic_open_held` now takes `(g1 g2 : gname)` — `live_gen k (1/2) g1` for the
arm-half and `ic_payload … g2 v` for the payload — and the proof needed
**no change at all** beyond one explicit-argument line: the OUT branch's
two refutations use the count fragment and `live_whole_share_absurd`
(neither of which reads the arm's gname, because `iref_tok` carries its own
`live_frac`), EMPTY uses `ic_id_agree`, and HELD frames.  The pre-approved
fallback (a duplicated `ic_open_held_out`) is NOT needed and should be
struck.  iput's +0x44 nlink undo passes the two equal, as predicted.

**THE ONE THING §17.6 DID NOT SEE, and it is three lines.**  Putting the
pending on `ic_payload`'s FALSE polarity makes `ic_payload … g false` stop
being DEFINITIONALLY `ic_unloaded`, and `ic_open_held`'s MID branch was
refuting `ic_mid_arm`'s bare `ic_unloaded` by handing it to
`ic_payload_excl` at `v = false`.  That type-checks only under the old
definition.  Repair: `IcacheEscrow.ic_unloaded_size` (the `i_size` cell out
of a bare stock) and `ic_payload_unloaded_excl` beside `ic_payload_excl`,
both trivial, and `ic_payload_size`'s false case now goes through the
former.  §17.6.3 (1) was right that `ic_mid_arm` holds `ic_unloaded`
directly — it just did not follow the consequence into the refutation that
used the coincidence.

**WHERE THE FILL'S `ity_shoot` ACTUALLY WENT, and why it is ONE `iMod`.**
§17.6 said "on both payload-building branches of the `:974` split".  It is
cleaner one line earlier: the shoot goes immediately after `clearbody dn`,
inside the same `fupd_wp`, BEFORE the three-way pool split.  `dn` is fixed
by then (it is `ds !!! islot inum`, decoded off the buffer), the resulting
`#Hshot` is persistent and survives all three branches, and the type-0
branch simply carries a spent token into a `panic_wp_any` divergence, which
costs nothing.  Discharging it per-branch would have been two `iMod`s and a
duplicated context.

**`live_slot_regen` COMPILED AS THE PROBE PREDICTED**, first try, verbatim
from §17.6.3 (2) — and so did the `ga → ga'` rename over
`ProofIput.v:1688–2013` (§14.9's "one proof whose spec applications name
their arguments" held: five sites, all mechanical).

**THE CONSUMER END, measured.**  `SpecIlock`'s post gained
`ity_shot g (di_type dn)` (§17.6 (5)'s form, not §17's older
`∃ ty, … ∗ ⌜di_type dn = ty⌝` — the two are the same proposition and the
shorter one is directly usable by `ity_shot_agree`).  `ProofIlock` needed
FOUR lines beyond the `iMod`: `il_cont` and `il_epilogue` gain the
conjunct, the CACHED arm destructs it out of the payload it already had,
and the UNCACHED arm splits the pending out beside the
`inode_raw`/`ipool_shape` pair.  The five iunlock-family consumers were one
line each exactly as priced.

**`inode_pay`, and the one place its shape is not §17.6's.**  §17.6 wrote
the witness with `fc_wbool C` inside `inode_pay`, which has no `C`; the
built form takes the bool as a parameter, exactly as the pipe arm takes
`fc_wbool C` for `pipe_ref`:

    inode_pay γx Q g v wr q := cinv fileipN γx (inode_held_short v Q) ∗
                               cinv_own γx q ∗ inode_shr_held_gen v (q*Q) g ∗
                               ∃ ty, ity_shot g ty ∗
                                     ⌜wr = true -> bv_unsigned ty <> T_DIR_z⌝

with `file_payload` calling it at `(fp_ig pn) (fc_ip C) (fc_wbool C)`.
`inode_pay_alloc` had to change shape too, and the reason is worth
recording: the publisher cannot NAME the generation until it has shed the
reference, so the lemma now takes `inode_held_short v Q`,
`inode_shr_held_gen v Q g` and `ity_shot g ty` rather than a whole
`inode_held` — with `FileInvDefs.inode_held_shed_gen` supplying the first
two.  sys_open therefore sheds, reads `g`, discharges the witness against
ilock's postcondition, and only then installs the `fpnames`.

**THE RIPPLE OF `inode_pay` WAS TWO FILES**, as §17.6.4 predicted for the
payload and better than it predicted for the consumers: `ProofFileclose`
(two argument lists) and `ProofPipealloc` (four `MkFPNames`, for the new
field).  fileread, filestat, filedup and kexit carry the payload opaquely
and did not move a character — the audit §17 asked for, done by the build.

## 18. THE OP-WIDE SET LEDGER (the budget ruling, 2026-08-12): contracts
## go SET-FORM, because create is the same wall one level up

S3k's link-2 question ("cost function vs arm disjunction; one credit
vs two") is answered by looking one campaign stage ahead. create's
single transaction runs ialloc + iupdate×3 + dirlink×4; the sum of
their COUNTED budgets is far past MAXOPBLOCKS, but the op's distinct-
block set is ~5 (parent data, parent inode, child inode, bitmap,
maybe indirect). Absorption must therefore work ACROSS CALLS within
one op — a per-call counted premise can never express that, and any
per-call slack ruling would be answering the wrong question.

**RULING:**
1. **Budget-bearing fs contracts move to SET FORM at the seam**:
   writei (and, when S5 reopens them, dirlink/ialloc/iupdate's
   budget clauses) take `log_opS γ u Sb` in and return
   `log_opS γ u' Sb'` with an EXPLICIT bound on `Sb' ∖ Sb` (the
   blocks this call may have logged: its data-block window, the
   bitmap block, the file's indirect block, the inode block) and
   `u' ≥ u − (genuine allocations)`. The counted sconf form is
   DERIVED at Sb := ∅ for compatibility, exactly wp_balloc_gen's
   pattern. A caller (filewrite's loop; create's body) threads ONE
   set across all its calls and pays each distinct block once.
2. **bmap: ONE credit (the bitmap), arm-wise exact** — S3k proved the
   cross-iteration indirect credit buys only slack (10 → 7) at real
   contract complexity; under set-form the op-wide set bound is what
   callers consume, and 2B+2 ≤ 10 closes writei. Take (B)'s arm-wise
   exact set-growth per disjunct — the caller must COMPUTE its set,
   so exact growth per arm is the usable form; S3k's measured sizing
   says the arms discharge at one built-once epilogue.
   The two-credit machinery (log_amort_adopt/reserve, wi_fset) stays
   in WriteiBudget.v, proven, for the day slack is needed.
3. wi_cost_tight's non-monotonicity trap applies to every consumer
   re-check; the empty-range arm is audited explicitly.

Sequencing: S3l = links 2+3+4 under this ruling (bmap arm-wise
one-credit set-form; writei's premise = log_opS with the B+3-shaped
bound; dirlink re-discharged); S3m = ProofFilewrite + LinkFilewrite.
create's S5 brief inherits clause 1 for its op-wide set.


## 19. THE FRESH-TYPE WITNESS (fs-sysfile S5c, 2026-08-12): **STOP-AND-REPORT.**
## The fact is not obtainable anywhere inside the icache/region layer, and
## §17.6.1's own reachable trace is the reason — not the receipt algebra

S5b left `create` blocked on `di_type dn = ty` at its `ilock(ip)` and named
two exits, (A) a REF-1 bridge from the slot index to the inum index and (B)
a §16 re-opening.  This section works the coordinator's three-stability
derivation against the code, **refutes one stability outright, localises the
other two, and then refutes BOTH of S5b's exits with a trace this design
document already certified as reachable.**  Nothing in `iris/` moved.

The one-sentence finding: *the obstruction is not what the claimant could be
handed, it is WHEN — there is a sixteen-byte window in `ialloc`, between the
claim at +0x9a and the `iget` at +0xaa, in which the claimant owns no
resource naming the inum at all, and §17.6.1 shows the window is inhabited.*

### 19.1 THE THREE STABILITIES, CHECKED AGAINST THE CODE

**(i) TYPE-STABILITY — REFUTED AS A PROPERTY OF THE MODEL.**
`InodeRegion.ireg_write_au` (`InodeRegion.v:652`) is the ghost step behind
every `iupdate`, and its only constraint on the new record is
`bv_unsigned (di_type dn') <> 0` (`InodeRegion.v:659`).  So *any* holder of
`dinode_at γi inum dn` may retype `ty -> ty'` and the invariant is
re-established.  "No writer retypes an allocated inode" is true of this
TREE'S CALLERS — create's five inode stores are `ProofCreateParts.cr_setf`,
whose whole content is that "type, size and addrs do not move" — but callers
are not what an interleaving argument may quantify over.  In this
development the only thing constraining a concurrent hart is the invariants,
and the invariants permit the retype.  §17's story ("a generation sees at
most one fill, so agreement never crosses a re-type") is sound because the
GENERATION is bumped, not because the type is stable; the two must not be
conflated.  Repairable at one premise — §19.6 Part 1 — and it should be
repaired whether or not create is ever unblocked.

**(ii) NO-FREE-UNDER-REFERENCE — TRUE AND PROVABLE, BUT ONLY FROM create's
`iget` ONWARD.**  The free path's opener is
`IcacheEscrow.ic_open_auth_ref` (`IcacheEscrow.v:1108`), whose second
premise is `M !! k = Some (q, 1%positive)` (`IcacheEscrow.v:1112`).  A second
referrer makes the count at least 2 (`positiveR` has no zero, §14.5), so the
premise is unsatisfiable, and `IcacheInv.live_whole_share_absurd`
(`IcacheInv.v:1345`) refutes any further liveness slice at REF-1.  create's
own reference is therefore a complete block on anybody's free of that inum —
`ProofIput.v:1366` is the site.  Verified, and it is the one piece of the
coordinator's analysis that survives intact.

**(iii) GENERATION-STABILITY — TRUE, same window, same reason.**  A recycle
needs the slot free (`M !! k = None`, refuted by
`IcacheInv.iref_tok_free_absurd`) and the free-path regen
(`IcacheInv.live_slot_regen`, `IcacheInv.v:1400`) needs the whole liveness
unit, which (ii) denies.  So the `g` create's reference names is current at
its `ilock`.

**The trap is in the word "onward".**  (ii) and (iii) both start at create's
`iget`.  The claim is sixteen bytes earlier.

### 19.2 THE WINDOW, STATED SO IT IS NOT RE-DERIVED

`ProofIalloc.v:1451` runs `ireg_claim_au` at +0x9a; `ProofIalloc.v:1622`
calls `iget` at +0xaa.  Between them the claimant holds **nothing that names
the inum** — and that is not an oversight, it is §16's whole design:
`ireg_claim_au` (`InodeRegion.v:751`) takes no resource premise and pays out
`True`, because ialloc holds neither the itable spinlock nor any sleeplock
and the only serialiser it has is the BUFFER (§16.1/§16.2).  `SpecIalloc.v`
says so in its own header at line 83: the `ialloc_fresh ty` fact "says
nothing about the region's state at RETURN time — by then another hart may
already have locked the new inode."  That sentence is the whole of §19.

Every candidate mechanism, including the four new ones priced in §19.5,
needs one of: exclusive ownership of the region's element (S5b constraint 3),
a monotone snapshot plus a CURRENCY proof, or an invariant clause tied to
something exclusive the claimant owns.  All three want a resource at the
moment of the claim.  There is none, and there cannot be one — see §19.3(a).

### 19.3 §17.6.1 IS THE UNIVERSAL REFUTATION

The claim-and-hit sequence this document certified in §17.6.1 — every step
a proven instruction stream — puts a **live foreign reference on the claimed
inum's entry at the instant of the claim**, and then two referrers on one
entry at one generation:

> iput at +0x54 bumps the slot to `g'` under the itable lock, releases at
> +0x5c and has not yet run `ip->ref--`; the entry is CACHED at `ref = 1`;
> `ProofIalloc.v:1451` claims that very inum, buffer-serialised, with no
> cache lock; `ProofIalloc.v:1622`'s `iget` then takes the **HIT** arm and
> bumps `ref` to 2.

Four consequences, and together they close every door S5b left open:

**(a) The claim cannot TAKE anything, either.**  The one shape that would
have closed the window is a per-inum "no referrer exists" licence parked in
the region's type-0 arm, which `ireg_claim_au` would collect as it retags.
§17.6.1 has a referrer at that instant, so the licence would be in that
referrer's hand and `ireg_claim_au` would be **unprovable on a reachable
trace**.  A licence the claim may find missing is a licence that proves
nothing.

**(b) S5b's exit (A) is REFUTED.**  There is no "this entry has exactly one
referrer and it is me" witness to expose at ialloc's `iget`, because ialloc's
`iget` can take the HIT arm at `ref` 1 -> 2.  `SpecIget.v`'s header states
the design constraint that forbids even ASKING which arm ran: "Which of the
two happened is invisible to the caller, and must be: xv6's whole point is
that a second `iget` of a cached inode is indistinguishable from the first."
The index bridge S5b sized was the easy half; the uniqueness it was to carry
does not exist.

**(c) S5b's constraint (3) is FORCED, not a spelling accident.**  No content
of a claim-box arm can be made refutable at the ORDINARY fill, because the
ordinary fill's caller may legitimately hold a share of the very slot at the
very generation the claimant is using.  The assembly argument that would
have produced the contradiction — `live_whole_share_absurd` read positively,
§17.6.2's own move — cannot be assembled: create never holds the whole
holder mass, since its own `iget` may be the HIT.

**(d) The window's hazard is real and it is the FREE.**  As far as every
invariant knows, the foreign referrer may carve a share, `ilock` (its fill
reads `ialloc_fresh ty` and does not panic — the type is nonzero), and then
`iput`: the free test is `ref == 1 && nlink == 0`, and the claim's record has
`nlink = 0` by construction (`SpecIalloc.v:159`, `ialloc_fresh`; the header
at line 78 says "NLINK STAYS 0 until the caller's own `iupdate`").  Its REF-1
premise is satisfiable precisely because the claimant has no reference yet.
A third `ialloc` then re-claims the inum at `ty'`, and create's `ilock`
returns `ty'`.  With Part 1 (§19.6) landed, this FREE-AND-RECLAIM is the
*only* surviving hazard in the window — which is what makes the owed
obligation in Part 3 minimal and auditable.

### 19.4 WHAT THE FILL ALREADY GIVES, AND HOW BIG THE DEFICIT ACTUALLY IS

Worth recording because it shrinks Part 3's debt to sixteen bits.
`InodeRegion.ireg_withdraw` (`InodeRegion.v:924`) already pays out
`⌜fresh_shape (ds !!! islot inum)⌝` beside the fragment, and
`ProofIlock.v:1000` already destructs it into `Hfty/Hfsz/Hfad`.  So on the
claim-box arm the fill ALREADY knows size = 0, addrs = all-zero and
type <> 0 — S5a finding 1's "the other three dirlink premises all follow
from `di_size dn = 0`" is available with no new machinery the moment the arm
can be forced.  **The entire missing quantity is the sixteen-bit type
VALUE**, and the only frame in the system that holds it is ialloc's.

### 19.5 DEATH CERTIFICATES

**(a) "Nothing new — the ity/generation machinery already implies it."**
DEAD.  The shot's VALUE is decided by the fill, at the region's record and
nowhere else: `ProofIlock.v:1030` is the single `ity_shoot g (di_type dn)`,
placed there because it is "the only instruction in this kernel that knows
`di_type`".  create's only handle on that value is `SpecIlock.v:285`'s
`ity_shot g (di_type dn)` — the very term it is trying to evaluate.  Closing
by `IcacheRef.ity_shot_agree` (`IcacheRef.v:457`) needs a SECOND,
independent `ity_shot g ty`, and `ty` lives in one frame which cannot reach
the pending: the pending is parked inside `ic_payload`'s UNLOADED polarity
(`IcacheEscrow.v:538`), behind the entry's sleeplock, and `iget`'s recycle
parks it at +0x7c (`ic_close_mid_to_parked`) with no payout.  *And the
suggested repair — "strengthen `SpecIalloc`'s `dn'`-fact from documentation
to a stable fact" — is not available:* the facts at `SpecIalloc.v:286-288`
are about the region at CLAIM time, and §19.2/§19.3(d) make each of them
possibly false at RETURN time.  Strengthening a false statement is not a
retrofit.

**(b) "A type cell in the LIVENESS agree — `gname` becomes `gname × type`."**
DEAD, and by a sharper argument than "the type is unknown at the recycle"
(which is true — `live_slot_alloc`, `IcacheInv.v:493`, mints before any
bread).  Grant the strong form: let ialloc widen `iget` and supply `ty` at
the mint, so the recycle parks `ity_shot g ty` instead of `ity_pending g`.
The LATER fill must still re-establish the LOADED polarity's
`ity_shot g (di_type d)` at the record it withdrew — with the pending
already spent it can only AGREE, i.e. it must prove `di_type d = ty` against
the region, which is the original goal.  **A pre-shot generation makes the
fill circular; a post-shot one makes it uninformative.**  There is no third
timing.

**(c) "The escrow learns the inum -> slot key at ialloc's `iget`."**  DEAD on
§19.3(b).  The KEY is learnable — create does know its `k` — but the key was
never the missing thing; the UNIQUENESS was, and §17.6.1 exhibits its
failure.  Every packaging of premises (i)-(iii) into an additive
`wp_ilock_fresh` bottoms out at "and the arm is refuted because I am the
only referrer", which is false.

**(e) THE MARKER AS THE CARRIER — the strongest new candidate, and it still
dies.**  `InodeRegion.imark` (`InodeRegion.v:355`) is already the per-inum
EXCLUSIVE baton the tree lacks elsewhere, and its ghost value slot is
*unused* ("no marker entry is ever updated -- only moved",
`InodeRegion.v:288`).  Holding it proves a great deal: the fragment is in
the region, and no other cache entry or pool bundle holds this inum's record
(`imark_excl` :361 against `ipool_alloc`'s `dinode_at`, plus
`dinode_at_excl` :328).  It is genuinely the right shape.  It is
nevertheless unusable, for the reason S5b's table gave and this stage can
now make exact: **the marker's value can be written only by an agent holding
both the element and the authority — i.e. by `ireg_withdraw` (:924) or
`ireg_free_au` (:834), the fill and the free.  Never by `ireg_claim_au`,
which is the only agent that knows `ty`.**  Every mirror clause one might add
to `ireg_body` (marker value tracks the claim box, or the converse) is
unmaintainable at exactly the transition that matters.

**(f) A THIRD KEY SPACE INSIDE `γi`** — a claim ticket at a `claim_key z`
alongside `imark_key z`, which has the real virtue of dodging §16.5's
packaging argument entirely (no new gname, so `ireg_inv`'s signature — named
in THIRTY files — does not move).  DEAD on S5b's constraint (4), which this
stage can sharpen into three exhaustive cases: a ticket that a RE-CLAIM must
update is blocked by any outstanding copy, so `ireg_claim_au` becomes
unprovable; a ticket the re-claim ignores is stale-indistinguishable from the
live one; and a PERSISTENT ticket (`ghost_map`'s `↪□`) can never be
re-issued at all.

**(g) AN AMBIENT PER-INUM ONE-SHOT** — `icfg` gains a `Z -> gname` array so
the generation needs no storage, and the authority parks in `ireg_body`
without touching any signature.  The cleanest algebra of the four.  DEAD on
CURRENCY: the fill shoots the CURRENT per-inum generation, and create's proof
that its generation is still current is exactly "no free since MY claim",
which is §19.3(d)'s hazard.  Generations solve staleness only where a
CURRENCY resource exists — §17.6's slot generations have `live_gen` and the
mass ledger; an inum has nothing, because the free that would bump it is
slot-indexed.

**(h) THE VIRGIN-RECORD DISTINCTION** — block the thief's FREE instead of the
thief's REFERENCE, by refusing `ireg_free_au` on a never-committed claim box.
DEAD, and instructively: a legitimately freed inode's record at
`ireg_free_au` is post-`itrunc` — type <> 0, size 0, addrs zero, nlink 0 —
which is LITERALLY `fresh_shape` (`InodeRegion.v:270`) and literally
`ialloc_fresh ty`'s shape.  **The region cannot tell a virgin claim box from
a truncated corpse.**  A "committed" token minted by an ordinary `iupdate` is
mintable by the thief too, since it holds the metadata cells and may write
any nlink it likes.

### 19.6 THE RULING

Every candidate reduces to ONE proposition, and it is not an icache fact:

> **NO THREAD OTHER THAN THE CLAIMANT CAN NAME A JUST-CLAIMED INUM.**

In xv6 that is true because a free inum appears in no directory and `iget`'s
only two inum sources are `dirlookup` and `ialloc` itself.  In this
development it is unavailable: `SpecIget` is stated for an arbitrary `inum`
(deliberately — see its header's premise discussion), and `DirView.dir_ok`
(`DirView.v:855`) says only that a directory's live records name inums the
region COVERS (`dir_inums_ok`, :824), never that they name ALLOCATED ones.
`SpecIlock.v:110` already flagged the gap in the abstract — "a caller premise
'this inum is allocated' would be undischargeable today (allocatedness is
directory-structure knowledge — namei/ialloc, future work)".  §19 is the
bill for that sentence.

**PART 1 — LAND NOW (stage-sized, independently correct, no ruling needed).**
`ireg_write_au` gains the premise
`di_type dn' = 0 \/ di_type dn' = di_type dn`, making §19.1(i) a THEOREM of
the region rather than a claim about callers.  The disjunct is what iput's
free path takes; everybody else takes the equation.  This is worth doing on
its own merits: it removes a latent gap in §17's whole type story, and it
reduces §19.3's residual hazard from {retype, free-and-reclaim} to
{free-and-reclaim} alone, which is what makes Part 3's debt one line long.

**PART 2 — THE DISCHARGE (project-sized, NOT this campaign's).**  The
allocatedness invariant: `DirView.dir_ok`'s conjunct strengthened from
"covers" to "allocated", a matching premise on `SpecIget`, and the
preservation obligation discharged in every function that writes a directory
(`dirlink`, `create`, `sys_unlink`) plus the boot layer (`IcacheBoot`).  This
is `fs-namei`'s and `fs-inode`'s territory, it re-opens §15, and it is the
only thing that discharges Part 3.

**PART 3 — THE UNBLOCK (what S5d does).**  create takes the fact as a
THREADED PURE HYPOTHESIS, exactly as `SpecIalloc` takes
`SpecPrintkGen.printk_gen_contract` and every sleeping contract takes
`SpecPanic.panic_wp_any`: an `ilock_fresh_contract`-shaped `Prop` premise on
`wp_create_sconf_body`, so that `Print Assumptions` stays at the standing six
and **every consumer of create sees the debt in its own statement**.  This is
the tree's established shape for "true of the kernel, not yet provable from
the invariants", and `SpecBalloc.v`'s header ("READ THIS BEFORE TRUSTING THE
STANDING SIX") is the precedent to imitate verbatim.

*The recommended statement of the threaded contract* is an ADDITIVE
`wp_ilock_fresh` whose post adds `⌜dn = ialloc_fresh ty⌝` — not merely
`di_type dn = ty`.  Three reasons: it is what the kernel actually
guarantees (create's `ilock` is the first fill and reads exactly the claim's
record); it is what the fresh arm already produces internally (§19.4); and
`ProofCreateParts.cr_made_setf` already proves
`cr_setf (ialloc_fresh ty) mj mn 1 = create_made ty mj mn`, so the `made`
arm of the frozen `SpecCreate` falls out with no further work and all four
`dirlink` premises are discharged at once.

**WHAT THIS COSTS THE FROZEN CONTRACT.**  S5a's "nothing in `SpecCreate.v`
moves under any of the three rulings" does not survive Part 3: the contract
gains one `Prop` premise.  That is a one-line, additive, purely-hypothetical
change and it does not touch the arms, the budget or the return shape — but
it is a change, and the freeze note should be amended rather than quietly
broken.

### 19.7 BLAST RADIUS, PRICED PER FILE

*Part 1 (recommended for the next implementation stage):*

| file | change |
|---|---|
| `InodeRegion.v` | one premise on `ireg_write_au` (:652); the proof body does not move — the premise only travels |
| `SpecIupdate.v` | the same premise on `wp_iupdate_gen_body` / `wp_iupdate_cred_body`; both, since S5b split them |
| `ProofIupdate.v` | pass it at the one `ireg_write_au` call site |
| `ProofIput.v` | discharge by the `= 0` disjunct (the `ip->type = 0` flush) |
| `ProofItrunc.v` | discharge by the equation (`ip->size = 0` only) |
| `ProofWritei.v` | discharge by the equation (`wi_dinode` moves size/addrs) |
| `LinkIupdate.v` and the two cones | rebuild only |

Nothing else names `ireg_write_au` (`SpecLogWrite.v` mentions it in prose
only).  No signature that 30 files carry (`ireg_inv`, `ic_escrow`,
`dinode_at`) is touched, so §16.5's packaging argument is respected.

*Part 3:* `SpecCreate.v` (+1 premise), `ProofCreate.v` (uses it at +0xb4),
`LinkCreate.v` (threads it).  Zero files outside create's own three.

*Part 2* is not priced here; it is a project brief, not a retrofit.

### 19.8 WHAT S5d MAY BUILD WITHOUT ANY RULING

Six of create's eight arms do not need the fact at all, and the walk order
S5a prescribed (back to front) reaches them first: the epilogue join at
+0x74, `fail:` (+0x11c..+0x132), the two `iunlockput`-and-return tails
(+0x76, +0xc6) and the `found` arm.  Only the two `made` arms need it — the
mkdir arm at its `dirlink(ip, ".")` and the T_FILE arm at sys_open's fd-type
witness (S5a finding 1's second bullet).  So S5d is a real stage under any
ruling: build the six, take Part 1, and gate the two `made` arms behind the
Part 3 hypothesis.

### 19.6 RATIFIED (coordinator, 2026-08-12): §19's three parts

Part 1 lands with S5d (the type-stability disjunct on ireg_write_au —
six files, no signature moves). Part 3 unblocks create: the fresh-
record fact rides as a NAMED assumed Prop premise (ialloc_fresh_fill,
spelled ⌜dn = ialloc_fresh ty⌝ at create's fresh ilock), the
printk_gen_contract precedent — visible in contract text, threaded
by sys_open/mkdir/mknod, accepted at the adequacy client, RETIRED by
Part 2. Part 2 (the allocatedness invariant) is a recorded frontier
project beside crash recovery and the image-wf discharge. SpecCreate
gains exactly the one additive premise; its freeze note is amended
accordingly.

### 19.7 §19.6 PART 3 SUSPENDED (coordinator + user, 2026-08-12): the
### assumed Prop may be FALSE on a reachable trace

The user challenged the named-assumption route, and following the
token alternative to its end broke the assumption itself. Post-Part-1
the type changes only by free or re-claim, so a token must block the
WINDOW-FREE — but the stale holder's ilock/iunlockput inside ialloc's
sixteen-byte window is machine-reachable (its iput sees ref==1,
valid-by-its-own-fill, nlink==0 — ialloc leaves nlink 0), and a
resource cannot forbid a machine-reachable step; it only wedges the
escrow on the stale holder's proof (S5b's constraint 3, generalized:
ANY blocker of a reachable step is dead, whether it blocks a fill or
a free). After the window-free, a competing ialloc can RE-CLAIM the
inum at another type: the fresh fill then sees ty₂ ≠ ty, so
⌜dn = ialloc_fresh ty⌝ is falsifiable, not merely unprovable — a
different beast from panic/printk's unproven-but-true contracts.

Consequences: (a) SpecCreate stays frozen at S5a's form — no premise;
(b) the expected re-ruling (S5e, after the in-flight walk's
reachability read): create's made arm WEAKENS to the existential type
with sys_open reading the actual type from its own ilock witness —
the §15 precedent (make the ugly arm honest, don't assume it away);
(c) if the object code genuinely admits the hijack (create building
on an inum a racer re-typed), kernel-defects.md gains its first
entry: O_CREATE can hand a writable fd to an inode a concurrent
mkdir made a directory — exactly the unsoundness §17 guards, now
guarded by sys_open checking what it SEES rather than what it
assumed. Part 2 (allocatedness) remains the eventual cure.
