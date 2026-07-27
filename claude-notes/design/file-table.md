# Design: the open-file table (`struct file` / `ftable`)

`kernel/file.c`'s `ftable` is xv6's second reference-counted object pool (after
`bcache`, and alongside `itable`), and it is the one with the most complicated
sharing: the same `struct file` can be named by several file descriptors of one
process, by several processes, and by several CPUs executing syscalls at once.
This file fixes the resource model those patterns are proved against.

Rocq: geometry, the algebra and the predicates live in `FileInv.v`; the
per-function specs are `SpecFile*.v` / `ProofFile*.v` / `LinkFile*.v` in the
usual spec-module shape (`design/spec-modules.md`), with the decode layer in
`WpFileallocDecode.v`.

The fractional sharing this design rests on is generic, so it lives in
`RiscvPtsto.v`, not here: `mem_pointsto_agree` / `mem_pointsto_frac_split`,
their byte-window forms `mem_bytes_agree` / `mem_bytes_frac_split`, and the
`word{2,4,8}_pointsto_{agree,frac_split}` lifts — plus `word2_pointsto` (`↦₂`)
itself, for `short major`. Any other reference-counted kernel object
(`struct inode`, `struct buf`) wants exactly these.

## Geometry

```c
struct file { enum {FD_NONE,FD_PIPE,FD_INODE,FD_DEVICE} type; int ref;
              char readable; char writable; struct pipe *pipe;
              struct inode *ip; uint off; short major; };
struct { struct spinlock lock; struct file file[NFILE]; } ftable;
```

`ftable`@0x80022460, lock@0 (24 B), `file[0]`@`ftable+0x18`, `sizeof(struct
file)` = 40 (the loop's `addi s1,s1,40`), NFILE = 100 — and one past the last
entry is `&disk`@0x80023418, which is the literal end pointer filealloc's scan
compares against. Field offsets, all corroborated by the disassembly
(`lw a5,4(s1)` / `sw a5,4(s1)` for `ref`):

| field | off | width |
|---|---|---|
| `type` | 0 | 4 |
| `ref` | 4 | 4 |
| `readable` | 8 | 1 |
| `writable` | 9 | 1 |
| `pipe` | 16 | 8 |
| `ip` | 24 | 8 |
| `off` | 32 | 4 |
| `major` | 36 | 2 |

`fnode k := acur (KernelSyms.ftable + 24) 40 k` (`ArrCursor.acur`, as for
`bnode`/`inode_lock`), and `a_ftype`/`a_fref`/… are the field addresses in the
exact `add_vec … (sign_extend' 64 imm)` form the instructions compute.

## What protects what

Three different disciplines, and the model has to keep them apart:

1. **`ref` is protected by `ftable.lock`.** Every core's `filealloc` scans the
   `ref` field of *every* entry, so no entry's `ref` cell can belong to a
   reference holder — all NFILE of them live in the lock's resource.
2. **`type`/`readable`/`writable`/`pipe`/`ip`/`major` are effectively immutable
   while `ref > 0`,** and are read with no lock at all (`fileread` reads
   `f->type`, `f->readable`, `f->ip`). The caller of `filealloc` (`sys_open`,
   `pipealloc`) writes them *after* `filealloc` returns and *without* the lock;
   that is safe only because `ref == 1` and the only other reader of a
   non-owned entry is filealloc's scan, which touches `ref` alone.
   `fileclose` writes `type = FD_NONE` under the lock, at `ref == 0`.
3. **`off` is mutable and protected by `ip->lock`** (the inode sleeplock) when
   `type == FD_INODE`; for `FD_PIPE`/`FD_DEVICE` it is dead (note: it is *not*
   zero — `sys_open` only assigns `f->off = 0` on the `FD_INODE` path, so a
   device file inherits whatever the previous generation of the slot left).

Discipline 2 is the interesting one: it is exactly a reference-counted
read-share that becomes writable again once the count drops to zero.

## The core: a per-slot reference-count auth

```coq
Definition fileUR : ucmra := authUR (gmapUR nat (prodR fracR positiveR)).
```

One `gname` for the whole table. The authority `● M` lives in the ftable lock's
resource; `M !! k = Some (q, n)` means "slot `k` has `n` outstanding references
which between them hold fraction `q` of the slot's content", and `k ∉ dom M`
means the slot is free. A single reference is the fragment

```coq
Definition fref_tok γ k q : iProp Σ := own γ (◯ {[ k := (q, 1%positive) ]}).
```

The two components are what make the whole thing work together:

- the **count** is the physical `f->ref`, so the code's `ref == 0` /
  `--ref > 0` tests are directly about the ghost state;
- the **fraction** is a real `dfrac` on the content points-tos, so a reference
  holder can *read* the immutable fields with no lock and no invariant opening,
  and fractional agreement automatically gives every holder the *same* values —
  no separate `agree` ghost is needed.

Because `fracR` has no unit and `positiveR` has no zero, `Some (q,1) ≼ Some
(qt,n)` forces `n = 1 → q = qt`: **the holder of the only reference holds the
full fraction, hence write access.** That single fact is what licenses
`sys_open`'s unlocked initialization and `fileclose`'s `f->type = FD_NONE`.
This is RustBelt's `Arc` algebra; the `frac`-vs-`count` pairing is not
decoration, it is the whole trick.

### The content record and the reference predicate

```coq
Record fcontent := { fc_type : mword 32; fc_readable : mword 8;
                     fc_writable : mword 8; fc_pipe : mword 64;
                     fc_ip : mword 64; fc_major : mword 16; fc_off : mword 32 }.

Definition file_fields k dq C : iProp Σ :=          (* the 7 non-ref cells *)
  a_ftype k ↦₄{dq} fc_type C ∗ a_freadable k ↦ₘ{dq} fc_readable C ∗ … .

(* THE predicate: holding one reference on file slot [k]. *)
Definition file_ref γ k q C : iProp Σ :=
  fref_tok γ k q ∗ file_fields k (DfracOwn q) C ∗ file_payload q C.
```

`file_ref` is the unit of ownership everywhere: a process's `p->ofile[fd]`, a
syscall's local `struct file *f`, `pipealloc`'s two half-built files. Its
properties:

- **not persistent, not duplicable** — duplication is `filedup`, which must run
  under the lock and bump the physical count;
- **agreement**: `file_ref γ k q1 C1 ∗ file_ref γ k q2 C2 ⊢ ⌜C1 = C2⌝` (from
  fractional points-to agreement) — so two fds onto the same file see the same
  `type`/`ip`/… , for free;
- **`file_ref γ k 1 C` is writable** — the exclusive/uninitialized state.

### `file_payload`: the thing the file is a reference *to*

A `struct file` owns a reference on its pipe or its inode, created when the
file is initialized and consumed by `fileclose`'s `pipeclose`/`iput`. Rather
than parking it in the ftable invariant (which would force a "publish" ghost
step under a lock the code does not hold at initialization time), make it
**fractional too**, indexed by the type:

```coq
Definition file_payload q C : iProp Σ :=
  match fc_type C with
  | FD_PIPE            => pipe_ref (fc_pipe C) q
  | FD_INODE|FD_DEVICE => inode_ref (fc_ip C) q
  | FD_NONE            => emp
  end.
```

`inode_ref`/`pipe_ref` are themselves reference-counted objects with the same
shape, so a fraction of one is still a witness that the object is alive (enough
to `ilock`), and the last file reference (`q = 1`) recovers the whole thing to
hand to `iput`. `sys_open` supplies the `inode_ref` it got from
`namei`/`create` at the moment it writes `f->ip`; nothing has to be deposited
anywhere.

This is why the free state pins `fc_type = FD_NONE`: a free slot then carries
no payload, which is exactly the real xv6 invariant (`fileclose` writes
`FD_NONE` before releasing, and the BSS starts zeroed).

## The ftable lock invariant

```coq
Definition fslot (M : gmap nat (Qp * positive)) (k : nat) : iProp Σ :=
  match M !! k with
  | None        => a_fref k ↦₄ 0 ∗ ∃ C, ⌜fc_type C = FD_NONE⌝ ∗ file_fields k (DfracOwn 1) C
  | Some (q, n) => a_fref k ↦₄ (word32 (Zpos n)) ∗ ⌜Zpos n < 2^31⌝ ∗ file_rest k q
  end.

Definition file_rest k q : iProp Σ :=      (* the fraction NOT handed out *)
  match (1 - q)%Qp with
  | Some q' => ∃ C, file_fields k (DfracOwn q') C
  | None    => emp                          (* q = 1: all of it is out *)
  end.

Definition ftable_res γ : iProp Σ :=
  ∃ M, own γ (● M) ∗ ⌜∀ k, is_Some (M !! k) → (k < NFILE)%nat⌝ ∗
       [∗ list] k ∈ seq 0 NFILE, fslot M k.

Definition is_ftable γl γ : iProp Σ :=      (* persistent *)
  is_lock γl ftable_addr "ftable" (ftable_res γ).
```

The `Qp.sub`-shaped `file_rest` is the price of letting a lone holder be
writable; `q = 1` is the "everything is out" case and the invariant then holds
nothing but the `ref` cell. Everything else about a slot — all 36 content bytes
— is *outside* the lock, which is precisely why `fileread` needs no lock.

### The three ghost steps (all under `ftable.lock`)

They are stated in `FileInv.v` as pure `own`-level updates plus the points-to
regrouping, so the function proofs never touch the algebra. **All three are
proved** — they are what validates the algebra, and the `n≥2` close case is
the one that dictated its shape, so prove any variant of them before building
on it:

| step | code | update |
|---|---|---|
| `file_alloc_step` | filealloc: `ref==0` → `ref=1` | `M !! k = None ⇝ Some (1,1)`; invariant's full `file_fields` goes out as `file_ref γ k 1 C` |
| `file_dup_step` | filedup: `ref++` | `(qt,n),(q,1) ⇝ (qt,n+1),(q/2,1)·(q/2,1)`; splits the caller's points-to fraction in half |
| `file_close_step` | fileclose: `--ref` | `n≥2`: `(qt,n),(q,1) ⇝ (qt-q,n-1),ε`, the invariant absorbs `q` back into `file_rest`. `n=1`: validity forces `q=qt=1`, `Some(1,1),Some(1,1) ⇝ None,None`, and the closer walks away with fraction 1 of everything (so it can write `FD_NONE`) plus the whole `file_payload` for `pipeclose`/`iput` |

The `n≥2 → n-1` case is the one that fixes the shape of the algebra: the
returned fraction has to have somewhere to go, which is why the authority's
frac component tracks *outstanding* fraction rather than being pinned at 1.

## How the sharing patterns come out

- **Two cores in `filealloc`.** Serialized by `ftable.lock`. Each takes a slot
  whose `ref` is 0 and sets it to 1 before releasing, so they cannot collide.
  The scan reads *other* slots' `ref` cells — legal, they are all in the lock's
  resource — and never touches another slot's content cells, which is why the
  scan needs no fraction of anything.
- **A core initializing a fresh file while another core scans.** The scanner
  sees `ref == 1` and skips; the initializer holds `file_ref γ k 1 C` and hence
  fraction 1 of the content, so its unlocked stores are justified. The two
  disjoint resources (the `ref` cell in the lock, the content fields with the
  owner) are exactly xv6's argument, mechanized.
- **One file, many fds, many processes.** Each `p->ofile[fd]` holds its own
  `file_ref γ k q_i C` with an arbitrary positive `q_i`; the count in `M` is the
  number of such tokens and equals the physical `ref`. The proc's fd table is
  `[∗ list] fd < NOFILE, (ofile[fd] ↦₈ 0 ∨ ∃ k q C, ofile[fd] ↦₈ fnode k ∗
  file_ref γ k q C)`.
- **`fork`.** One `filedup` per open fd halves the parent's fraction and bumps
  the count; parent and child each end with a genuine `file_ref`.
- **`sys_dup`.** `fdalloc(f)` stores the pointer *before* `filedup(f)` runs, so
  there is a window with two `ofile` entries and one reference. This is not a
  hole: the fd table is thread-local (no lock, only the running thread reaches
  it), so `sys_dup` is proved as one unit whose intermediate state holds a bare
  `ofile[fd] ↦₈ fnode k` and whose `filedup` restores the invariant before the
  syscall returns.
- **`argfd` / a syscall using a file.** No reference is taken: the syscall
  borrows the process's own `file_ref` out of the (thread-local) fd table for
  the duration. `fileread`/`filewrite`/`filestat` therefore take
  `file_ref γ k q C` at an arbitrary `q`.
- **`exit`.** `fileclose` per fd; each returns its fraction, the last one gets
  `q = 1` and the payload.
- **`fileclose` racing a `fileread` on the same file.** Impossible by
  construction: reaching `n = 0` requires holding the only fragment, and any
  concurrent reader would be a second fragment.

## `off` — staged

`off` is the one field that is neither lock-free-immutable nor ftable-protected,
and it is the only genuinely hard part of the model. It is **not** needed by
`fileinit`, `filealloc`, `filedup`, `fileclose`, `filestat`, `sys_open` or
`pipealloc` — only by `fileread`/`filewrite` on an `FD_INODE` file.

**Stage 1 (what `FileInv.v` does today).** `off` is `fc_off`, an ordinary
fractional content field. This is sound and is exactly right for the free and
exclusive states: `sys_open`'s `f->off = 0` and `fileclose`'s `ff = *f` both
run at `q = 1`. It is simply not *strong* enough for `f->off += r` under a
shared reference, where the holder has only `q < 1`.

**Stage 2 (for `fileread`/`filewrite`).** Replace `fc_off` by a borrow protocol.
The obligations are: (a) a holder of *any* positive fraction plus `ilocked ip`
(with `fc_ip C = ip`) may take the cell out across several instructions;
(b) the exclusive holder (`q = 1`) must be able to take it back with **no**
inode lock at all, because `fileclose` never holds `ip->lock`. Sketch:

- a permanent per-slot global invariant `inv (offN.@k) (resident ∨ checked-out)`
  where *resident* is `∃ v, a_foff k ↦₄ v` and *checked-out* parks the
  borrower's `ilocked ip` token;
- exclusion between borrowers is `ilocked ip`'s own exclusivity (two borrowers
  of the same file, or of two files sharing an inode, would both need it);
- the parked token must be **fungible**, or the borrower cannot prove that what
  it takes back on return is what it put in. That is why the marker is
  `ilocked ip` and *not* a slice of the borrower's own fraction;
- to let the `q = 1` holder refute a stale checked-out state, the checked-out
  disjunct also parks one unit of a **separate, fungible liveness counter**
  (`authR (gmapUR nat natR)`, authority in the ftable invariant, one `◯{[k:=1]}`
  per reference). At `n = 0` the authority is `0`, so an outstanding `◯{[k:=1]}`
  is a contradiction and the cell must be resident.

Everything about stage 2 is confined to `file_off`/`file_fields`; keep `off`
factored out of the other six fields in `FileInv.v` so the swap touches one
definition rather than every caller.

## Open items

## Why `f->ref++` cannot overflow: the fd-slot resource

`filedup` increments `f->ref` with no check, and the invariant needs every
count to stay a faithful `int` (`< 2^31`) — that is what makes `ref == 0` mean
"free" and what the sign-extended branch tests read. **No unconditional
increment preserves a finite bound**, so this is not something `filedup` can
re-establish on its own, and it is not a pure fact about the table either.

It is a *whole-kernel conservation law*, and a slightly subtle one:

> every holder of a reference is a file descriptor of some process; there are
> at most `NPROC` processes with at most `NOFILE` descriptors each; that
> product is ~1000, nowhere near 2^31.

Nothing in `file.c` enforces it, so it is carried as a resource — `FdSlots.v`:

- `fd_slot γs` is one unit of "somewhere to put a file reference". The supply
  is fixed at `FDSLOTS = NPROC * (NOFILE + 4)` and minted once at boot by
  `fd_slots_alloc`; the `+4` is the per-process allowance for references a
  syscall holds in *locals* before installing them in a descriptor (`sys_open`
  one, `pipealloc` two).
- `ftable_res` holds `fd_slots_auth γs` **and**, per referenced slot,
  `fd_slots γs (Pos.to_nat n)` — one unit per outstanding reference. A
  descriptor naming a file has given its slot away and gets it back on close.
- The bound then needs no arithmetic and no ghost update at all: the units for
  one slot are literally `◯ n`, `◯ n ⋅ ◯ 1 = ◯ (S n)`, and auth validity
  against `● FDSLOTS` gives `n ≤ FDSLOTS`. `fd_slots_no_overflow` packages
  that as `Z.pos n < 2^31 ∧ Z.pos (n+1) < 2^31`.

So `filedup` **requires** an `fd_slot` and `fileclose` **returns** one;
`filealloc` consumes one too (it creates the first reference), and
`pipealloc` two. The `⌜Z.pos n < 2^31⌝` conjunct inside `fslot` is the *local
projection* of the bound — what a consumer walking the table actually needs,
so it does not have to reach for the authority at every slot. It is not an
independent assumption: every operation that changes a count re-derives it.

**Do not shortcut this with an axiom.** The missing step,
`∀ n, Z.pos n < 2^31 → Z.pos (Pos.succ n) < 2^31`, is *false* at
`n = 2^31 - 1`; asserting it makes every proof in every file that transitively
requires it vacuous. (A "dup budget" pool with a lifetime cap and no returns
was also tried and is strictly worse — it bounds calls rather than live
references, and its supply has no principled source.)

 **`lh`/`sh` leaves.** `↦₂` exists but nothing loads or stores a halfword yet;
  `sys_open`'s `f->major = ip->major` will need the leaves.
- **The next function.** `filealloc` is proven (`ProofFilealloc.v` /
  `LinkFilealloc.v`); `filedup` and `fileclose` are the natural next two —
  their ghost steps already exist and are proved, so the work is the
  instruction-level proof plus, for `filedup`, the overflow premise above.
- **Generalize the pool.** `bcache` (`b->refcnt` under `bcache.lock`), `itable`
  (`ip->ref` under `itable.lock`) and `ftable` are the *same* object: an array
  of slots with an int refcount under one spinlock, contents shared read-only
  while referenced and exclusive at count 0/1. Once `filealloc`/`filedup`/
  `fileclose` are proven, lift `FileInv.v`'s algebra and the three ghost steps
  into a `RefPool.v` parameterized by geometry + content predicate + payload,
  and re-instantiate it for the other two rather than cloning.
