# Design: `struct proc` — sharing disciplines and the resources for them

What exists today (`ProcGeom.v`, `SchedCtx.v`) models exactly the five fields
the yield/sched/sleeplock effort needed: `lock`, `state`, `chan`, `pid`,
`context`. Everything else in the 360-byte structure is unowned. This note
analyses how the *whole* structure is shared and fixes the resources that
should carry it, so that syscall-level proofs (`sys_getpid`, `sys_sbrk`,
`sys_dup`, `sys_open`, `fork`, `exit`, `wait`, `kill`) have something to
stand on.

Companion notes: `design/kernel-proofs.md` (the swtch/scheduler protocol as
built), `design/file-table.md` (the `struct file` reference discipline this
reuses verbatim), `completed/yield-sched.md` (how `proc_lock_res` came to be).

## Geometry

All offsets corroborated by disassembly (`addi a5,a0,208` + stride 8 × 16 in
`fdalloc`; `ld a1,72(a0)` / `ld a0,80(a0)` in `growproc`; `ld a0,336(s2)` /
`sd s1,336(s2)` in `sys_chdir`; `lw a5,48(a0)` in `acquiresleep`).
`sizeof(struct proc)` = 360 = `ProcGeom.proc_size`. ✓

> **Caveat on where to read instructions.** `xv6-riscv/kernel/kernel.asm` is
> *stale* relative to `kernel-rocq/KernelInstrs.v` — function symbols are
> shifted by 0xe. Struct offsets are unaffected (they are layout, not
> addresses), so the corroboration above stands, but any *instruction word or
> address* must come from `KernelInstrs.v` / `KernelSyms.v`, which are what the
> proofs actually build against.

| field | off | width | resource |
|---|---|---|---|
| `lock` (spinlock: `locked`@0, `name`@8, `cpu`@16) | 0 | 24 | `is_lock` / `p_lkcpu` |
| `state` | 24 | 4 | `proc_lock_res`, top level |
| `chan` | 32 | 8 | `proc_lock_res`, top level |
| `killed` | 40 | 4 | `proc_pub` |
| `xstate` | 44 | 4 | `proc_pub` |
| `pid` | 48 | 4 | ½ in `proc_pub`, ½ in `proc_priv` |
| `parent` | 56 | 8 | ❌ (belongs to `wait_lock`) |
| `kstack` | 64 | 8 | `is_kstack` (persistent) |
| `sz` | 72 | 8 | `proc_priv` / `proc_dormant` |
| `pagetable` | 80 | 8 | `proc_priv` / `proc_dormant` |
| `trapframe` | 88 | 8 | `proc_priv` / `proc_dormant` (pointer only) |
| `context` | 96 | 112 | `own_ctx` / `proc_ctx` |
| `ofile[16]` | 208 | 128 | `proc_ofiles` (a `file_ref` per non-null slot) |
| `cwd` | 336 | 8 | `proc_priv`; `cwd_ref` still `emp` |
| `name[16]` | 344 | 16 | `proc_priv` |

`NOFILE = 16`, `NPROC = 64` (`param.h`).

## The five sharing disciplines

The header comments in `proc.h` name three groups. The code has five, and the
difference matters — proc.h's "private to the process, so p->lock need not be
held" group is *not* uniformly private.

### 1. Lock-protected and genuinely mutable — `state`, `chan`, `killed`, `xstate`

Every core touches these on procs it does not own: `kill()` walks all 64 and
writes `killed`, `wakeup()` walks all 64 and compares `chan`, `scheduler()`
walks all 64 and reads/writes `state`, `wait()` reads a child's `xstate`.
Full ownership, always resident in the lock's resource. This is the group
`proc_lock_res` already covers (`state`, `chan`); `killed` and `xstate` join
it unchanged.

### 2. Lock-protected but immutable-while-allocated — `pid`

`allocproc` writes it once under the lock; after that nobody writes it. But it
is read two ways: by *other* cores under `p->lock` (`kill()`'s scan, `wait()`'s
`pp->pid`) and by the owning process with **no lock at all** (`sys_getpid`,
`acquiresleep`/`holdingsleep` — `jal myproc; lw a5,48(a0)`).

This is precisely `design/file-table.md`'s discipline 2: a
reference-counted read-share that becomes writable again when the last holder
goes away. And exactly as there, no ghost algebra is needed — a **points-to
fraction** gives agreement for free (`word4_pointsto_agree`). Half stays in the
lock resource so `kill()` can always read it; half travels with the running
process. `allocproc` reunites both halves in the `UNUSED` arm and so may write.

### 3. A different lock — `parent`

`wait_lock`, not `p->lock`, and it is read/written *across* processes
(`exit()` reparents its children onto `initproc`). Needs its own global lock
resource holding all 64 cells; keep it out of `proc_lock_res` entirely, or the
lock ordering `wait_lock` → `p->lock` becomes unstateable.

### 4. Write-once at boot — `kstack`

`procinit()` sets `p->kstack = KSTACK(p - proc)` and nothing ever writes it
again. `allocproc` reads it (`context.sp = p->kstack + PGSIZE`). This wants
to be **persistent**: `↦₈□` at the value `KvmMap.kstack_va j`. No threading,
readable from anywhere, and it ties the proc slot to the page-table world's
existing `kstack_va`/`kstack_vpn` facts.

### 5. Owned by whoever is *running* the process — `sz`, `pagetable`, `trapframe`, `ofile`, `cwd`, `name`

This is the interesting group, and the one with no home today. Almost every
syscall touches it with no lock held at all:

```
sysproc.c:48   addr = myproc()->sz;              sysproc.c:62  myproc()->sz += n;
syscall.c:15   if (addr >= p->sz || …)           syscall.c:18  copyin(p->pagetable, …)
syscall.c:142  num = p->trapframe->a7;           syscall.c:146 p->trapframe->a0 = …
sysfile.c:28   f = myproc()->ofile[fd]           sysfile.c:47  p->ofile[fd] = f;
sysfile.c:428  iput(p->cwd);                     sysfile.c:430 p->cwd = ip;
```

Unlocked is sound because only the running thread reaches them — but "the
running thread" is not the same as "state == RUNNING". Three other parties
touch this group:

- **`fork()`** mutates the *child's* `sz`/`pagetable`/`trapframe`/`ofile`/`cwd`/
  `name` while the child is `USED` and the parent holds the child's lock.
  `allocproc` likewise writes `trapframe`/`pagetable`/`context` under the lock.
- **`freeproc()`** (called from `wait()` by the *parent*) frees a `ZOMBIE`
  child's `trapframe` and `pagetable` under the child's lock.
- **`procdump()`** reads `p->name` and `p->pid` with no lock, for any p. This
  is racy debug code by design; it is out of scope, not a counterexample.

So the right statement is: **the group is exclusively owned, and the owner is
whoever last took the slot out of the lock invariant.** The lock invariant must
therefore be able to hold it back — conditionally on state, exactly the way it
already conditionally holds `proc_ctx` on `needs_ctx st`.

And crucially, for the two *parked* states it does **not** need to: a
`RUNNABLE`/`SLEEPING` process's private bundle is captured inside its parked
`valid_context`'s continuation closure, the same way `stack_own` is. Nothing in
`valid_context` or `p_sched` has to change to carry it — the closure captures
whatever the parking thread happened to own. That is the single biggest reason
this design is cheap to land.

Which gives the state-keyed table:

| `state` | who holds the private group | who holds the second `pid` half | context |
|---|---|---|---|
| `UNUSED` | lock invariant (free/zeroed shape) | lock invariant | lock invariant (`own_ctx`) |
| `USED` | the lock holder (allocproc/fork mid-flight) | the lock holder | the lock holder |
| `RUNNABLE` | the parked closure | the parked closure | lock invariant, `▷ proc_ctx` |
| `SLEEPING` | the parked closure | the parked closure | lock invariant, `▷ proc_ctx` |
| `RUNNING` | the running thread | the running thread | the running thread (`own_ctx`) |
| `ZOMBIE` | lock invariant (post-`exit` shape) | lock invariant | lock invariant (dead, `own_ctx`) |

Read the columns rather than the rows and the table collapses to **two
booleans**, which is what keeps the invariant flat (Layer 2 below): the private
group and the second `pid` half move together and are invariant-resident
exactly on `UNUSED ∨ ZOMBIE`; the context is invariant-resident either as a
live `▷ proc_ctx` on `RUNNABLE ∨ SLEEPING` — already exactly the existing
`needs_ctx` — or as dead cells inside the first bundle. Six states, two
independent guards, no nesting.

## The resources

Three layers, matching `design/code-organization.md`'s definitional-layer rule.
`ProcInv.v` is a new file above `ProcGeom.v` + `FileInv.v` and below
`SchedCtx.v` (which needs `SwtchCtx.v` for `proc_ctx`; no cycle).

### Layer 0 — `ProcGeom.v`: the missing field addresses

```coq
Definition p_killed    (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 40).
Definition p_xstate    (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 44).
Definition p_parent    (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 56).
Definition p_kstack    (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 64).
Definition p_sz        (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 72).
Definition p_pagetable (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 80).
Definition p_trapframe (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 88).
Definition p_cwd       (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 336).
Definition p_name      (pa : mword 64) : mword 64 := add_vec pa (mword_of_int 344).
```

`ofile` is an array, indexed by fd:

```coq
Definition NOFILE : nat := 16%nat.
Definition ofile_stride : Z := 8.
Definition p_ofile (pa : mword 64) (fd : nat) : mword 64 :=
  add_vec pa (mword_of_int (ofile_off + ofile_stride * Z.of_nat fd)).
```

Note this is *not* `ArrCursor.acur`, despite `ofile` being scanned by
`fdalloc`/`kexit` the way `ftable.file[]` is scanned by `filealloc`. `acur`
takes a **`Z` base**, which suits a fixed global (`fnode`, `bnode`); `p_ofile`
hangs off a per-slot `mword` base, so it takes `proc_addr`'s own `add_vec`
shape instead. The cursor lemmas a scan needs are proven directly, in the style
of `ProcGeom.proc_addr_succ`: `p_ofile_zero` (`addi rd,p,208`),
`p_ofile_succ` (`c.addi rd,rd,8`) and `p_ofile_shift_form` (the
`slli`/`addi 208` recomputation from a runtime fd). **No injectivity lemma is
needed** — a scan borrows one descriptor at a time through
`ProcInv.proc_priv_ofile_read`, so nothing has to know that two indices name
different cells.

Also add the two missing state codes (`UNUSED := 0`, `USED := 1`,
`ZOMBIE := 5`) alongside the existing `SLEEPING`/`RUNNABLE`/`RUNNING`, and
`inv_dormant` beside `needs_ctx`.

Each address must be stated in the *exact* form the instruction computes —
`sign_extend' 64 (… : mword 12)` for offsets that fit in 12 bits (all of them
except 336 and 344, which gcc materialises differently; check the disassembly
per access site, as `p_pid`/`p_lkcpu` already do).

### Layer 1 — `ProcInv.v`: the private bundle

Mirroring `FileInv.fcontent` / `file_fields`:

```coq
Record pprivate := MkPPriv {
  pv_sz        : mword 64;
  pv_pagetable : mword 64;
  pv_trapframe : mword 64;
  pv_ofile     : list (mword 64);   (* length NOFILE *)
  pv_cwd       : mword 64;
  pv_name      : list (bv 8);       (* length 16 *)
}.

Definition proc_fields (pa : mword 64) (dq : dfrac) (V : pprivate) : iProp Σ :=
  (p_sz pa        ↦₈{dq} pv_sz V ∗
   p_pagetable pa ↦₈{dq} pv_pagetable V ∗
   p_trapframe pa ↦₈{dq} pv_trapframe V ∗
   p_cwd pa       ↦₈{dq} pv_cwd V ∗
   p_name pa      ↦ₘ{dq}… pv_name V)%I.
```

**The fd slot owns a file reference.** This is the piece the question asks for,
and `FileInv.file_ref` is already the right unit of ownership — `file-table.md`
names `p->ofile[fd]` as one of its three intended holders:

```coq
Definition ofile_slot (γf : gname) (pa : mword 64) (fd : nat) (v : mword 64) : iProp Σ :=
  (p_ofile pa fd ↦₈ v ∗
   (⌜v = zero_reg⌝ ∗ fd_slot ∨
    ∃ (k : nat) (q : Qp) (C : fcontent),
      ⌜v = fnode k ∧ (k < NFILE)%nat⌝ ∗ file_ref γf k q C))%I.

Definition proc_ofiles (γf : gname) (pa : mword 64) (fs : list (mword 64)) : iProp Σ :=
  (⌜length fs = NOFILE⌝ ∗ [∗ list] fd ↦ v ∈ fs, ofile_slot γf pa fd v)%I.
```

Both directions of the disjunction get *refuted*, never assumed: `sys_close`
knows `v ≠ 0` from argfd and so kills the left disjunct, and `fdalloc` knows
`v = 0` and kills the right one with `FileInv.fnode_ne_zero` (a `struct file *`
out of the global table is never NULL). The two ends of "filling a descriptor"
are `ProcInv.ofile_slot_null` (open a null slot → the cell plus the fd-slot
unit it owned) and `ofile_slot_file` (a cell holding `fnode k` plus a
`file_ref` → a slot), which together are what fdalloc's install arm is made of.

`file_ref` is deliberately **not** persistent and not duplicable, which is
exactly right: `sys_dup` duplicating an fd *is* `filedup`, which must bump the
physical count under `ftable.lock`. `fdalloc` stores a pointer and consumes the
caller's `file_ref` ("takes over file reference from caller on success");
`sys_close` writes 0 into the slot and hands the `file_ref` to `fileclose`.
Naming the file by its slot index `k` with `⌜v = fnode k⌝` is what bridges
FileInv's index-keyed algebra to the pointer stored in memory; `acur_inj`
recovers `k` from `v`.

Then the whole bundle. `pid` is a separate argument rather than a record
field: it is the one member of the group with a *split* discipline (half here,
half permanently in the lock resource), and call sites want to name it.

```coq
Definition proc_priv (γf : gname) (pa : mword 64) (pid : mword 32) (V : pprivate) : iProp Σ :=
  (⌜uint (pv_sz V) <= uvm_maxsz⌝ ∗
   ⌜um_below (pv_sz V) (ud_um (pv_upt V))⌝ ∗
   p_pid pa ↦₄{#(1/2)} pid ∗
   proc_fields pa (DfracOwn 1) V ∗
   proc_pt_at pa (pv_upt V) ∗
   tf_page (ud_tfp (pv_upt V)) (pv_tf V) ∗
   proc_ofiles γf pa (pv_ofile V) ∗
   cwd_ref (pv_cwd V))%I.
```

**THE TWO SIZE CONJUNCTS.** `p->sz` never exceeds TRAPFRAME, and — the
one that carries weight — **nothing is mapped at or above it**
(`ProcPtOwn.um_below`). The second is what growproc pays uvmalloc's
freshness premise out of: the run `[PGROUNDUP(sz) .. sz+n)` is fresh in
`ud_um` precisely because the invariant says so, and no caller of growproc
could have supplied it (`completed/growproc.md`). Its price is that
`proc_priv_copy` takes `uptd_ext_sz (pv_sz V)` rather than `uptd_ext`: a
bare extension says the map only GREW, not WHERE, and the block cannot be
rebuilt without that. copyin/copyout pay it for free — vmfault backs a page
only after ruling out `va >= p->sz`.

**`p->sz <= MAXVA` is a conjunct of the block, not a premise of its
consumers.** It is a real invariant of a live process (exec and growproc are
the only writers and both bound the size), and where it lives is forced by the
"caller obligation the caller cannot discharge" rule: vmfault / copyin /
copyout sit *below* this altitude — they take the bare `p_sz` cell, not the
block — so they must keep taking the bound as a premise, but a function at
*this* altitude (fetchaddr) holds nothing but `proc_priv` and could not
discharge one. `proc_priv_sz_bound` is how such a caller pays the lower tier's
premise. Nothing in the tree constructs a `proc_priv` yet (allocproc is
unproven), so the conjunct costs no existing proof anything.

**`proc_priv` is the resource that goes alongside `cur_proc p`.** It is what
`sys_getpid` / `sys_sbrk` / `sys_dup` / `sys_chdir` open up, and it is what
threads through every syscall spec unchanged. Two projection lemmas cover
almost all uses:

```coq
Lemma proc_priv_pid γf pa pid V (q : Qp) :      (* the read-only pid fraction *)
  proc_priv γf pa pid V ⊣⊢ p_pid pa ↦₄{#(1/4)} pid ∗ (p_pid pa ↦₄{#(1/4)} pid -∗ proc_priv γf pa pid V).
Lemma proc_priv_ofile γf pa pid V fd v :        (* one fd slot, borrow-and-return *)
  (fd < NOFILE)%nat -> pv_ofile V !! fd = Some v ->
  proc_priv γf pa pid V -∗ ofile_slot γf pa fd v ∗
    (∀ v', ofile_slot γf pa fd v' -∗ proc_priv γf pa pid (upd_ofile V fd v')).
Lemma proc_priv_ofile_read γf pa pid V fd v :    (* just the CELL, unchanged *)
  pv_ofile V !! fd = Some v ->
  proc_priv γf pa pid V -∗
  p_ofile pa fd ↦₈ v ∗ (p_ofile pa fd ↦₈ v -∗ proc_priv γf pa pid V).
```

`proc_priv_ofile_read` is what a SCAN wants (`fdalloc`, `kexit`): the scan only
tests the stored pointer against 0, and going through the full accessor would
put `ofile_val`'s disjunction inside a loop invariant for nothing. It is
`proc_priv_ofile` closed at the same `v`, with `upd_ofile_id` collapsing the
descriptor update.

A third covers the whole address-space side at once:

```coq
(* THE GENERAL ONE: both the size and the descriptor move -- growproc. *)
Lemma proc_priv_addrspace γf pa pid V :
  proc_priv γf pa pid V -∗
  p_sz pa ↦₈ pv_sz V ∗ p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) ∗ proc_pt (pv_upt V) ∗
  (∀ P' szv', ⌜ud_root P' = ud_root (pv_upt V)⌝ -∗ ⌜ud_tfp P' = ud_tfp (pv_upt V)⌝ -∗
     ⌜uint szv' <= uvm_maxsz⌝ -∗ ⌜um_below szv' (ud_um P')⌝ -∗
     p_sz pa ↦₈ szv' -∗ p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) -∗ proc_pt P' -∗
     proc_priv γf pa pid (upd_sz (upd_upt V P') szv'))

(* ...and the COPY instance of it: the size stays put, the map only grew,
   and every entry it gained is below the size. *)
Lemma proc_priv_copy γf pa pid V :
  proc_priv γf pa pid V -∗
  p_sz pa ↦₈ pv_sz V ∗ p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) ∗ proc_pt (pv_upt V) ∗
  (∀ P', ⌜uptd_ext_sz (pv_sz V) (pv_upt V) P'⌝ -∗ p_sz pa ↦₈ pv_sz V -∗
     p_pagetable pa ↦₈ page_base (ud_root (pv_upt V)) -∗ proc_pt P' -∗
     proc_priv γf pa pid (upd_upt V P'))
```

This is the bridge from the `proc_priv` altitude down to the one
copyin/copyout/vmfault are stated at. The three pieces travel **together**
for the `proc_priv_tf` reason — a wand that returned only `proc_pt` would have
swallowed the `proc_priv` the two cells are still inside — and what comes back
is a descriptor *extending* the one that went out, because the copy may have
faulted pages in. `uptd_ext` pinning `ud_root` and `ud_tfp` is exactly what
keeps the two cells and the trapframe page described by the new descriptor, so
the block can be rebuilt rather than reconstructed.

The first one is exactly what `SpecAcquiresleep.v` / `SpecHoldingsleep.v`
already consume. Those take `p_pid pj ↦₄{dq} pidv` at a *universally
quantified* `dq`, so they compose with `proc_priv` **unchanged**, at
`dq := DfracOwn (1/4)` — and they should stay that way. Rewriting them to take
`proc_priv` would drag `fileG`/`γf` into the sleeplock layer purely to read a
pid. A bare fraction is the weaker premise and the honest one; that a caller
now obtains it from `proc_priv` rather than from thin air is a fact about the
caller, not about the callee's contract.

`kstack` is separate and persistent. It is stated over a bare address+value
rather than `proc_addr j` / `KvmMap.kstack_va j`, so `ProcInv.v` need not
depend on the page-table layer; the caller that cares supplies the tie:

```coq
Definition is_kstack (pa ks : mword 64) : iProp Σ := p_kstack pa ↦₈□ ks.
```

### Layer 2 — `SchedCtx.v`: the "any CPU can peek" resource

**Is the ownership discipline actually state-dependent?** For most of the
structure, no — and those fields belong at the top level of the invariant,
unconditionally, so that a caller reaching them never does a case analysis.
For exactly two bundles the answer is genuinely yes, and it cannot be
flattened away:

- **the saved context** — already state-dependent in the tree today
  (`needs_ctx st then ▷ proc_ctx pa else emp`), for the reasons in
  `completed/yield-sched.md`;
- **the private field block** — `sys_sbrk` does `myproc()->sz += n` with no
  lock held. If the invariant retained *any* fraction of `p_sz`, that store is
  unprovable. Same for `p_cwd` (`sys_chdir`), `p_ofile` (`fdalloc`,
  `sys_close`), `p_pagetable`/`p_name` (`exec`). So the invariant must give the
  whole block away while the process is live, and take it back when it is not.
  A fractional read-share — the trick that works for `pid`, which is never
  rewritten after `allocproc` — is exactly what does not work here.

So two detachable slots, and **that is the whole of what `p->lock` protects
conditionally.** What matters for usability is that they be *flat and
independent*: two single-boolean guards side by side, never a nested chain.
The condition for each is one decidable predicate on `st`:

```coq
(* needs_ctx st : RUNNABLE || SLEEPING -- already in ProcGeom.v.  The parked
   closure owns the private block too, so this arm carries nothing extra. *)

(* nobody outside the invariant owns this slot: allocproc/wait find it here *)
Definition inv_dormant (st : mword 32) : bool :=
  bool_decide (st = UNUSED) || bool_decide (st = ZOMBIE).
```

`kexit` nulls every `ofile[fd]` and sets `cwd = 0` *before* it goes `ZOMBIE`,
and `freeproc` additionally zeroes `trapframe`/`pagetable`/`sz`/`pid` — so the
dormant bundle **never holds a `file_ref` or an inode reference.** It is raw
cells plus pure facts, and `γf` does not appear in `proc_lock_res` at all:

```coq
Definition proc_dormant (pa : mword 64) : iProp Σ :=
  (∃ (V : pprivate) (pid : mword 32),
     (* the only value fact, and the one that carries weight: the dormant
        bundle owes no file and no inode reference. *)
     ⌜pv_ofile V = replicate NOFILE zero_reg /\ pv_cwd V = zero_reg⌝ ∗
     p_pid pa ↦₄{#(1/2)} pid ∗                (* reunites with the invariant's half *)
     proc_fields pa (DfracOwn 1) V ∗
     ofile_cells pa (pv_ofile V) ∗            (* bare cells: no file_ref clause *)
     ([∗ list] _ ∈ pv_ofile V, fd_slot) ∗     (* the NOFILE per-descriptor units *)
     fd_slots FDSPARE ∗                       (* ... and the process's allowance *)
     own_ctx (p_context pa))%I.

Definition proc_lock_res (γl : gname) (pa : mword 64) : iProp Σ :=
  (∃ (st : mword 32) (ch : mword 64) (kl xs pid : mword 32),
     (* ===== unconditional: every caller names these with no case analysis ===== *)
     p_state pa  ↦₄ st ∗
     p_chan pa   ↦₈ ch ∗
     p_killed pa ↦₄ kl ∗
     p_xstate pa ↦₄ xs ∗
     p_pid pa    ↦₄{#(1/2)} pid ∗
     (* ===== two independent single-boolean slots, side by side ===== *)
     (if needs_ctx st   then ▷ proc_ctx pa   else emp) ∗
     (if inv_dormant st then proc_dormant pa else emp))%I.
```

`pid` is existential inside `proc_dormant` rather than an index: the
invariant's own half of the cell is always resident in `proc_pub`, and two
halves of the same points-to agree for free, so indexing would only duplicate
what `word4_pointsto_agree` already gives. The payoff is that `proc_slots` is
a function of `st` **alone**.

The `∃ V` lives inside `proc_dormant`, not at the top level: outside the
dormant arm there is no `V` to talk about, and hoisting it would leave an
unconstrained junk record bound in every other case.

`proc_dormant` is *not* indexed by `st`, and deliberately carries none of
`freeproc`'s other zeroing (`pid = 0`, `sz = 0`, `pagetable = 0`,
`trapframe = 0`). Nobody consumes those: `freeproc` branches at runtime on
`if (p->trapframe)` / `if (p->pagetable)`, and `allocproc` overwrites both
without reading. Every fact stated here is an obligation on *every* release,
so a fact with no consumer is pure cost — and, as the recast lemma below
shows, an `st`-indexed fact set would also break the UNUSED/ZOMBIE symmetry
for free.

With this shape **no caller ever destructs more than one guard**:

| caller | needs | guards touched |
|---|---|---|
| `wakeup` | `state`, `chan` | none |
| `kill` | `state`, `killed`, `pid` | none |
| `wait` | `xstate`, `pid`, child's pagetable/trapframe | `inv_dormant` only |
| `scheduler` | `state`, the parked context | `needs_ctx` only |
| `allocproc` | `state`, `pid`, the free block | `inv_dormant` only |
| `sleep` / `yield` / `sched` | `state`, `chan`, own context | `needs_ctx` only |

`kill` and `wakeup` — the two functions that walk procs they do not own — reach
everything they touch at the top level and never learn the state. And because
the two `pid` halves are plain points-to fractions,
`word4_pointsto_agree` tells `kill()` that the pid it reads under the lock is
the pid the running thread believes it has. No ghost state.

`procs_inv γ Φ γf γs` is unchanged in shape: 64 `is_lock`s over the new
`proc_lock_res`. It stays persistent, which is what "any CPU can peek" means
operationally — a core acquires, opens, does its business, and reassembles.

`proc_held j γl st ch` (the lock-held/contents-out form in the chain payload)
grows the `killed`/`xstate`/`pid`-half cells the same way.

The one lemma that keeps the guards out of the common case — a state change
that does not move any resource, which is *every* state change except the six
allocation/parking transitions:

```coq
Definition proc_slots (pa : mword 64) (st : mword 32) : iProp Σ :=
  ((if needs_ctx st   then ▷ proc_ctx pa       else emp) ∗
   (if inv_dormant st then proc_dormant pa else emp))%I.

Lemma proc_slots_recast pa st st' :
  needs_ctx st' = needs_ctx st -> inv_dormant st' = inv_dormant st ->
  proc_slots pa st -∗ proc_slots pa st'.
```

Both side conditions are `vm_compute`, and the proof is `destruct` on two
booleans. Because `proc_dormant` is not `st`-indexed, this holds in *both*
directions for every pair of states in the same guard class — it subsumes the
existing `proc_lock_res_wakeup` (SLEEPING → RUNNABLE) and covers `kill`'s
SLEEPING → RUNNABLE identically, with no guard ever opened.

## What moves where, and when

- **`allocproc`** (PROVEN — `projects/proc-struct-resources.md` S6) finds
  `UNUSED`, so `inv_dormant` opens and hands it `proc_dormant` — the field
  cells, `own_ctx`, and the second pid half. It writes `pid` (both halves in
  hand — `ProcInv.p_pid_join` / `p_pid_split`), flips to `USED` (both guards
  now `false`, so the release owes nothing), and allocates the trapframe and
  pagetable. Turning `proc_dormant` into a `proc_priv` is a pure
  repackaging (`ProcInv.proc_priv_intro`): the `⌜pv_ofile V = replicate
  NOFILE zero_reg⌝` fact discharges every `ofile_slot`'s null disjunct with
  no `file_ref` to conjure.
  It **returns with the lock still held**, at `USED`, handing the caller
  `proc_held j γl USED ch` beside the block; building the initial
  `valid_context` for `forkret` — and so **capturing `proc_priv` inside that
  closure** — is the CALLER's step, not allocproc's. allocproc leaves the
  save area as raw cells with `ra = forkret` and `sp = kstack + PGSIZE`;
  turning that into a member of the scheduler chain is a Löb argument about
  forkret and belongs to whoever parks the process. Releasing at `RUNNABLE`
  then leaves only `▷ proc_ctx` behind, matching the table.
- **`fork`** holds the child's lock across `USED`, so it holds the child's
  `proc_priv` and may write `sz`/`pagetable`/`ofile`/`cwd`/`name` freely.
  Each `np->ofile[i] = filedup(p->ofile[i])` consumes a fresh `file_ref`
  minted by `filedup` and installs it in the child's `ofile_slot`.
- **scheduler dispatch** needs no change: the resumed thread's `proc_priv`
  comes back out of its own parked closure, not out of `p_sched`.
- **`exit`** closes every fd (each `ofile_slot` surrenders its `file_ref` to
  `fileclose`, leaving `⌜v = 0⌝`) and `iput`s `cwd` — which is exactly what
  reduces its `proc_priv` back down to a `proc_dormant`. It then parks forever
  at `ZOMBIE`, handing that bundle to the `inv_dormant` guard.
- **`wait`/`freeproc`** opens `inv_dormant` on a `ZOMBIE` child, frees the
  trapframe page and pagetable, and closes it again at `UNUSED` — the *same*
  `proc_dormant`, no recasting needed, which is the payoff for not indexing
  it by `st`.

## What is built

Landed and compiling:

The two fd-slot conjuncts are what make `FDSLOTS` add up exactly: procinit
routes `NPROC * (NOFILE + FDSPARE)` — the WHOLE minted supply — and each
dormant block parks one process's share. `proc_dormant_unused` hands the
`FDSPARE` allowance out as its own conjunct, because for a live process it
travels *beside* `proc_priv` rather than inside it (see
[`file-table.md`](file-table.md) for why: `proc_priv`'s accessors all swallow
the block, so a syscall could not hold its allowance and still pass
`proc_priv` to a callee).

- **`ProcGeom.v`** — all 15 field addresses, `NOFILE`/`PNAMELEN`, the three
  missing state codes, `inv_dormant` + its six `vm_compute` facts, and the
  `p_ofile` cursor lemmas (`p_ofile_zero` / `_succ` / `_shift_form`).
- **`ProcInv.v`** (new, between `FileInv.v` and the spec files) — `pprivate`
  and its updaters, `proc_fields`, `pname_cells`, `ofile_cells`, `ofile_slot`
  (+ `ofile_slot_null` / `ofile_slot_file`), `proc_ofiles`, `cwd_ref`,
  **`proc_priv`**, its projections (`proc_priv_pid`, `proc_priv_ofile`,
  `proc_priv_ofile_read`, `proc_priv_pid_agree`), **`proc_dormant`** +
  `proc_dormant_to_priv`, and `is_kstack`.  Plus, from allocproc: the one
  producer `proc_priv_intro` (+ `upd_pt`), `tf_page_of_page_own` (kalloc's
  page IS a trapframe page), the `ctx_cells` ⇄ byte-buffer accessor
  (`ctx_cells_run` / `wcells_bytes_acc` / `own_ctx_bytes`, which is what
  `memset(&p->context, 0, 112)` runs over), and `p_pid_join` /
  `p_pid_split`.

**`procs_inv` also carries every proc's kstack.** `p->kstack` is write-once
at procinit, so `is_kstack` is persistent and `SchedCtx.procs_inv` holds one
per slot (`procs_inv_kstack`). It has to live there rather than in a
caller's precondition because allocproc reads `p->kstack` of the slot its
SCAN found — an index no premise could have named in advance — and being
persistent it costs every existing consumer nothing.
- **`sys_getpid`** — `SpecSysGetpid.v` / `ProofSysGetpid.v` /
  `LinkSysGetpid.v`, in the standard spec-module shape. The whole function,
  entry to return, over `proc_priv`. `Print Assumptions` shows only the Sail
  model's declared primitives and the standard classical axioms — no
  kernel-level axiom, and `proof_coverage.py` picks it up as `proven`.

`sys_getpid` is the smallest thing that exercises the split, and it exercises
exactly one edge of it: `cpu_own` supplies `cur_proc p` for `myproc()`, and
`proc_priv_pid`'s read-only ¼ fraction serves the `c.lw a0,48(a0)` — with no
lock, no `procs_inv`, no `γl` anywhere in the spec. The two fresh instruction
decodes are the `jal ra,myproc` and that `c.lw`; the 16-byte frame is
byte-identical to `cpuid`'s, so its eight decodes and its frame-cancel lemma
are reused. One wrinkle worth knowing: ra/s0 are saved and restored *across*
the `myproc` call, so the final `callee_saved` does not factor through
`callee_saved_trans` and each of the fourteen conjuncts is discharged on its
own (the `cs_through` shape, as in `ProofHoldingsleep.v`).

Not yet done — the `proc_lock_res` rewiring. `proc_slots` and the new
`proc_lock_res` belong in `SchedCtx.v` (they mention `proc_ctx`), and swapping
them in re-proves yield/sched/sleep/wakeup. Nothing in `ProcInv.v` depends on
that swap, so it can land on its own; see
[`projects/proc-struct-resources.md`](../projects/proc-struct-resources.md).

## The trapframe page, and where the page table lives

`p_trapframe` owns only the *pointer*. The page it names is `tf_page tfp ws`
(`ProcInv.v`): all 36 `struct trapframe` words with their **values**, plus the
3808-byte tail owned anonymously so a `kfree` can hand the whole page back.
The nth syscall argument is word `tf_arg_idx n = 14 + n` — which is exactly the
immediate field `argraw`'s `c.ld a0,<112+8n>(a5)` encodes.

That page used to be `ProcPtOwn.proc_tf_own`, a contents-**existential**
`phys_page_own` inside `proc_pt_own`. Two independent reasons it had to move:

- **Ownership.** `mem_pointsto` is *defined* in terms of `↦ₚ`
  (`phys_to_mem_map`'s proof: `rewrite /mem_pointsto. iExists ppn. iFrame`), so
  a VA-tier `↦₈` on a trapframe word and `phys_page_own` over the same page are
  the *same* resource. Holding both would have made `proc_priv` provably
  `False` — and every spec taking it vacuously true, which compiles.
- **Values.** `phys_byte_any = ∃ b, a ↦ₚ b` forgets the contents, but
  `argint`'s whole contract is the *value* of `tf->aN`.

So mapping and cells stay in `proc_pt_at` (`upt_tree_spec` still maps
TRAPFRAME, `proc_pt_wf` still demands `page_valid`, and both `p->pagetable` and
`p->trapframe` cells are still owned there); only the bytes left. This is the
evolution `ProcPtOwn`'s own comment anticipated — "precisely so it can later
gain STRUCTURE … without disturbing anything else."

`tf_page` is stated at the **physical** tier, indexed by the ppn, because the
page is reached from both sides — the kernel's identity map (`argraw`'s
`ld a0,112(a5)`) and the user table's TRAPFRAME va (uservec/userret). Each
access site converts with `RiscvPtsto.phys_to_mem_claim` / `mem_to_phys_claim`,
the same idiom the software page-table walks use for PT slots.

`pprivate` therefore has no `pv_pagetable`/`pv_trapframe`: `proc_pt_at` pins
both cells to `page_base (ud_root …)` / `page_base (ud_tfp …)`, so the
descriptor `pv_upt : uptd` determines them and a separate value field could
only be dead weight or disagree.

**`proc_dormant` is indexed by `st`.** The address-space cells are keyed on
`bool_decide (st = ZOMBIE)`: a ZOMBIE still owns a live table and trapframe
page, which is exactly what `wait()`/`freeproc` reclaim, while at UNUSED
`freeproc` has freed both and zeroed the cells. The disjunction is tied to the
state rather than free — and consequently `proc_slots_recast` is restricted to
the **live** class (`inv_dormant st = false`), because ZOMBIE → UNUSED
genuinely moves resources and is `freeproc`'s job, not a recast.

> **Performance landmine.** `iFrame` must not be allowed to search inside
> these predicates. `proc_pt` reaches `pt_frame` and a big-op over the page
> footprint; with the `Frame` instances free to unfold it, the two one-line
> `proc_priv` projections took **300 s and 15.7 GB** (definitions alone: 2 s).
> `Typeclasses Opaque proc_pt proc_pt_at` (ProcPtOwn) and
> `Typeclasses Opaque tf_words tf_tail tf_page` (ProcInv) bring the file to
> **8 s** — about 158×. `ProcPtOwn` already did this for `phys_page_own` /
> `upt_pages_own`; the outer predicates need it just as much. Lemmas that must
> see inside now say `rewrite /tf_page` explicitly.

## `sys_close`: the descriptor that gives up its reference

`sys_getpid` reads one private field; `sys_close` is the first proof that
*changes* the private block, and the only interesting thing it changes is one
descriptor:

```
proc_priv γf p pid V   ⇝   proc_priv γf p pid (upd_ofile V fd 0)
```

The three moving parts, all already in `ProcInv.v`:

- **`proc_priv_ofile`** borrows descriptor `fd` and takes back a descriptor
  holding a *different* value — that accessor's `∀ v'` is exactly the shape
  the store needs, and it is why nothing about the fd table has to be an
  invariant. No lock is taken anywhere in sys_close's own body: the array is
  thread-local, so the window between `p->ofile[fd] = 0` and `fileclose(f)`
  returning — descriptor null, reference loose in a register — is
  unobservable.
- **`ofile_slot`'s disjunction** does the case analysis for free: argfd
  reports `fv ≠ 0`, which refutes the left disjunct, so the reference and its
  `k < NFILE` fall out with no extra premise.
- **The `fd_slot` conservation law closes the loop.** The slot gave its unit
  away when it named a file; `fileclose` returns exactly one; the emptied
  descriptor takes it back. That is the *only* reason sys_close's
  postcondition is provable, and it is the proc-side end of the law whose
  file-side end is `FileInv.fslot` (see `design/file-table.md`).

The instruction-level lessons (a 4-byte local in the upper half of a frame
slot, deriving "this stack address is not null", indexing `p_ofile` at a
symbolic fd, and factoring a branch join) are in
[`../projects/proc-struct-resources.md`](../projects/proc-struct-resources.md).

## Holes to be honest about

- **`cwd` has no `inode_ref`.** There is no inode model in the tree
  (`git log`: "started fs, but not crash reasoning"; no `Inode*.v`). The
  `cwd_ref γi ip` above is a placeholder with the same shape as `file_ref`
  — a per-slot fractional auth over `itable`. Until it exists, `pv_cwd`'s
  validity clause should be literally `emp` and the cell owned bare, so the
  bundle can land now and gain the clause later without restating callers.
- **`p_trapframe` owns only the pointer.** The 35-word trapframe *page* is a
  separate resource keyed by that pointer value; the current tree's user-mode
  work assumes one fixed trapframe at `TRAMPOLINE - PGSIZE`, so per-proc
  trapframe pages are a seam, not a solved problem.
- **`parent` / `wait_lock` is deliberately out of scope here.** It is a
  different lock with a documented ordering constraint against `p->lock`;
  it deserves its own note when `wait`/`exit` get attempted.
- **`procdump` is unprovable as written** (unlocked reads of `name` and `pid`
  on arbitrary procs). Making `name` persistent-after-`allocproc` would fix
  the `name` half but not `pid`; the honest answer is to leave `procdump`
  unverified.
- **`USED`/`RUNNING` mapping to `emp` leaks rather than fails.** A thread that
  sets `state = USED` and releases without a matching re-acquire drops the
  private bundle on the floor. That is a safety-preserving leak, and proving it
  cannot happen would need a ghost token per slot — not worth it.
