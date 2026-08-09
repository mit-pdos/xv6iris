# Project: filling `cwd_ref` — the inode-reference hole

This is S5 of [`proc-struct-resources.md`](proc-struct-resources.md), promoted
to its own file because it stopped being blocked and started being urgent.

## Why now

`ProcInv.cwd_ref v` is `FileInv.inode_ref v 1`, which is literally `emp` — a
deliberate placeholder with `ofile_slot`'s shape, introduced so the contracts
that surrender an inode reference could be written before an inode model
existed. `IcacheInv.v` **is** that model now (it landed with idup), so the
excuse is gone, and two things have made the hole cost real money:

- **`idup` was proved against the real model** (upstream `8f5470a3`), so its
  contract wants `is_itable`, `itable_inv`, an `IrefSlots.iref_slot` and an
  actual `IcacheInv.inode_ref γ k q dev inum`. `cwd_ref` can supply none of
  it, so `kfork` — whose `np->cwd = idup(p->cwd)` is the only caller — has to
  carry all five as premises plus `pv_cwd Vp = ientry ck`. **No caller of
  kfork can discharge them**, so kfork's contract is honest but unusable
  until this lands.
- **The tree is now inconsistent about the hole**: `iput` is stated over the
  `emp` placeholder while `idup` is stated over the real model, so which
  vocabulary a function's contract inherits depends on which of the two it
  happens to call. That is exactly the "abstraction starts to leak" signal
  durable-notes' guiding principle says to stop and fix.

## THE SHAPE: NO NULL ARM

```coq
Definition cwd_ref (v : mword 64) : iProp Σ :=
  (∃ (k : nat) (q : Qp) (dev inum : mword 32),
     ⌜v = ientry k /\ (k < NINODE)%nat⌝ ∗ inode_ref k q dev inum)%I.
```

- **The fraction is EXISTENTIAL.** `cwd_ref v := inode_ref v 1` cannot
  survive fork: `SpecIdup` halves the caller's share, exactly as
  `SpecFiledup` halves a `file_ref`'s. `ofile_slot` already hides a
  descriptor's fraction for that reason and this is the same move. (The
  present `1` is only satisfiable because the predicate is `emp`.)
- **The `k < NINODE` conjunct** is what lets a holder open the itable's
  per-slot accessors (`IcacheInv.iref_cells_acc`, `islots_acc_upd`) without
  a range premise the caller could not discharge.
- **THERE IS NO `v = zero_reg` DISJUNCT, AND THAT IS THE POINT.**

### Why the non-null arm is the whole predicate

A live process must be known to have a non-null cwd, and that fact must NOT
be something any state transition has to re-establish: `SLEEPING ->
RUNNABLE -> RUNNING` is `SchedCtx.proc_slots_recast`, a resource-free move,
and it stays free only because `proc_slots` mentions neither `proc_ctx`'s
nor `proc_dormant`'s contents. Putting a `cwd <> 0` conjunct anywhere near
`proc_slots` would break exactly that.

With no null arm, nothing has to be said at all:

```coq
Lemma ientry_nonzero k : (k <= NINODE)%nat -> ientry k <> zero_reg.
(* three lines from IcacheInv.ientry_unsigned, which reads
   bv_unsigned (ientry k) = KernelSyms.itable + 24 + 136*k -- a kernel
   address.  The file's own comment already calls injectivity, the scan
   step and the sentinel "corollaries" of that one fact; this is a fourth. *)
```

so `cwd_ref v ⊢ ⌜v <> zero_reg⌝`, hence `proc_priv γf pa pid V ⊢
⌜pv_cwd V <> zero_reg⌝` **as a projection of the block, for free**. The
block travels with the running thread at RUNNING and is swallowed into
`▷ proc_ctx` by the park at RUNNABLE/SLEEPING, so the fact rides inside the
Löb'd obligation and no recast ever looks at it.

### But `proc_priv` must then NOT cover the construction window

`pv_cwd V = 0` is pinned in five places, and only three of them are dormant
states:

| where | state | block |
|---|---|---|
| `SpecAllocproc`'s FOUND arm | **USED, live** | `proc_priv` |
| kfork, allocproc's return .. the `sd a0,336(s4)` at +0xac | **USED, live** | `proc_priv` |
| `ProcInv.proc_dormant` / `proc_dormant_unused` | UNUSED | `proc_dormant` |
| `SpecFreeproc.fp_rest` | UNUSED | (freeproc's split) |
| `ProcInv.proc_priv_to_dormant_zombie`, `SpecKexit` | ZOMBIE | `proc_dormant` |

The dormant ones are fine — `proc_dormant` is a different predicate and does
not contain `cwd_ref`. The first two are the problem: allocproc hands back a
LIVE `proc_priv` for a process whose cwd it has not yet set, and kfork holds
it that way for 150 bytes.

So **split the cwd off the block for the construction window**, the same
move S4c made for the fd table (a deficit block is not `proc_priv ∗
anything`, so split at the component the callee does not touch):

```coq
Definition proc_priv_nocwd γf pa pid V := (* everything but the two below *)
Definition proc_priv γf pa pid V :=
  (proc_priv_nocwd γf pa pid V ∗ p_cwd pa ↦₈ pv_cwd V ∗ cwd_ref (pv_cwd V))%I.
```

with `proc_priv_split_cwd` / `proc_priv_join_cwd` as the two directions.
`ProcInv.proc_fields` currently bundles `p_sz`, `p_cwd` and the name array,
so this means lifting `p_cwd` out of `proc_fields` — a local restructuring
of one definition.

**The blast radius of that split is four files, not thirty-three.**
`SpecAllocproc`'s found arm returns `proc_priv_nocwd` + `p_cwd ↦ 0` +
`iref_slot` instead of `proc_priv`; `ProofAllocproc` assembles that instead
(it currently ends at `proc_priv_intro`); `SpecKfork`/`ProofKforkB4` join the
block at the `sd a0,336(s4)`; `SpecUserinit` (assumed) restates. Every other
consumer of `proc_priv` — all 33 spec files — sees no change and silently
gains the `cwd <> 0` projection.

`ProcInv.cwd_ref_null` is RETIRED (there is no `cwd_ref 0` to introduce).
Its one consumer, `ProofKexit.v:1419`, moves to the split instead: kexit's
`sd x0,336(s3)` takes the block apart with `proc_priv_split_cwd`, spends the
reference on `iput`, and rebuilds a `proc_dormant` at ZOMBIE from
`proc_priv_nocwd` + the zeroed cell + the `iref_slot` iput handed back.

## THE LAYERING PROBLEM, AND THE FIX

The obvious move — define `FileInv.inode_ref` as `IcacheInv.inode_ref` —
**creates a dependency cycle**: `IcacheInv` requires `IrefSlots`, and
`IrefSlots` requires `FileInv`. Measured, the cycle is one edge wide and it
is there for one constant:

```
IrefSlots.v:48  Require Import FileInv.      (* solely for NFILE *)
FileInv.v:73    Definition NFILE : nat := 100%nat.
```

Nothing else in `IcacheInv`'s cone touches `FileInv` — checked:
`InodeInv`, `LogInv`, `FsCrash`, `PipeInv` and `ArrCursor` all have zero
references to it.

**The fix is to factor the REFERENCE out of the INVARIANT.** The reference
predicate needs none of `IcacheInv`'s heavy machinery:

```coq
iref_tok γ k q     := own γ (◯ {[ k := (q, 1%positive) ]}).
inode_ident k dq d n := i_dev (ientry k) ↦₄{dq} d ∗ i_inum (ientry k) ↦₄{dq} n.
inode_ref γ k q d n  := iref_tok γ k q ∗ inode_ident k (DfracOwn q) d n.
```

— an `own` over the Arc-like algebra plus two `↦₄` cells. `LogInv` /
`FsCrash` / `InodeInv` are needed only by `itable_body` / `itable_res` /
`is_itable`, i.e. by the LOCK and the INVARIANT, not by the token.

So: a new low file **`InodeRef.v`** holding `NINODE`, `ISLOTSZ`, `ientry` and
its geometry lemmas, the icache ghost algebra and class, `iref_tok`,
`inode_ident`, `inode_ref` and their split/agree lemmas. `IcacheInv.v`
`Require Export`s it and keeps everything else, so no existing `IcacheInv.`
qualified name changes. The target layering:

```
ProcGeom ─► FdSlots (FDSLOTS, and NFILE moves here)
              ├─► IrefSlots            (IREFSLOTS; requires FdSlots, not FileInv)
RiscvPtsto ─►┴─► InodeRef              (ientry, iref_tok, inode_ident, inode_ref)
                     ├─► FileInv       (file_payload's inode share IS this one)
                     │      └─► ProcInv (cwd_ref = the disjunction above)
InodeInv/LogInv/FsCrash ─► IcacheInv   (Require Export InodeRef; the lock + invariant)
```

`NFILE` moves to `FdSlots.v`, which already computes `FDSLOTS` from
`NPROC`/`NOFILE` and requires only `ProcGeom`. (While there: `NINODE` is
currently defined TWICE, in `IcacheInv.v` and `SpecIinit.v`. Fold both into
`InodeRef.v`.)

## THE GNAME MUST BE CANONICAL, NOT THREADED

`IcacheInv.inode_ref` takes `γ : gname`. If `cwd_ref` inherited it, so would
`proc_priv`, `proc_dormant`, and every one of the **33 spec files** that
mention `proc_priv` — a parameter change, not just a class constraint.

Do what `FdSlots` and `IrefSlots` already do and put the name in the class.
`IrefSlots.v`'s own comment is the precedent and states the reason verbatim:

> the ghost NAME lives in the class: there is exactly one iref-slot supply
> per system, and threading a `γ` would drag a filesystem ghost name through
> `ProcInv.proc_dormant` and every scheduler spec purely so that an empty cwd
> can hold a token.

The same sentence is true of the itable authority, and there is exactly one
itable per system. So `InodeRef.v` defines

```coq
Class icacheG Σ := IcacheG { icache_inG :: inG Σ irefUR; icache_name : gname }.
```

and `iref_tok k q := own icache_name (◯ …)`. `is_itable γl γ` drops to
`is_itable γl`; `SpecIdup.v` / `ProofIdup.v` / `LinkIdup.v` restate, which is
one function's worth of churn.

**What still propagates is the CLASS**, `!icacheG Σ` and `!irefslotG Σ`, into
every file that mentions `proc_priv` — capacity, no resource, no change to
any statement's shape. That is the unavoidable half, and `fileclose` already
paid it for `bioG`/`logG`/`fsCrashG` (see
[`../completed/fileclose.md`](../completed/fileclose.md), "The ghost CLASSES
do propagate, and that part is unavoidable").

> **Write the checker before the sweep.** A class sweep has a silent failure
> mode that no build catches, and `SpecFreeproc.v` already carries a comment
> about it: Rocq PRUNES a class the body does not use, so a `Module Type`'s
> `Parameter` that re-introduces it will not match the `Definition` it is
> supposed to seal. Run `tools/lemma_diff.py` after every batch, and confirm
> each `Module Type`'s binder list against the `_body` it seals rather than
> adding the class everywhere by regex.

## THE ROUTING: EXACTLY `fd_slots FDSPARE`, and it is S4b again

With no null arm, the `iref_slot` unit has nowhere to hide inside `cwd_ref`,
and that is the right answer: it is routed the way the fd allowance already
is. The accounting is a bijection — **at every instant each process either
holds a real cwd reference (with a unit parked against it in the itable, by
`IcacheInv.islot`'s `iref_slots (Pos.to_nat n)`) or has a null cwd and holds
the free unit itself** — which is what makes `IrefSlots.IREFSLOTS =
NPROC*(1 + IREFSPARE) + NFILE` literally true rather than merely plausible.
Those `NPROC` units are currently minted and handed to nobody, the same
oversight S4b fixed for fd slots.

- `ProcInv.proc_dormant` parks `iref_slots (1 + IREFSPARE)` beside its
  existing `fd_slots FDSPARE` — the `1` is the cwd's own unit (the block is
  at `pv_cwd = 0` in both dormant states) and `IREFSPARE` is the allowance
  for references a syscall holds in locals;
- `proc_dormant_unused` returns the allowance as its own conjunct, and
  allocproc passes it and the cwd unit out beside `proc_priv_nocwd`, for the
  same reason `fd_slots FDSPARE` is not inside `proc_priv`: every
  `proc_priv` accessor is borrow-and-return and its wand swallows the block,
  so a syscall holding its allowance out of the block could not then pass the
  block to a callee;
- `SpecProcinit` takes `iref_slots (NPROC * (1 + IREFSPARE))`, i.e. all of
  `IREFSLOTS` except the `NFILE` units the ftable already holds;
- `SpecFreeproc.fp_rest` gains the same two conjuncts (it already spells
  `pv_cwd V = 0` and already holds the `p_cwd` cell inside `proc_fields`).

kfork's `iref_slot` premise then disappears not because the child's cwd_ref
carries the unit, but because **allocproc hands the unit to kfork** along
with the raw block — which is where it was always going to have to come
from, since allocproc is the function that took the slot out of
`procs_inv`.

## ORDER OF WORK

**Do NOT start this until kfork's proof has landed.** It touches `ProcInv.v`,
which is near the bottom of the tree — a full rebuild, ~45 min — and kfork's
six block proofs are written against the current shapes. The right sequence
is:

1. land `kfork` proven and linked against today's contract (five icache
   premises and all);
2. then this project, with **kfork's contract simplification as the
   acceptance test**: `SpecKfork.v` should shed `γil`, `γi`, `ck`, `cq`,
   `cdev`, `cinum`, the `iref_slot`, the `inode_ref`, the `is_itable` /
   `itable_inv` premises and the `pv_cwd Vp = ientry ck` side condition,
   and `kfork_post` should shed its `∃ q'` conjunct — because the parent's
   reference is back inside its own `proc_priv` where it belongs.

**The proof-side edit is ONE line, and it is already marked in the tree.**
`ProofKforkB4.kfk_cwd_ref_any : ⊢ cwd_ref v` is the hole written down — it
holds at an arbitrary `v` precisely because the predicate is `emp` — and its
single use, at the `sd a0,336(s4)` at +0xac, conjures the child's cwd
reference out of nothing while **idup's second half is dropped on the
floor**. There is no honest alternative today: the placeholder
`FileInv.inode_ref` and the real `IcacheInv.inode_ref` idup returns are
different predicates with no bridge. When this project lands, delete that
lemma and make +0xac consume the second half instead — which is the whole
reason idup returns two. The lemma carries a `#`-banner comment saying so,
so a `grep` for `kfk_cwd_ref_any` finds the work.

That ordering also means the sweep is validated by a real consumer instead of
by itself.

## THE OTHER CONTRACTS THAT MOVE

- **`SpecIput.v`** — assumed (`LinkIput.v`'s Axiom), so restating it costs no
  proof, but it must be restated HONESTLY: it already takes `cwd_ref ip`,
  which is now the real predicate and now implies `ip <> 0` on its own, so
  its precondition does not change a character. What it must GAIN is an
  `iref_slot` in its POSTCONDITION: the reference it destroys frees a place
  for another one, and kexit needs that unit to build its ZOMBIE block.
  Today iput returns nothing, which is sound only because the predicate is
  `emp`.
- **`SpecFileclose.v`** — the last closer of an FD_INODE/FD_DEVICE file
  recovers fraction 1 of the payload's inode share and hands it to iput.
  `FileInv.file_payload` already carries `inode_ref (fc_ip C) q`
  fractionally, so this is where the "the two must be the same predicate
  rather than two holes" decision pays off: nothing about fileclose's
  ledger changes, the predicate underneath it just stops being `emp`.
  `FileInv.inode_ref_split` (`inode_ref v (q1+q2) ⊣⊢ …`) must be re-proved
  against the real predicate — it is `IcacheInv.inode_ident_split` plus the
  Arc algebra's own split, both of which exist.
- **`SpecKexit.v` / `ProofKexit.v`** — `sd x0,336(s3)` zeroes `p->cwd`. The
  block is taken apart with `proc_priv_split_cwd` before `iput`, and the
  ZOMBIE block is rebuilt from `proc_priv_nocwd` + the zeroed cell + the
  `iref_slot` iput handed back. `ProofKexit.v:1419`'s `iApply cwd_ref_null`
  is the one line that goes away.
- **`SpecAllocproc.v` / `SpecFreeproc.v`** — both already report
  `pv_cwd V = 0`, so both are on the null arm; what they gain is the parked
  unit travelling with `proc_dormant`.

## WHAT THIS DOES NOT DO

It does not give `p->cwd` a NAME in `pprivate`. `pv_cwd` stays the raw
`mword 64` the cell holds, and the slot index is recovered existentially from
`v = ientry k` (`IcacheInv.ientry_inj` is what makes that determinate). Adding
a `pv_cwd_slot : nat` field would put a filesystem index inside a scheduler
record for no consumer — `sys_chdir` is the only function that will ever want
to name it, and it can bind it at its own call site.
