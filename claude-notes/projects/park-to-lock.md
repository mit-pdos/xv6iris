# park-to-lock: deleting the global parked-scheduler invariant

Branch `park-to-lock`, off `main` at `cae9c3e3`.  `main` is untouched and
green.  Read `claude-notes/design/proc-struct.md` §"The scheduler's saved
context" for the design; this file is the worklist.

## What changed and why

`scheds_inv` was a global Iris invariant with one slot per hart.  Each slot
held that hart's parked-`scheduler()` record and half of `cpus[h].proc`, and a
per-proc `ghost_var bool` (`park_hlf`) recorded whether the record was resident
in the slot or checked out by the running thread.

The bool was not bookkeeping.  Opening an `inv` puts both possible slot
contents under `▷`, and `scheds_put` has to refute "a record is already
resident"; two `valid_context`s give only `▷ False`, which is useless in a bare
fancy update.  Any global box with two states needs a timeless exclusive
flip-flop, so deleting the bit meant deleting the box.

The record now lives in the running proc's own `p->lock`, in a new
`is_running` arm of `proc_slots`.  Every parking path already holds that lock.

## The new definitions (SchedCtx.v, ProcGeom.v)

    Definition run_slot (pa : mword 64) : iProp Σ :=
      (own_ctx (p_context pa) ∗
       ∃ h : CPU,
         hart_at pa (1/2) h ∗
         cpu_proc_half h pa ∗
         ▷ sched_vc_at h (a_cpu_ctx (cid_word_of h)) pa)%I.

    Definition proc_slots (pa : mword 64) (st : mword 32) : iProp Σ :=
      ((if needs_ctx st   then ▷ proc_ctx pa   else emp) ∗
       (if is_running st  then run_slot pa     else emp) ∗
       (if inv_dormant st then proc_dormant pa st else emp) ∗
       (if not_running st then hart_at_any pa  else emp))%I.

Four guards, same as before, so every existing destructuring pattern and lemma
arity survives.

`park_own`/`park_hlf`/`park_full`/`park_at`/`park_at_full` and their lemmas are
gone.  The same `ghost_var` family is retyped from `bool` to `CPU` and renamed
`hart_own`/`hart_hlf`/`hart_full`/`hart_at`/`hart_at_any` — the HART TAG.  It
names the hart a RUNNING proc is running on.

The tag exists because `run_slot`'s `∃ h` does not collapse on its own: the
lock is hart-free, the record is not.  Agreeing `cpu_proc_half h pa` against
the thread's own half does NOT collapse it — two harts each holding half of
*their own* `c->proc`, both reading `&proc[j]`, is satisfiable.  "At most one
hart runs proc j" is a global fact whose invariant would be the box again.  The
tag is timeless, so the collapse works under `▷`.

`IntrDefs.cpu_claim` carries the tag half beside the state half, so the whole
push_off/acquire/release/pop_off transport (`cpu_claim_pay`, `cpu_claim_ext`,
`arm_pay`, `sie_arm`) moves it for free with no further edits.

Two lemmas do the work at the parking seam, both in SchedCtx.v:
`proc_slots_running` (tag half + slot → `st = RUNNING`, whole tag, `own_ctx`,
the `c->proc` half, the record) and `proc_slots_running_intro` (the converse).

## The `c->proc` half — AND AN OPEN QUESTION, SEE STEP 0 BELOW

`cpus[h].proc` is split in two.  One half is in `IntrDefs.cpu_cells`, i.e. in
the running thread's `cpu_own`; a thread reads the field with it (`myproc()`).
The other half is what makes the field WRITABLE, since a store needs the whole
cell, and only the scheduler ever writes it.

It used to be collected by main out of all eight harts and sunk into
`scheds_inv`, because that box was the only place a hart could later find its
own half again.  With the box gone it travels with its hart:
`BootShared.boot_hart_bss` carves the whole cell, `BootBridge.boot_bridge`
passes one half into `cpu_own` and the other straight through, and
`SpecScheduler` takes it as a premise.  Dispatch stores `&proc[j]` and deposits
the half in that proc's `run_slot`; reclaim takes it back out of the lock and
stores 0.  main stops being the collector.

That is the state of the branch as committed.  **Step 0 below argues the split
should not exist at all any more, and should be tried first.**

NOTE, this was got wrong once: the half must NOT be a conjunct of `proc_held`.
`proc_held` is the generic lock-holder payload, taken by allocproc and kill on
procs the holder is not running, and `cpu_proc_half i (proc_addr j)` asserts
hart `i` IS running proc `j`.  If the split survives step 0 it belongs in
`run_slot`, which `is_running` guards, and nowhere else.

## Deleted

- `SchedCtx.v`: `schedsN` body, `sched_slot`, `scheds_inv`, `slot_acc`,
  `scheds_take`, `scheds_put`, `scheds_dispatch`, `scheds_idle`,
  `scheds_reclaim`, `scheds_alloc`, `cpu_own_full_is_vacuous`,
  `scheds_put_take` (317 lines).
- `ProcGeom.v`: the whole `park_*` family, `running_claim`,
  `running_claim_park`.
- `SpecKerneltrap.kt_proc_res` — its entire content was the swept
  `running_claim`, leaving a syntactically dangling definition.
- ~260 swept premises (`running_claim γs j -∗`, `scheds_inv γs -∗`, and their
  inline/bundled forms) across ~60 files.

## State: what compiles

Green as of `d6070118`:
`ProcGeom`, `IntrDefs`, `SchedCtx`, `CpuOwn`, `SpecProcinit`, `SpecScheduler`,
`SpecMain`, `SpecMainSecondary`, `SpecKerneltrap`, `SpecAllocproc`,
`RiscvAdequacy`, `RiscvPtsto`, `BootShared`, `BootBridge`, `BootChain`,
`ProofAllocproc`, `ProofMain`.

The tree as a whole does not build.

## Remaining work, in dependency order

### 0. FIRST: does `cpus[h].proc` still need to be split at all?

Probably not.  Try removing the split before writing any of the parking
proofs, because those are what would bake the assumption in.

The argument that it is now dead weight:

- The tie between "proc `j` is RUNNING" and "hart `h` runs it" is carried by
  the HART TAG, a ghost variable, not by the memory cell.
- The tie between a thread's own `c->proc` and its identity is carried by
  `cpu_own`'s index: `cpu_own n eb p C false` contains `cpu_proc_half cpu_id p`
  and `cpu_claim p` is indexed by the same `p`, so `myproc()` is provable from
  the thread's own half alone.
- `run_slot`'s `∃ h` collapses off the tag, not off the cell.
- With `scheds_inv` gone, NO invariant reads `cpus[h].proc`.  The field is
  genuinely private to hart `h`, which is what the C does.
- The one thing the split provably bought was `SchedCtx.cpu_own_full_is_vacuous`
  — a thread holding the whole cell contradicted `scheds_inv`'s fraction, which
  is what forced `scheds_take` to be non-trivial.  That lemma is deleted.  The
  comment at `IntrDefs.v:688-696` still cites it as the reason for the split;
  it is a fossil, not a justification.

So: give `cpu_own` the whole cell and see what fails.

- `IntrDefs.cpu_cells`: `cpu_proc_half cpu_id p` → `a_cpu_proc cid_word ↦₈ p`.
- `SchedCtx.run_slot`: drop the `cpu_proc_half h pa` conjunct, keeping the tag
  half and the record.  Adjust `proc_slots_running` /
  `proc_slots_running_intro` (their only consumers — nothing is written
  against them yet, which is why now is the moment).
- Revert today's boot plumbing: `BootShared.boot_hart_bss` back to carving one
  cell rather than two halves, `BootBridge.boot_bridge`'s pass-through premise
  and output, and the `cpu_proc_half cpu_id p0` premise on `SpecScheduler`,
  `SpecMain`, `SpecMainSecondary`, `ProofMain.mn_grp_started`.  See commit
  `4f99b421` for exactly what to undo.
- Churn it costs: `SpecScheduler.sc_cpu_own_open` / `sc_cpu_own_mk`,
  `ProofMyproc.v:378`, and whatever else destructures `cpu_cells`.  Strictly
  less than it deletes.

If it holds, the scheduler's two stores need no lock and no invariant at all —
they are plain stores to private memory — which is a much better story than the
one currently written above.  If the scheduler turns out to be unable to
produce the whole cell at its stores, that surfaces in step 5 and the conjunct
goes back; better to learn it from a failed obligation than to keep a conjunct
with no justification.

### 1. `ProofKwait.v` (7 sites) — mechanical

- `:580` `proc_slots gs pa ZOMBIE -∗ proc_dormant pa ZOMBIE ∗ park_at_full pa false`
  → `hart_at_any pa`.
- `:1240`, `:1551` premises `park_at_full (proc_addr k) false` → `hart_at_any`.
- `:1338` `park_at_full_elim` → the tag is now taken whole; the split is
  unnecessary because `proc_held` no longer carries a half.  Compare the
  already-done `ProofAllocproc.v` edit at what was line 871: the two-line
  elim+split just disappears and the single `Hpark` flows through.
- `:1407-1408` the rejoin `park_at_full_intro` + `park_split` likewise
  disappears; `Hheld` destructures to five conjuncts, not six.

### 2. `ProofKexit.v` (2 sites)

- `:26` stale comment.
- `:1161` `scheds_take` — real surgery, same shape as ProofYield below.

### 3. `ProofYield.v` (7) — DO THIS ONE FIRST of the parking paths

It is also the test for step 0: if dropping the `c->proc` conjunct from
`run_slot` breaks anything on the parking side, it breaks here.

It exercises the full round trip and validates the design end to end.

- `:734` `scheds_take γs ⊤ CIDa j` (check the record out just before
  `jal sched`) → `proc_slots_running`: the thread holds `p->lock` on itself at
  RUNNING, so opening `proc_slots` gives the record, the `c->proc` half and the
  whole tag directly, no fancy update.
- `:207` `scheds_put γs ⊤ CID0 j` (the resumed thread's first move, on the
  hart it woke up on) → `proc_slots_running_intro`.
- `:453` `rewrite /running_claim; iExact "Hpark"` — the postcondition no longer
  owes a receipt.
- `:26-30` stale header comment.

### 4. `ProofSleep.v` (13) — same shapes as ProofYield

`:1003` take, `:266` put, `:599` the `running_claim` iExact, `:25-31`,
`:258`, `:629`, `:996-997` comments.

### 5. `ProofScheduler.v` (9) — the only real rewrite

Its two `c->proc` stores stop being mask-changing steps: no invariant holds a
fraction of the cell any more, so the scheduler simply has both halves in hand
under the lock it already holds.  The proofs get shorter but have to be
rebuilt, not patched.

- `:572` `scheds_idle` — delete; the 0 → 0 no-op existed only to keep the
  invariant closed across the loop head.
- `:1175`, `:1435` `park_at_full_elim` / `park_at_full_intro` → `hart_*`.
- `:1211-1217` `scheds_dispatch` → plain store: reassemble the cell from
  `cpu_cells`' half and the scheduler's own, store `&proc[jj]`, split, one half
  back to `cpu_cells` and one into `run_slot` via `proc_slots_running_intro`
  (with `hart_update` to point the tag at this hart).
- `:1360-1366` `scheds_reclaim` → plain store: `proc_slots_running` returns the
  half, reassemble, store 0, split, keep one as the idle spare.
- `:556-558` stale comment.

### 6. Stale comments only

`IntrDefs.v:688-696` (see step 0 — this one is a fossil either way), `SchedCtx.v:69,73` (`schedsN` and the `fin_enum_lookup` /
`cpu_enum_lookup` plumbing are now unused — delete if nothing else wants them),
`SpecScheduler.v:56`, `SpecConsoleread.v:26`, `SpecIput.v:54-55`,
`SpecBalloc.v:96-97`, `SpecKexit.v:58`, `ProofBwrite.v:418-419`,
`ProofAcquiresleep.v:60-61`, `ProofUartwrite.v:68-69`, `ProofSysPause.v:92-93`.

## Build discipline

`eval $(opam env --switch=/shared/xv6rocq)` before any `make`, including in
background shells, or `CoqMakefile` is rewritten with the wrong Rocq version.
Build with `make -f CoqMakefile -jN` from `iris/`; pick `N` by RAM, not cores.
Always grep the log for `Error`.  Never `git add -A` from a parent directory —
use `git add -A .` from `iris/`, or explicit paths.
