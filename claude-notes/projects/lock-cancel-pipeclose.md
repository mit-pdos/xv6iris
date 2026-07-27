# Project: cancellable locks, and pipeclose

Freeing a kalloc'd object whose first member is a `struct spinlock`.
`pipeclose`'s `kfree(pi)` needs `page_own pi` — all 4096 bytes — but the
lock's own storage lives inside a permanent Iris `inv`, and `lock_name`
discards the 8-byte name field forever. This project makes a lock's storage
reclaimable and then proves `pipeclose`.

Design and rationale: [`../design/pipe.md`](../design/pipe.md). The short
version of the key idea, because it is not obvious:

> A lock's storage is reclaimable exactly when the *right to touch it* is a
> resource rather than free knowledge. That is the real xv6 rule for a
> kalloc'd object: you may take `pi->lock` only while you hold a reference to
> the pipe.

## Done (landed on main, tree green at each)

| commit | what |
|---|---|
| `c053872` | `lock_openable γ lk R Tc Dc` in `WpLock.v`; `lock_openable_inv` (`inv` → `emp`/`False`), `lock_openable_cinv` (`cinv` → `cinv_own γc q`/`cinv_own γc 1`), `is_lock_openable`, `newlock_c`. `lock_inv`, `is_lock`, `lock_name`, `newlock` unchanged. |
| `5d98998` | the ten leaves in `WpSconfLock.v` restated over `lock_openable`; the eight call sites in `ProofAcquire`/`ProofRelease`/`ProofHolding` converted. `SpecAcquire`/`SpecRelease`/`SpecHolding` untouched. |
| `ae7a255` | `wp_sw_zero_lockcancel_s_sconf` — the word clear that destroys the invariant instead of closing it. |
| `0f93891` | `wp_sw_zero_lockfin_s_sconf` — the same store with the invariant's fate left to a caller-supplied finisher. This is the pivot for proving release once and instantiating it twice. |

Verified facts worth not re-deriving:

- **`WpSconfLock.v` is the only file in the tree that ever opens a lock.**
  Everything else merely holds `is_lock` and passes it down. Checked by
  grepping for `is_lock_inv` and for `lockN`.
- The ten leaves are used **only** by `ProofAcquire.v`, `ProofHolding.v`,
  `ProofRelease.v` (eight call sites). Earlier greps for the string
  `lockinv` gave false hits — `ProofSched` uses the whole-function
  `Holding.wp_holding_lockinv_*`, `ProofReleasesleep` has a *hypothesis named*
  `"Hlockinv"`, `WpAmo` has a comment. Grep per lemma name, not for the
  substring.
- `ACQUIRE`/`RELEASE`/`HOLDING` are instantiated by thirteen proofs
  (`ProofKalloc`, `ProofKfree`, `ProofFilealloc`, `ProofFiledup`, `ProofSleep`,
  `ProofWakeup`, `ProofYield`, `ProofSched`, `ProofClockintr`,
  `ProofSysUptime`, `ProofAcquiresleep`, `ProofReleasesleep`,
  `ProofHoldingsleep`). Keep their statements restated so none of these move.

## Task 1 — `RELEASE_CANCEL`

Prove release **once** over `wp_sw_zero_lockfin_s_sconf` and instantiate it
twice. Do NOT branch inside the proof and do not duplicate its 229-line tail.

1. `ProofRelease.v`: the single call to `wp_sw_zero_lockopen_s_sconf`
   (currently around line 236, `0x1a: sw zero,0(s1)`) moves to
   `wp_sw_zero_lockfin_s_sconf`, threading the finisher through from the
   spec's premises. Everything before and after is unchanged.
2. `SpecRelease.v`: `wp_release_sconf_body` gains `(Tc Dc Out : iProp Σ)`,
   takes `lock_openable γl lka R Tc Dc` and `Tc` in place of
   `is_lock γl lka s R`, takes the finisher premise, and its continuation
   gains `Out -∗`. Name it `wp_release_gen_sconf_body`.
3. Two module types from the one proof:
   - `RELEASE` — the **verbatim current statement**, instantiated at
     `Tc := emp`, `Dc := False`, `Out := emp`, with the finisher discharged by
     closing (left conjunct of both `∧`s) and `is_lock_openable` supplying the
     accessor. The thirteen consumers must not change.
   - `RELEASE_CANCEL` — `Tc := Dc := cinv_own γc 1`,
     `Out := lka ↦₄ 0 ∗ lock_cpu lka ↦₈ zero_reg ∗ R`, finisher discharged by
     taking the raw contents and surrendering `Dc`.
4. Delete `wp_sw_zero_lockopen_s_sconf` and `wp_sw_zero_lockcancel_s_sconf`
   once nothing uses them — they are near-duplicates of the finisher leaf and
   should not linger as a family.

Note `Tc` and `Dc` must be the *same* resource for the cancelling instance:
`cinv_own γc q ∗ cinv_own γc 1` is invalid, so you cannot hold a separate
credential and certificate. `lock_openable_cinv` at `q := 1` is the shape
wanted, and it is exactly what a caller holding every share of the object has.

## Task 2 — an acquirable cancellable lock

`pipeclose` calls `acquire` before it calls `release`, so `ACQUIRE` needs the
same treatment: `wp_acquire_sconf_body` over `lock_openable γl lk0 R Tc Dc` +
`Tc`, returning `Tc`, with the current statement restated at `emp`/`False` as
`ACQUIRE`. `ProofAcquire`'s two leaf call sites already pass `R emp False`;
they become `R Tc Dc` and thread the returned credential instead of dropping
it as `_`.

Check whether `HOLDING` needs it too — `release` calls `holding()` internally,
so probably yes; `ProofRelease` applies `Holding.wp_holding_lockinv_locked_s_sconf`.
**Unverified.**

## Task 3 — `SpecInitlock` returns the name field owned

The 8 bytes at `lk+8` are inside the page and `kfree` memsets them, so
`lock_name`'s `↦₈□` makes the page unreclaimable. Change `SpecInitlock`'s
postcondition to hand back `c_name ↦₈ vname` instead of `lock_name lk s`
(strictly stronger), and have each caller re-derive `lock_name` with the
existing `RiscvPtsto.word_pointsto_persist`.

Callers of `wp_initlock_sconf` (verified): `ProofKinit`, `ProofBinit`,
`ProofIinit`, `ProofUartinit`, `ProofInitsleeplock`, `ProofPipealloc`,
`WpInitlockWrapper`. Seven, plus `SpecInitlock.v` and `ProofInitlock.v`
themselves.

For a pipe the field must end up inside `pipe_res`, not discarded, so that
`lock_cancel`/the finisher returns it with the rest.

## Task 4 — `PipeInv` over `cinv`

- `is_pipe` holds `cinv lockN γc (lock_inv γl pi (pipe_res γp pi))` instead of
  `is_lock`, plus `⌜page_valid pi⌝`.
- `pipe_ref γp w q := own (pn_end γp w) q ∗ cinv_own (pn_cancel γp) (q/2)`,
  so that **both ends at 1** gives `cinv_own γc 1`, which is the licence to
  destroy; and any positive share gives a positive credential, which is the
  licence to acquire. Both components are fractional, so splitting and
  recombining still work.
- `pipe_res` grows the lock's name field (Task 3) and keeps everything else it
  has. It does **not** need a "dead" disjunct: the finisher design means the
  last closer keeps `pipe_res` rather than handing it back, so lock lifetime
  never leaks into the pipe layer.
- `new_pipe` moves from `newlock` to `newlock_c` and additionally hands out the
  cancel shares; `ProofPipealloc` follows (its `new_pipe` call site, and the
  `is_pipe` in `pipealloc_post`).

## Task 5 — pipeclose

34 instructions at `0x80004440`, straight-line with two branches; callees
`acquire`, `wakeup`, `release`, `kfree`, all with existing specs.

```c
void pipeclose(struct pipe *pi, int writable) {
  acquire(&pi->lock);
  if (writable) { pi->writeopen = 0; wakeup(&pi->nread); }
  else          { pi->readopen  = 0; wakeup(&pi->nwrite); }
  if (pi->readopen == 0 && pi->writeopen == 0) { release(&pi->lock); kfree((char *)pi); }
  else release(&pi->lock);
}
```

Shape of the proof:

- precondition takes `pipe_ref γp w 1` for the end `writable` selects
  (`fileclose` passes `f->writable`), plus `is_pipe`;
- clearing the flag deposits that end's token via `pipe_endstate_close`;
- reading the other flag as 0 extracts the other end's full token
  (`pipe_endstate_closed`) — now both ends are held, i.e. `cinv_own γc 1`;
- the freeing arm uses `RELEASE_CANCEL`, which returns the two lock words and
  `pipe_res`; `PageFields`' lemmas run backwards reassemble `page_own pi`
  (`bwin_split`/`bwin_rebase` are equivalences; `word{4,8}_pointsto_bytes`
  exists in `RiscvPtsto`), then `kfree`;
- the non-freeing arm uses ordinary `RELEASE` after re-closing `pipe_res`.

`wakeup`'s spec (`SpecWakeup`) is available; check what it demands of
`cpu_own`/`procs_inv` — **unverified**.

## Conventions to follow

- Wrapper recipe (`../durable-notes.md`): the generic lemma gets the NEW name;
  the old name becomes a restatement with the VERBATIM original statement.
  Getting this backwards is what broke 8 call sites needlessly once already.
- Spec-module shape (`../design/spec-modules.md`): `SpecF.v` / sealed functor /
  `LinkF.v`, and keep whole-function proofs in that shape so
  `tools/proof_coverage.py` sees them.
- Verify "these files depend on X" by grepping the actual lemma names, never a
  substring of them.
