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

## Done (landed on main, full clean build green at each)

| commit | what |
|---|---|
| `c053872` | `lock_openable γ lk R Tc Dc` in `WpLock.v`; `lock_openable_inv`, `lock_openable_cinv`, `is_lock_openable`. |
| `5d98998` | the ten leaves in `WpSconfLock.v` restated over `lock_openable`; the eight call sites converted. |
| `ae7a255`, `0f93891` | the word-clear leaves; `wp_sw_zero_lockfin_s_sconf` is the one that survives. |
| `efd7c15` | **Tasks 1 + 2.** `HOLDING` generic outright; `ACQUIRE_GEN`/`ACQUIRE`; `RELEASE_GEN`/`RELEASE`/`RELEASE_CANCEL`, one proof instantiated twice. `lock_finisher` + `lock_finisher_close`/`_destroy` in `WpLock.v`. The close-only and destroy-only word-clear leaves deleted. |
| `d00cc1e` | **Task 3.** `SpecInitlock` hands the name field back OWNED (`c_name ↦₈ name`); `lock_name_intro` seals it, and all seven callers do so. |
| `a84dd8c` | **Task 4.** `is_pipe` over `cinv`; `pipe_ref` carries half the cancel token; `pipe_bank`; `pipe_openmark`; `pipe_res_cancel`; `newlock_c_delayed`. |

Verified facts worth not re-deriving:

- **`WpSconfLock.v` is the only file in the tree that ever opens a lock.**
  Everything else merely holds the accessor and passes it down.
- `HOLDING`'s consumers are exactly `ProofAcquire`, `ProofRelease`,
  `ProofSched` — three call sites, which is why it was generalized in place
  rather than restated. `ACQUIRE`/`RELEASE` have thirteen, which is why they
  were restated. Grep per lemma name, never for a substring (`lockinv` gives
  false hits).
- ``Context `{!cinvG Σ}` `` in a file that has not `Require Import`ed
  `iris.base_logic.lib.cancelable_invariants` **silently auto-generalizes
  `cinvG` as a fresh variable**, and the failure surfaces much later as
  "cannot infer the implicit parameter cinvG0". Require it.
- A lemma named in a file that only gets it *transitively* is not in scope:
  `Require Import` for `WpLock` had to be added to `WpInitlockWrapper` and
  `ProofUartinit`, which had been using `lock_name` only as a term.

## Task 5 — pipeclose (the remaining work)

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

Everything it needs now exists. The shape:

- precondition takes `pipe_ref γp w 1` for the end `writable` selects
  (`fileclose` passes `f->writable`), plus `is_pipe`;
- `ACQUIRE_GEN` at `Tc := cinv_own (pn_cancel γp) (1/2)`, the accessor from
  `PipeInv.is_pipe_openable`. The credential comes back out;
- clearing the flag: `pipe_endstate_take` yields the end ghost, the closer's
  half of the cancel token, **and the marker** (`pipe_openmark`), then
  `pipe_endstate_close` puts the end ghost back;
- the branch on the other flag decides which release runs:
  - other end still open → deposit the half with `pipe_bank_deposit`,
    reassemble `pipe_res`, ordinary `RELEASE`;
  - other end closed → `pipe_bank_keep` (the bank is already full), keep the
    half, reassemble `pipe_res`, and call `RELEASE_CANCEL` at `q := 1/2` with
    `PipeInv.pipe_res_cancel γp pi w` as the completion wand and
    `Out := pipe_bytes pi`;
- release then hands back `pi ↦₄ 0`, `lock_cpu pi ↦₈ 0` and `pipe_bytes pi`;
  run `PageFields`' lemmas backwards (`bwin_split`/`bwin_rebase` are
  equivalences, `word{4,8}_pointsto_bytes` is in `RiscvPtsto`; the forward
  direction is `PipeInv.page_own_pipe_raw`) to rebuild `page_own pi`, then
  `kfree`.

Two things still **unverified**:

- `wakeup`'s spec (`SpecWakeup`) — what it demands of `cpu_own`/`procs_inv`,
  and whether it can be called while holding `pi->lock` (it takes the proc
  locks, so the lock order matters to nothing in the logic, but check the
  `av`/stack budget);
- the frame/stack budget for the whole function, and hence its `K`.

`LinkPipeclose` cannot exist before `fileclose`, same as `LinkPipealloc` —
see [`../design/pipe.md`](../design/pipe.md).

## Conventions to follow

- Wrapper recipe (`../durable-notes.md`): the generic lemma gets the NEW name;
  the old name becomes a restatement with the VERBATIM original statement.
  Worth it at thirteen call sites, not at three.
- Spec-module shape (`../design/spec-modules.md`): `SpecF.v` / sealed functor /
  `LinkF.v`. A generic proof plus two instances is three module types and
  three functors — `RELEASE_GEN` is proved once and `ReleaseOfGen` /
  `ReleaseCancelOfGen` derive the two public ones; `LinkRelease.v` applies all
  three.
- Verify "these files depend on X" by grepping the actual lemma names, never a
  substring of them.
