# The per-CPU held-lock set

The design and its phase-1 landing are in
[`design/kernel-proofs.md`](../design/kernel-proofs.md) §Spinlocks and in
`LockSet.v`'s own header. This file is what is LEFT.

## Where it stands

Phase 1 is in: every hart owns `cpu_locks S`, a held-lock set tied to
`lk->cpu` by co-ownership of that field, maintained by acquire and release.
It is **hidden** — it rides inside `IntrDefs.cpu_hart` under
`cpu_locks_any := ∃ S, cpu_locks S`, and no contract in the tree mentions it.
So it currently proves nothing to a caller; it is the substrate.

## Phase 2: make `S` an index of `cpu_own`

`CpuOwn.cpu_own n eb p C b` gains the set: `cpu_own n eb p C b S`. This is the
whole payoff and the whole cost.

- **The cost is a tree-wide interface sweep**: `cpu_own` is named in ~312
  files / ~2300 sites. Mechanical (thread `S` unchanged through every
  balanced function, exactly as `n` is threaded), but it is one atomic
  change — see `completed/explicit-cpuid.md` for the last sweep of this
  shape and its scoreboard of contracts that were stated falsely and
  compiled anyway.
- **Delete on the way**: `IntrDefs.cpu_locks_any`, `CpuOwn.cpu_own_locks_acc`,
  and the `Slk` plumbing in `ProofAcquire`/`ProofRelease` — with the index
  exposed, the callers simply name the set. `IntrDefs.cpu_priv` stays: the
  set travels with the cells across every SIE seam either way.
- **The `b = true` arm gets `S = ∅`**, beside the `n = 0 ∧ eb = true` it
  already carries. Then `sie_arm true`'s `cpu_hart 0 true p` says "a hart
  with interrupts enabled holds no spinlock", which is the theorem the whole
  abstraction exists for. It cannot be stated while `S` is hidden: pop_off
  at the level-0 boundary would have to prove `S = ∅` about a set it cannot
  name. (Do NOT reach for the alternative — a `size S + k = n` invariant with
  push-credit tokens handed out by push_off and taken by pop_off. It works,
  but it is machinery this phase deletes.)
- **acquire's precondition becomes `lk ∉ S`.** Phase 1 derives it inside the
  leaf from the cpu field (`LockSet.cpu_locks_fresh`); with the index exposed
  it can instead be demanded, and then propagated: a function that acquires
  while ∀S-generic carries the premise on its own contract. That propagation
  IS the no-reentrance discipline, and it is what the ~50 acquire call sites
  will owe. Trivial at `S = ∅`; an address disequality when nested.

## Phase 3: lock ORDER

With `S` an index, replace `lk ∉ S` by "`lk` is below everything in `S`" in
some order on lock addresses. Nothing in phases 1–2 forecloses it: the set
already carries the addresses, and the premise slot is already there.

## Two things to know before touching this

- **A `gset` with an unconditional insert and a membership tie is
  INCONSISTENT** (insert `lk` twice, delete once, read `lk ∈ ∅`). Either the
  insert is conditional or the structure is a multiset. Phase 1 is a genuine
  gset because the insert's side condition is discharged from the `lk->cpu`
  cell rather than assumed.
- **`set_solver` does not work over `gset (mword n)`** — see the durable
  notes. Every set side condition here is discharged by named lemma.
