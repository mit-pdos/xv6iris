# Discharging `iput_acquiresleep_order_ADMITTED`

The tree's one admitted statement, and the only one. `ProofIput.v:423` assumes

```coq
Axiom iput_acquiresleep_order_ADMITTED :
  forall lks : gset string, locks_below lks "itable" -> locks_below ({["itable"]} ∪ lks) "sleep lock".
```

**It is FALSE, not merely unproven** — `lock_rank` is a closed computation, so
`vm_compute` refutes it and `locks_below_not_elem` turns it into `False`. Every
theorem whose proof reaches it is logically vacuous, which is everything
downstream of `iput`. `Print Assumptions` on any of them names it; that is the
tripwire.

Why no ranking can license the edge, and why xv6 is nonetheless correct, is in
[`completed/lock-set.md`](../completed/lock-set.md) §"THE ONE UNLICENSED EDGE":
`iput` (`kernel/fs.c:341-348`) holds `itable.lock` (14) across `acquiresleep`
(4), and with `proc` (9) below `itable` and `sleep lock` below `proc` there is
no room to place `itable` between them. xv6's own justification is the comment
at `fs.c:339` — `ip->ref == 1` means no other process can have `ip` locked, so
the `acquiresleep` cannot block.

**The discharge changes the OBLIGATION rather than assuming it.** An
`acquiresleep` that cannot block never reaches `sleep_prepare`, so it raises no
order premise, so there is nothing to admit.

## The plan, in order

**1. A FRESH tier on acquire. LANDED.** `SpecAcquire.v` states one body per
level indexed by its held-set precondition and instantiates it twice — `s ∉
lks` (`wp_acquire_fresh_sconf`) and `locks_below lks s` (`wp_acquire_sconf`),
the latter a corollary of the former by `wp_acquire_pre_weaken`. See
[`design/kernel-proofs.md`](../design/kernel-proofs.md) §Spinlocks for the shape
and for why the order is policy rather than a proof obligation. Release needed
nothing: it takes no order premise at all, only `lks ∖ {[s]}`.

**2 + 3. A NON-BLOCKING `acquiresleep`, whose LOCKED branch is REFUTED.
LANDED** as `Acquiresleep.wp_acquiresleep_nb_sconf` (`SpecAcquiresleep.v` /
`ProofAcquiresleep.v`). It takes `"sleep lock" ∉ lks` — the fresh tier, no rank
bound anywhere — plus the caller's evidence that the lock is free, and returns
the ordinary holder bundle. `Print Assumptions` on it names only the Sail model
axioms. What it needed is below.

**4. `ProofIput.v` deletes the axiom.** `NOT DONE`, and it is now the only step
left. What it needs is the icache half: the inode sleeplocks become TRACKED
(`SleepLock.is_sleeplock_tok`), each `iref` share carries a `slh_tok` share of
the same fraction, the itable invariant owns the `slh_auth` total, and REF-1
turns "`ip->ref == 1` and I hold the only reference" into `slh_auth γ None` —
which is exactly `wp_acquiresleep_nb_sconf`'s premise. Then `iput` swaps its
nested call for the non-blocking one and the axiom goes.

**The reference is ALREADY fractional, which is what makes this fit.**
`IcacheRef.iref_tok k q` is `iref_frag k q ∗ live_frac k q` at a `q : Qp`, so a
`slh_tok γ q` share can ride at *the same* `q` with no new algebra — which is
also the reason the sleeplock's share had to be a fraction rather than a whole
token: many `struct file`s share one inode reference and any of them may race
for `ip->lock`. Three things to settle when it is written: the sleeplock's `γ`
must be canonical rather than existential per slot (the same requirement
[`cwd-ref.md`](cwd-ref.md) records for the itable gname), `ilock`/`iunlock`
move to the `_gen` contracts so the deposit is threaded, and the itable
invariant has to relate its `slh_auth` total to the `ref` word it already
tracks. No new premise on
`iput` is needed: `wp_iput_gen` states its bound at its cone minimum `"log"`
(1), so `locks_below_not_elem` gives `"sleep lock" ∉ lks` outright and
`"sleep lock" ∉ {["itable"]} ∪ lks` needs only that the two names differ. The
single consumption site is `ProofIput.v:1881`.

## What the sleeplock layer grew for step 3

### The HELD arm cannot stay pure, and that is forced

`sl_res`'s held disjunct used to be `⌜v ≠ 0⌝` and nothing else, which is why no
caller could ever prove a sleeplock FREE. The refutation has to COST the
acquirer something, and the argument is short enough to keep: a client's
evidence `P` that the lock is free must satisfy `P ∗ (held arm) ⊢ False`; but
`P` is a frame for the acquire's ghost step, so if the held arm could be
manufactured out of the free arm alone, a frame-preserving update would carry
`P` across it and `P ∗ (held arm)` would be consistent after all. **The acquirer
must bring a resource of its own and leave it in the lock.**

So `SleepLock.v` indexes the resource by a DEPOSIT `H : Qp → iProp Σ`
(`sl_res_gen` / `is_sleeplock_gen`), acquiresleep's contract consumes `H q` and
releasesleep's hands it back. Two instances:

- `sl_untracked` (`fun _ => emp`) — the ordinary sleeplock. `is_sleeplock`,
  `sl_res`, `new_sleeplock`, `sl_fresh_new` and all four `wp_*_sconf` contracts
  are its shorthands, so **every existing client reads exactly as before** and
  no file outside the sleeplock layer changed.
- `slh_tok γ` — the TRACKED sleeplock (`is_sleeplock_tok`, `sl_fresh_new_tok`).

### The counting camera, and why the share is a FRACTION

`WpLock.slhUR = prodUR (excl_authUR (leibnizO Qp)) (authUR (optionUR ufracR))`,
carried under the sleeplock's OWN gname — the `γ` of `is_sleeplock γl γ …` — so
no client-visible predicate gained an index. It lives in `lockG`/`lockΣ` rather
than in a class of its own **because a new class would put a `!slhG Σ` in the
ambient context of all ~35 files that so much as mention `is_sleeplock`**; a
sleeplock already needs `lockG` for its inner spinlock, so a second field
reaches every one of them for free and `SystemAdequacy`'s instantiation is
unchanged.

- `slh_tok γ q` is a q-share of "somebody may hold this sleeplock",
  `slh_auth γ t` the total handed out, `t = None` the AUTHORITATIVE ZERO. It
  refutes every share (`slh_auth_none_no_tok`), and that is the whole mechanism.
- **`ufrac`, not `frac`**: the total is a sum over however many references
  exist and is not capped at 1.
- **fractions rather than whole tokens** because one inode reference is shared
  by many `struct file`s, all of which may race for the inode's sleeplock — so
  the right to attempt the lock has to split along with the reference.
- the `excl_auth Qp` half PINS the deposited fraction: the holder's token is
  `sleeplocked_q γ q`, the authority `sl_hauth γ q` rides with the deposit
  inside the lock, and `sl_res_open_held_q` makes releasesleep recover exactly
  the share it put in. Handing back "some" fraction would leave a client whose
  reference is itself split unable to rebuild its own share.
- `sleeplocked γ := ∃ q, sleeplocked_q γ q` keeps the old name and the old
  arity for every untracked client.

### How the proof was split so the loop could be dropped

`ProofAcquiresleep.v` now has three pieces where the nested contract used to be
one 830-line lemma:

- `asl_nloop_proof` — the wait loop (Route B's locked branch). It was an
  `iAssert … with "[]"` inside the nested contract, i.e. it already used nothing
  but the persistent context, so lifting it out cost only its binders.
- `asl_nested_core` — prologue, entry `acquire`, the `locked := 1` /
  `pid := myproc()->pid` stores, the interior release, the entry dispatch —
  with the LOCKED arm handed off to whatever `asl_nloop` the caller supplies,
  and the held-set precondition down to FRESHNESS because nothing in it reaches
  `sleep_prepare`.
- the two contracts over it: the blocking one supplies `asl_nloop_proof`, the
  non-blocking one supplies a REFUTATION.

**`asl_nexit`/`asl_nloop` carry a routed resource `X`, and that is not
decoration.** The entry test picks exactly one arm, and the non-blocking
instance needs its authority on BOTH: to refute the locked arm, and to hand
back on the free one. A static split is impossible, so the core takes `X` and
routes it — `emp` for the blocking caller, `slh_auth γsl (Some q)` for the
non-blocking one.

**The refutation itself is three lines.** Reaching the loop means the held arm
holds somebody's share `q'`; the call still holds the `q` it minted from the
zero and has not yet spent; the authority says the total is exactly `q`; and
`q + q' ≤ q` is false in `Qp` (`Qp.not_add_le_l`).

## What NOT to try

- **Do not weaken `lock_rank`, reorder the table, or add a tiebreaker.** The
  cycle is real in the raw edges and the ranking is already the second one; the
  audit behind it is in `completed/lock-set.md` and moving a rank moves nineteen
  contracts by fixpoint over the call graph.
- **Do not look for a consistent axiom.** The goal is refutable, so any axiom
  that closes it is too.
- **Do not push the fresh tier down through `sleep_prepare`/`sleep`.** That
  makes the locked branch provable at the cost of deleting the order discipline
  from the part of the tree it actually protects. The branch is unreachable;
  refute it.
