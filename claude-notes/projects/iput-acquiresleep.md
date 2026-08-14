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

**2. The nested `acquiresleep` contract moves to the fresh tier.** `NOT DONE.`
`SpecAcquiresleep.wp_acquiresleep_nested_body`'s premise becomes
`"sleep lock" ∉ lks` in place of `locks_below lks "sleep lock"`. Its interior
`acquire(&slk->lk)` / `release(&slk->lk)` pair then wants nothing more: the
acquire takes the fresh tier directly, and the release cancels with
`locks_add_del` from the same non-membership.

**3. The LOCKED branch has to be REFUTED, not proved — this is the real work.**
The nested contract currently proves that branch as a Löb loop, and that branch
reaches `sleep_prepare`, which acquires `p->lock` at `"proc"` (9). Under the
fresh tier there is no bound to hand it, and no true one exists: iput's held set
contains `"itable"` (14). So the branch must become unreachable, which is what
"non-blocking" means and what REF-1 buys. The caller supplies evidence that the
sleeplock is FREE (icache REF-1 exclusivity, [`design/fs-icache.md`](../design/fs-icache.md)),
the `lk->locked != 0` test is decided at the leaf, and the whole sleep cone
drops out of the contract.

**4. `ProofIput.v` deletes the axiom.** No new premise on `iput` is needed —
which is worth knowing before anyone designs one in. `wp_iput_gen` states its
bound at its cone minimum `"log"` (1), and `1 <= 4`, so `locks_below_mono` to
`"sleep lock"` and then `locks_below_not_elem` gives `"sleep lock" ∉ lks`
outright; `"sleep lock" ∉ {["itable"]} ∪ lks` needs only that the two names
differ. The single consumption site is `ProofIput.v:1881`.

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
