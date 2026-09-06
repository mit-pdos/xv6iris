# Project: a context parked under a context

**STATUS 2026-09-06: DESIGN CHECKPOINT, awaiting the owner's go-ahead for
implementation.**  Prototype on `main` (the one-log machine with load–load
relaxation); the two-log store–store work is parked on branch
`relaxed-ww-twolog` and will consume this design.  Skeleton:
`iris/CtxParkedProto.v`, compiled against `TsoCtx.v`'s public unseal
lemmas, every law PROVED, no admits.  Reviewed once (a Fable subagent,
2026-09-06); the review's required items are folded in below.  §8 lists
the decisions left to the owner.

## 0. The rule

A parked record names the CONTEXT it is parked under, not a stamp:

    ctx_under ξ ξ'      "ξ's bound and every write of ξ are justified at ξ'
                         exactly as a fact of ξ' would be"

Parking and resuming are statements about two contexts running on one hart
and need no fence, no view receipt and no stamp.  The stamp form
(`ctx_parked ξ T`, unchanged) survives as the ROOT of a chain: the record a
lock invariant holds, a box's record, a racy-tier record.

## 1. Why the shape changes, and what it does and does not buy

Under the one-log machine a stamp T did two jobs at once: "ξ's facts are
issued at indices ≤ T" and "a reader whose view has passed T sees them".
Store–store relaxation separates the two lines (issue index versus drain
position), and a thread's dirty facts at its park are its hart's buffered
stores: they have no drain position until that hart's next release fence.
The branch found two places that stamp a record: the park at `swtch`
(`TsoCtxPark.ctx_park_box`) and the lock's release deposit
(`WpLock.lock_pay_intro`, `TsoCtx.ctx_deposit`).  "Dominated by ξ'"
removes the FIRST: ξ' is running on the same hart, so ξ's buffered stores
are ξ''s own messages there, and whatever later makes ξ''s facts visible
elsewhere makes ξ's visible too.  The SECOND -- stamping the lock record at
release and cashing it at acquire -- is where the branch mints its receipt
(`relaxed-ww.md` §2.3) and is untouched here; see §6 for the alternative
that would fold it into the same mechanism, and its price.  On `main` the
new shape is simply more general than the pair `ctx_parked XIp Tp ∗
ctx_floor ξl Tp` it replaces (§3, `ctx_under_of_pair`).

## 2. The construct

    key_at ξ' (t, a) := llb (ctx_bound_name ξ') t ∨ dset_in (ctx_dirty_name ξ') (t, a)

the justification a byte fact at ξ' carries, factored out (persistent).

    ctx_under ξ ξ' := ∃ B D, ctx_at ξ 1 B D ∗ ctx_floor ξ' B ∗ [∗ set] k ∈ D, key_at ξ' k

Sealed.  Laws, all interp-free and all proved in the skeleton:

| law | statement | proof |
|---|---|---|
| `ctx_park_under` | `own_context ξ' -∗ own_context ξ ==∗ own_context ξ' ∗ ctx_under ξ ξ'` | same hart: ξ's dirty keys are this hart's own messages, so registering them at ξ' keeps ξ''s `dirty_ok`; ξ''s bound rises to `max B' B` under the joined view receipt; ξ''s watermark joins by `llb_max` |
| `ctx_resume_under` | `own_context ξ' -∗ ctx_under ξ ξ' ==∗ own_context ξ' ∗ own_context ξ` | ξ's new bound is B' (≥ B by the floor), its receipt K'; every key is under B' or registered at ξ' (hence ξ''s `dirty_ok` at this hart); watermark `max W' K'` |
| `ctx_under_morph` | `CtxMorph (λ ξ', ctx_under ξ ξ')` | the pointsto morph's argument once per key, plus `ctx_floor_dom` |
| `ctx_under_move` | `CtxMove (λ ξ', ctx_under ξ ξ')` | `ctx_move_floor` per clean key, `ctx_move_wrote` per dirty key |
| `ctx_under_of_pair` | `ctx_parked ξ T -∗ ctx_floor ξ' T -∗ ctx_under ξ ξ'` | pure: every key ≤ T |
| `ctx_stamped_of_under` | `ctx_parked ξ' T -∗ ctx_under ξ ξ' ==∗ ctx_parked ξ' T ∗ ctx_parked ξ T` | a record under a stamped root is stamped at the root's stamp; a bupd, the child's bound rises to T; a convenience, unused on the lock path |
| `ctx_under_floor` | `ctx_under ξ ξ' -∗ ctx_floor ξ lo -∗ ctx_under ξ ξ' ∗ ctx_floor ξ' lo` | the floor rides up |
| `ctx_under_excl`, `ctx_under_running_excl` | one parent at most; never parked and running | the whole authority is inside |

Rules that follow, stated once at the definition:

- The token is a resource about ξ''s authority through lower bounds and
  memberships only, so it is preserved by everything that happens to ξ':
  ξ' may be parked under a third context, stamped, resumed on another
  hart, moved or morphed, and the child stays validly parked.  The
  watermark join at park is what makes a later stamp of the parent cover
  the child's keys.
- Chains resume parents first.  There is no transitivity law (ξ's keys
  registered at P are not registered at S).  Nothing is ever parked under a
  parked context (the park needs the parent's running token), but a
  running parent with children under it may itself park.
- There is no deposit into a parked child: it would need `ctx_dom parent
  child`, whose target bound must exceed the parent's dirty watermark,
  which sits above the hart's view.  A child is filled while it RUNS
  (`CtxMove`) and parked afterwards.
- A pinned scheduler context that is never stamped accumulates the keys of
  every record ever parked under it.  Sound (membership is justification,
  not ownership) and free of proof-term cost (the set is abstract).
- Every law is sound because parent and child share one ambient hart; no
  two-hart variant is ever to be stated.

For the two-log branch's stage D: `key_at` must become `ctx_pointsto`'s
clean/dirty bit verbatim (a `dpos_ev`-shaped clean arm), defined once and
used by `ctx_pointsto_def`; `ctx_under_of_pair` becomes
receipt-conditioned (`drain_lb A N M` with `W ≤ N`, floor at `M`);
`ctx_under_morph` is the one proof that reads `ctx_dom_def` and is
rewritten against the two-arm dom.  Nothing else in the file changes.

The stamped form keeps its name and every law: `ctx_parked ξ T`,
`ctx_park`, `ctx_resume`, `ctx_parked_raise`, `ctx_parked_alloc`,
`ctx_dom_of_parked_lb`, `ctx_absorb_lb`, `hart_view_lb_get`, `lock_pay`,
`lock_pay_won`, `lock_pay_intro(_llb)`, `ctx_deposit`, `ctx_dom_to_parked`.
The new token lives in its own file (`TsoCtxUnder.v`, under the
`TsoCtxPark.v`/`TsoCtxMove.v` precedent), so `TsoCtx.v` does not move.

## 3. What the shape replaces

**The thread record at `swtch`.**  At the crossing the parker holds two
running tokens, its own and the target's (the resume half runs first);
the parker parks under the TARGET, and the resumed thread reads the record
parked under its own context:

    park_tok   None XIo := ctx_under XIo cur_ctx      (read by the resumed thread)
    resume_tok None XIt := ctx_under XIt cur_ctx
    proc_ctx_at ξl pa   := ∃ XIp, ctx_under XIp ξl ∗ ▷ valid_context p_sched None (p_context pa) pa XIp

In `SwtchCtx.valid_context_pre` the `park_tok` conjunct must be written at
the record's identity and hart, `(XI := XIp) (CID := h)`, not at the
section's ambient ones (today's `park_tok None` is ξ-free and hides this).
`ctx_resume_floor` retires; `ctx_park_box` and `ctx_parked_alloc` leave
the swtch path but stay while fork keeps its box (§7 step 4).  The scheduler's release after `swtch` then deposits an
ordinary payload at `cur_ctx`: `proc_ctx_at_of_tok`, `proc_ctx_boxed`,
`proc_lock_res_deposit`, `proc_lock_pay_of_box` and both arms of
`proc_slots_park_box` retire for that path, and `ProofScheduler.v`'s
post-swtch release (the `ReleaseIn` prelude) becomes a plain release.
`WpLockIn.v` stays as long as any producer still hands a pre-parked
payload (see fork).

**Fork and userinit keep their box.**  The child record is built by
`ProofForkretPark.v`: a running twin filled by `ctx_move`, then parked,
then the rows that only MORPH (`park_globals`: five handle families;
`proc_priv`: six families including the page-table tree) are deposited
into the parked twin with `ctx_deposit`.  Under the new shape a parked
child admits no deposit (§2), so those rows would have to move while the
twin runs, which needs a `CtxMove` instance per row family: nine exist
against sixty-three `CtxMorph` instances, and the tree's morph is
hand-built.  So the producer keeps building `ctx_parked XIc T ∗ ctx_floor
ξb T` with its box, and `proc_ctx_at ξb pa` in the new shape is one
`ctx_under_of_pair` away at the boundary; the `SpecForkretPark` /
`ParkCap` / `ProofUserinit` chain keeps its shape.  Writing the `CtxMove`
twins is a separate, optional sweep.

**Staging.**  `ctx_under_of_pair` converts every producer of the old pair
at its boundary, so the sweep goes consumer-first: `proc_ctx_at`'s body
and instance, `park_tok`/`resume_tok`, both `swtch` halves (`SwtchCtx.v`
and `ProofSwtch.v` move together), then the scheduler's release.

## 4. Boxes

The box (`CtxBox.v`, `ctx-box.md`) is the two-lock object: a buffer's
header is owned by `bcache.lock` while `refcnt = 0` and by the buffer's
sleeplock while `refcnt > 0`.  The parent relation cannot express it, for
two reasons, neither of which is "no running token at the decrement":

- The second-winner problem.  A record parked under a thread is reachable
  only by that thread, but two threads may take references 0→1 and 1→2
  under `bcache.lock`, and the second may win `acquiresleep` first; the
  header must be reachable by whichever wins.  Only a third-party
  invariant (the box) or the sleeplock's own free-arm record can serve
  both, and the 0→1 thread cannot put the record into the sleeplock's
  payload without taking `lk->lk`.
- The phase change is under the other lock.  At the 1→0 decrement the
  record moves from "reachable from the sleeplock" to "reachable from
  `bcache.lock`", under `bcache.lock` only.  Inside an invariant a record
  can only be parked under a STAMPED root, since nobody holds the running
  token of an invariant's context.

So the box keeps its stamped root `ctx_parked ξb T`; on `main` boxes do
not change at all.  Priced and rejected: moving the record between the two
locks' payloads by opening the other lock's invariant under `bcache.lock`
(provable on `main`; replaces 1776 proven lines and three instances with a
cross-namespace protocol per instance; breaks `ctx-box.md` §4's
tripwires; buys nothing under two logs, where the receipt still comes
from the last holder's release fence).  Recording the parked key set in
the L2 register, or re-parenting through the returned reference, changes
who knows which stamps to floor, not who can reach the record.

For the two-log branch: the box's root is a third-party root and will be
treated differently from the lock's per-release root (an author-indexed
stamps camera for the box, `TsoCtxTwin3`'s shape; the fence receipt on the
lock record).  The L2 path ((e) after `acquiresleep`, (f) before
`releasesleep`) needs no stamp there; the L1 path at `refcnt = 0` needs the
record stamped at a drain position covering the last holder's writes,
obtained at that holder's `release(&lk->lk)` fence and folded at `brelse`'s
decrement through the existing reference (`box_ref_decr` raising `sr_td`).

## 5. What does not move

`own_context`, `ctx_pointsto`, `ctx_floor`, `ctx_dom`, `CtxMorph` and its
instances, `CtxMove` and its instances, `hart_view_lb`, the stamped record
and its whole law family (§2), the lock handle and invariant, `locked`,
every acquire/release spec, every box transition, the racy tiers,
`BootShared.v`'s two stamped roots (`cpu_ctx_free`, the `started` record).

## 6. The alternative that would unify locks with threads (not in scope)

Per-lock persistent contexts: each lock owns a context ξL; acquire
resumes it from the invariant's stamped record with the AMO receipt (as
today), moves the payload to `cur_ctx` (`CtxMove`), and parks the empty
lock context under the winner (`ctx_park_under ξL cur_ctx`, carried in
`locked` as `ctx_under ξL cur_ctx`); release resumes it, moves the payload
back, stamps it.  Under two logs the release stamp becomes the fence
publication and the deposit/absorb/dom family is deleted from the LOCK
path (boxes and the racy roots keep it).  Cost: a `CtxMove` twin for essentially every `CtxMorph` payload
instance (sixty-three), the acquire/release/sleeplock spec surface
(`lock_pay`/`lock_pay_won` in seven files, the `_in` forms, `sl_pay`, the
R2 fold), and `locked`'s body.  A separate ruling and a multi-week sweep;
recorded here so the "mostly deletions" framing is attached to the design
that earns it.

## 7. Order of work

1. `iris/TsoCtxUnder.v`: the skeleton's content under its final name
   (§8 (a) decides the token's name).
2. `SwtchCtx.v` + `ProofSwtch.v`: `park_tok`/`resume_tok` bodies, the
   `(XI := XIp) (CID := h)` fix, the two swtch halves.
   `valid_context_pre_contractive` is unaffected (`ctx_under` does not
   mention the recursive occurrence); `park_tok_timeless` follows from
   `ctx_under_timeless`.
3. `SchedCtx.v`: `proc_ctx_at` body and instance; retire the swtch-path
   deposit family; `ProofScheduler.v`'s post-swtch release as a plain
   release; `ProofForkretPark.v`: `ctx_under_of_pair` at the boundary.
4. Rebuild from `SwtchCtx.v` up; `TsoCtxPark.v`'s `ctx_park_box`,
   `ctx_resume_floor` and `ctx_box_over` retire when their last users go.
5. Notes: `ctx-box.md` §1 (the tiers), a contexts section in the design
   notes, this file to `completed/`.

## 8. Decisions for the owner

(a) **Name.**  The owner asked for `ctx_parked ξ ξ'`.  Taking the name
now means renaming today's `ctx_parked ξ T` (seventeen real files, a full
rebuild under `TsoCtx.v`, merge noise against the branch's `ctx_parked ξ
B W A`).  The reviewer recommends `ctx_under` now and the rename at the
branch's stage D, when `TsoCtx.v` is rewritten anyway.
(b) **Fork.**  Keep the box at fork (§3, one line) or write the `CtxMove`
twins for `park_globals`/`proc_priv` and retire the box there too.
(c) **Per-lock contexts (§6).**  Whether to rule on it now or after the
branch's stage C.
