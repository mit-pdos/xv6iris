# tso-kpt-lane.md — the KPT lane (§0.36′ steps 1–3), worklist and measurements

*Lane workspace: `/shared/xv6iris-3-kpttree` (a copy of the fliptree taken at the
certified r21 boundary).  Remote build tree:
`/mnt/rocq/trees/_shared_xv6iris-3-kpttree`.  This file is the KPT lane's own
record; the lock lane owns `tso-machine-flip.md` and nothing here is written
there.*

Governing text: `tso-port.md` §0.36′.  Inputs consumed, not rebuilt: A6.105
(`lk_floor`'s ratified two-armed shape), A6.106 (the one-gate cascade
measurement, `ctx_phys_pin_mint_top` / `kptree_publish_top`), A6.107
(`ghost_step` / `wp_fence_gs_s_sconf`, the non-draining barrier leaf).

---

## K1. THE BASELINE, CERTIFIED IN THIS LANE'S OWN TREE

Cold whole-tree build (per-subtree `coq_makefile`, `-j90`, 440 s), sentinel
`MAKEEXIT=2` + `DONE`:

> **1100 `.vo` of 1338 `.v`** in `iris/`.

The 238 files without a `.vo` reduce to **9 root failures** — the rest are their
reverse-dependency cone (`Link*`, `Umode*`, `U*`, `SystemAdequacy`,
`SystemAssumptions`, `Pt2WalkPt`, `Proof{Acquire,Release,Holding,User,Userret,
Uservec}`, the three further `ProofVirtioDiskRw*` files).  The 9 roots are
character-for-character A6.107's set:

> `ProofForkretPark`, `ProofKernelvec`, `ProofMain`, `ProofSwtch`,
> `ProofVirtioDiskIntr`, `ProofVirtioDiskRwD`, `UptWalkPt`, `UserMemPt`,
> `WpSconfLock`.

So the lane's copy **is** the r21 boundary; every number below is against it.

## K2. WHAT `ProofMain` IS ACTUALLY RED AT — one error, and it is the arity

```
File "./ProofMain.v", line 996, characters 36-37:
Error: The term "t" has type "ptree" while it is expected to have type "nat".
```

`ProofMain:996` still calls `kpt_inv_alloc` at its **pre-A6.71 arity**
(`root_ppn t M E`, three resources, two results); the current signature is
`kpt_inv_alloc root_ppn B t M E` and it additionally wants
`llb loglen_name B` and `kptb_unset`, and returns `kpt_bound B` as a third
result.  The `kptb_unset` one-shot is already threaded into
`mn_grp_kvm`'s premises and left unused.

Behind that first error stands a second, not yet reached by the compiler: the
`Kvminithart.wp_kvminithart_sconf` application at ProofMain (and its twin at
`ProofMainSecondary:640`) takes eight arguments now — the eighth is
`KptShare.kpt_creds` (`SpecKvminithart.v:103`) — and ProofMain passes seven.
So ProofMain owes **`kpt_bound B` + `view_lb … B` for hart 0 at `main+0x76`**,
which is exactly the object §0.36′ exists to supply.

## K3. THE MEASUREMENT THAT STOPS STEP 3 — the publication's bound is above its own author's view, and hart 0 never gets back below it

§0.36′ steps 1–3 place the publication at `main+0xac` and run
`KptPublish.kptree_publish_top`, whose bound is `length g.(glog)`.  Measured end
to end, that site cannot serve **hart 0**, and the reason is not a missing
lemma:

### (a) hart 0 needs the walker credential *after* `main+0xac`, forever

`ProofMain.mn_grp_started` runs `0xac fence rw,w`, `0xb0 sw a4,0(a5)`
(`started = 1`), `0xb2 j 0x3e`, `0x3e jal scheduler`, and then
`Scheduler.wp_scheduler_sconf` — under `sie_cap_gpr KT1`, whose translation
regime is `SRegime.kpt_res_at = tlb_snap_ok ∗ kpt_inv ∗ kpt_creds`
(`SRegime.v:1591`, tied to `tlb_res_pt` at `:1635`).  Every access from `0xb0`
onward — the `started` store itself, scheduler's prologue stores, everything
after — is translated through the shared table and therefore spends
`kpt_creds`.  There is no point at which hart 0 stops needing it.

### (b) hart 0 cannot buy the published arm at `0xac`

`kpt_slot_bytes_pin` spends `view_lb … (hart_agent cpu_id) B`, and
`TsoCtx.ledger_read_pin_ok` uses it for exactly one step: `B ≤ g.(gtv) cpu_id`.
`kptree_publish_top` pins at `B = length g.(glog)` and — by its own header —
**deliberately hands back no `hart_view_lb`**.  At `0xac` hart 0's view is
strictly below the log top (its own stores are buffered; A6.105's finding), and
the barrier there is `Barrier_RISCV_rw_w`, for which `RiscvLang.fence_drains` is
false, so `TsoMemPa.fence_post` moves the view by nothing (A6.106 §1, A6.107 §1).
**No artifact can close this: the machine does not advance hart 0's view at that
instruction.**

### (c) and it cannot keep the boot arm either, because the two arms are mutually exclusive on the same ghost key

`PtTree.pt_slot_own` is `phys_ledger_word_pin a dq w B (pte_slot_set w)` at
`KTier B` and `TsoCtx.ctx_phys_word_pointsto xi a dq w` at `UTier xi`.  Unfolded,
the ctx form asserts the ts fragment `a ↪[ts_name]{dq} (t, TsoMemPa.ts_pay_none)`
(read off `CtxPinMint.ctx_phys_ts_own`'s own statement), and the pinned form
asserts the same key at `ts_pay_pin Sv B`.  Two fragments of one `ghost_map` key
must agree on the value, so **no fraction split lets the invariant hold the
pinned tree while hart 0 holds a registered view of it**.  Publication is
all-or-nothing (`ctx_phys_pin_mint`'s own note: "the fraction is `DfracOwn 1`
and cannot be weakened").  And `KptShare.kpt_body` needs `DfracOwn 1` at
`KTier B`, so `kpt_inv` cannot be allocated until hart 0 has given the table
away.

### (d) therefore

> **Publishing at `main+0xac` hands hart 0 a bound its own view will not reach
> until its next AMO, and takes away the only other credential it has, at the
> exact instruction where it enters `scheduler()`.  §0.36′ steps 1–2 are sound
> in shape; step 3's SITE is not reachable as written.**

This is *not* A6.106's finding restated.  A6.106 measured that the fence at
`0xac` is the wrong kind for `pub_step`, and A6.107 removed that obstruction by
building the drain-free `ghost_step` publication.  What is measured here is one
tier further on: the drain-free publication is fine for *the secondaries* and
useless for *the publisher*, because a pin is a statement indexed by the
reader's view and the publisher is the one reader guaranteed to be below it.

## K4. WHERE THE EXIT IS, MEASURED — the bound has to be one the publisher has already passed, and only an AMO can say so

`KptPublish.kptree_publish` (§5, the drain arm) is *already* the right shape for
hart 0: it pins at `B = g.(gtv) cpu_id` and hands back `hart_view_lb
(g.(gtv) cpu_id)` for free off `CtxPinMint.hart_view_lb_now`.  Its only premise
is `drained g` ≡ `own_pub (hart_agent cpu_id) g.(glog) ≤ g.(gtv) cpu_id`, and
that premise is **stronger than the mint needs**.  Following it down:

* `KptPublish.kptree_publish → … → CtxPinMint.ctx_phys_pin_mint →
  ctx_phys_ts_own` (`CtxPinMint.v:109`).  `ctx_phys_ts_own` uses `drained` in
  **one** place: the DIRTY arm of the byte's own clean/dirty bit, where
  `TsoGhost.dirty_ok`'s right disjunct gives "this is my own message at index
  `i`" and the only available bound on `S i` is `own_pub`.
* Its CLEAN arm needs **no drain at all**: `t ≤ B ≤ K ≤ g.(gtv) cpu_id`, the
  last step off `own_context`'s own `view_lb … K` receipt.  `dirty_ok`'s LEFT
  disjunct (`⌜k.1 ≤ B⌝`) closes it the same way (`CtxPinMint.v` proof, first
  bullet of each case).

So the mint at the publisher's own view goes through for any byte whose
justification sits on the left arm.  Two facts then bracket the gap:

1. **AT AN AMO THE MINT ALREADY WORKS AND COSTS NOTHING.**  The AMO leaf's fact
   is `length g.(glog) ≤ g.(gtv) cpu_id` (`TsoCtx.ctx_absorb`'s premise), and
   `TsoMemPa.own_pub_le` gives `own_pub h glog ≤ length glog`, so the AMO fact
   **implies** `drained g`.  `KptPublish.kptree_publish` therefore goes through
   verbatim at any AMO after `kvminit`, at bound `g.(gtv) cpu_id`, handing back
   `hart_view_lb` and `llb` free.  Nothing has to be built for that site.
2. **AND NOTHING DURABLE RECORDS IT AFTERWARDS.**  `TsoCtx.ctx_bound_raise`
   (`TsoCtx.v:438`) re-proves its `[∗ map] k ∈ D, dirty_ok … B k` with
   `TsoGhost.dirty_ok_mono`, which keeps every entry on the arm it was created
   with — a byte the hart wrote stays on the "my own message" arm forever, and
   that arm carries no bound relating `k.1` to anything the hart has passed.
   `own_context`'s single watermark `W` does not help: it covers the hart's
   LATER stores too, so `W ≤ K` is false as soon as the hart stores again.  And
   `ctx_phys_pointsto`'s own clean/dirty bit is fixed when the byte is written.
   **So "my writes to these bytes predate my last AMO" is a fact that exists
   only AT that AMO and is lost the moment the leaf closes.**

### K4a. THE SETTLE ALREADY EXISTS — IT IS `ctx_park`; AND A SETTLE OF `own_context` IS USELESS, WHICH IS WHAT PICKS THE DESIGN

The first shape I priced for the settle was "re-prove `own_context`'s `Hoks` on
the left arm at an AMO".  **That is already in the tree, and measuring it refutes
its own usefulness — which is the finding that fixes the design.**

* `TsoCtx.ctx_park` (`TsoCtx.v:549`) is exactly the settle, and it is
  INTERP-FREE: it sets `T := K ⊔ W` off the token's own two receipts, raises the
  bound to `T` with one `mono_nat_own_update`, and yields `ctx_parked ξ T`, whose
  statement carries `⌜∀ k ∈ dom D, k.1 ≤ T⌝` — **every dirty entry under the
  bound**, as a visible pure conjunct.  Its own header says so: *"ONE BOUND-RAISE
  converts every dirty entry to clean."*
* `TsoCtx.ctx_resume` (`:570`) re-founds the running token *"with every dirty
  entry on its clean arm"* (`iLeft. iPureIntro. apply HDT.`), from
  `hart_view_lb K ∗ ⌜T ≤ K⌝`.
* So `ctx_park ; ctx_parked_llb ; hart_view_lb_get ; ctx_resume` is a four-line
  composite, all four parts existing, that settles a running context at any AMO.

**And it buys nothing**, because `own_context ξ` after the resume is *the same
proposition* it was before: its `[∗ map] k ∈ D, dirty_ok … B k` is a disjunction
either way, and a later proof that opens it still has to handle the right arm.
The strengthening exists only in `ctx_parked`'s pure conjunct, i.e. only while
the context is PARKED.

> **THE GENERAL LAW THIS MEASURES, and it is the lane's own version of §0.35′'s
> lesson: outside an AMO, no resource in this model can certify "log position
> `X` is at or below MY view" unless it was minted as `hart_view_lb X` at an AMO.
> `llb loglen_name X` only ever gives `X ≤ length glog`.  So the comparison
> between the table's write positions and the publisher's view is provable at
> exactly one kind of instruction, and the only durable record of it is the park
> protocol's own stable pair `ctx_parked ξ T ∗ hart_view_lb T`.**

### K4b. WHICH NAMES THE DESIGN: the kernel page table wants its OWN, PARKED context

Put K4d and K4a together and §0.36′(b) reads as a recipe rather than a sketch:

1. the table is registered to a context of its own, `ξ_pt`, not to hart 0's
   running context;
2. hart 0 **parks** `ξ_pt` (`ctx_park`, interp-free) after `kvminit`, getting
   `ctx_parked ξ_pt T` with `llb loglen_name T` and `⌜every PTE write ≤ T⌝` —
   `T` IS §0.36′(b)'s *"PT-validity stamp"*;
3. at its next AMO — any boot-time `acquire`; the table need not be in hand, only
   the stamp — hart 0 takes the stable pair `hart_view_lb K ∗ ⌜T ≤ K⌝`
   (`TsoCtx.hart_view_lb_get`), which is persistent and survives every step to
   `main+0xac` and beyond;
4. from there `TsoCtxAbsorbLb.ctx_dom_of_parked_lb` / `ctx_absorb_lb` hand the
   table's facts to ANY running context that holds a receipt past `T` — **with
   no interp**, which is what makes it usable at `0xac` and inside `scheduler`;
5. the `started` deposit carries `ctx_parked ξ_pt T` (or the domination) plus
   `⌜T ≤` the flag write's position `⌝`, and a secondary that has read
   `started == 1` and drained has a receipt past it.  That is §0.36′(b)'s bound
   relation, literally.

Every piece of that is built: `ctx_park`, `ctx_parked_llb`, `hart_view_lb_get`,
`ctx_dom_of_parked_lb`, `ctx_absorb_lb`, `own_context_floor_view`.  What is NOT
built is the step-(3) receipt's site — a boot-time AMO on hart 0's arm, i.e. the
lock lane's `acquire`, which must hand back `hart_view_lb (log top)` for the
caller to keep.  **That single postcondition is the whole of what this lane is
waiting on**, and §0.35′(iii) is already committed to producing it.

The kernel table is the ideal client for this shape: `HartSKpt.kpt_noupd` proves
its PTEs are never written back (A and D are preset in `kperm_flags`, so
`update_PTE_Bits` declines for every access kind), so it is written once, by
`kvminit`, and never mutates again — a context that owns it can be parked
immediately and never needs to run.

### K4c. AND THE DRAIN IS TRUE AT `0xac` — it is not carried, which is a different problem

Worth recording, because it says the ruling's instinct about the SITE is right
and only the bound is wrong.  Read off `ProofUserinit.v`'s decode table, the tail
of `userinit()` after `+0x2e jal ra,release` is

```
  +0x32 .. +0x36   c.ldsp ra / s0 / s1
  +0x38            c.addi16sp sp,32
  +0x3a            c.jr ra
```

— three loads and two register ops, **no stores** — and `ProofMain.mn_grp_started`
then runs `auipc`, `addi`, `c.li`, `fence` (`0xa2`, `0xa6`, `0xaa`, `0xac`), also
**no stores**.  `release`'s `amoswap.w zero,zero,(a0)` is hart 0's last own
message, and an AMO leaves the hart at the log top (`TsoCtx.ctx_absorb`'s own
premise `length g.(glog) ≤ g.(gtv) cpu_id` is the fact that leaf establishes).
`own_pub` is unchanged from there to `0xac` and `gtv` only grows, so

> **`drained g` — `own_pub (hart_agent cpu_id) g.(glog) ≤ g.(gtv) cpu_id` — HOLDS
> at `main+0xac`.  Nothing in the tree carries it there.**

Contrast `main+0x76`, where the same publication would be attempted immediately
after `kvminit` wrote the table: there `drained` is maximally FALSE.  So `0xac`
is the right instruction and `kptree_publish` (not `kptree_publish_top`) is the
right gate; what is missing is a way to say at `0xac` what `release`'s AMO knew.
Threading a global "no own writes since" token through every store leaf is the
expensive spelling and is refused.  K4b's parked-stamp is the cheap one: it does
not carry the drain at all, it carries a comparison that was already made.

**AND THE SITE IS THE LOCK LANE'S, WHICH HAS NOT BUILT IT YET.**
`TsoCtx.ctx_bound_raise` (`TsoCtx.v:438`) has **no client in the tree**: its only
occurrences outside its own file are three COMMENTS in `WpLock.v` (`:818`,
`:824`, `:1376`) describing the acquire-side absorb §0.35′(iii) names.  So
nothing this lane needs has a producer yet, and the KPT lane cannot make one
without editing `WpLock`/`WpSconfLock`, both on its forbidden list.  **Step 3
stops here and is handed across.**

### K4d. AND THE RIGHT BOUND IS THE PUBLISHER'S **CONTEXT** BOUND — which is §0.36′(d) read literally

`ctx_phys_pin_mint` pins at `g.(gtv) cpu_id`, a HART fact, and hart 0's hart
receipt at `0xac` is `own_context`'s own `view_lb … K`.  But §0.36′(d) says
*"kpt_creds restates ξ-relatively"*, and doing that literally gives a strictly
better statement of the whole tranche:

```coq
  (* §0.36′(d), and it is §0.35′'s buy/carry/cash one tier up *)
  Definition kpt_creds : iProp Σ :=
    (∃ B : nat, kpt_bound B ∗ TsoCtx.ctx_floor cur_ctx B)%I.
```

* **It is still persistent** (`ctx_floor` is `llb` on the context's bound name),
  so `tlb_res_pt`'s arity does not move and the eight threading files stay
  opaque — A6.105's rule again.
* **It cashes for free**: `own_context ξ` carries `ctx_at ξ 1 B_ξ D`,
  `view_lb … K` and `⌜B_ξ ≤ K⌝`, so `ctx_floor ξ B` gives `B ≤ B_ξ ≤ K ≤
  g.(gtv) cpu_id` — exactly what `TsoCtx.ledger_read_pin_ok` spends, with no
  hart receipt in the residue at all.  It also *survives a migration*, which the
  `view_lb … (hart_agent cpu_id)` form does not (§0.35′'s whole point, one tier
  up).
* **hart 0 gets it at `0xac` for nothing**, PROVIDED the publication bound is
  `B := B_ξ` (the publisher's context bound) rather than `length g.(glog)`:
  `ctx_floor ξ B_ξ` is already inside `own_context`.
* **the secondaries get it exactly as §0.36′(b) says**: `B_ξ ≤ K ≤` (position of
  the `started` write, which is later in hart 0's program order), so a secondary
  that has read `started == 1` has a view past `B_ξ`, and `ctx_bound_raise` at
  its own ξ′ turns that into `ctx_floor ξ' B_ξ`.  That IS the bound relation the
  ruling names, and it needs no `view_lb` in the residue either.

So the ruling's own clause (d) fixes clause (3)'s bound, and **everything then
reduces to the single obligation `t ≤ B_ξ` for each of the table's slots** —
which is the comparison K4a/K4b localise, and nothing else.

## K5. WHAT LANDED — §0.36′ step 2's gate twin

`HartSKpt.kpt_slot_bytes_ctx`, purely additive, beside `kpt_slot_bytes_pin`:

```coq
  Lemma kpt_slot_bytes_ctx (img mem : bytemap) (log : list pwmsg)
      (V : agent -> nat) (tv : nat) (rs : regstate) (d : dev_state)
      (xi : CtxId) (dq : dfrac) (a : Arch.pa) (w : mword 64) :
    V (hart_agent cpu_id) = tv ->
    gen_heap_interp mem -∗ tso_interp_of riscv_eraGS img mem log V -∗
    TsoCtx.own_context xi -∗ pt_slot_own (UTier xi) a dq w -∗
    ⌜forall tv', (tv <= tv')%nat -> forall j, (j < 8)%nat ->
       exists b, tso_read img log (hart_agent cpu_id) tv' (pa_add a j) = Some b
                 /\ b ∈ pte_slot_set w j⌝ ∗ …(all four given back)
```

Its conclusion is `kpt_slot_bytes_pin`'s **character for character**, so
`fobl_of_sets` / `fobl_ex_of_sets` and everything above them consume it
unchanged — which is A6.106 §5's "the gate goes two-armed" with the arity
fixed.  It is built off `TsoCtx.ctx_phys_load_bytes_ok` (`TsoCtx.v:4026`), whose
conclusion is at `hart_agent cpu_id` — exactly `HartMFetch.fobl_ram`'s
quantifier, and A6.106 §4's point that the pinned arm's ∀-agent form is stronger
than the walk needs.

Two things it does that the pinned arm does not, both forced and both cheap:

* it takes `gen_heap_interp mem` as well — a ctx fact's TIMESTAMP is in the tso
  ghosts but its VALUE is in the flat cell, so the tie reads against both
  (`TsoCtx.ctx_load_ok`'s own note).  Every caller of the walk gate holds
  `mstate_interp`, whose second conjunct is that;
* it discharges the byte-set obligation with `kpt_slot_set_self`, a local copy
  of `KptPublish.pte_slot_set_self` (eight lines, off `PtAdBits.pte_set_ad_refl`
  and `PtTree.pte_ad_byte0_set_ad`), kept local so `HartSKpt` gains no new
  dependency edge.

**Not wired.**  Threading it into `kpt_path_obl` means giving that lemma the
`gen_heap_interp` its callers already hold and making its `kpt_bound`/`view_lb`
pair a disjunction — and there is no point doing that while the arm it would
serve has no exit (K3/K4).  It is landed as the measured artifact that §0.36′
step 2 is available and costs nothing.

## K6. THE NUMBER

**1100 `.vo` of 1338, RED-9 — the A6.107 set, held**, sentinel-backed
(`MAKEEXIT=2` + `DONE`, round r1, 300 s).  `HartSKpt.v` is deep, so the round
recompiled **554 files** — its whole reverse cone — and the error roots came back

> `ProofForkretPark`, `ProofKernelvec`, `ProofMain`, `ProofSwtch`,
> `ProofVirtioDiskIntr`, `ProofVirtioDiskRwD`, `UptWalkPt`, `UserMemPt`,
> `WpSconfLock`

with the full 238-file no-`.vo` list **identical character for character to r0**
(`diff`).  **Red-list delta 0.**  `^Abort` / `^Admitted` / `^Axiom` are 0 in
`HartSKpt.v`; `kernel-rocq` / `user-rocq` untouched.

> **SEVENTH INSTANCE OF THE LANE'S RECURRING SHAPE** (A6.106 §4 counted six).
> The settle K4 asks for is `ctx_park`/`ctx_resume`, written for §0.27′'s park
> protocol; the ξ-relative cash-in K4d asks for is
> `TsoCtx.own_context_floor_view`, written for §0.35′'s lock floor; the
> interp-free transport K4b asks for is `TsoCtxAbsorbLb.ctx_dom_of_parked_lb`,
> written for the M2 sites.  *Again nothing had to be built — and this time the
> expensive step was noticing that one of the already-built laws does not help.*

## K7. WHAT IS OWED

1. **To the lock lane — and it is ONE postcondition, not a mechanism.**
   `acquire` must hand its caller the receipt its AMO already establishes:
   `hart_view_lb K` (persistent, so it costs the caller nothing to keep) at a
   `K` the caller can compare a parked stamp against — i.e. `hart_view_lb_get`'s
   output, exposed rather than consumed inside the leaf.  §0.35′(iii) is already
   committed to producing exactly that.  With it, K4b's five steps are all
   existing lemmas and the KPT lane closes on its own.
2. **To the owner** — the ruling's step 3 as written ("the publication moves to
   `main+0xac` … `kptree_publish_top`") is refuted by K3: the top-of-log bound is
   above its own publisher's view, and there is no instruction between `0xac` and
   `scheduler`'s first AMO that raises that view.  Recommended repair, in order
   of confidence:
   * **K4b** — give the kernel table its OWN context, park it after `kvminit`,
     and let the park protocol's stable pair be §0.36′(b)'s "PT-validity stamp".
     Every lemma exists; the one input is (1).
   * **K4d** — restate `kpt_creds` ξ-relatively as
     `∃ B, kpt_bound B ∗ ctx_floor cur_ctx B` (the ruling's own clause (d)),
     which is the right SHAPE regardless of which repair lands and whose cash-in
     `TsoCtx.own_context_floor_view` is already written.
   * **fallback**, if neither closes — an author-indexed second arm on
     `TsoMemPa.pin_ok` ("the agent whose message is latest reads it at every
     view", which `TsoMemPa.visibleb`'s own second disjunct already licenses).
     Whole-tree (`ts_pay`/`ts_ok`), and NOT recommended.
3. **Still open in this lane, blocked on (1)** — step 1 (`tlb_res_pt`'s
   two-armed last conjunct, which is what carries hart 0 from `main+0x76` to
   wherever the table's facts become transportable), the rest of step 2
   (`kpt_path_obl`'s disjunction, off K5's landed twin), `ProofMain:996`'s
   arity, and `ProofMain`'s missing eighth argument to `wp_kvminithart_sconf`.

## K8. BUILD RECIPE FOR THIS LANE'S TREE

```sh
cd /shared/xv6iris-3-kpttree            # NOT a git checkout; no .gitignore
flock /tmp/claude-gcp.lock \
  /shared/xv6iris-3/gcp-rocq/run-on-gcp --sync-only   # → _shared_xv6iris-3-kpttree
# then, detached on the VM, per-subtree coq_makefile (never the top-level make):
#   for d in model-xv6iris kernel-rocq user-rocq; do (cd $d && coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile -j90); done
#   cd iris && coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile -j90 -k
```
Cold round: 440 s.  The flock is shared with the lock lane and that lane holds it
across its whole build-and-poll, so a wait of ten minutes or more is normal and
is not a hang.

## K9. FILES THIS LANE CHANGED

* `iris/HartSKpt.v` — `kpt_slot_set_self`, `kpt_slot_bytes_ctx` (additive only;
  inserted between `kpt_slot_bytes_pin` and `fobl_of_sets`).

Nothing else.  No spec signature moved; no file on the lane's forbidden list was
opened.
