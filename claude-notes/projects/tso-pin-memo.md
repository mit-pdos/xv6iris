# DECISION MEMO — the per-address history invariant for canon-stable racy cells

READ-ONLY ANALYSIS (2026-08-26) against the main repo on branch `tso` @ `c1bd706d`
for the notes and the FLIP WORKSPACE for the machine/kit code (durable mirror:
`/shared/xv6iris-3-fliptree-backup`); nothing in either tree was modified, and the
one probe (§7) was compiled and removed.
PURPOSE: the owner-decision record for A6.47 ruling 3's replacement — the
canon-stable racy-cell question — whose ask is §8's three rulings.

Read against the flip note A6.36–A6.47 and the fliptree at `.../fliptree/iris/`. One
probe compiled green (below).

---

## 0. THE HEADLINE, AND IT REFRAMES THE QUESTION: THE OBLIGATION IS FALSE BEFORE THE HISTORY INVARIANT EVEN ENTERS

A6.47's ruling-3 refutation is correct but it stops one step short. The gap is not
only that `phys_ledger_at` knows the latest write. **The obligation the walk has to
discharge quantifies the value OUTSIDE the view**, so no per-address history fact of
any shape can discharge it.

`HartMFetch.v:589`:

```coq
Definition fobl_ram (img : TsoMemPa.bytemap) (log : list pwmsg)
    (tv : nat) (pa : Arch.pa) (n : N) {m : N} (w : bv m) : Prop :=
  ∀ tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
    tso_read_bytes img log (hart_agent cpu_id) tv' pa n w.
```

and the predicate-indexed PT read (`PtTreeAdue.v:934`) asks for

```coq
        (∃ w, ⌜fobl_ram img log tv pa 8 w⌝ ∗ ⌜P w⌝) ∗
```

— **one `w`, good at every reachable view.** After a completed A/D write-back at
timestamp `t` above a reader's view, the reader at `tv' < t` reads the OLD word and
at `tv' ≥ t` reads the NEW one. Two values, one existential. The statement is false
of the machine.

It is false at the machine rule too, not just at the PT lemma.
`HartEvents.wp_hart_ram_read_plain` (`:150–164`) and its `swp` twin (`:629–641`) both
read:

```coq
       tso_interp_of riscv_eraGS img σ.(mem) log V ={⊤,∅}=∗
       ∃ w : bv (8 * n),
         ⌜∀ tv' : nat, (tv <= tv')%nat -> (tv' <= length log)%nat ->
            tso_read_bytes img log (hart_agent cpu_id) tv'
              (Interface.ReadReq.pa req) n w⌝ ∗
```

The `∃ w` is outside because the rule needs `w` to name the resumption
`C (hread_resume (bv_unsigned w) m)` before the machine picks `tvn`. **So the first
ruling is not "which history ghost"; it is "the plain read rule gets a
value-after-view twin."**

The good news is that it costs nothing. The generalized rule

```coq
       ⌜∀ tv', (tv ≤ tv')%nat → (tv' ≤ length log)%nat →
          ∃ w, tso_read_bytes img log h tv' pa n w ∧ P w⌝ ∗
       ▷ (|={∅,⊤}=> … ∗
            (∀ tvn w, ⌜tv ≤ tvn⌝ -∗ ⌜tvn ≤ length log⌝ -∗
               ⌜tso_read_bytes img log h tvn pa n w⌝ -∗
               view_lb … h tvn -∗ WP (C (hread_resume (bv_unsigned w) m))))
```

**subsumes the existing one**, and the existing statement is re-derivable from it
verbatim — the derivation is the byte-wise determinism step already sitting in the
current proof at `HartEvents.v:197–201` (`bv_eq_of_bytes` on `Hrd tvn` vs
`Hbytes'`). So this is exactly A6.47 ruling 2's move made once more (parameterise the
continuation), with the same measured cost: **the eleven existing call sites do not
move** (`HartPilot:442`, `HartSMem:1946/2045`, `HartMFetch:702/801`,
`HartMemRun:521`, `HartMLoad:418`, `PtTreeAdue:724/987`, `SmodeCorePt:1069/1176`).

---

## 1. THE SECOND MEASUREMENT: RULING 3'S `⌜t ≤ B⌝` IS TRUE FOR TWO OF THE THREE SLOTS

A/D is defined only on LEAF PTEs, and the tree agrees: every write path targets
`pt_addr0 p1 vpn` and nothing else — `HartSKpt.kpt_leaf_write_node` (`:547`),
`KptShare.tlb_res_pt_translateAddr_at` (`:366–373`). Levels 2 and 1 are boot-written
and never written again, and `kpt_slot_node`'s two pinned specialisations
(`kpt_pte2_node`, `kpt_pte1_node`) already read them at an EXACT value.

So the withdrawn tie is not wrong, it is **mis-scoped**:
`∃ t, ⌜t ≤ B⌝ ∗ phys_ledger_at a dq w t` is a stable, re-establishable conjunct for
interior slots (nothing above `B` touches them; re-closing the invariant re-proves it
by `id`), and `ledger_read_at_ok` + the boot receipt discharges those two levels
TODAY. **Only the leaf needs new machinery.** That halves the problem and should be
recorded before anything is built.

## 2. THE THIRD MEASUREMENT: A/D VARIANCE LIVES ENTIRELY IN BYTE 0

`PtAdBits.v:34`:

```coq
Definition pte_set_ad (w : mword 64) (a d : mword 1) : mword 64 :=
  update_subrange_vec_dec w 7 0 (…)
```

bits 6 and 7 only (`pte_canon_inv`'s proof case-splits on exactly `k =? 6` /
`k =? 7`). So the canon class of a word is **four words differing only in byte 0**,
and a BYTE-KEYED confinement fact is exactly as strong as a window-keyed one: bytes
1..7 pin to singletons, byte 0 to a 4-element set. This matters because every ghost
in the ledger is byte-keyed (`ts_name : ghost_map Arch.pa nat`), so the fix can stay
byte-keyed and needs no window-shaped ghost.

---

## 3. CANDIDATE (i), INV-LOCAL HISTORY BIG-OP — **REFUTED, and the refutation is short**

The coverage claim is not statable over ghosts alone. Write the honest form:

```coq
Ψ := □ ∀ i m, ledger_msg_at i m -∗ ⌜a ∈ dom (pm_map m) → canon-pure m a⌝
```

To PROVE `Ψ` you must, from an arbitrary persistent fragment `i ↪[logm_name]□ m`,
conclude `i < |log|` — and that step is `ghost_map_lookup` against
`ghost_map_auth (era_logm_name E) 1 LM`, which lives in `tso_interp_at`
(`RiscvPtsto.v:2175`) and is **never inside an invariant body**. Inside `kpt_body`
there is no auth, so `Ψ` is unprovable there; and it cannot be *carried* either,
because carrying it would amount to asserting a fact about messages that do not exist
yet.

The element-exclusivity argument (kpt_inv owns the γts element at full fraction,
`ledger_store_ok`'s premise is `[∗ map] a ↦ v ∈ Pold, phys_ledger a (DfracOwn 1) v`
with `dom Pold = dom Pnew`, so every append touching `a` opens kpt_inv) is TRUE and is
the real reason the property holds. But it is an induction over the machine's step
relation, and **the only place that induction can live is the state interpretation** —
that is what a state interpretation *is*. So (i)'s big-op is sound only as bookkeeping
*under* an interp tie; on its own it is the same class of unprovable statement A6.36
deleted `wp_hart_ram_read_strong` for.

Verdict: **(i) does not stand alone. Rule it out explicitly so nobody builds it.**

## 4. CANDIDATE (iii), PER-ADDRESS WRITE-HISTORY GHOST — sound, general, and dominated

`γwl : Arch.pa → list nat` with the interp tie `i ∈ γwl a ⟺ message i touches a` is
sound and inductive. Costs, measured:

- the ⟸ direction forces the fragment into the ledger element (a store must hold
  `γwl a` to extend it), i.e. the same edit to `phys_ledger`/`ctx_pointsto` that (ii)
  needs, PLUS a second ghost map;
- entries grow without bound; every consumer does list reasoning where (ii) does set
  membership;
- it delivers a *history*, but the walk does not want a history — it wants the
  confinement conclusion, and deriving that from a list of timestamps requires
  re-running the `read_down` scan against the list at proof time, at every discharge.

**The M4 dual-use claim does not hold up.** I checked `WpLock.v:271–327` and the flip
note's M4 entry (note lines 873–890): the marker is the **parked-context** idiom —
"the invariant must hold the cell's context PARKED, the acquirer mints `ctx_dom` from
it with `ctx_dom_of_parked` and moves the word with `ctx_morph_word`" — not a racy-
history fact. The lock word is taken by AMO (top-view read,
`swp_hart_ram_read_excl`), and `lk_cpu_res` is transferred exclusively, not read
racily. So (iii) buys generality nobody has asked for.

Verdict: **strictly dominated by (ii). Not the racy kit's foundation; there is no
second customer today.**

## 5. CANDIDATE (ii), THE CANON PIN — **RECOMMENDED**, in a refined form

### 5.1 The tie, and it is the pure statement the walk actually wants

Pin payload `(B, S)` with `B : nat` a floor and `S : gset (bv 8)` the allowed byte
values. One new conjunct in `tso_interp_at` / `tso_interp_of`:

```coq
  ⌜∀ a B Sv, CP !! a = Some (B, Sv) →
     ∀ (h : agent) (tv' : nat), (B ≤ tv')%nat →
       ∃ b, tso_read img log h tv' a = Some b ∧ b ∈ Sv⌝
```

Note what this is NOT: it is not a history, not a list of messages, not a timestamp
comparison. It is **the discharge conclusion itself, stored where it can be
maintained** — which is why the walk's final lemma is a one-liner off it (§5.5). The
floor `B` is unavoidable: at mint time a slot's pre-PT history contains the `kalloc`
memset's `0`, which is not in the canon class, so an unconditional tie is false. `B`
is the pin's *publication* bound, fixed at mint and never moved.

### 5.2 Where the side condition lives: **in the ghost element's value, not in the gate's premises**

The question asks whether the gate's γts-element premise can carry the pin status so
unpinned payers are unaffected. **Yes, and that is the whole design.** Change

```coq
  tsomem_tsG :: ghost_mapG Σ Arch.pa nat
```

(`TsoGhost.v:79`) to `ghost_mapG Σ Arch.pa (nat * option (gset (bv 8) * nat))`, and
keep the SEALED definitions pinned to the unpinned value:

```coq
  Definition phys_ledger_def a dq v :=
    (∃ t, phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, None))%I.
```

Then:

- **every existing store gate is sound with no new premise.** `ledger_store_ok`,
  `ctx_store_ok`, `ledger_store_win_ok` all take `phys_ledger`/`ctx_pointsto` for the
  whole footprint; by definition those elements are unpinned, so the tie's frame arm
  applies definitionally. Unpinned payers are untouched in *statement* and nearly
  untouched in *proof* (the change is inside the seal).
- a pinned tier
  `phys_ledger_pin a dq v t B S := phys_pointsto a dq v ∗ a ↪[ts_name]{dq} (t, Some (S,B))`
  gets its own gate `ledger_store_pin_ok` whose only extra premise is `vnew ∈ S`.
- minting a pin is a `ghost_map_update` at full fraction — one-way, done once, and
  A6.9's "the ledger has no mint" rule is preserved (no element is created, only
  updated).

Element sites to touch, counted: **`ts_name` occurs 21 times across 4 files**
(`TsoCtx.v` ×11, `RiscvPtsto.v` ×4, `RiscvExec.v` ×1, `DiskInv.v` ×1 comment). The
element appears in exactly six sealed definitions — `ctx_pointsto_def` (`:493`),
`ctx_phys_pointsto_def` (`:1619`), `phys_ledger_def` (`:1941`), `phys_ledger_at`
(`:1982`), `pristine_byte` (`:1454` and `RiscvPtsto:1521`), `ledger_elem0` (`:2073`) —
plus two `ghost_map_auth` update sites (`ctx_store_bytes` `:1701–1711`,
`ledger_store_bytes` `:2145–2149`). **`phys_ledger_at` has zero occurrences outside
`TsoCtx.v`.** This is a genuinely contained change.

### 5.3 Soundness at every arm

- **Hart store arms** — `ledger_store_ok` (`TsoCtx.v:2177`): frame for unpinned,
  `vnew ∈ S` for pinned. Both proved by the probe's `pin_ok_app` /
  `pin_ok_app_frame` (§7).
- **The A/D write-back** — `HartSKpt.kpt_leaf_write_node` via
  `HartMStore.wobl_ram_ledger_ex`. `m0' = pte_set_ad q0 a d` is already derived in that
  proof at `:562` (`Hset`), so `vnew ∈ S` is `pte_set_ad_testbit` at byte 0. One pinned
  twin of `wobl_ram_ledger_ex`.
- **DMA** — `RiscvLang.v:1353` / `:1429`:
  `(W = ∅ ∧ log' = glog) ∨ (W ≠ ∅ ∧ log' = glog ++ [PWMsg W disk_agent])`. The disk
  never writes a PT slot, so the frame arm is free. **Caveat that is not the pin's
  fault:** ruling 4 is not started, and `VirtioProto.virtio_proto_step` still performs
  the `gen_heap` update itself — so today the DMA append does not pay `ts_name` *at
  all*, which already breaks the EXISTING `latest` tie. Ruling 4 is a prerequisite for
  the ledger's soundness with or without the pin.
- **Power / era wipe** — `RiscvLang.v:1291–1293`:
  `g'.(glog) = [] ∧ g'.(gimg) = g'.(gmem) ∧ ∀ c, g'.(gtv) c = 0`, and the era's ghosts
  are re-allocated wholesale (`era_interp` is dropped under `if g.(gpow)`,
  `RiscvPtsto.v:2209`). **The pin map starts empty in a fresh era. Zero obligation.**
  (Also: adequacy does not yet allocate `era_ts_name` at all — `RiscvAdequacy.v` has no
  `ts_name` mention — so the boot-allocation cost is pending work either way, step 6 of
  §7's order.)

### 5.4 Stability: the pin fragment is persistent and the tie is NOT in the invariant

`pin_at a B S := a ↪[ts_name]□ …`-shaped persistent fragment (or a separate
discarded-fraction entry). The invariant-stability question that killed (i) does not
arise: **nothing in `kpt_body` asserts anything about the log.** `kpt_body`'s arity and
body are UNCHANGED; only `PtTree.pt_slot_own`'s `None` arm moves from
`phys_ledger_word` to its pinned twin, which the A6.21 tier index exists precisely to
localize (`PtTree.v:934–962`: `pt_slot_own_forget` / `_ker` are the only two laws, and
`pt_slot_own_forget` is what all ~50 consumer files actually use).

**And this is the answer to A6.47's arity worry.** `kpt_inv` has **142 mentions across
36 files** (I re-measured; the note's "~130 / 35" is right). The pin carries `B`
*inside the ghost element*, so **`kpt_inv` needs no parameter at all** — the tree-wide
sweep is avoided, not paid. The reader learns `B` from the pin fragment inside the
opening, and matches it against its own receipt via a one-shot agreement ghost
`kpt_bound B` — a 30-line copy of `KptGhost.kpt_lb`'s existing shape — carried in the
per-hart `tlb_res_pt` (`KptShare.v:135`, 4 touch points: `_intro`, `_open`,
`_satp_acc`, `_kpt_inv`).

### 5.5 The walk's final discharge lemma

```coq
  Lemma kpt_leaf_node_canon_obl (root_ppn : mword 44) (t0 : ptree)
      (vpn : mword 27) (p2 p1 leaf0 : mword 64) (a0 d0 : mword 1) (B : nat) :
    ptree_maps t0 vpn p2 p1 (pte_set_ad leaf0 a0 d0) ->
    kpt_bound B -∗ view_lb view_name loglen_name (hart_agent cpu_id) B -∗
    kpt_lb t0 -∗ kpt_inv root_ppn -∗
    xread_obl_ex_v (pt_addr0 p1 vpn) (fun w => pte_canon w = pte_canon leaf0)
```

with `xread_obl_ex_v` the value-after-view obligation of §0. Its proof: open `kpt_inv`
(already done at `HartSKpt.v:127`), read the leaf's eight pinned elements out of
`pt_slot_own None`, apply `ledger_read_pin_ok` per byte (which is
`ledger_read_vis_ok`'s proof with `tso_read_of_latest` replaced by the interp's pin
conjunct — ~15 lines), reassemble. Levels 2/1 keep `kpt_slot_node` verbatim on
`ledger_read_at_ok` + `⌜t ≤ B⌝`.

The one genuinely new PT-layer lemma is the **byte→word reassembly**: from
`b_j = nth_byte leaf0 j` for `j ≥ 1` and `b_0` agreeing with `nth_byte leaf0 0` outside
bits 6–7, conclude `∃ w, read = w ∧ pte_canon w = pte_canon leaf0`. `bv_eq_testbit` +
`pte_set_ad_testbit`, both already in `PtAdBits.v`. Estimate 40–60 lines. **This is the
only piece I did not probe.**

### 5.6 The one residual sub-problem, stated honestly: hart 0's pre-`started` window

`ProofMain.v:974` calls `kpt_inv_alloc` **before** `kvminithart` (`:995`), so hart 0
sets `satp` and then walks — on every instruction fetch — through the SHARED
invariant, at a view below `B`, with A6.41's measurement saying nothing drains it. So
the pin's `B ≤ tv'` arm does not serve hart 0's first walks. Two ways out, and the
owner should pick:

- **(a) reuse ruling 1's disjunction.** Make the pin's tie two-armed exactly as
  `ledger_vis` is (`TsoCtx.v:2013`): `(B ≤ tv') ∨ h = A`, with `A` the pin's recorded
  author. The mint then needs, per slot, the author fragment for the slot's latest boot
  write — which `ledger_store_ok` now hands back (ruling 1) but which the boot
  PT-construction lane must *keep*. That threading lands in `BootCarve` / `TransPt` /
  `KptTree`'s store sites — **the already-red boot lane**, so it is queued work rather
  than new fallout.
- **(b) move the publication.** Keep `tlb_inv_pt` (the exclusive bundle, which
  `KptShare.v:34–39` deliberately preserves) across hart 0's window and mint the pins at
  `__sync_synchronize` — a `Barrier_RISCV_rw_rw`, which `RiscvLang.fence_drains`
  (`:645`) DOES drain, so hart 0 emerges with a top receipt and needs no author arm
  ever. Cost: `ProofMain`'s publication moves, and hart 0's window discharges at the
  exclusive tier with `ledger_vis_own` (single-valued there, because no other hart
  writes PT slots before `started`).

I lean **(b)**: it needs no new pin field, it uses the drain the ISA and the model both
already have, and it makes every hart use one gate — which is the property A6.47 ruling
1 was chosen for.

## 6. CANDIDATE (iv), THE DEGENERATE SCOPE — **not actually cheaper; it collapses into (ii)**

"Hard-code an A/D-only tie into a per-slot persistent accumulator" fails for the SAME
reason (i) fails: an accumulator held anywhere but the interp cannot state coverage.
Once you move it to the interp, the only difference from (ii) is that the payload is
`(bv 64, mask)` instead of `gset (bv 8)` — a saving of zero lines, at the cost of a
machine-layer interp conjunct that names `pte_canon` (a layering violation
`RiscvPtsto.v` does not have today). **Reject (iv); take (ii) with a generic payload.**

---

## 7. THE PROBE — RUN, GREEN, FIRST TRY

I wrote and compiled `ZZPinProbe.v` against `TsoMemPa.vo` (leaf file, no Iris; 1.0 s
compile) and then removed it from the fliptree. It proves, over the real machine:

```coq
Definition pin_ok img log a B Sv : Prop :=
  forall (h : agent) (tv' : nat), (B <= tv')%nat ->
    exists b, tso_read img log h tv' a = Some b /\ b ∈ Sv.

Lemma pin_ok_mint img log a B Sv t v :
  latest img log a t v -> (t <= B)%nat -> v ∈ Sv -> pin_ok img log a B Sv.

Lemma read_down_app_frame img log m h tv a t :        (* NOT in TsoMemPa *)
  (t <= length log)%nat ->
  read_down img (log ++ [m]) h tv a t = read_down img log h tv a t.

Lemma pin_ok_app img log m a B Sv :
  pin_ok img log a B Sv ->
  (msg_byte m a = None \/ exists b, msg_byte m a = Some b /\ b ∈ Sv) ->
  pin_ok img (log ++ [m]) a B Sv.

Lemma pin_ok_app_frame …                              (* the unpinned-store arm *)
```

Total: 75 lines, all four green. What this settles: **the mint obligation is exactly
A6.47's refuted `t ≤ B` tie** (false as a standing invariant, true as a *creation*
obligation — that is the whole re-framing), **the store gate's side condition is
exactly `vnew ∈ S`**, and **an append that misses a pinned address is free with no
premise at all**. `read_down_app_frame` is a genuine gap in `TsoMemPa` —
`read_down_app_below` (`:295`) demands `t ≤ tv`, which a reader below the append does
not have.

THE FILE: `/shared/xv6iris-3-fliptree-backup/ZZPinProbe.v`.

THE COMPILE LINE (copy the file into the fliptree's `iris/`, compile, then remove it —
the `eval` must be chained into the same command, durable-notes' switch rule):

```sh
cp /shared/xv6iris-3-fliptree-backup/ZZPinProbe.v FLIPTREE/iris/ && \
cd FLIPTREE/iris && eval $(opam env --switch=/shared/xv6rocq) && \
coqc -w -notation-overridden -R . xv6iris -R ../model-xv6iris Riscv \
     -R ../kernel-rocq Kernel -R ../user-rocq User ZZPinProbe.v
# ~1.0 s, no output = green.  Then:
rm -f FLIPTREE/iris/ZZPinProbe.{v,vo,vos,vok,glob} FLIPTREE/iris/.ZZPinProbe.aux
```

**Next probe, if the owner wants one before committing:** the §5.5 byte→word
reassembly against `PtAdBits.vo`, ~40 lines. It is the only unvalidated pure step.

---

## 8. RANKED RECOMMENDATION

**Owner rulings needed (three, in this order):**

1. **Ratify the value-after-view read rule.** `wp/swp_hart_ram_read_plain_ex` beside
   the existing pair, existing rule re-derived from it, eleven call sites unmoved.
   Without this ruling nothing else matters — the obligation is false as stated. *(This
   is ruling 2's move applied to the value instead of the receipt.)*
2. **Rule (i) and (iv) out, adopt (ii) with the element-carried pin, reject (iii).**
   Record the reason for (i) in one sentence — *coverage needs the log auth, which lives
   only in the interp* — so it is not re-proposed. Record that (iii) has no second
   customer: the M4 marker at `WpLock` is the parked-context idiom, not a racy history.
3. **Pick (a) or (b) for hart 0's pre-`started` window** (§5.6). I recommend (b), the
   drain at `__sync_synchronize`.

**Mechanical work, once ruled (≈15 files, ≈40 statements, no tree-wide sweep):**

`TsoMemPa` (+4 pure lemmas, 3 of them already proved) → `TsoGhost` (1 class field) →
`RiscvPtsto` + `RiscvExec` (the tie, twice, ~8 edits) → `TsoCtx` (6 sealed defs + 2
auth updates + 5 new pinned lemmas) → `HartEvents` (2 new rules, 0 call sites) →
`HartMFetch`/`PtTreeAdue` (`fobl_ram_ex`, 1 obligation restated) → `PtTree` (the `None`
arm) → `KptGhost` (`kpt_bound`, a `kpt_lb` copy) → `KptShare` (mint + residue field,
`kpt_body` UNCHANGED) → `HartMStore` (1 pinned store twin) → `HartSKpt` (the discharge)
→ `ProofMain` (1 mint site) → boot lane (already red).

**What this buys beyond unblocking `HartSKpt`:** the 142-site / 36-file `kpt_inv` arity
sweep A6.47 flagged is **not paid** — the bound rides in the ghost element. And the
`⌜t ≤ B⌝` tie A6.47 withdrew is **partially reinstated**, correctly scoped, for levels
2 and 1.

**One prerequisite outside this lane:** ruling 4 (`WpUart` / `virtio_proto_step` turned
inside out) is required for the DMA append to pay `ts_name` at all. That is a
pre-existing hole in the `latest` tie, not something the pin creates — but any interp
tie, including today's, is unsound until it lands.
