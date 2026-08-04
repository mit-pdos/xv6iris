# Project: crash safety / power cycling (in-logic, generational)

Design: [`../design/crash.md`](../design/crash.md) — read it first; it
carries the full architecture and the decision record.

## Status (2026-08-03)

**Milestone 0 — the mechanism prototype — is DONE and AXIOM-FREE:
`iris/CrashProto.v`** (in `_CoqProject`; a leaf, no Sail imports, compiles
in seconds). It validates every novel Iris mechanic of the design
end-to-end on a miniature language with the same structural properties:
generation-indexed stateless thread expressions with corpse arms; the
power thread (PowerOff bumps the generation, PowerOn resets + FORKS the
new generation via `prim_step`'s `efs` — stock Iris handles the fork
obligations fine); the generational `state_interp` (mono-nat counter +
gen→era-gname registry with the dom-shape + durable disk auth + the
era-existential memory auth, abandoned at PowerOff); `wp_dead` from one
mono-nat lower bound; the base-rule FOUR-WAY case split in `wp_work`
(live / dead / current-but-off REFUTED BY THE REGISTRY SHAPE / unborn
refuted by the birth bound); the crash-spanning `crash_inv` (toy P_fs =
"disk cell 0 is even") opened instantaneously around the one disk-writing
step and FRAMED by both power arms; and `proto_adequacy` via stock
`wp_strong_adequacy` over the singleton pool `[PowerE]`, with ONE
hypothesis (initial disk even) and a conclusion that also extracts the
invariant's pure shadow at every reachable state.
`Print Assumptions proto_adequacy_closed` = closed under the global
context.

Proof-engineering gotchas the prototype paid for (they will recur in the
real port):

- `mono_nat_lb_own_le` / `mono_nat_own_update` have an IMPLICIT `{n}`
  that is still an evar when the `≤` side condition is presented, so a
  bare `[lia|]` dies with "Cannot find witness" — pin it:
  `(mono_nat_lb_own_le (n := gn) (S gen) with "Hlb")`.
- `simpl`/`/=` UNFOLDS `set_seq` when its length exposes a constructor
  (`S gn + 0` reduces to `S (…)`; `gn + 1` does not), leaving the two
  sides of a registry-dom equation with different heads — `f_equal; lia`
  then fails. Rewrite the pure bound equality first
  (`assert (reg_bound σ' = reg_bound σ) by (rewrite /reg_bound /=; lia)`)
  and finish with `exact Hdom`.
- Inside an adequacy proof the `set`-bound ghost record is NOT a
  typeclass instance: apply the client WPs with explicit instances
  (`@wp_power Σ HPG …`), or the wand premise `crash_inv` elaborates at a
  mismatched instance and `iSpecialize … with "Hcinv"` fails with
  "cannot instantiate".
- `lia` on a proofmode goal needs `exfalso` first (an `envs_entails` is
  not arithmetic), and a `⌜∃ j, d = 2 * j⌝` inside `%I` needs the
  `%nat` ascription or `*` parses as a type product.

Remaining milestones below are the real-tree port; the prototype is the
template for milestones 1–4.

## Milestones (in order; each ends with a green full build)

1. **`riscvGS` fixed/era split + generational `state_interp`** — a pure
   refactor: composite class keeps the name `riscvGS` and its accessors,
   `state_interp` gains the fixed conjuncts (γgen mono-nat, registry,
   durable disk tie) in an always-live trivial form (one generation,
   `gpow = true` baked). Tree stays green with no statement changes.
   Touches RiscvPtsto/RiscvExec — bottom of tree, so every iteration is a
   full rebuild: validate with `make -f CoqMakefile -j16 -k`, run
   `tools/lemma_diff.py` and `tools/spec_vacuity.py` on touched files.
2. **Language + the GenId sweep** — **STAGE 2a LANDED (green, checkers
   clean, baseline 5 axioms)**: the four loop expressions carry an INERT
   generation index (`LoopE gen cpu`, …; no `prim_step` arm reads it, so
   the tree is exactly as strong as before), `Class GenId := gen_id : nat`
   ambient alongside CpuId, `Notation Loop := (LoopE gen_id cpu_id)`, and
   the tree-wide binder sweep. Lessons from the sweep (recurring):
   - **Never insert `GenId` blindly next to `CpuId`**: a PURE helper
     (`rget`/`tp_pin`, HartTp.v) gains a PHANTOM implicit that no use
     site can infer — undefined-evar errors far away. `wp_next` is pure
     transport and takes no GenId at all.
   - **Callee-parameter foralls stay gen-free**: a `_gen` function's
     per-callee parameter `forall (CID : CpuId), <wp body>` quantifies
     the RESUMING hart only; the body's GEN resolves from the enclosing
     section (the callee runs at the caller's generation).
   - **Hart-free continuation sections** (the `wp_next`-shaped `asl_*`/
     `pw_*`/`sp_*`/`uw_*`/`fw_*` blocks binding `(CID0 : CPU)`): one
     section-level `Context \`{GEN : GenId}.` (or a per-definition
     binder) — and mind digit-containing names when scripting
     (`pw_minus1`, `sp_exit0` escape `[a-z_]*`).
   - The `wp_next (fun (CID : CpuId) => …)` continuation lambdas — all
     ~250 — need NO change: gen stays ambient across a migration, which
     is exactly the intended same-generation-resumption semantics.
   **STAGE 2b LANDED**: inert `ggen`/`gpow` gstate fields (every arm
   preserves them; nothing reads them). **STAGE 2c LANDED**: the
   mono-nat generation ghost in `riscvFixedGS` (`riscv_gen_name`),
   `gen_auth (ggen g)` as `state_interp`'s fourth conjunct framed by all
   four lifting rules, `gen_born`/`gen_dead` (the persistent birth/death
   certificates), adequacy allocation. Deliberately DEFERRED from 2c:
   the gen→era REGISTRY — its value type must be Σ-free data (an era as
   plain gnames + gname lists, `park_name : nat → gname` becomes an
   NPROC list, `gen_heapGS` reconstructed from the fixed `gen_heapGpreS`
   + two stored gnames), because a `ghost_mapΣ nat (riscvEraGS Σ)`
   functor cannot mention Σ. Land that reshape together with its first
   consumer.
   **STAGE 2d LANDED**: `gen_born gen_id` rides in `minstret_inv` (third
   persistent conjunct; one destructure site, inside MinstretInv.v).
   **STAGE 2e-pre (next)**: the Σ-free era reshape — `riscvEraGS`
   becomes plain data (gnames + gname LISTS: `era_reg_names`/
   `era_strans_names`/`era_sie_names` length-NCPU, `era_park_names`
   length-nproc, heap/meta gnames with `gen_heapGS` reconstructed from a
   new fixed `gen_heapGpreS` field), compat accessors via `nth`, so the
   record is a legal `ghost_map` VALUE type (`ghost_map` constrains only
   keys, but the FUNCTOR `ghost_mapΣ nat (riscvEraGS Σ)` cannot mention
   Σ — hence Σ-free).
   **STAGE 2e** (the semantic switch, with milestone 3), design settled:
   - `PowerModel.v`: `boot_shape` (initially: the device corollary's
     hypotheses — Hram/plic_ok/virtio not-live+zero counters/`v_disk`
     preserved; hart reset registers join at M6), `dev_reset`.
   - Language: real arms gated on `gpow = true ∧ ggen = gen`; corpse
     self-loop arms on the complement; `PowerLoopE` — PowerOff bumps
     ggen + drops gpow, PowerOn sets gpow + `boot_shape` reset + forks
     `(LoopE ggen <$> enum CPU) ++ [UartLoopE ggen; DiskLoopE ggen;
     PlicLoopE ggen]`.
   - **The off-refutation WITHOUT the registry dom-shape**: a second
     fixed mono-nat `γstart` tracking STARTED generations, value
     `ggen + (if gpow then 1 else 0)` — monotone under both arms
     (PowerOff: ggen+1, pow 0 → same count; PowerOn: +1).
     `gen_started gen := lb (gen+1)`; a thread at `ggen = gen ∧ ¬gpow`
     contradicts it (count = gen, lb says ≥ gen+1). The registry keeps
     the dom-shape only for PowerOn's fresh-insert side condition.
   - `state_interp` goes ∃-era: fixed conjuncts + `∃ R, registry auth R
     ∗ ⌜dom R = set_seq 0 started⌝ ∗ (gpow → ⌜R !! ggen = Some E⌝ ∗
     interp E g)` where `interp E g` is today's triple stated at an
     EXPLICIT era record (new `_at`-parameterized forms of
     gregs_interp/gen_heap_interp/dev_interp).
   - `gen_cert := gen_born gen_id ∗ gen_started gen_id ∗
     gen_id ↪[γreg]□ riscv_eraGS` replaces `gen_born` in `minstret_inv`;
     the ~5 raw lifting rules take it as one explicit persistent premise
     (their interior callers extract it from `minstret_inv`); the live
     branch's era agreement is elem-vs-auth on the registry.
   - `wp_dead` from `gen_dead`; four-way split: dead / live /
     off-refuted-by-`gen_started` / unborn-refuted-by-`gen_born`.
   - `wp_power_loop` (surgery: fresh era allocation over the reset
     state, registry insert, both counters bumped appropriately, fork
     obligations from the client's joint ∀-era entailment) + the minimal
     adequacy over `[PowerLoopE]`.
   **ALL OF STAGE 2e LANDED** (with milestones 3 and 4): the semantic
   switch, `wp_dead`, the four-way base-rule split, `power_boot_res`
   (the ∀-era client bundle in RAW, ERA-EXPLICIT ghost forms — the
   polished ambient forms are these at `riscv_eraGS := HE` by pure
   conversion, so no instance gymnastics), `wp_power_loop`, and
   `riscv_power_adequacy` (pool `[PowerLoopE]`, machine starts OFF,
   any schedule of power cycles).  THE WHOLE TREE COMPILED UNCHANGED
   above the base rules.  Baseline 5 axioms.  Notable proof facts:
   `state_interp` in a goal is the irisGS PROJECTION — unfold it with
   `rewrite /state_interp /=` BEFORE `unfold power_interp`; and inside
   `wp_power_loop` allocate the heap with `gen_heap_init_names` (the
   names-form keeps the reconstructed `era_memGS_of` instance
   ι-convertible — `gen_heap_init`'s bundled form needs record η, which
   Coq does not have).
   **Remaining: M5** (durable disk) and **M6** (boot composition).

## M5 (durable disk) — steps 1-4 LANDED, step 5 remains

The disk-image ghost must survive power cycles; anything linear parked
in an ERA invariant is stranded at a crash (invariants are never
deallocated), and `virtio_proto` — which rides in the per-era
`disk_inv` — used to own `∃ dmap, ghost_map_auth (dn_img γ) 1 dmap ∗
⌜disk_view dmap (v_disk v)⌝`.

**LANDED (M5a — 658 files green, `spec_vacuity` clean, `lemma_diff`
reporting only the deliberate `disk_view` move, `Print Assumptions
riscv_power_adequacy` still exactly the 5 `rv64d.*` axioms):**

1. **The image name is FIXED-layer.** `riscvFixedGS` carries
   `riscvF_diskGS :: diskImgG Σ` + `riscv_disk_name`;
   `VirtioProto.disk_ghosts_alloc` no longer allocates `gimg`, it
   CONSTRUCTS `DiskNames riscv_disk_name gslot gnc gnp gclaim gcfg`.
   `dn_img` stays a field, so every client statement (`disk_bytes γ …`)
   is textually unchanged and the fragments survive an era; the era's
   OTHER disk ghosts (slots/nc/np/claim) stay era-fresh, which is what
   we want — in-flight requests die with the device reset.
2. **The auth+tie is `power_interp`'s FOURTH conjunct**, as
   `disk_dur_interp g := disk_img_auth riscv_disk_name (v_disk (dvirtio
   (gdev g)))`. `disk_view` MOVED from DiskPtsto.v to VirtioModel.v — it
   has to be stated in the iris-free model, since the auth it ties now
   lives below the driver protocol — and `disk_img_auth γi dk := ∃ dmap,
   ghost_map_auth γi 1 dmap ∗ ⌜disk_view dmap dk⌝` lives in a NEW tiny
   file **`iris/DiskImg.v`** together with the class `diskImgG` that
   types it. That file exists for ONE reason, and it is the trap this
   milestone nearly fell into: **the fixed-layer AUTH and DiskPtsto's
   FRAGMENTS must carry the same `ghost_mapG Σ Z (bv 8)` INSTANCE.** A
   field in `riscvFixedGS` and the old `diskGhostG.disk_img_inG` are two
   different Σ slots whose resources cannot interact, they print
   identically, and *no proof can bridge two abstract instances* — the
   symptom is `iSpecialize: cannot instantiate … ghost_map_auth (dn_img
   γd) … with … ghost_map_auth riscv_disk_name …` at the WpUart seam.
   Since RiscvPtsto sits BELOW DiskPtsto, neither can take the class
   from the other, so it goes in a file below both; `diskGhostG` dropped
   its image field (and `diskGhostΣ` its `ghost_mapΣ Z (bv 8)`, which
   moved to `diskImgΣ`), which leaves `riscvFixedGS`'s
   `riscvF_diskGS :: diskImgG Σ` the UNIQUE source of that instance in
   every riscvGS context — so no consumer needed a `Context` change.
   Two alternatives were considered and rejected, both for the same
   reason: threading an instance-equality premise, or making the fixed
   layer carry an abstract `(Z -> bv 8) -> iProp Σ` field, would each
   have to be discharged BY THE ADEQUACY CLIENT — which only ever sees
   an ABSTRACT `riscvGS Σ` and therefore cannot prove anything about the
   fixed layer's disk ghost. Both would have forced a new parameter into
   `riscv_system_adequacy`'s client entailment.
3. **Preservation.** `RiscvLang.run_v_disk` (hart steps, over
   `DevModel.dev_read_v_disk`/`dev_write_v_disk`) and
   `RiscvLang.uart_step_v_disk`; `plic_step` and the disk's own
   latch/idle arms need no lemma (their `d'` is `d` or `set_dplic d _`,
   so the framing is by conversion). All four base rules now
   destructure `(Hgauth & Hsauth & HR & Hdur)`; three FRAME the
   conjunct and **only `wp_disk_step` hands it over** — its callback
   receives `disk_img_auth (v_disk (dvirtio d))` and owes
   `disk_img_auth (v_disk (dvirtio d'))`. `wp_disk_loop` (WpUart.v)
   threads it: frame on latch/idle, and through the modified
   `virtio_proto_step` on the DMA completion.
4. **Both power arms frame it** (PowerOff touches no device state;
   PowerOn's `boot_shape` gives `dvirtio g' = virtio_reset (dvirtio g)`
   and `virtio_reset` keeps `v_disk` by conversion), and adequacy
   allocates it EMPTY (`disk_view ∅ _` is vacuous). `riscvGpreS` gained
   `riscv_pre_diskGS`, `riscvΣ` gained `ghost_mapΣ Z (bv 8)`.

Deliberate interface changes (all justified, none silent):
`virtio_proto_intro_gen` lost its `ghost_map_auth`+`disk_view`
premises; `virtio_proto_intro` / `virtio_proto_cfg_write` /
`virtio_proto_stable` lost their now-dead `v_disk` premises (3 call
sites: ProofVirtioDiskInit ×2, WpVirtioDev ×1); `virtio_proto_step`
TAKES `ghost_map_auth (dn_img γ) 1 dmap` + `⌜disk_view dmap (v_disk v)⌝`
and RETURNS `∃ dmap'` with the tie at the post-state;
`disk_ghosts_alloc_mint` was DELETED — with the auth in the fixed layer
it is exactly `disk_ghosts_alloc` followed by
`DiskPtsto.disk_bytes_mint` against the (still empty) durable auth, and
it had no caller. (NB: `lemma_diff` sees only COLUMN-0 declarations, so
a lemma deleted from inside a `Section` — as this one was — is invisible
to it. It did report DiskPtsto's `disk_view` as GONE: that is the move
to VirtioModel.)

Proof-engineering gotchas this milestone paid for:

- **Adding a conjunct to `power_interp` breaks the base rules' dead
  branches in a confusing way.** `state_interp` is ONE ∗-conjunct of
  `wp_lift_step`'s goal, so after `iFrame "Hgauth Hsauth"` the residue
  is `(∃R …) ∗ disk_dur_interp g` — a single goal, not two — and the
  old `iSplitL "HRauth Hera"` then splits state_interp from the WP
  instead. The symptom is *"iExists: ((∃ R …) ∗ disk_dur_interp g) not
  an existential"*. Fix: nest (`iSplitL "HRauth Hera Hdur"` then split
  inside).
- **`bv` is NOT in scope in RiscvExec.v** (`Require Import RiscvLang`
  does not re-export stdpp's `bitvector.definitions`), so a rule
  statement cannot spell `gmap Z (bv 8)` there. Another reason the raw
  ∃-form is packaged as `DiskImg.disk_img_auth`.
- **The gname still needs an equation.** `dn_img` stays a field of
  `disk_names` (so every `disk_bytes γ …` keeps its spelling), so
  `wp_disk_loop` takes `dn_img γd = riscv_disk_name` as a pure premise
  and `disk_ghosts_alloc` EXPORTS it (`⌜dn_img γ = riscv_disk_name⌝`, as
  its first conjunct — the client is the only one who knows which γ was
  allocated). The conversion happens in the two `iEval (rewrite ±Himg)
  in "…"` at the wp_disk_loop seam; VirtioProto's lemmas stay in their
  own vocabulary (`disk_img_auth (dn_img γ) …`).
- **`iExists` / `iDestruct … as (x)` DO see through folded definitions**
  (two layers deep; measured on a scratch file). No `rewrite /def` is
  needed before introducing or destructuring a definition that unfolds
  to an `∃`.
- **Transport a `disk_view` across a preservation lemma with a named
  `assert`, not with `rewrite` on the ⌜⌝ goal.** State it in the
  POST-state's own spelling (`disk_view dmap (v_disk (dvirtio (mdev
  σ2')))`), prove it by `rewrite Hvd; exact Hdview`, and close the
  proofmode goal with `exact` — whether the goal's gstate projections
  got reduced by `/=` is unpredictable, and `exact` is conversion-robust
  while ssreflect's `rewrite` is not.

## M5b (crash_inv + the write-permit hook) — LANDED

The mechanism is in place and instantiating it is FS work. What landed:

- **The crash predicate is a fixed-layer FIELD**: `riscvFixedGS` gained
  `riscv_crash_pred : iProp Σ` (a plain iProp field is legal — only the
  ERA record has to be Σ-free, because it is a `ghost_map` VALUE). That
  one decision is what keeps `P_fs` out of every `dev_inv`-adjacent
  signature: no statement between RiscvPtsto and the disk thread names
  it, so device.md's "a `dev_inv_body`-adjacent parameter ripples
  through every device file" warning never fires.
- `crashN := nroot .@ "crash"`, `crash_inv := inv crashN
  riscv_crash_pred` (persistent), both in RiscvPtsto.v.
- **The permit** `disk_write_permit := (▷ riscv_crash_pred ==∗ ▷
  riscv_crash_pred)`, with `disk_write_permit_trivial : ⊢
  disk_write_permit`. Deliberately a BARE later-to-later BASIC update:
  the interesting part is the closure, not the type — the log's
  commit-flip wand will curry its own abstract-state ghosts and the
  block it is about into the permit at enqueue time. A basic update goes
  through at whatever mask `wp_disk_loop` holds with `crashN` and
  `diskN` both open, which is why no mask annotation is needed; and a
  SERIALIZED writer (xv6's log, one commit at a time under the log lock)
  needs nothing conditional.
- **The consumption instant** (the part that had to be got right):
  `virtio_proto_step` hands a `disk_write_permit` back to its caller, and
  `wp_disk_loop` — which now takes `crash_inv` persistently — opens
  `crashN` in the DMA-completion arm ONLY, spends the permit on the
  `▷`-body and closes. That is the only opening of `crashN` in the tree,
  and the seam is FINAL: when the log lands, only where the permit COMES
  FROM changes.
- **The enqueue-side deposit is NOT there, and `slot_pend_res` is the
  wrong home for it — see the blocker below.** Today
  `virtio_proto_step` MINTS the identity permit. No driver spec changed.
- **Adequacy**: both theorems take `(Pc : iProp Σ)` and `(HPc : ⊢ Pc)`,
  allocate `inv_alloc crashN ⊤ Pc` (the body ι-reduces to
  `riscv_crash_pred` once the constructor field is filled with `Pc`),
  and hand `crash_inv` out — in the single-generation client bundle and
  in `power_boot_res`, so every boot gets the SAME invariant, which is
  what makes a durability property span power cycles. The device
  corollary passes `Pc := True` and `bi.True_intro _`.

**THE BLOCKER, and it is a design decision, not a proof difficulty: an
iProp CANNOT be deposited in `slot_pend_res`.** The plan was to put
`disk_write_permit` in the OUT arm of `slot_pend_res` (the `vs_data`
precedent: an exclusive resource taken across a sleep must be recorded
where the invariant keys on the request). That was tried and reverted:

- `disk_inv_body` (which contains `virtio_proto`, which contains
  `slot_pend_res`) MUST be `Timeless`. Every site that opens it — eight
  today, `iInv … as ">…"` — does so from INSIDE an MMIO atomic-update
  accessor (`wp_store_s_sconf_au` and friends), where there is no step
  left to absorb a `▷`, so a non-timeless body cannot be used there at
  all and the fix is not "add an `iNext`" anywhere.
- A permit is a wand over an ARBITRARY `riscv_crash_pred`, so it is never
  timeless, and there is no way to smuggle an iProp through a timeless
  invariant: saved propositions are not timeless either
  (`own γ (to_agree (Next P))` over a non-discrete OFE). Only pure data
  and discrete ghost state can live in `disk_inv`.

So the enqueuer→completion channel needs a home of its own. Two designs,
both viable, to decide WITH the log:
  (a) **A second, non-timeless era invariant for the permits**, with a
      timeless ghost SKELETON: body `∃ S : gset nat, permit_auth S ∗
      [∗ set] p ∈ S, permit_at p`. Both halves work under a `▷`:
      `▷(A ∗ B)` splits, the timeless `▷A` strips, the auth update
      happens outside the later, and a permit is ADDED under the later
      (`▷B ∗ permit ⊢ ▷(B ∗ permit)`), which is all the enqueuer needs —
      it never has to USE a permit. The device thread CAN use one,
      because `wp_disk_step`'s callback has its own `▷` between the two
      legs: open the permit invariant in the FIRST (⊤→∅) leg and the
      existing `iNext` strips it. Cost: one namespace, a per-position
      permit key (positions are already `dn_slot`-keyed), and threading
      the new invariant through the publish leaf and `wp_disk_loop`.
  (b) **Make `P_fs` closed under in-flight writes** — the shape real WAL
      crash proofs have ("the disk is the last committed state, or a
      committed state plus a partial log") — and discharge the completion
      from the invariant's OWN content plus the pure fact that this write
      is one of the pending ones. Then nothing is deposited per slot at
      all; the commit-flip write is the only one that needs a
      distinguished permit. Needs "which writes are pending" to be
      expressible where the wand is stated.
(a) is the mechanical one; (b) is how the FS proof will most likely want
to be organized, and it may make (a) unnecessary. Neither is blocked by
anything that landed here.

Gotchas:

- `iInv` works on a FOLDED invariant definition (`crash_inv`), same as
  the existing `disk_inv`/`uart_inv` — no `rewrite /crash_inv` needed.
- The permit must be applied to the `▷`-body: `iInv` on a non-timeless
  body hands out `▷ riscv_crash_pred` and wants it back, which is
  exactly the permit's type. Do NOT strip the later (the crash predicate
  is arbitrary, so it is not timeless).
- Hand the permit back from `virtio_proto_step` unconditionally rather
  than as `if vs_is_out sl`: the caller does not know the direction (the
  completing slot is chosen inside the lemma), and for a read the
  identity permit is honest — no disk byte moved.
- `crashN` (`nroot .@ "crash"`) is disjoint from `devN`-derived
  namespaces, so opening it inside the already-open `diskN` is one
  `solve_ndisj`; and a BASIC update (`==∗`) is mask-agnostic, which is
  exactly why the permit needs no mask annotation.

**THE STRANDED-FRAGMENT QUESTION (resolved as a recorded decision for
the FS work, not by code).** `virtio_proto`'s live arm parks `disk_bytes`
fragments of the now-DURABLE map inside the per-era `disk_inv`
(`slot_pend_res` for in-flight requests, `slot_done_res` for completed
ones not yet reclaimed). A power cycle abandons that invariant, so those
fragments become unreachable while the durable AUTH still remembers their
keys: the affected offsets can never be re-minted (minting requires
`dmap !! o = None`) and never re-claimed. Sound — nothing false is
provable, the image itself is intact — but the keys are lost. The FS
instantiation must pick one:
  (a) **Keep durable fragments out of slots**: redesign `dn_img` so a
      slot deposits a COPY rather than the exclusive entry — a
      fractional/persistent-agreement entry (`ghost_map_elem` at a
      fraction, or a separate agreement map keyed by offset) so the
      enqueuer keeps a claim that survives the era. Costs a rework of
      `disk_bytes_update`'s exclusivity argument at the completion.
  (b) **Accept per-crash key loss** and have recovery mint FRESH blocks:
      `P_fs` is then stated over the offsets the FS still holds, and boot
      re-mints the in-flight window from the auth (which needs an
      auth-side "forget these keys" update — `ghost_map_delete` on the
      stranded range, performed by the power arm, which is the only
      holder of the auth at that instant).
Note (b) is the cheaper one and it fits the power arm's existing access
to the auth; (a) is the one that keeps the crash proof local to the log.
**The decision belongs with the log's crash proof** — it is exactly the
question "what does recovery know about a request that was in flight when
the power died?", and the answer depends on the WAL discipline, not on
this layer.

Still future work (unchanged): the FS instantiation of `P_fs` (log
recovery, recovery-aware boot), and the initial `disk_bytes` MINT for
clients over the mkfs image — adequacy allocates the durable map EMPTY
and `power_boot_res` says nothing about the disk, so `Pc` cannot yet
speak about disk content. That mint is `DiskPtsto.disk_bytes_mint` at
the empty auth, and it has to be threaded into both adequacy theorems'
client bundles together with the FS's abstract state.

## M6a (boot_shape pins the reset machine) — LANDED

`boot_shape` used to say only "same generation, power on, memory is
RAM-shaped, disk reset". It now pins everything a boot proof has to READ
off a fresh machine, and nothing more:

- **`reset_regs c rs`** (RiscvLang.v) pins twelve register VALUES per
  hart: PC = 0x80000000, `cur_privilege = Machine`, `hart_state =
  HART_ACTIVE tt`, `mhartid = c` (the hart index — this is what ties
  `_entry`'s per-hart stack carve and SpecMain's arm choice to the CPU
  the thread runs on), `mstatus = 0xA00000000` (SXL=UXL=2, MIE=MPRV=0 —
  the model's own `sail_model_init`, = `BootBridge.mstatus_reset`),
  `misa = 0x800000000014112D` (= `RiscvFetchExec.MISA_C`), `mseccfg = 0`,
  `menvcfg = 0` (so `_get_MEnvcfg_LPE = 0`), `htif_tohost_base = None`,
  `elp = landing_pad_bits_backwards NO_LP_EXPECTED` (the model's
  `reset_elp`), `pma_regions = pma_boot`, `pmpcfg_n = pmpcfg_boot`.
  Everything `SpecEntry.wp_entry_boot` ∀-quantifies —
  mepc/satp/medeleg/mideleg/mie/mcounteren/stimecmp/pmpaddr_n and the
  GPRs — is deliberately NOT pinned: `boot_shape` stays as weak as the
  hardware. Values, not predicates: the properties the boot proof needs
  (`pmp_all_off`, `pma_allows_all`, the MISA bits, mstatus's
  MIE/MPRV/SXL, menvcfg's LPE) live above RiscvLang and are M6's bridges.
- **Memory** is now pinned exactly: `(∀ a, ram_lo ≤ a < ram_hi →
  gmem !! mword_of_int a = Some (boot_byte a))` — RAM is TOTAL (what lets
  a client carve main's memory precondition) and holds the LOADED IMAGE
  (what lets it read the kernel text back out) — plus the old "nothing
  outside RAM". `boot_byte a := default byte0 (boot_image !! a)` with
  `boot_image` the ELF's loadable bytes FILTERED to `[ram_lo, img_end)`.
  The filter is the trick that makes ".bss is zero-filled" SYMBOLIC: at
  or above `img_end` the lookup is `None` by `map_lookup_filter_None`, so
  no proof ever walks either 20k-entry literal map.
- **The image is nameable in the language**: RiscvLang.v now does
  `From Kernel Require KernelInstrs KernelData`. Measured cost: ~0.03 s
  per importing file (the .vo's are 3 MB/1.4 MB but load lazily), and
  zero instance risk — both are stdpp-only generated literals, no Sail,
  no iris. This is what makes the image a fact of the SEMANTICS rather
  than an assumption bolted onto a client.
- **Devices**: `duart = uart0_state`, `dplic = plic0_state` (+
  `PlicPlan.plic_ok_plic0`, so a boot client can allocate `plic_inv`),
  `dvirtio = virtio_reset <the old disk>` (unchanged — the image
  survives).
- **`boot_facts g'`** is the client-facing half (everything except the
  two bookkeeping equalities relating the new machine to the dead one),
  and it is what `Hboot` takes in `wp_power_loop` and in
  `riscv_power_adequacy` — replacing the old three premises
  (Hram/gpow/∃virtio), which it subsumes.
- **`iris/PowerBoot.v`** (new) holds the canonical reset machine
  `boot_gstate` (reset regs written over the dead machine's, `boot_mem`,
  reset devices) and `boot_shape_boot_gstate`, which is now
  `wp_power_loop`'s PowerOn reducibility witness — the ONE place that
  knows how to construct a reset machine.

Gotchas (all paid for here):

- **`Qed` never came back** on the "nothing outside RAM" direction when
  it went through `elem_of_list_to_map_2` on the 134M-entry
  `list_to_map` (the reverse direction puts the list into the proof
  term). Fix: CUT THE DOMAIN with a `base.filter` on the map instead of
  arguing about the list's keys, and the fact becomes one
  `map_lookup_filter_Some`. The forward direction
  (`elem_of_list_to_map`) is cheap and stays.
- **Never `split_and!; try reflexivity` across `boot_shape`'s
  conjuncts.** On the memory clause `reflexivity` tries to unify a lookup
  in that same giant map with `Some _` and computes the list. One tactic
  per conjunct.
- **`injection` on an `Arch.pa * bv 8` pair equation does not come
  back** (the pa width is an unreduced `if 64 =? 32 …`);
  `apply (f_equal fst)` + `cbn` is instant.
- `mword`, `mword_of_int`, `vec`, `vector_init` live in
  **SailStdpp.Values**, not Operators_mwords, and RiscvLang must spell
  them QUALIFIED (importing Values would make `Countable_mword`
  canonical and retype `gmem`). `uint` is in Operators_mwords.
- PowerBoot.v is iris-free, so it uses vanilla `rewrite a, b` with
  COMMAS (ssreflect's space-separated form is not available there).

**TWO THINGS M6 MUST FIX FIRST — both discovered here, neither
fudgeable:**

1. **`RiscvFetchExec.pma_allows_all` is not satisfiable as stated.** It
   demands `∀ (a : mword 64) (n : Z), ∃ r, matching_pma_region regions
   (Physaddr a) n = Some r ∧ <permissive>` — over ALL widths `n`,
   including ones that wrap the 64-bit space, and `range_subset` (rv64d
   6273) fails exactly on the wrap (it compares `a_begin ≤u a_end`
   relative to the region base). So no table can satisfy it, and every
   spec taking it as a premise is today vacuously satisfied. `boot_shape`
   pins `pma_boot` — ONE all-permitting region over the whole space,
   which is the honest platform model and satisfies the predicate for
   every non-wrapping access. M6 must restrict `pma_allows_all` to the
   widths the model itself allows (`1 ≤ n ≤ 4096`, `uint a + n ≤ 2^64`;
   the Sail source's own precondition comment says as much) and thread
   the bound at its use sites, after which `pma_allows_all pma_boot`
   becomes provable.
2. **`hw_config` has no construction site anywhere in the tree** — it is
   only ever consumed, so nothing has yet had to produce
   `misa ↦ᵣ□ …`/`mseccfg`/`pma_regions`/`htif_tohost_base`/`elp`. With
   `reset_regs` pinned, M6 can finally build it from the reset cells:
   `RiscvPtsto.reg_pointsto_persist` per cell (template:
   `TimerCap.v:95`), then the pure facts by `vm_compute`. The bridges it
   needs, none of which landed here: `KernelSyms._entry = 0x80000000`,
   `MISA_C = <the pinned misa>` (reflexivity), `pmp_all_off
   pmpcfg_boot`, `pma_allows_all pma_boot` (blocked on 1 — UNBLOCKED, see
   M6b-pre below), mstatus's MIE/MPRV/SXL from `0xA00000000`,
   `_get_MEnvcfg_LPE 0 = 0`.

## M6b-pre (1) `pma_allows_all` made satisfiable — LANDED

The predicate quantified over ALL widths and ALL addresses, so it held of
NO PMA table at all: `matching_pma_region` compares an access's END
address against the region's *relative to the region base*
(`range_subset`, rv64d.v:6273), so an access whose byte range wraps the
64-bit space matches nothing, whatever the table. Every spec taking it as
a premise — the whole M-mode/S-mode fetch and data-access tower — was
therefore vacuously satisfiable. Repaired shape (RiscvFetchExec.v), ONE
premise:

```coq
Definition pma_access_ok (a : mword 64) (n : Z) : Prop :=
  1 <= n <= 4096 /\ uint a + n < 18446744073709551616.

Definition pma_allows_all (regions : list PMA_Region) : Prop :=
  forall (a : mword 64) (n : Z), pma_access_ok a n -> exists r, …
```

- **The address bound is STRICT — `< 2^64`, not the `<= 2^64` M6a
  guessed.** `range_subset`'s third comparison is `a ≤u a + n`; at
  `uint a + n = 2^64` the end address wraps to 0 and the comparison fails
  for every `a ≠ 0`, so the non-strict shape is unsatisfiable at the one
  address `2^64 - n` and the repair would have to be done twice.
- `1 <= n <= 4096` is the Sail source's own precondition comment on
  `matching_pma_region`. `pma_boot`'s satisfiability only needs `0 <= n`;
  the width bound is kept because it is what keeps the predicate honest
  for a table with finitely-sized regions.
- Bundling both halves into ONE named premise is what keeps an applier to
  a single extra argument.
- `KptPt.pma_allows_pte_read` and `PtTreeAdue.pma_allows_pte_write` took
  the same treatment at their fixed width 8, spelled as the RAW
  inequality `uint a + 8 < 2^64`: both files sit BELOW RiscvFetchExec and
  cannot name `pma_access_ok`. `pma_allows_all_pte_read` /
  `pma_allows_all_pte_write` bridge the two forms with
  `pma_access_of_no_wrap`.

**THE DISCHARGE LAYER IS TACTIC-FREE, AND THAT IS NOT COSMETIC.**
`ltac:(lia)` at an applier fails with *"Cannot find witness"* even on the
CLOSED goal `1 <= 4 <= 4096` — the `bitvector.tactics` zify hook, once any
`bv` is in the context (hit in InstrBytes.v and PtTreeAdue.v). That cost
two full build cycles. So every premise an applier passes is either a
fact it already owns or a boolean check closed by `eq_refl`:

- `pma_width_ok n eq_refl eq_refl` (literal width) /
  `pma_width_le n m Hlo Hhi eq_refl` (a variable width, from its own
  `0 < n` and `n <= m` with `m` closed — `width`/`k` at WpSconfMem,
  UserMemPt, UserMemClassify) — both RiscvFetchExec.v.
- `pma_access_ram _ _ Hram <width>` — 45 of the 72 sites: `s_mem_chunk` /
  `s_fetch_chunk` / `udata_read_word_g` already hand out `addr_is_ram`.
- `pma_access_lt _ _ _ (proj2 Hrange) eq_refl <width>` — the device
  windows (WpPlic, WpVirtioDev) already take
  `<base> <= uint a8 < <base> + <size>`; `WpUart.uart_pa_access_ok` is the
  same move packaged for `uart_pa off`.
- `Pt4kWalk.pte_addr_at_no_wrap` — STRUCTURAL, no context at all: a PTE
  slot address is a 44-bit ppn ++ a 9-bit index ++ 000, hence < 2^56.
  Restated as `CommonWalk.u_pte_addr_no_wrap` and
  `PtTree.pt_addr0_no_wrap` for the walk layer's two spellings (19 sites
  in KptTree / TransPt / UserPtTree).
- `pma_access_canonical` (from `RiscvPtsto.mem_canonical`, the source M6a
  expected to be the common one) exists but has NO user: every applier
  turned out to have something sharper.

**72 applier sites over 22 files, and NO LATENT BUG** — every site could
supply the bound. Two families had to EXTRACT the fact rather than find
it: the M-mode 8-byte load/store leaves (WpMmodeLoad / WpMmodeStore) and
the trapframe-word leaves (UserretPt / UservecPt) own a `↦ₚ₈` and read
`addr_is_ram` off it with
`iDestruct (phys_word_pointsto_ram with "Hbw") as %Hram_ea`, which must
come BEFORE the `↦ₚ₈` is destructured into `(%Halign & Hbytes)` (a
pure-conclusion `iDestruct` keeps its input, so nothing is lost; in the
two Pt files the `iIntros` pattern had to stop destructuring it inline).

Gotchas worth keeping:

- **A scripted `(H addr)` → `(H addr bound)` rewrite must MOVE the closing
  paren.** Appending the new argument inside the address's own application
  gives *"Illegal application (Non-functional construction)"* naming the
  ADDRESS as the non-function — one build cycle.
- Closed `Z` order goals need no `lia`: `Z.lt x y` is `(x ?= y) = Lt`
  (so `reflexivity`) and `Z.le x y` is `(x ?= y) <> Gt` (so
  `discriminate`). That is how the arithmetic inside the helper lemmas is
  closed. Where real arithmetic is needed, package it over plain `Z`
  variables in a top-level lemma (`pma_no_wrap_Z`) and apply it as a
  closed fact.
- The `-k` build only reveals ONE FRONTIER per cycle: a failure in a
  bottleneck file (InstrBytes, PtTreeAdue) skips everything above it, so
  budget several cycles and fix appliers proactively by grepping for the
  application sites first. Grep for the applied HYPOTHESIS names, not for
  `pma_allows_all`: the sites are named `Hpma_all` / `Hpma0` / `Hpmar` /
  `Hpmaw` / `Hall` / `Lpma` / `Hpma'`, and a grep that misses one family
  (`Lpma`, in SmodeCorePt and TrampStepPt) costs a cycle.

Still open from the M6a bridge list: `pmp_all_off pmpcfg_boot` (needs a
`vec_access_dec`-of-`vector_init` fact at a SYMBOLIC index — `pmpcfg_boot`
is `vector_init 64 (mword_of_int 0)`, and the out-of-range default is the
`Inhabited` zero, so the property does hold at every index).

## M6b-pre (2) `hw_config` / `mmode_config` / `boot_D` — LANDED

`iris/BootConfig.v` (new) is the home: the first CONSTRUCTION site either
bundle has ever had. All four results are `Closed under the global
context`. What it holds:

- `pma_allows_all_pma_boot` — **the payoff of (1)**: the M6a-pinned table
  (one region, base 0, size 2^64-1, all-permitting) satisfies the repaired
  predicate. The proof is `range_subset`'s three unsigned comparisons at
  region base 0, over `uint_to_bits64` (`uint (to_bits 64 n) = n` in
  range, from `PrintintArith.gsi64`) and `RiscvExtras`'
  `add_vec64_unsigned` / `sub_vec64_unsigned` / `bv_wrap_small`. All of
  its arithmetic is packaged in ONE plain-`Z` helper (`pma_boot_arith`)
  for the `lia` reason above.
- `boot_D : CPU -> gset register` — the documented MINIMUM a boot client
  asks adequacy for: the twelve `reset_regs` registers (PC,
  cur_privilege, hart_state, mhartid, mstatus, misa, mseccfg, menvcfg,
  htif_tohost_base, elp, pma_regions, pmpcfg_n) + nextPC (`pc_is` owns
  BOTH, and `reset_regs` does not pin it) + pmpaddr_n + what
  `wp_entry_boot` quantifies (mepc, satp, medeleg, mideleg, mie,
  mcounteren, stimecmp) + the `minstret_inv` cells (minstret,
  `R_bool minstret_increment`, mcycle, mtime, mip) + the GPR file
  (x1..x31) + the wire pins (sig_seip, sig_meip — the existing device
  client's whole `D`).
- `hw_config_intro` / `mmode_config_intro` — from the AMBIENT `↦ᵣ` cells
  at the pinned `reset_regs` values (`power_boot_res`'s era-explicit elems
  are these by pure conversion, per M2's note). `reg_pointsto_persist` on
  the five frozen cells (misa, mseccfg, pma_regions, htif_tohost_base,
  elp; template `TimerCap.v:95`) is the only ghost step; every pure
  conjunct is `vm_compute` on a pinned value. `mmode_config_intro` is
  `InstrBytes.mmode_config_rebuild` at the pinned mstatus `0xA00000000`,
  whose three MIE/MPRV/SXL facts are `vm_compute`.

**THE IMPORT-HEADER TRAP, and it cost real time.** A file whose header
is `From stdpp Require Import gmap finite list_numbers
bitvector.definitions` + `SailStdpp.ConcurrencyInterface*` +
`SailStdpp.TypeCasts` (i.e. RiscvFetchExec's own header) cannot STATE an
iris entailment at all: even `Lemma t : hw_config -∗ hw_config` fails with
*"The term hw_config has type upred.uPred (iprop.iProp_solution.iResUR
?Σ) while it is expected to have type bi_car ?PROP0"* — the `bi_car`
canonical structure never resolves and `Σ` stays an evar, on a section
that has `Context `{!riscvGS Σ}` right there. It is the same family as
durable-notes' `SailStdpp.Values` instance leak, and the diagnosis is
misleading: the error points at the lemma, not at the header. **Copy the
header of an existing file that states the bundle you are building**
(InstrBytes.v, for `hw_config`/`mmode_config`) and add only what you need
on top; do not assemble one from the low-level files' headers. The pure
half of the same file compiled fine throughout, which is what makes this
look like a lemma bug.

Still open from the M6a bridge list: `pmp_all_off pmpcfg_boot`, and the
`KernelSyms._entry = 0x80000000` / `MISA_C = <the pinned misa>` bridges
(the latter is `reflexivity` and is used inside `hw_config_intro`).

## M6b (IN PROGRESS) — the boot-image carving library

`iris/BootCarve.v`: from `power_boot_res`'s raw memory conjunct plus the
raw kmap fragments plus the pure `boot_facts g'`, produce the bundles
SpecEntry/SpecMain's preconditions mention, so the eventual boot
composition is pure assembly.

### Slice 1a — the three-way split, LIFTED (LANDED)

The four steps were inlined in `riscv_system_adequacy`'s proof; they are
now `BootCarve.v` lemmas and that proof APPLIES them, so there is one
copy and the crash-layer boot client (same raw inputs at a fresh era)
reuses it:

- `kmap_static_claims_intro` — the persisted static-claims bundle out of
  the raw kmap fragments. **This goes FIRST**, and the order is forced by
  the resources rather than by taste: the claims come from the kmap
  fragments, which do not overlap the memory map at all, and BOTH memory
  halves need the whole bundle to do their identity upgrade. (So the
  question "can the physical cut precede the claims persist?" does not
  arise — the persist depends on nothing in the memory map.)
- `boot_bytes_split` — the raw byte map cut at `text_end`
  (`sub_text g` / `supra_text g`).
- `boot_text_persist` — the sub-`text_end` half: raw `pointsto` + the RAM
  fact → `↦ₚ`, the static claim → `↦ₓ`, then `text_pointsto_persist` →
  the immutable `↦ₓ□` image.
- `boot_data_own` — the `text_end`-and-above half → the OWNED `↦ₘ` image.

Plus, in BootConfig.v beside the other reset facts, the last item of
M6a's bridge list: **`pmp_all_off pmpcfg_boot`**. `pmpcfg_boot` is
`vector_init 64 0` and `pmp_all_off` quantifies over a `Z` index with NO
range premise, so the OUT-OF-RANGE reads are what the proof turns on:
`vec_access_dec` falls back on the `Inhabited` default, which for
`mword 8` is the same zero byte the vector is filled with (below the
range that fallback is taken by `access_list_inc`'s own guard, above it
by `nth` running off the list). `pmpcfg_boot_entry` is the reusable "every
index reads zero" fact; the two predicates then follow by `vm_compute`.

**TWO TRAPS, both paid for here and both worth knowing before touching
this file:**

- **Never write a `gmap Arch.pa (bv 8)` BINDER in this file** — index
  everything by the `gstate` instead (`boot_raw_bytes g`,
  `boot_text_raw g`, `boot_data_raw g`). BootCarve must `Require Import
  KptPt`/`KMap` (for the mword-27 claim instances that §1 needs), and
  those make `Instances.Countable_mword` canonical for `Arch.pa`; a
  binder written here is then a DIFFERENT type from `RiscvLang`'s `gmem`
  field. The two print identically and the CALLER fails with *"has type
  `@gmap Arch.pa (bv_eq_dec …) …` while it is expected to have type
  `@gmap Arch.pa (@Instances.Decidable_eq_mword …) …`"*. Writing the
  binder as `(mm : _)` does NOT help (the `_` elaborates at the canonical
  instance from the body's `big_sepM`); naming the state does, and it is
  what every caller has anyway. Trying to fix it by dropping the Values
  imports just moves the failure to §1.
- **Apply every lifted lemma at the EXPLICIT instance** inside adequacy:
  `iMod (@boot_text_persist Σ HR g Hram with …)`. The `set`-bound era
  record is not a typeclass instance, so a bare `iMod` fails with
  *"iSpecialize: cannot instantiate … `↪[kmap_name]` … with …
  `↪[γk]`"* — the same M0 gotcha, now hit from the other side.
- `rewrite <- (map_filter_union_complement P mm)` does not work when `mm`
  is a local VARIABLE ("cannot instantiate ?b because mm is not in its
  scope" — the replacement mentions `mm`). Go forward instead: `pose
  proof` the equation and `iAssert` the union form, closing it with
  `rewrite Heq`. And a `¬` written inside that `iAssert` parses in
  `bi_scope` as bi-negation, so the complement filter needs its own
  named definition (`co_sub_text`).

### Slice 1b — the generated range facts + `kernel_text` (LANDED, partial)

**The range wall is gone, and the fix is in the DUMPER.** `tools/dump_elf.py`
now emits, after each per-byte `gmap Z (bv 8)` it generates, the map's KEY
RANGE as a decidable check closed by one `vm_compute`
(`rocq_range_lemmas`):

```coq
Definition <map>_lo : Z := 0x…%Z.   Definition <map>_hi : Z := 0x…%Z.
Lemma <map>_range_bool :
  bool_decide (map_Forall (fun (a : Z) (_ : bv 8) =>
                 (<map>_lo <= a < <map>_hi)%Z) <map>) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma <map>_range (a : Z) (b : bv 8) :
  <map> !! a = Some b -> (<map>_lo <= a < <map>_hi)%Z.
```

The proof term is `eq_refl` — **no list ever enters it**, which is the whole
point: the hand proof would have to go back through `list_to_map`
(`elem_of_list_to_map_2`) and that `Qed` does not come back. Cost measured:
~1 s of `vm_compute` per map. Bounds are LITERALS because `kernel-rocq/`
sits below `iris/` and cannot name `ram_lo`/`text_end`/`img_end`; BootCarve
bridges them by `lia`.

Facts now available, and both matter for what is left:
- `kernel_bytes` keys ∈ `[0x80000000, 0x80006120)` — entirely below
  `text_end` (0x80007000), so the whole text map lands in `sub_text`.
- `kernel_data` keys ∈ `[0x8000541e, 0x8000a220)`. Two things to know:
  it **STRADDLES `text_end`** (which is exactly why `KernelDataInv.kernel_data`
  filters at `text_end` — the sub-etext bytes belong to the `↦ₓ□` half), and
  its upper bound is **exactly `img_end`**, which is what makes the
  `boot_byte` lookup land inside `boot_image`'s filter.

`BootCarve.kernel_text_intro` is the first NAMED bundle: from the `↦ₓ□` half
plus `boot_facts`' RAM-total-and-loaded clause it produces
`KernelText.kernel_text`. It CONSUMES NOTHING (both the input half and
`kernel_text` are persistent), so the same half still serves the physical
cuts. `boot_byte_text` is the one-line bridge "the loader left
`kernel_bytes`' byte at its address" (`lookup_union_Some_l` on
`kernel_bytes ∪ kernel_data`, then the `< img_end` filter).

**REGEN SAFETY (the hard requirement) — verified:** `make dump` at the
pinned `XV6_REV` produced `40 insertions(+), 0 deletions(-)` across
`kernel-rocq/KernelInstrs.v` and `KernelData.v` — every byte-map literal
UNCHANGED, only the appended lemmas. Same for `user-rocq/Sync{Instrs,Data}.v`.
Procedure to repeat: `make dump`, then `git diff --stat kernel-rocq/` and
confirm insertions only; a single deletion means image drift and the regen
must be reverted, not committed.

**VERIFICATION (complete):** the full `-k` rebuild the regen forces came
back green -- 674 files, zero errors -- and `lemma_diff` / `spec_vacuity` /
`proof_coverage --check` are clean, with `Print Assumptions` on BOTH
`riscv_power_adequacy` and `riscv_device_adequacy` still exactly the 5
`rv64d.*` axioms.

**BUDGET WARNING for any future dumper change:** regenerating `kernel-rocq/`
invalidates `RiscvLang.vo` (RiscvLang names the image) and therefore the
WHOLE iris tree — a dumper edit costs one full ~15 min rebuild, not a
single-file check.

### Slice 1b — what still remains

- **`kernel_data_intro`.** `KernelDataInv.kernel_data` is `↦ₘ□`
  (PERSISTED), while the data half arrives OWNED, and main needs the .bss
  cells owned. So `supra_text` needs a SECOND cut, at `img_end`: below it →
  persist into `kernel_data`; at or above it → stays owned for slice 2's
  typed cells. The two are disjoint because `kernel_data`'s upper bound IS
  `img_end` (see above) and every `main_globals_raw` cell is .bss. The
  `< img_end` range fact is already generated.
- **The PHYSICAL cuts**: the `stack0` pages (`stack_own_phys` per hart) and
  the `entry_ld_ea` word, as raw `↦ₚ`, taken out of `supra_text` before the
  `↦ₘ` upgrade — a key-set deletion on that filtered map plus the per-byte
  presence from `boot_facts`.

### Slice 2 — typed cells (NOT STARTED)

The 4/8-byte cells at kernel-symbol addresses that `main_locks_raw` /
`main_globals_raw` demand, out of consecutive `↦ₘ` bytes with their image
values (bss = 0 symbolically, via `boot_byte`'s filter being `None` at or
above `img_end`; data = the dump's words). Follow InstrBytes'
`word_pointsto_join4` / `word_pointsto_join8` and `kernel_data_window`'s
style; the addresses and widths are uniform, so a small combinator family
("W consecutive `↦ₘ` bytes at a symbol address, with the image's value")
beats forty bespoke lemmas. NB `main_globals_raw`'s conjuncts are mostly
CONTENTS-EXISTENTIAL, which makes them strictly easier than the two that
are not (`kmem+24 ↦₈ 0` and `d_used_idx ↦₂ wrap16 0`) — those two need the
bss-is-zero clause.

### Slice 3 — the kinit page run (NOT STARTED)

`[s1entry, PHYSTOP)` → `[∗ list] p ∈ ps, page_own p` + `prun phystop
s1entry ps` (KallocInv's shapes), peeled SYMBOLICALLY — never enumerate
(durable-notes' large-map rules). Open question to settle from
`SpecMain.wp_main_boot_sconf_body`'s actual precondition rather than from
the design: it asks for `(K_kvmmake + 64 + 3 < length ps)` and nothing
else about the 64 kstack pages, i.e. **the kstacks come out of the same
`ps` budget** and do NOT need a separate bundle.

**M6** — the boot composition as the ∀-era entailment instantiating
`power_boot_res` (absorbs main-boot's outstanding item), now over the
pinned `boot_facts`: carve the image out of the RAM-total memory
(`kernel_text` from `boot_byte` on `[ram_lo, img_end)`, the bss zeros
above it), build `hw_config`/`mmode_config` per hart from the reset
cells, run `wp_entry_boot` on every forked hart, and hand each `main`
its half via `BootBridge.boot_bridge`.
3. **Death machinery**: `wp_dead`, the base rules' four-way case split
   (`> gen` dead / live / off-refuted-by-registry / `< gen`
   refuted-by-birth-bound), birth lb + era registration folded into the
   per-era `minstret_inv` (zero statement churn).
4. **`wp_power_loop` + the minimal adequacy** (fixed-layer allocation
   only; hypothesis `P_fs (v_disk g0)`), validated end-to-end on the
   device-only pool (`cs = []`, the `riscv_device_adequacy` analogue):
   "power-cycle the machine forever, never stuck" with trivial `P_fs`.
   This exercises fork, corpse arms, era surgery, and the framed durable
   conjunct before any kernel content is involved.
5. **Durable disk layer**: relocate the `dn_img` auth out of
   `virtio_proto`/`disk_inv` into the fixed `state_interp` conjunct
   (`γdur`), allocate `crash_inv`, add the `vslot` write permits +
   `wp_disk_loop`'s consumption of them. Mind device.md's warning that a
   `dev_inv_body`-adjacent parameter ripples through every device
   spec/proof file — keep `P_fs` a Section Context in the proto files,
   explicit only at alloc/adequacy.
6. **Main-boot composition** as the ∀-era joint boot entailment
   (`∀ HE gen g', boot_shape g' → initial resources ={⊤}=∗ per-thread
   WPs`). This IS main-boot.md's outstanding "whole-system adequacy
   composition" — build it directly in this form so first boot and every
   reboot share it.

## Future work (after the milestones)

- FS instantiation of `P_fs` (log recovery; recovery-aware boot proved
  from any `P_fs`-image rather than the pristine mkfs image) once the
  log/FS layers exist.
- Decide the torn-write knob (see the design note's recorded modeling
  choices) when the log's crash proof is designed — request-atomic is the
  current recorded choice.
