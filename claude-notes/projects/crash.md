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
   pmpcfg_boot`, `pma_allows_all pma_boot` (blocked on 1),
   mstatus's MIE/MPRV/SXL from `0xA00000000`, `_get_MEnvcfg_LPE 0 = 0`.

## M6b-pre (NOT STARTED — scoped 2026-08-04, execute in this order)

Two prerequisites, both identified in M6a. The scoping below is measured,
not guessed.

**(1) Make `pma_allows_all` satisfiable.** Current shape
(RiscvFetchExec.v:60):
```coq
forall (a : mword 64) (n : Z), exists r,
  matching_pma_region regions (Physaddr a) n = Some r /\ <permissive>
```
The fix is the two bounds the model itself assumes (the Sail source's own
precondition comment on `matching_pma_region` is `1 <= width <= 4096`):
```coq
forall (a : mword 64) (n : Z),
  1 <= n <= 4096 -> uint a + n <= 2^64 -> exists r, …
```
`uint a + n <= 2^64` is the one that matters: `range_subset` (rv64d.v:6273)
compares `a_begin ≤u a_end` *relative to the region base*, so a wrapping
access matches NO region, whatever the table.

BLAST RADIUS, measured: `pma_allows_all` appears 141 times in 35 files,
but almost all of those THREAD it as a premise (`pma_allows_all
(register_lookup pma_regions σ.(sregs)) ->`) and are unaffected. What
needs work is the APPLIER sites — the lemmas that instantiate the ∀ and
hand a `matching_pma_region … = Some region` hypothesis down (30 files
carry such hypotheses, always at a CONCRETE width 2/4/8, so the `1 <= n
<= 4096` half is a literal check). Each applier must produce `uint a + n
<= 2^64` from its local context; in every real case the address is owned
and therefore canonical, so `RiscvPtsto.mem_canonical` (`uint a < 2^38`)
is the source — the work is threading that fact from the points-to to the
applier, NOT inventing it. Start at `RiscvFetchExec.pma_allows_all_pte_read`
(→ `KptPt.pma_allows_pte_read`, which is also address-unbounded and needs
the same treatment) and walk outward; expect the bound to stop at the
first lemma that already owns the bytes.

**A proof that cannot supply the bound is a LATENT BUG, not an
inconvenience**: it means the proof only went through because the
unbounded premise was unsatisfiable. Record any such site rather than
weakening around it.

Then: `pma_allows_all pma_boot` (the M6a-pinned table: one region, base 0,
size 2^64-1, all-permitting) becomes provable — `range_subset` reduces to
`a ≤u a + n` under the new bound.

**(2) Construct `hw_config`.** It has NO construction site in the tree
today (only consumers), which is why nothing has had to produce
`misa ↦ᵣ□ …`. With M6a's `reset_regs` pinning the values, the recipe is:
take the per-hart register elems out of `power_boot_res` (they arrive as
`ghost_map_elem … (existT r (register_lookup r (g'.(gregs) c)))`, i.e. AT
the `reset_regs` values), `RiscvPtsto.reg_pointsto_persist` the five
frozen ones (misa, mseccfg, pma_regions, htif_tohost_base, elp — template
`TimerCap.v:95`), and discharge the pure facts by `vm_compute` from the
pinned values. `mmode_config` additionally wants hart_state/cur_privilege
/mstatus at a fraction (all pinned) plus `minstret_inv` (allocated by the
client, not here).

`boot_D : CPU -> gset register` (to define in PowerBoot.v) is the
documented MINIMUM the boot client must ask adequacy for: the twelve
`reset_regs` registers (PC, cur_privilege, hart_state, mhartid, mstatus,
misa, mseccfg, menvcfg, htif_tohost_base, elp, pma_regions, pmpcfg_n)
+ pmpaddr_n + the eight `wp_entry_boot` quantifies (mepc, satp, medeleg,
mideleg, mie, mcounteren, stimecmp) + the `minstret_inv` cells
(minstret, mcycle, mtime, mip) + the GPR file. Cross-check against
`riscv_system_adequacy`'s `D` at the existing client before fixing it.

## M6b (NOT STARTED) — the boot-image carving library

`iris/BootCarve.v`: from `power_boot_res`'s raw mem conjunct plus
`boot_facts`, produce the bundles SpecEntry/SpecMain's preconditions
mention. Three slices, each landable green on its own:
(a) the three-way split — sub-`text_end` bytes → `kernel_text` (lift the
    `Htext` ↦ₓ□ persist block out of `riscv_system_adequacy`'s proof into
    a reusable lemma instead of duplicating it, together with the
    `kmap_static_claims` persist step), `[text_end, img_end)` →
    `kernel_data` + owned ↦ₘ, and the PHYSICAL cuts (stack0 pages for
    `stack_own_phys`, the `entry_ld_ea` word) taken out BEFORE the ↦ₘ
    upgrade;
(b) typed 4/8-byte cells at kernel-symbol addresses with their image
    values (bss = 0, data = the dump's words), following InstrBytes'
    `word_pointsto_join4` and `kernel_data_window`;
(c) the kinit page run `[s1entry, PHYSTOP)` → `[∗ list] p ∈ ps, page_own p`
    + `prun`, peeled SYMBOLICALLY (durable-notes large-map rules).
Nothing wires into adequacy until M6c/M6d.

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
