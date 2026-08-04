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

**REMAINING (M5b): `crash_inv` and the write permits.**
`inv crashN (∃ …, disk_bytes-frags ∗ P_fs …)` with `P_fs` an iProp over
fixed-layer ghosts; allocated once in `riscv_power_adequacy`'s fixed
allocation (client supplies the initial `P_fs`); both power arms never
open it. The initial MINT of the client's `disk_bytes` over the mkfs
image lands here too (deferred from M5a: adequacy allocates the auth
empty and `power_boot_res` says nothing about the disk yet) — it is
`DiskPtsto.disk_bytes_mint` at the empty auth. The vslot WRITE PERMIT
(the `vs_data` precedent): the enqueuer deposits an iProp wand
alongside the OUT slot; `virtio_proto_step` consumes it to re-establish
`P_fs` after updating the auth. **Watch:** `virtio_proto`'s live arm
still parks `disk_bytes` fragments (`slot_pend_res`/`slot_done_res`) of
the now-DURABLE map inside the per-era `disk_inv`, so a crash strands
the fragments of every in-flight block — sound, but those bytes can
never be re-claimed. Either the permit design must hand them back at
the crash boundary, or `P_fs` must be stated over the not-in-flight
range only. Decide this WITH the permits, not after.

**M6** — the boot composition as the ∀-era entailment instantiating
`power_boot_res` (absorbs main-boot's outstanding item); tighten
`boot_shape` with the device-reset facts (uart/plic reset, so the
device corollary can run under power) and the harts' reset registers
(SpecEntry.v's coming-out-of-reset state, so `wp_entry_boot` composes).
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
