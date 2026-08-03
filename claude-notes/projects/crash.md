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
2. **Language + the GenId sweep**: `ggen`/`gpow` gstate fields, generation
   indices on the four loop expressions + corpse arms, `PowerLoopE`
   (PowerOff bumps ggen; PowerOn forks), `PowerModel.v` (`boot_shape`,
   `dev_reset`, pure). Ambient generation: `Class GenId := { gen_id : nat }`,
   `Notation Loop := (LoopE gen_id cpu_id)` — a Context-binder sweep
   across the WP files with statements textually unchanged; follow
   [`../completed/explicit-cpuid-porting-guide.md`](../completed/explicit-cpuid-porting-guide.md)
   (the failure modes that compile are the risk). Every lifting rule's
   `prim_step` inversion gains the corpse/power disjuncts. Fix the two or
   three representative files by hand first; the rest is subagent
   fan-out.
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
