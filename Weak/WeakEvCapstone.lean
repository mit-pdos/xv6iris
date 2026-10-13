/-
Weak: **THE ONE-MACHINE CAPSTONE** (B3.2 + B4): event-language adequacy composed with the Layer-1
robustness theorem, through the instance `WeakEvInst` and the projection `WeakEvPf.ecfgOf`.

Rocq: `iris/WeakEvCapstone.v` @ xxvzwolszwmp (1cc222280).

## The Rocq header, in substance

The soundness chain, with no seam: (1) event-language adequacy (`WeakEvAdequacy`), (2) φ ⟹
`epfViolationFreeHart` (`WeakEvAdequacy.weakEvPfViolationFree`), (3) THE INSTANCE (§§1–5): the
event language's promise-free machine `WeakEvPf.epfStep` IS `wpPfStep pstepEv pclsEv` at
`P := Pexv6`, `D := DevStates`, through `ecfgOf`, in BOTH directions, (4) Layer 1
(`WeakRobustMain.robustMainBundle`), and (§7) their composition `xv6EvWeakRobust`.  ⇒ (a pf step
of the projection is an `epfStep`) holds at the same label; ⇐ holds at the RUN level only (the
`epfStep` label is under-determined by `elabelOk`: `fence.i` admits `LSilent` there while the
program half emits the inert `LFence false false false false`).  §0 names the three
label-indexed slots of a `wpPfStep` (side condition `pfOk`, log effect `pfLog`, view effect
`pfWs`); at the projected configuration they ARE `WeakEvInst`'s `elabOk`/`elabLog`/`elabWs`.
§6: the retag moves only `wmAk`, so the fulfil accounting survives it.  §7's ledger: the WP
package, the fresh-era facts about σ0, the behavior, and the Layer-1 package `mainPremises`
served at canonical bundles (the supplier is quantified over every behavior because the
capstone RETAGS before running Layer 1).

LAYOUT (`WeakEvPf` header): hart `c` is agent `c.val`, the disk agent is `nDisk = NCPU`.  The
pool has two UARTs, the disk and the PLIC (`epoolList`: disk at `NCPU+2`, PLIC at `NCPU+3`); the
UART and PLIC programs carry NO agent of their own (`EPFUart` is attributed to `nDisk`, `EPFPlic`
to `plicAgent`), so `eags` is still harts `++ [disk]`.

## Deviations from Rocq

1. NAMES: the tree's camelCase (map below).  File-qualified (in
   `notes/weak-port-dupnames.json`): `WeakEvCapstone.pfLog`, `WeakEvCapstone.wpPfStepInv`,
   `WeakEvCapstone.wmClassOfRelp`.  `fin_to_nat c` ↦ `c.val`; `<[i := x]> l` ↦ `l.set i x`;
   `l !! i` ↦ `l[i]?`; `default x o` ↦ `o.getD x`; `S (length l)` ↦ `l.length + 1`; `enum CPU`
   ↦ `cpus`; `Interface.Ret tt` ↦ `FreeM.pure ()`; `list_insert_id` ↦ the Lean-only
   `listSetSelf`.
2. O2 — THE FETCH LABEL `LIFetch` (Lean-only, `WeakPromise` deviation 8).  `pfOk`/`pfLog`/`pfWs`
   gain the `LIFetch` arm of `wpPfStep.PFIFetch` (`ifetchOk … 0`, log and view unchanged).  The
   pf machine checks a fetch at instruction view 0 while the language checks it at the hart's
   own view `σ.wgitv c` (`WeakEvInst.elabOk`, Stage B), so:
   - `pfOkHart` is stated for NON-fetch labels (Rocq: all labels, an equality); the Lean-only
     `pfOkOfElabHart` (⇐, all labels, via `ifetchOkAnti`) and `pfOkHartElab` (⇒, under the
     fetch-view premise) replace it where it is used;
   - ⇒ needs, per projected state, THE FETCH-VIEW PREMISE `efetchItvOk P σ` (Lean-only): a view-0
     admissible fetch the hart's program emits is admissible at `σ.wgitv c`.  It is DISCHARGED
     whenever the fetched bytes are never written (`efetchItvOkOfUnwritten`: the cross-file fact
     "kernel text never written"; at the run level `efetchItvOkRunOfUnwritten`: no reachable log
     writes a fetched byte), but no lemma here proves the kernel's text unwritten, so the
     run-level form is CARRIED by the capstone (premise (b')).
   - `pfOkDisk` gains the premise "`l` is not a fetch" (`pstepDiskNoFetch`).
3. DEVICES — THE ⇐ DIRECTION (`WeakEvPf` deviations 2, 9, `WeakEvInst` deviation 5).  The
   fabric is `Efab` (the device states plus the residual UART/PLIC programs, read off the pool by
   `efabOf`), so `ecfgOf`'s `pcDev` moves on a device step (`ecfgOfUset`/`ecfgOfPset` restated;
   Lean-only `ecfgOfUartStep`, `ecfgOfPlicStep`, `ecfgOfPinStep`).  `epfStep`'s device arms are
   any non-forking, log-preserving step of a UART or PLIC PROGRAM; the program half steps only the
   PLAIN nodes (`WeakEvInst.fdevStep`: no bus-master access, no `join`, the wire write only for
   the PLIC), so ⇐ holds at a PLAIN POOL: `epPlain P` (Lean-only: `DevPlain false` UARTs,
   `DevPlain true` PLIC), true of `epInit` (`epPlainInit`) and kept by every `epfStep`
   (`epPlainStep`, `epPlainRun`, from `WeakEvInst.uartBodyPlain`/`plicBodyPlain`).
   `epfStepWpPfStep` / `epfRunWpPfRun` / `epfRtcWpPfRtc` take `epPlain ρ.1` (Rocq: no premise).
   A UART step is a `pdiskUart` move of the disk agent; a PLIC step is `pstepPlic` at
   `plicAgent` = its target hart at a wire write, a `pdiskUart` move of the disk otherwise.  So
   `epfStepWpPfStep` still quantifies the agent existentially beside the label (`∃ i' l'`; Rocq:
   `∃ l'` at the same `i`) — the agent is `plicAgent P.epPlic` / `nDisk`, i.e. `i` itself.
   Lean-only: `devSetPinCases`, `devNodePlainNoPin`, `plicAgentFdev`, `epHsetSelf`, `hartPfStep`,
   `diskPfStep`.
4. DEVICES — THE ⇒ DIRECTION: NO DEVICE PREMISE (owner decision Q1).  `WeakEvInst`'s program
   half steps the device programs exactly as the language does, so every pf device step of
   `ecfgOf P σ` is the projection of an `epfStep` at the same agent and label: a `pstepPlic`
   step is `EPFPlic` at a wire write (`eplicStepFactor`), a `pdiskUart` step is `EPFUart` /
   `EPFPlic` off one (`wdevOfFdevStep`, `plicAgentFdev`).  `wpPfStepEpfStep`,
   `wpPfRtcEpfRtc`, `epfPfViolationFree` and the capstone carry ONLY the fetch-view premise
   (deviation 2) at every `epfRun`-reachable state (Rocq: no premise).  The earlier Lean-only
   `evDevResidue`/`evDevCover`/`evCover` are gone.
5. THE FETCH-SOURCE PREMISE (`WeakRobustMain` deviation 5): `robustMainBundle` takes
   `fetchSrcOk TS`, which nothing about the event instance discharges in general
   (`fetchSrcOkTsZero` does when fetches answer only timestamp 0).  The capstone's robustness
   supplier (d) returns `mainPremises nDisk TS DS ∧ fetchSrcOk TS` (Rocq: `main_premises`).
6. THE WP PACKAGE / CAMERAS: `WeakEvAdequacy.weakEvPfViolationFree`'s verbatim (its deviations 2,
   3: `[MachGpreS hlc GF] [WeakGpreS GF]`, `D : CPU → List Register` with `hD`, the device
   fragments as `[∗list] d ∈ DevId.all, devFragAt …`).  `Σ`, `riscvGpreS`, `weakGpreS` ↦ `hlc`,
   `GF`, `MachGpreS`, `WeakGpreS`.
7. `ts_oblivious` has a fourth (fetch) clause in Lean (`WeakRobustSim` deviation 4), discharged by
   `WeakEvInst.pstepEvTsIfetch`.  Lean's `tsOblivious` takes the value-equality hypothesis
   FIRST; the `WeakEvInst` lemmas take it second (`hts.symm`).
8. `eps_init` pins the disk at `PDisk none` and every hart at `FreeM.pure ()` with `none` parked
   fence, as Rocq; the initial FABRIC is `efInit σ.wgdev` (every residual device program at
   `.pure ()`, `WeakEvPf.efabOfInit`), so `ecfgOfInit`, `epfPfViolationFree` and the capstone
   state `wpInit (imgZ σ.wgimg) (efInit σ.wgdev) (epsInit σ)` (Rocq: `dev_state σ`), and the
   capstone's types are `Wpcfg Pexv6 Efab` / `Ptraces Pexv6 Efab` / `Pdevs Efab`.  `map_is_fmap`
   is `rfl` in Lean (kept as `mapIsFmap`).
9. PROOFS: per-arm case analysis replacing `pf_inv_old`; `wp_pf_rtc_epf_rtc` by TAIL induction on
   the pf run (Rocq: head), `epf_rtc_wp_pf_rtc` likewise.

**Rocq → Lean name map.**  `pf_ok` `pfOk`, `pf_log` `WeakEvCapstone.pfLog`, `pf_ws` `pfWs`,
`pf_cfg` `pfCfg`, `wp_pf_step_intro` `wpPfStepIntro`, `wp_pf_step_inv`
`WeakEvCapstone.wpPfStepInv`, `eags_lookup_inv` `eagsLookupInv`, `eags_upd_hart` `eagsUpdHart`,
`eags_upd_disk` `eagsUpdDisk`, `eags_eq` `eagsEq`, `eregs_apply_at` `eregsApplyAt`,
`eregs_apply_ne` `eregsApplyNe`, `elab_ws_ne` `elabWsNe`, `eib_apply_at` `eibApplyAt`,
`eib_apply_ne` `eibApplyNe`, `pf_ok_hart` `pfOkHart`, `pf_log_hart` `pfLogHart`, `pf_ws_hart`
`pfWsHart`, `pf_ok_disk` `pfOkDisk`, `pf_log_disk` `pfLogDisk`, `pf_ws_disk` `pfWsDisk`,
`ecfg_of_hart_upd` `ecfgOfHartUpd`, `ecfg_of_disk_upd` `ecfgOfDiskUpd`, `ecfg_of_dev`
`ecfgOfDev`, `ecfg_of_reg` `ecfgOfReg`, `elab_apply_elabel_ok` `elabApplyElabelOk`,
`epf_step_of_hart` `epfStepOfHart`, `epf_step_of_disk` `epfStepOfDisk`, `wp_pf_step_epf_step`
`wpPfStepEpfStep`, `ecfg_of_hset` `ecfgOfHset`, `edlab_ok_pf_ok` `edlabOkPfOk`,
`epf_step_wp_pf_step` `epfStepWpPfStep`, `epf_run_wp_pf_run` `epfRunWpPfRun`,
`epf_rtc_wp_pf_rtc` `epfRtcWpPfRtc`, `wp_pf_rtc_epf_rtc` `wpPfRtcEpfRtc`, `eps_init` `epsInit`,
`map_is_fmap` `mapIsFmap`, `ecfg_of_init` `ecfgOfInit`, `pstep_ev_lat_free_half`
`pstepEvLatFreeHalf`, `pstep_ev_lat_free_prog` `pstepEvLatFreeProg`, `pstep_ev_ts_oblivious`
`pstepEvTsOblivious`, `wm_class_of_relp` `WeakEvCapstone.wmClassOfRelp`, `pcls_ev_obl`
`pclsEvObl`, `pcls_ev_eqr` `pclsEvEqr`, `epf_pf_violation_free` `epfPfViolationFree`,
`efulfil_acct` `efulfilAcct`, `efulfil_acct_retag` `efulfilAcctRetag`, `xv6_ev_weak_robust`
`xv6EvWeakRobust`.  Lean-only: `listSetSelf`, `pfOkOfElabHart`, `pfOkHartElab`, `efetchItvOk`,
`efetchItvOkOfUnwritten`, `efetchItvOkRunOfUnwritten`, `devSetPinCases`, `devNodePlainNoPin`,
`plicAgentFdev`, `ecfgOfUset`, `ecfgOfPset`, `ecfgOfUartStep`, `ecfgOfPlicStep`, `ecfgOfPinStep`,
`epHsetSelf`, `hartPfStep`, `diskPfStep`, `epPlain`, `epPlainInit`, `epPlainStep`, `epPlainRun`.

**Not ported:** nothing (the Rocq `Print Assumptions` audit comment is not a declaration).

**Statements checked** (by hand, against Rocq): all; the changed ones are deviations 2–5 and 8
(`pfOkHart`, `pfOkDisk`, `wpPfStepEpfStep`, `epfStepWpPfStep`, `epfRunWpPfRun`, `epfRtcWpPfRtc`,
`wpPfRtcEpfRtc`, `ecfgOfInit`, `epfPfViolationFree`, `xv6EvWeakRobust`).
-/
import Weak.WeakEvInst
import Weak.WeakEvAdequacy
import Weak.WeakRetag

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-! ## 0. THE UNIFORM SHAPE OF A `wpPfStep` -/

section pfUniform

variable {P D : Type}
variable (pstep : P → D → Wlabel → P → D → Prop)
variable (pcls : P → Wlabel → Wstate → WmClass)

/-- The side condition of a pf step, as a function of the label. -/
def pfOk (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (l : Wlabel) : Prop :=
  match l with
  | LSilent => True
  | LDev .. => True
  | LFence .. => True
  -- the LOAD keeps its pin (deviation D-8 of the Rocq tree)
  | LLoad aq lat base tvs asrc =>
      asrc = [] ∧ readOk cfg.pcImg cfg.pcLog ag.paWs aq lat base tvs
  | LStore _ _ data _ _ => data ≠ []
  | LRmw aq _ base tvs data _ _ =>
      data ≠ [] ∧ tvs.length = data.length ∧
      readOk cfg.pcImg cfg.pcLog ag.paWs aq false base tvs ∧
      exclOk cfg.pcLog i base tvs (cfg.pcLog.length + 1)
  | LRegW .. | LCtrl _ | LInstr => True
  | LExLoad aq base tvs _ => readOk cfg.pcImg cfg.pcLog ag.paWs aq false base tvs
  | LExStore _ base data _ _ =>
      data ≠ [] ∧ exwinOk cfg.pcLog i ag.paWs base data.length (cfg.pcLog.length + 1)
  -- O2 (deviation 2): `PFIFetch`'s view-0 check
  | LIFetch base tvs => ifetchOk cfg.pcImg cfg.pcLog 0 base tvs

/-- The log effect of a pf step. -/
def WeakEvCapstone.pfLog (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (l : Wlabel) : List Wmsg :=
  match l with
  | LStore rl base data asrc vsrc =>
      cfg.pcLog ++ [⟨base, data, some i, pcls ag.paSt (LStore rl base data asrc vsrc) ag.paWs⟩]
  | LRmw aq rl base tvs data asrc vsrc =>
      cfg.pcLog ++ [⟨base, data, some i, pcls ag.paSt (LRmw aq rl base tvs data asrc vsrc) ag.paWs⟩]
  | LExStore rl base data asrc vsrc =>
      cfg.pcLog ++ [⟨base, data, some i, pcls ag.paSt (LExStore rl base data asrc vsrc) ag.paWs⟩]
  | LSilent | LLoad .. | LFence .. | LDev .. | LRegW .. | LCtrl _ | LInstr | LExLoad ..
  | LIFetch .. => cfg.pcLog

/-- The view effect of a pf step. -/
def pfWs (cfg : Wpcfg P D) (ag : Wpagent P) (l : Wlabel) : Wstate :=
  match l with
  | LLoad aq _ base tvs _ => loadPostRun ag.paWs aq base (tvs.map Prod.fst)
  | LStore rl base data asrc vsrc =>
      storePostRunD ag.paWs rl (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc) base data.length
        (cfg.pcLog.length + 1)
  | LRmw aq rl base tvs data asrc vsrc =>
      storePostRunD
        (loadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst))
        rl (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc) base data.length (cfg.pcLog.length + 1)
  | LFence pr pw sr sw => fencePost ag.paWs pr pw sr sw
  | LRegW rd srcs => regwPost ag.paWs rd (srcsView ag.paWs srcs)
  | LCtrl srcs => ctrlPost ag.paWs (srcsView ag.paWs srcs)
  | LInstr => instrPost ag.paWs
  | LExLoad aq base tvs asrc =>
      exloadPostRunD ag.paWs aq (srcsView ag.paWs asrc) base (tvs.map Prod.fst)
  | LExStore rl base data asrc vsrc =>
      storePostRunD ag.paWs rl (srcsView ag.paWs asrc) (srcsView ag.paWs vsrc) base data.length
        (cfg.pcLog.length + 1)
  | LSilent | LDev .. | LIFetch .. => ag.paWs

def pfCfg (cfg : Wpcfg P D) (i : Nat) (ag : Wpagent P) (l : Wlabel) (st' : P) (d' : D) :
    Wpcfg P D :=
  ⟨cfg.pcImg, WeakEvCapstone.pfLog pcls cfg i ag l, d',
   cfg.pcAgs.set i ⟨st', pfWs cfg ag l, ag.paProm⟩⟩

theorem wpPfStepIntro (i : Nat) (l : Wlabel) (cfg : Wpcfg P D) (ag : Wpagent P) (st' : P)
    (d' : D) :
    cfg.pcAgs[i]? = some ag →
    pstep ag.paSt cfg.pcDev l st' d' →
    pfOk cfg i ag l →
    wpPfStep pstep pcls i l cfg (pfCfg pcls cfg i ag l st' d') := by
  intro hlk hps hok
  cases l with
  | LSilent => exact wpPfStep.PFSilent cfg ag st' d' hlk hps
  | LLoad aq lat base tvs asrc =>
    obtain ⟨rfl, hrd⟩ := hok
    have h := wpPfStep.PFLoad (pstep := pstep) (pcls := pcls) (i := i) cfg ag aq lat base tvs []
      st' d' hlk hps hrd
    rw [srcsViewNil, loadPostRunD0] at h
    exact h
  | LStore rl base data asrc vsrc =>
    exact wpPfStep.PFStore cfg ag rl base data asrc vsrc _ st' d' hlk hps hok rfl
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨hne, hlen, hrd, hex⟩ := hok
    exact wpPfStep.PFRmw cfg ag aq rl base tvs data asrc vsrc _ st' d' hlk hps hne hlen hrd hex rfl
  | LFence pr pw sr sw => exact wpPfStep.PFFence cfg ag pr pw sr sw st' d' hlk hps
  | LDev => exact wpPfStep.PFDev cfg ag st' d' hlk hps
  | LRegW rd srcs => exact wpPfStep.PFRegW cfg ag rd srcs st' d' hlk hps
  | LCtrl srcs => exact wpPfStep.PFCtrl cfg ag srcs st' d' hlk hps
  | LInstr => exact wpPfStep.PFInstr cfg ag st' d' hlk hps
  | LExLoad aq base tvs asrc =>
    exact wpPfStep.PFExLoad cfg ag aq base tvs asrc st' d' hlk hps hok
  | LExStore rl base data asrc vsrc =>
    obtain ⟨hne, R, hR, hb, hl, hex⟩ := hok
    exact wpPfStep.PFExStore cfg ag rl base data asrc vsrc _ R st' d' hlk hps hne hR hb hl hex rfl
  | LIFetch base tvs => exact wpPfStep.PFIFetch cfg ag base tvs st' d' hlk hps hok

/-- THE LOAD PIN: the inversion needs the step to emit no load operand list. -/
theorem WeakEvCapstone.wpPfStepInv (i : Nat) (l : Wlabel) (cfg c' : Wpcfg P D) :
    lbLdepfree l →
    wpPfStep pstep pcls i l cfg c' →
    ∃ (ag : Wpagent P) (st' : P) (d' : D), cfg.pcAgs[i]? = some ag ∧
      pstep ag.paSt cfg.pcDev l st' d' ∧ pfOk cfg i ag l ∧ c' = pfCfg pcls cfg i ag l st' d' := by
  intro hdf h
  cases h with
  | PFSilent _ ag st' d' hlk hps => exact ⟨ag, st', d', hlk, hps, trivial, rfl⟩
  | PFLoad _ ag aq lat base tvs asrc st' d' hlk hps hrd =>
    have ha : asrc = [] := hdf
    subst ha
    refine ⟨ag, st', d', hlk, hps, ⟨rfl, hrd⟩, ?_⟩
    simp only [pfCfg, WeakEvCapstone.pfLog, pfWs, srcsViewNil, loadPostRunD0]
  | PFStore _ ag rl base data asrc vsrc k st' d' hlk hps hne hk =>
    subst hk
    exact ⟨ag, st', d', hlk, hps, hne, rfl⟩
  | PFRmw _ ag aq rl base tvs data asrc vsrc k st' d' hlk hps hne hlen hrd hex hk =>
    subst hk
    exact ⟨ag, st', d', hlk, hps, ⟨hne, hlen, hrd, hex⟩, rfl⟩
  | PFFence _ ag pr pw sr sw st' d' hlk hps => exact ⟨ag, st', d', hlk, hps, trivial, rfl⟩
  | PFDev _ ag st' d' hlk hps => exact ⟨ag, st', d', hlk, hps, trivial, rfl⟩
  | PFRegW _ ag rd srcs st' d' hlk hps => exact ⟨ag, st', d', hlk, hps, trivial, rfl⟩
  | PFCtrl _ ag srcs st' d' hlk hps => exact ⟨ag, st', d', hlk, hps, trivial, rfl⟩
  | PFInstr _ ag st' d' hlk hps => exact ⟨ag, st', d', hlk, hps, trivial, rfl⟩
  | PFExLoad _ ag aq base tvs asrc st' d' hlk hps hrd => exact ⟨ag, st', d', hlk, hps, hrd, rfl⟩
  | PFExStore _ ag rl base data asrc vsrc k R st' d' hlk hps hne hR hb hl hex hk =>
    subst hk
    exact ⟨ag, st', d', hlk, hps, ⟨hne, R, hR, hb, hl, hex⟩, rfl⟩
  | PFIFetch _ ag base tvs st' d' hlk hps hif => exact ⟨ag, st', d', hlk, hps, hif, rfl⟩

end pfUniform

/-! ## 1. The agent layout -/

/-- `list_insert_id` (Lean-only name). -/
theorem listSetSelf {A : Type} (l : List A) (i : Nat) (x : A) : l[i]? = some x → l.set i x = l := by
  intro h
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 h
  subst heq
  exact List.set_getElem_self hlt

theorem eagsLookupInv (P : Epool) (σ : WGState) (i : Nat) (ag : Wpagent Pexv6) :
    (eags P σ)[i]? = some ag →
    (∃ c : CPU, i = c.val ∧ ag = ehartAg P σ c) ∨ (i = nDisk ∧ ag = ediskAg P) := by
  intro h
  unfold eags at h
  by_cases hlt : i < NCPU
  · rw [List.getElem?_append_left (by simp [enumCPULength, hlt]), List.getElem?_map] at h
    cases hc : cpus[i]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact Or.inl ⟨c, (finEnumLookupNat NCPU i c hc).symm, h.symm⟩
  · rw [List.getElem?_append_right (by simp [enumCPULength]; omega)] at h
    simp only [List.length_map, enumCPULength] at h
    have hk : i - NCPU = 0 := by
      cases hk : i - NCPU with
      | zero => rfl
      | succ k => rw [hk] at h; simp at h
    rw [hk] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact Or.inr ⟨by unfold nDisk; omega, h.symm⟩

theorem eagsUpdHart (P P' : Epool) (σ σ' : WGState) (c : CPU) :
    (∀ c', c' ≠ c → ehartAg P' σ' c' = ehartAg P σ c') →
    ediskAg P' = ediskAg P →
    eags P' σ' = (eags P σ).set c.val (ehartAg P' σ' c) := by
  intro hne hd
  unfold eags
  rw [List.set_append_left _ _ (by simp [enumCPULength, c.isLt]), hd]
  congr 1
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_set, List.getElem?_map, List.getElem?_map]
  by_cases hj : c.val = j
  · subst hj
    rw [enumCPULookup]
    simp [enumCPULength, c.isLt]
  · rw [if_neg hj]
    cases hc : cpus[j]? with
    | none => rfl
    | some c0 =>
      have hc0 : c0 ≠ c := by
        intro he
        exact hj (by rw [← he]; exact finEnumLookupNat NCPU j c0 hc)
      simp only [Option.map_some]
      rw [hne c0 hc0]

theorem eagsUpdDisk (P P' : Epool) (σ σ' : WGState) :
    (∀ c, ehartAg P' σ' c = ehartAg P σ c) →
    eags P' σ' = (eags P σ).set nDisk (ediskAg P') := by
  intro hh
  unfold eags nDisk
  rw [show ehartAg P' σ' = ehartAg P σ from funext hh]
  rw [List.set_append_right _ _ (by simp [enumCPULength])]
  simp [enumCPULength]

theorem eagsEq (P P' : Epool) (σ σ' : WGState) :
    (∀ c, ehartAg P' σ' c = ehartAg P σ c) → ediskAg P' = ediskAg P → eags P' σ' = eags P σ := by
  intro hh hd
  unfold eags
  rw [show ehartAg P' σ' = ehartAg P σ from funext hh, hd]

/-- Pointwise readings of `WeakEvInst`'s σ-transformer components. -/
theorem eregsApplyAt (σ : WGState) (c : CPU) (ors : Option RegFile) :
    eregsApply σ c ors c = ors.getD (σ.wgregs c) := by
  cases ors with
  | some rs => exact gregInsertEq _ _ _
  | none => rfl

theorem eregsApplyNe (σ : WGState) (c : CPU) (ors : Option RegFile) (c' : CPU) :
    c' ≠ c → eregsApply σ c ors c' = σ.wgregs c' := by
  intro hne
  cases ors with
  | some rs => exact gregInsertNe _ _ _ _ hne
  | none => rfl

theorem elabWsNe (σ : WGState) (c : CPU) (l : Wlabel) (c' : CPU) :
    c' ≠ c → elabWs σ c l c' = σ.wgws c' := by
  intro hne
  cases l <;> simp only [elabWs] <;> first | rfl | exact gwsInsertNe _ _ _ _ hne

theorem eibApplyAt (σ : WGState) (c : CPU) (oib : Option Ibch) :
    eibApply σ c oib c = oib.getD (σ.wgib c) := by
  cases oib with
  | some v => exact gibInsertEq _ _ _
  | none => rfl

theorem eibApplyNe (σ : WGState) (c : CPU) (oib : Option Ibch) (c' : CPU) :
    c' ≠ c → eibApply σ c oib c' = σ.wgib c' := by
  intro hne
  cases oib with
  | some v => exact gibInsertNe _ _ _ _ hne
  | none => rfl

/-- The side condition at a hart, for a NON-fetch label (deviation 2). -/
theorem pfOkHart (P : Epool) (σ : WGState) (c : CPU) (l : Wlabel) :
    (∀ base tvs, l ≠ LIFetch base tvs) →
    pfOk (ecfgOf P σ) c.val (ehartAg P σ c) l = elabOk σ c l := by
  intro hnf
  cases l <;> first | rfl | exact absurd rfl (hnf _ _)

/-- ⇐ at every label (Lean-only, deviation 2): the language's fetch check is at a view `≥ 0`. -/
theorem pfOkOfElabHart (P : Epool) (σ : WGState) (c : CPU) (l : Wlabel) :
    elabOk σ c l → pfOk (ecfgOf P σ) c.val (ehartAg P σ c) l := by
  intro h
  cases l with
  | LIFetch base tvs => exact ifetchOkAnti _ _ _ _ _ _ (Nat.zero_le _) h
  | _ => exact h

/-- ⇒ at every label (Lean-only, deviation 2), under the fetch-view upgrade. -/
theorem pfOkHartElab (P : Epool) (σ : WGState) (c : CPU) (l : Wlabel) :
    (∀ base tvs, l = LIFetch base tvs →
      ifetchOk (imgZ σ.wgimg) σ.wglog 0 base tvs →
      ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) base tvs) →
    pfOk (ecfgOf P σ) c.val (ehartAg P σ c) l → elabOk σ c l := by
  intro hf h
  cases l with
  | LIFetch base tvs => exact hf base tvs rfl h
  | _ => exact h

theorem pfLogHart (P : Epool) (σ : WGState) (c : CPU) (l : Wlabel) :
    WeakEvCapstone.pfLog pclsEv (ecfgOf P σ) c.val (ehartAg P σ c) l
      = elabLog σ c l (pclsEv (ehartAg P σ c).paSt l (σ.wgws c)) := by
  cases l <;> rfl

theorem pfWsHart (P : Epool) (σ : WGState) (c : CPU) (l : Wlabel) :
    pfWs (ecfgOf P σ) (ehartAg P σ c) l = elabWs σ c l c := by
  cases l <;> simp only [pfWs, elabWs] <;> first | rfl | exact (gwsInsertEq _ _ _).symm

/-- THE DISK stays fully dependency-free (D-6). -/
theorem pfOkDisk (P : Epool) (σ : WGState) (l : Wlabel) :
    lbDepfree l → lbFused l →
    (∀ aq rl base tvs data asrc vsrc, l ≠ LRmw aq rl base tvs data asrc vsrc) →
    (∀ base tvs, l ≠ LIFetch base tvs) →
    pfOk (ecfgOf P σ) nDisk (ediskAg P) l → edlabOk σ P.epDws l := by
  intro hdf hfu hnr hnf hok
  cases l with
  | LSilent => trivial
  | LLoad aq lat base tvs asrc => exact hok
  | LStore rl base data asrc vsrc => exact ⟨hdf.1, hdf.2, hok⟩
  | LRmw aq rl base tvs data asrc vsrc => exact absurd rfl (hnr _ _ _ _ _ _ _)
  | LFence => trivial
  | LDev => trivial
  | LRegW => exact hdf.elim
  | LCtrl => exact hdf.elim
  | LInstr => exact hdf.elim
  | LExLoad => exact hfu.elim
  | LExStore => exact hfu.elim
  | LIFetch base tvs => exact absurd rfl (hnf _ _)

theorem pfLogDisk (P : Epool) (σ : WGState) (l : Wlabel) :
    WeakEvCapstone.pfLog pclsEv (ecfgOf P σ) nDisk (ediskAg P) l
      = edlabLog σ l (pclsEv (.PDisk P.epDp) l P.epDws) := by
  cases l <;> rfl

theorem pfWsDisk (P : Epool) (σ : WGState) (l : Wlabel) :
    lbDepfree l → lbFused l → pfWs (ecfgOf P σ) (ediskAg P) l = edlabWs σ P.epDws l := by
  intro hdf hfu
  cases l with
  | LStore rl base data asrc vsrc =>
    obtain ⟨rfl, rfl⟩ := hdf
    simp only [pfWs, edlabWs, ediskAg, srcsViewNil, storePostRunD0]
    rfl
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨rfl, rfl⟩ := hdf
    simp only [pfWs, edlabWs, ediskAg, srcsViewNil, loadPostRunD0, storePostRunD0]
    rfl
  | LExLoad => exact hfu.elim
  | LExStore => exact hfu.elim
  | _ => rfl

/-- ... and the four shapes of a projected configuration after one step. -/
theorem ecfgOfHartUpd (P : Epool) (σ : WGState) (c : CPU) (h' : ehst) (l : Wlabel) (k : WmClass)
    (ors : Option RegFile) (oib : Option Ibch) (obar : Option barrier_kind) (d' : DevStates) :
    ecfgOf (epHset P c h') (elabApply σ c l k ors oib obar d')
      = ⟨imgZ σ.wgimg, elabLog σ c l k, { efabOf P σ with efDev := d' },
         (eags P σ).set c.val
           ⟨.PHart c (ehartM h') (ors.getD (σ.wgregs c)) (ehartFn h') (oib.getD (σ.wgib c)),
            elabWs σ c l c, ∅⟩⟩ := by
  have hne : ∀ c', c' ≠ c →
      ehartAg (epHset P c h') (elabApply σ c l k ors oib obar d') c' = ehartAg P σ c' := by
    intro c' hc'
    simp only [ehartAg, epHset, elabApply, if_neg hc', eregsApplyNe σ c ors c' hc',
      elabWsNe σ c l c' hc', eibApplyNe σ c oib c' hc']
  have hag : ehartAg (epHset P c h') (elabApply σ c l k ors oib obar d') c
      = ⟨.PHart c (ehartM h') (ors.getD (σ.wgregs c)) (ehartFn h') (oib.getD (σ.wgib c)),
         elabWs σ c l c, ∅⟩ := by
    simp [ehartAg, epHset, elabApply, eregsApplyAt, eibApplyAt]
  have heq := eagsUpdHart P (epHset P c h') σ (elabApply σ c l k ors oib obar d') c hne rfl
  unfold ecfgOf
  rw [heq, hag]
  rfl

theorem ecfgOfDiskUpd (P : Epool) (σ : WGState) (dp' : Option (DM Dres)) (dws' : Wstate)
    (l : Wlabel) (k : WmClass) (d' : DevStates) :
    ecfgOf (epDset P dp' dws') (edlabApply σ l k d')
      = ⟨imgZ σ.wgimg, edlabLog σ l k, { efabOf P σ with efDev := d' },
         (eags P σ).set nDisk ⟨.PDisk dp', dws', ∅⟩⟩ := by
  have heq := eagsUpdDisk P (epDset P dp' dws') σ (edlabApply σ l k d') (fun _ => rfl)
  unfold ecfgOf
  rw [heq]
  rfl

theorem ecfgOfDev (P : Epool) (σ : WGState) (d' : DevStates) :
    ecfgOf P (ewgDev σ d') = ⟨imgZ σ.wgimg, σ.wglog, { efabOf P σ with efDev := d' }, eags P σ⟩ :=
  rfl

theorem ecfgOfReg (P : Epool) (σ : WGState) (c : CPU) (rs' : RegFile) :
    ecfgOf P (ewgReg σ c rs')
      = ⟨imgZ σ.wgimg, σ.wglog, efabOf P σ,
         (eags P σ).set c.val
           ⟨.PHart c (ehartM (P.epH c)) rs' (ehartFn (P.epH c)) (σ.wgib c), σ.wgws c, ∅⟩⟩ := by
  have hne : ∀ c', c' ≠ c → ehartAg P (ewgReg σ c rs') c' = ehartAg P σ c' := by
    intro c' hc'
    simp only [ehartAg, ewgReg, gregInsertNe _ _ _ _ hc']
  have hag : ehartAg P (ewgReg σ c rs') c
      = ⟨.PHart c (ehartM (P.epH c)) rs' (ehartFn (P.epH c)) (σ.wgib c), σ.wgws c, ∅⟩ := by
    simp only [ehartAg, ewgReg, gregInsertEq]
  have heq := eagsUpdHart P P σ (ewgReg σ c rs') c hne rfl
  unfold ecfgOf
  rw [heq, hag]
  rfl

/-- The residual device programs are the fabric's (deviation 4): a UART / PLIC update moves only
the `Efab` component of the projection (Lean-only). -/
theorem ecfgOfUset (P : Epool) (σ : WGState) (i : UartId) (m : DevProg (.uart i)) :
    ecfgOf (epUset P i m) σ = ⟨imgZ σ.wgimg, σ.wglog, efUset (efabOf P σ) i m, eags P σ⟩ := by
  cases i <;> rfl

theorem ecfgOfPset (P : Epool) (σ : WGState) (m : DevProg .plic) :
    ecfgOf (epPset P m) σ = ⟨imgZ σ.wgimg, σ.wglog, { efabOf P σ with efPlic := m }, eags P σ⟩ :=
  rfl

theorem epHsetSelf (P : Epool) (c : CPU) : epHset P c (P.epH c) = P := by
  cases P with
  | mk g h dp dws u0 u1 pl =>
    simp only [epHset, Epool.mk.injEq, and_true, true_and]
    funext c'
    by_cases hc : c' = c
    · subst hc; simp
    · simp [hc]

/-- THE THREE DEVICE SHAPES of a projected configuration (Lean-only, deviation 4): a UART step and
a PLIC gateway step at the disk agent, a wire write at its target hart. -/
theorem ecfgOfUartStep (P : Epool) (σ : WGState) (i : UartId) (m' : DevProg (.uart i))
    (ds' : DevStates) (k : WmClass) :
    ecfgOf (epUset P i m') (edlabApply σ (LDev .dev 0 [] [] []) k ds')
      = pfCfg pclsEv (ecfgOf P σ) nDisk (ediskAg P) (LDev .dev 0 [] [] []) (.PDisk P.epDp)
          (efUset { efabOf P σ with efDev := ds' } i m') := by
  have hs : (eags P σ).set nDisk (ediskAg P) = eags P σ := listSetSelf _ _ _ (eagsDisk P σ)
  cases i
  · show (⟨imgZ σ.wgimg, σ.wglog, ⟨ds', m', P.epU1, P.epPlic⟩, eags P σ⟩ : Wpcfg Pexv6 Efab)
      = ⟨imgZ σ.wgimg, σ.wglog, ⟨ds', m', P.epU1, P.epPlic⟩, (eags P σ).set nDisk (ediskAg P)⟩
    rw [hs]
  · show (⟨imgZ σ.wgimg, σ.wglog, ⟨ds', P.epU0, m', P.epPlic⟩, eags P σ⟩ : Wpcfg Pexv6 Efab)
      = ⟨imgZ σ.wgimg, σ.wglog, ⟨ds', P.epU0, m', P.epPlic⟩, (eags P σ).set nDisk (ediskAg P)⟩
    rw [hs]

theorem ecfgOfPlicStep (P : Epool) (σ : WGState) (m' : DevProg .plic) (ds' : DevStates)
    (k : WmClass) :
    ecfgOf (epPset P m') (edlabApply σ (LDev .dev 0 [] [] []) k ds')
      = pfCfg pclsEv (ecfgOf P σ) nDisk (ediskAg P) (LDev .dev 0 [] [] []) (.PDisk P.epDp)
          { efabOf P σ with efDev := ds', efPlic := m' } := by
  have hs : (eags P σ).set nDisk (ediskAg P) = eags P σ := listSetSelf _ _ _ (eagsDisk P σ)
  show (⟨imgZ σ.wgimg, σ.wglog, ⟨ds', P.epU0, P.epU1, m'⟩, eags P σ⟩ : Wpcfg Pexv6 Efab)
    = ⟨imgZ σ.wgimg, σ.wglog, ⟨ds', P.epU0, P.epU1, m'⟩, (eags P σ).set nDisk (ediskAg P)⟩
  rw [hs]

theorem ecfgOfPinStep (P : Epool) (σ : WGState) (c : CPU) (mm b : Bool)
    (k : Unit → DevProg .plic) :
    ecfgOf (epPset P (k ()))
        (elabApply σ c (LDev .dev 0 [] [] []) .WCplain (some (pinSet (σ.wgregs c) mm b)) none none σ.wgdev)
      = pfCfg pclsEv (ecfgOf P σ) c.val (ehartAg P σ c) (LDev .dev 0 [] [] [])
          (.PHart c (ehartM (P.epH c)) (pinSet (σ.wgregs c) mm b) (ehartFn (P.epH c)) (σ.wgib c))
          { efabOf P σ with efPlic := k () } := by
  have he := ecfgOfHartUpd P σ c (P.epH c) (LDev .dev 0 [] [] []) .WCplain (some (pinSet (σ.wgregs c) mm b)) none
    none σ.wgdev
  rw [epHsetSelf] at he
  have hag := congrArg Wpcfg.pcAgs he
  show (⟨imgZ σ.wgimg, σ.wglog, ⟨σ.wgdev, P.epU0, P.epU1, k ()⟩,
      (ecfgOf P (elabApply σ c (LDev .dev 0 [] [] []) .WCplain (some (pinSet (σ.wgregs c) mm b)) none none
        σ.wgdev)).pcAgs⟩ : Wpcfg Pexv6 Efab)
    = ⟨imgZ σ.wgimg, σ.wglog, ⟨σ.wgdev, P.epU0, P.epU1, k ()⟩,
       (eags P σ).set c.val
         ⟨.PHart c (ehartM (P.epH c)) (pinSet (σ.wgregs c) mm b) (ehartFn (P.epH c)) (σ.wgib c),
          σ.wgws c, ∅⟩⟩
  rw [hag]
  rfl

/-- The PLIC program's agent off a wire write is the disk (Lean-only). -/
theorem plicAgentFdev {m m' : DevProg .plic} {ds ds' : DevStates} :
    fdevStep .plic m ds m' ds' → plicAgent m = nDisk := by
  intro h
  cases m with
  | pure => rfl
  | op o k =>
    cases o with
    | setPin => exact h.elim
    | _ => rfl

/-! ## 2. ⇒ : EVERY LAYER-1 PF STEP OF THE PROJECTION IS AN `epfStep` -/

theorem elabApplyElabelOk (σ : WGState) (c : CPU) (l : Wlabel) (k : WmClass)
    (ors : Option RegFile) (oib : Option Ibch) (obar : Option barrier_kind) (d' : DevStates) :
    elabOk σ c l →
    (∀ aq base tvs, l ≠ LLoad aq true base tvs []) →
    elabelOk σ c l (elabApply σ c l k ors oib obar d') := by
  intro hok hlat
  cases l with
  | LSilent => exact ⟨rfl, rfl⟩
  | LLoad aq lat base tvs asrc =>
    obtain ⟨rfl, hrd⟩ := hok
    cases lat
    · exact ⟨rfl, rfl, hrd, rfl, gwsInsertEq _ _ _⟩
    · exact absurd rfl (hlat aq base tvs)
  | LStore rl base data asrc vsrc => exact ⟨⟨_, rfl⟩, hok, gwsInsertEq _ _ _⟩
  | LRmw aq rl base tvs data asrc vsrc =>
    obtain ⟨hne, hlen, hrd, hex⟩ := hok
    exact ⟨hne, hlen, hrd, hex, ⟨_, rfl⟩, gwsInsertEq _ _ _⟩
  | LFence pr pw sr sw => exact ⟨rfl, gwsInsertEq _ _ _⟩
  | LDev => exact ⟨rfl, rfl⟩
  | LRegW rd srcs => exact ⟨rfl, gwsInsertEq _ _ _⟩
  | LCtrl srcs => exact ⟨rfl, gwsInsertEq _ _ _⟩
  | LInstr => exact ⟨rfl, gwsInsertEq _ _ _⟩
  | LExLoad aq base tvs asrc => exact ⟨hok, rfl, gwsInsertEq _ _ _⟩
  | LExStore rl base data asrc vsrc =>
    obtain ⟨hne, hex⟩ := hok
    exact ⟨⟨_, rfl⟩, hne, hex, gwsInsertEq _ _ _⟩
  | LIFetch base tvs => exact ⟨hok, rfl, rfl⟩

/-- The hart's program half assembles into an `epfStep`: `EPFBoundary` at a boundary,
`EPFCycle` otherwise. -/
theorem epfStepOfHart (P : Epool) (σ : WGState) (c : CPU) (l : Wlabel) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates)
    (oib : Option Ibch) (obar : Option barrier_kind) :
    ethreadLive σ P.epGen →
    pstepNode c (ehartM (P.epH c)) (σ.wgregs c) (ehartFn (P.epH c)) (σ.wgib c) σ.wgdev l m' ors
      fn' d' oib obar →
    elabOk σ c l →
    epfStep c.val l (P, σ)
      (epHset P c (some (m', fn')),
       elabApply σ c l (pclsEv (ehartAg P σ c).paSt l (σ.wgws c)) ors oib obar d') := by
  intro hl hps hok
  have hlat : ∀ aq base tvs, l ≠ LLoad aq true base tvs [] := by
    rintro aq base tvs rfl
    exact pstepNodeLatFree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hps
  have hlbl := elabApplyElabelOk σ c l (pclsEv (ehartAg P σ c).paSt l (σ.wgws c)) ors oib obar d'
    hok hlat
  have hcy : ecycleStep P.epGen σ c (ehartM (P.epH c)) (ehartFn (P.epH c))
      (.Sail P.epGen c m' fn')
      (elabApply σ c l (pclsEv (ehartAg P σ c).paSt l (σ.wgws c)) ors oib obar d') :=
    (ecycleStepFactor _ _ _ _ _ _ _).2 ⟨l, m', ors, fn', d', oib, obar, rfl, hps, hok, rfl⟩
  match hh : P.epH c with
  | some (m, fn) =>
    rw [hh] at hcy
    exact epfStep.EPFCycle c l P σ m fn (some (m', fn')) _ hl hh hcy hlbl
  | none =>
    -- the boundary: the monad is `pure ()`, the program half emits `LInstr` and clears the bits
    rw [hh] at hps
    obtain ⟨tick, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hps
    rw [elabApplyInstr]
    exact epfStep.EPFBoundary c P σ tick hl hh

theorem epfStepOfDisk (P : Epool) (σ : WGState) (l : Wlabel) (dp' : Option (DM Dres))
    (d' : DevStates) :
    ethreadLive σ P.epGen →
    pdiskProg P.epDp σ.wgdev l dp' d' →
    edlabOk σ P.epDws l →
    epfStep nDisk l (P, σ)
      (epDset P dp' (edlabWs σ P.epDws l),
       edlabApply σ l (pclsEv (.PDisk P.epDp) l P.epDws) d') := by
  intro hl hps hok
  have hst : ediskStep P.epGen P.epDp P.epDws σ (.EDisk P.epGen dp' (edlabWs σ P.epDws l))
      (edlabApply σ l (pclsEv (.PDisk P.epDp) l P.epDws) d') :=
    (ediskStepFactor _ _ _ _ _ _).2 ⟨l, dp', d', rfl, hps, hok, rfl⟩
  have hdf : lbDepfree l :=
    pstepDiskDepfree P.epDp (efabOf P σ) l dp' { efabOf P σ with efDev := d' } (Or.inl ⟨hps, rfl⟩)
  have hlbl : edlabelOk P σ l (edlabWs σ P.epDws l)
      (edlabApply σ l (pclsEv (.PDisk P.epDp) l P.epDws) d') := by
    cases l with
    | LSilent => exact ⟨rfl, rfl⟩
    | LLoad aq lat base tvs asrc =>
      obtain ⟨rfl, hrd⟩ := hok
      cases lat
      · exact ⟨rfl, rfl, hrd, rfl, rfl⟩
      · exact absurd hps (pdiskProgLatFree _ _ _ _ _ _ _)
    | LStore rl base data asrc vsrc =>
      obtain ⟨rfl, rfl, hne⟩ := hok
      exact ⟨rfl, rfl, ⟨_, rfl⟩, hne, rfl⟩
    | LRmw => exact hok.elim
    | LFence => exact ⟨rfl, rfl⟩
    | LDev => exact ⟨rfl, rfl⟩
    | LRegW => exact hdf.elim
    | LCtrl => exact hdf.elim
    | LInstr => exact hdf.elim
    | LExLoad => exact hok.elim
    | LExStore => exact hok.elim
    | LIFetch => exact hok.elim
  exact epfStep.EPFDisk l P σ dp' _ _ hl hst hlbl

/-- THE FETCH-VIEW PREMISE (Lean-only, deviation 2): a view-0 admissible fetch the hart's program
emits is admissible at the hart's own instruction view. -/
def efetchItvOk (P : Epool) (σ : WGState) : Prop :=
  ∀ (c : CPU) (base : Int) (tvs : List (Nat × BitVec 8)) (st' : Pexv6) (d' : Efab),
    pstepEv (ehartAg P σ c).paSt (efabOf P σ) (LIFetch base tvs) st' d' →
    ifetchOk (imgZ σ.wgimg) σ.wglog 0 base tvs →
    ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) base tvs

/-- ... discharged when the fetched bytes are never written ("kernel text never written"). -/
theorem efetchItvOkOfUnwritten (P : Epool) (σ : WGState) :
    (∀ (c : CPU) (base : Int) (tvs : List (Nat × BitVec 8)) (st' : Pexv6) (d' : Efab),
       pstepEv (ehartAg P σ c).paSt (efabOf P σ) (LIFetch base tvs) st' d' →
       ∀ j : Nat, j < tvs.length → ∀ lo hi : Nat, ¬ writesIn σ.wglog (base + (j : Int)) lo hi) →
    efetchItvOk P σ := by
  intro hfr c base tvs st' d' hps h0 j t v hj
  exact ⟨(h0 j t v hj).1, hfr c base tvs st' d' hps j (lookup_lt_Some hj) _ _⟩

/-- ... and at the run level, from "no reachable log writes a fetched byte" (Lean-only). -/
theorem efetchItvOkRunOfUnwritten (ρ0 : Epool × WGState) :
    (∀ ρ, rtc epfRun ρ0 ρ →
       ∀ (c : CPU) (base : Int) (tvs : List (Nat × BitVec 8)) (st' : Pexv6) (d' : Efab),
         pstepEv (ehartAg ρ.1 ρ.2 c).paSt (efabOf ρ.1 ρ.2) (LIFetch base tvs) st' d' →
         ∀ j : Nat, j < tvs.length → ∀ lo hi : Nat, ¬ writesIn ρ.2.wglog (base + (j : Int)) lo hi) →
    ∀ ρ, rtc epfRun ρ0 ρ → efetchItvOk ρ.1 ρ.2 :=
  fun h ρ hr => efetchItvOkOfUnwritten ρ.1 ρ.2 (h ρ hr)

/-- ⇒ at the step level (deviation 4: the device arms follow the device PROGRAMS, so no device
premise; deviation 2: the fetch-view premise). -/
theorem wpPfStepEpfStep (i : Nat) (l : Wlabel) (P : Epool) (σ : WGState)
    (c' : Wpcfg Pexv6 Efab) :
    ethreadLive σ P.epGen →
    efetchItvOk P σ →
    wpPfStep pstepEv pclsEv i l (ecfgOf P σ) c' →
    ∃ P' σ', epfStep i l (P, σ) (P', σ') ∧ ecfgOf P' σ' = c' := by
  intro hl hfetch hstep
  have hdf : lbLdepfree l := by
    cases hstep <;> (apply pstepEvLdepfree; assumption)
  obtain ⟨ag, st', d', hlk, hps, hok, rfl⟩ :=
    WeakEvCapstone.wpPfStepInv pstepEv pclsEv i l _ _ hdf hstep
  have hlk' : (eags P σ)[i]? = some ag := hlk
  rcases eagsLookupInv P σ i ag hlk' with ⟨c, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- A HART
    cases st' with
    | PDisk dp' => exact (show False from hps).elim
    | PHart cpu' m' rs' fn' ib' =>
      obtain ⟨hc, ors, oib, obar, rfl, rfl, hnode | hplic⟩ := hps
      rw [hc]
      · -- the cycle event
        have hok' := pfOkHartElab P σ c l
          (fun base tvs hlf h0 => hfetch c base tvs
            (.PHart c m' (ors.getD (σ.wgregs c)) fn' (oib.getD (σ.wgib c))) d'
            (by rw [← hlf]; dsimp only [ehartAg, pstepEv]
                exact ⟨rfl, ors, oib, obar, rfl, rfl, Or.inl hnode⟩) h0) hok
        obtain ⟨hnode, hd⟩ := hnode
        obtain ⟨e, rfl⟩ : ∃ e, d' = { efabOf P σ with efDev := e } := ⟨_, hd⟩
        refine ⟨_, _, epfStepOfHart P σ c l m' ors fn' e oib obar hl hnode hok', ?_⟩
        rw [ecfgOfHartUpd, pfCfg, pfLogHart, pfWsHart]
        rfl
      · -- THE PLIC WIRE: the PLIC program sits at a wire write to `c` (deviation 4)
        rw [hc]
        obtain ⟨mm, b, k, hpl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hplic
        have hpl' : P.epPlic = .op (.setPin c mm b) k := hpl
        have hw : wdevStep P.epGen .plic rootTask P.epPlic σ (k ())
            (elabApply σ c (LDev .dev 0 [] [] []) .WCplain (some (pinSet (σ.wgregs c) mm b)) none none σ.wgdev) [] := by
          rw [hpl']
          exact Or.inl ⟨(), rfl, (eplicStepFactor P.epGen c mm b σ _ []).2 ⟨rfl, rfl⟩⟩
        have hs := epfStep.EPFPlic P σ _ (k ()) hl hw rfl
        rw [hpl'] at hs
        exact ⟨_, _, hs, ecfgOfPinStep P σ c mm b k⟩
  · -- THE DISK AGENT
    cases st' with
    | PHart cpu' m' rs' fn' ib' => exact (show False from hps).elim
    | PDisk dp' =>
      have hps' : pstepDisk P.epDp (efabOf P σ) l dp' d' := hps
      rcases hps' with ⟨hprog, hd⟩ | huart
      · obtain ⟨e, rfl⟩ : ∃ e, d' = { efabOf P σ with efDev := e } := ⟨_, hd⟩
        have hps2 : pstepDisk P.epDp (efabOf P σ) l dp' { efabOf P σ with efDev := e } :=
          Or.inl ⟨hprog, rfl⟩
        have hnr : ∀ aq rl base tvs data asrc vsrc, l ≠ LRmw aq rl base tvs data asrc vsrc := by
          rintro aq rl base tvs data asrc vsrc rfl
          exact pstepDiskNoRmw _ _ _ _ _ _ _ _ _ _ _ hps2
        have hnf : ∀ base tvs, l ≠ LIFetch base tvs := by
          rintro base tvs rfl
          exact pstepDiskNoFetch _ _ _ _ _ _ hps2
        have hdfd : lbDepfree l := pstepDiskDepfree _ _ _ _ _ hps2
        have hfud : lbFused l := pstepDiskNoEx _ _ _ _ _ hps2
        have hok' := pfOkDisk P σ l hdfd hfud hnr hnf hok
        refine ⟨_, _, epfStepOfDisk P σ l dp' e hl hprog hok', ?_⟩
        rw [ecfgOfDiskUpd, pfCfg, pfLogDisk, pfWsDisk P σ l hdfd hfud]
        rfl
      · -- THE DEVICE THREADS: one step of a UART program or of the PLIC gateway (deviation 4)
        obtain ⟨rfl, rfl, ⟨u, m', ds', hf, rfl⟩ | ⟨m', ds', hf, rfl⟩⟩ := huart
        · have hf' : fdevStep (.uart u) (epU P u) σ.wgdev m' ds' := by
            rw [← efUOf P σ u]; exact hf
          have hs := epfStep.EPFUart u P σ (edlabApply σ (LDev .dev 0 [] [] []) .WCplain ds') m' hl
            (wdevOfFdevStep P.epGen (epU P u) m' σ ds' hf') rfl
          exact ⟨_, _, hs, ecfgOfUartStep P σ u m' ds' .WCplain⟩
        · have hs := epfStep.EPFPlic P σ (edlabApply σ (LDev .dev 0 [] [] []) .WCplain ds') m' hl
            (wdevOfFdevStep P.epGen P.epPlic m' σ ds' hf) rfl
          have hag : plicAgent P.epPlic = nDisk := plicAgentFdev hf
          rw [hag] at hs
          exact ⟨_, _, hs, ecfgOfPlicStep P σ m' ds' .WCplain⟩

/-! ## 3. ⇐ : `epfRun` IS A `wpPfRun` OF THE PROJECTION -/

theorem ecfgOfHset (P : Epool) (σ : WGState) (c : CPU) (h' : ehst) :
    ecfgOf (epHset P c h') σ
      = ⟨imgZ σ.wgimg, σ.wglog, efabOf P σ,
         (eags P σ).set c.val
           ⟨.PHart c (ehartM h') (σ.wgregs c) (ehartFn h') (σ.wgib c), σ.wgws c, ∅⟩⟩ := by
  have hne : ∀ c', c' ≠ c → ehartAg (epHset P c h') σ c' = ehartAg P σ c' := by
    intro c' hc'
    simp only [ehartAg, epHset, if_neg hc']
  have hag : ehartAg (epHset P c h') σ c
      = ⟨.PHart c (ehartM h') (σ.wgregs c) (ehartFn h') (σ.wgib c), σ.wgws c, ∅⟩ := by
    simp [ehartAg, epHset]
  have heq := eagsUpdHart P (epHset P c h') σ σ c hne rfl
  unfold ecfgOf
  rw [heq, hag]
  rfl

theorem edlabOkPfOk (P : Epool) (σ : WGState) (l : Wlabel) :
    edlabOk σ P.epDws l → pfOk (ecfgOf P σ) nDisk (ediskAg P) l := by
  intro h
  cases l with
  | LStore rl base data asrc vsrc => exact h.2.2
  | LRmw => exact h.elim
  | LExLoad => exact h.elim
  | LExStore => exact h.elim
  | LIFetch => exact h.elim
  | _ => exact h

/-- A hart step of the program half, at the projection (Lean-only). -/
theorem hartPfStep (P : Epool) (σ : WGState) (c : CPU) (l : Wlabel) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab)
    (oib : Option Ibch) (obar : Option barrier_kind) (k : WmClass) :
    pstepHart c (ehartM (P.epH c)) (σ.wgregs c) (ehartFn (P.epH c)) (σ.wgib c) (efabOf P σ) l m'
      ors fn' d' oib obar →
    pfOk (ecfgOf P σ) c.val (ehartAg P σ c) l →
    k = pclsEv (ehartAg P σ c).paSt l (σ.wgws c) →
    wpPfStep pstepEv pclsEv c.val l (ecfgOf P σ)
      ⟨imgZ σ.wgimg, elabLog σ c l k, d',
       (eags P σ).set c.val
         ⟨.PHart c m' (ors.getD (σ.wgregs c)) fn' (oib.getD (σ.wgib c)), elabWs σ c l c, ∅⟩⟩ := by
  intro hps hok hk
  subst hk
  have h := wpPfStepIntro pstepEv pclsEv c.val l (ecfgOf P σ) (ehartAg P σ c)
    (.PHart c m' (ors.getD (σ.wgregs c)) fn' (oib.getD (σ.wgib c))) d' (eagsHart P σ c)
    (by dsimp only [ehartAg, pstepEv]; exact ⟨rfl, ors, oib, obar, rfl, rfl, hps⟩) hok
  rw [pfCfg, pfLogHart, pfWsHart] at h
  exact h

/-- A disk step of the program half, at the projection (Lean-only). -/
theorem diskPfStep (P : Epool) (σ : WGState) (l : Wlabel) (dp' : Option (DM Dres))
    (d' : Efab) (k : WmClass) :
    pstepDisk P.epDp (efabOf P σ) l dp' d' →
    pfOk (ecfgOf P σ) nDisk (ediskAg P) l →
    lbDepfree l → lbFused l →
    k = pclsEv (.PDisk P.epDp) l P.epDws →
    wpPfStep pstepEv pclsEv nDisk l (ecfgOf P σ)
      ⟨imgZ σ.wgimg, edlabLog σ l k, d',
       (eags P σ).set nDisk ⟨.PDisk dp', edlabWs σ P.epDws l, ∅⟩⟩ := by
  intro hps hok hdf hfu hk
  subst hk
  have h := wpPfStepIntro pstepEv pclsEv nDisk l (ecfgOf P σ) (ediskAg P) (.PDisk dp') d'
    (eagsDisk P σ) hps hok
  rw [pfCfg, pfLogDisk, pfWsDisk P σ l hdf hfu] at h
  exact h

/-- A device program either sits at a `setPin` node or does not (Lean-only). -/
theorem devSetPinCases {dv : DevId} (m : DevProg dv) :
    (∃ (c : CPU) (mm b : Bool) (k : Unit → DevProg dv), m = .op (.setPin c mm b) k) ∨
    (∀ (c : CPU) (mm b : Bool) (k : Unit → DevProg dv), m ≠ .op (.setPin c mm b) k) := by
  cases m with
  | pure a => exact Or.inr (fun _ _ _ _ h => by cases h)
  | op o k =>
    cases o with
    | setPin c mm b => exact Or.inl ⟨c, mm, b, k, rfl⟩
    | _ => exact Or.inr (fun _ _ _ _ h => by cases h)

/-- Off a wire write, a plain node is plain without the pin (Lean-only). -/
theorem devNodePlainNoPin {dv : DevId} (m : DevProg dv) :
    devNodePlain true m →
    (∀ (c : CPU) (mm b : Bool) (k : Unit → DevProg dv), m ≠ .op (.setPin c mm b) k) →
    devNodePlain false m := by
  intro hp hnp
  cases m with
  | pure a => trivial
  | op o k =>
    cases o with
    | setPin c mm b => exact absurd rfl (hnp c mm b k)
    | _ => exact hp

/-- THE POOL'S DEVICE PROGRAMS ARE PLAIN (Lean-only, deviation 3): the UARTs pin-free, the PLIC
with its wire write.  True of a fresh era (`epPlainInit`) and kept by every `epfStep`
(`epPlainStep`, from `uartBodyPlain` / `plicBodyPlain`). -/
def epPlain (P : Epool) : Prop :=
  DevPlain false P.epU0 ∧ DevPlain false P.epU1 ∧ DevPlain true P.epPlic

theorem epPlainInit (gen : Nat) : epPlain (epInit gen) := ⟨.pure _, .pure _, .pure _⟩

theorem epPlainStep (i : Nat) (l : Wlabel) (ρ ρ' : Epool × WGState) :
    epfStep i l ρ ρ' → epPlain ρ.1 → epPlain ρ'.1 := by
  intro h hp
  cases h with
  | EPFBoundary => exact hp
  | EPFCycle => exact hp
  | EPFDisk => exact hp
  | EPFUart u P σ σ' m' _ hs _ =>
    cases u
    · exact ⟨devPlainStep (uartBodyPlain _) hp.1 hs, hp.2.1, hp.2.2⟩
    · exact ⟨hp.1, devPlainStep (uartBodyPlain _) hp.2.1 hs, hp.2.2⟩
  | EPFPlic P σ σ' m' _ hs _ => exact ⟨hp.1, hp.2.1, devPlainStep plicBodyPlain hp.2.2 hs⟩

theorem epPlainRun (ρ ρ' : Epool × WGState) : rtc epfRun ρ ρ' → epPlain ρ.1 → epPlain ρ'.1 := by
  intro h
  induction h with
  | refl => exact id
  | tail _ hs ih =>
    obtain ⟨i, l, hs⟩ := hs
    exact fun hp => epPlainStep i l _ _ hs (ih hp)

/-- ⇐ at the step level, the agent and the label existential (deviation 3), at a plain pool. -/
theorem epfStepWpPfStep (i : Nat) (l : Wlabel) (ρ ρ' : Epool × WGState) :
    epPlain ρ.1 →
    epfStep i l ρ ρ' →
    ∃ i' l', wpPfStep pstepEv pclsEv i' l' (ecfgOf ρ.1 ρ.2) (ecfgOf ρ'.1 ρ'.2) := by
  intro hpl h
  cases h with
  | EPFBoundary c P σ tick hl hh =>
    -- the boundary: the `elabApply` shape `elabApplyInstr` names
    refine ⟨c.val, LInstr, ?_⟩
    have hk : pclsEv (ehartAg P σ c).paSt LInstr (σ.wgws c) = .WCplain := rfl
    have hst := hartPfStep P σ c LInstr (riscvStep tick) none none (efabOf P σ) (some ibNone) none
      .WCplain (by
        simp only [hh, ehartM, ehartFn]
        exact Or.inl ⟨⟨tick, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩) trivial hk.symm
    dsimp only
    rw [← elabApplyInstr σ c .WCplain ibNone, ecfgOfHartUpd]
    exact hst
  | EPFCycle c l P σ m fn h' σ' hl hh hcy hlbl =>
    -- one cycle event
    obtain ⟨l1, m1, ors, fn1, d1, oib, obar, he, hps, hok, rfl⟩ :=
      (ecycleStepFactor _ _ _ _ _ _ _).1 hcy
    rw [ehexpSail] at he
    injection he with _ _ hm hf
    refine ⟨c.val, l1, ?_⟩
    have hst0 : (ehartAg P σ c).paSt = .PHart c m (σ.wgregs c) fn (σ.wgib c) := by
      simp only [ehartAg, hh, ehartM, ehartFn]
    have hst := hartPfStep P σ c l1 m1 ors fn1 { efabOf P σ with efDev := d1 } oib obar _
      (by simp only [hh, ehartM, ehartFn]; exact Or.inl ⟨hps, rfl⟩)
      (pfOkOfElabHart P σ c l1 hok) (by rw [hst0])
    dsimp only
    rw [ecfgOfHartUpd, hm, hf]
    exact hst
  | EPFDisk l P σ dp' dws' σ' hl hst hlbl =>
    -- one disk event
    obtain ⟨l1, dp1, d1, he, hps, hok, rfl⟩ := (ediskStepFactor _ _ _ _ _ _).1 hst
    injection he with _ hdp hdws
    subst hdp hdws
    refine ⟨nDisk, l1, ?_⟩
    have hps2 : pstepDisk P.epDp (efabOf P σ) l1 dp' { efabOf P σ with efDev := d1 } :=
      Or.inl ⟨hps, rfl⟩
    have hdfd : lbDepfree l1 := pstepDiskDepfree _ _ _ _ _ hps2
    have hfud : lbFused l1 := pstepDiskNoEx _ _ _ _ _ hps2
    have h := diskPfStep P σ l1 dp' _ _ hps2 (edlabOkPfOk P σ l1 hok) hdfd hfud rfl
    dsimp only
    rw [ecfgOfDiskUpd]
    exact h
  | EPFUart u P σ σ' m' hl hs hlog =>
    -- a UART step: a plain, pin-free node (the pool invariant)
    have hnp : devNodePlain false (efU (efabOf P σ) u) := by
      rw [efUOf]
      cases u
      · exact devPlainNode hpl.1
      · exact devPlainNode hpl.2.1
    have hs' : wdevStep P.epGen (.uart u) rootTask (efU (efabOf P σ) u) σ m' σ' [] := by
      rw [efUOf]; exact hs
    obtain ⟨d', hdisk, -, -, rfl⟩ :=
      euartStepPstepDisk P.epGen u (efabOf P σ) m' P.epDp P.epDws σ σ' rfl hnp hs'
    refine ⟨nDisk, (LDev .dev 0 [] [] []), ?_⟩
    have h := wpPfStepIntro pstepEv pclsEv nDisk (LDev .dev 0 [] [] []) (ecfgOf P σ) (ediskAg P) (.PDisk P.epDp) _
      (eagsDisk P σ) hdisk trivial
    dsimp only
    rw [ecfgOfUartStep]
    exact h
  | EPFPlic P σ σ' m' hl hs hlog =>
    -- a PLIC step: the wire write at its target hart, the gateway at the disk
    refine ⟨plicAgent P.epPlic, (LDev .dev 0 [] [] []), ?_⟩
    dsimp only
    rcases devSetPinCases P.epPlic with ⟨c, mm, b, k, hpin⟩ | hnp
    · obtain ⟨rfl, -, hall, -, rfl⟩ :=
        eplicStepPstepHart P.epGen rootTask c mm b k (efabOf P σ) m' σ σ' [] hpin hs
      have h := hartPfStep P σ c (LDev .dev 0 [] [] []) (ehartM (P.epH c)) (some (pinSet (σ.wgregs c) mm b))
        (ehartFn (P.epH c)) { efabOf P σ with efPlic := k () } none none .WCplain (hall _ _ _)
        trivial rfl
      rw [hpin, ecfgOfPinStep P σ c mm b k]
      exact h
    · have hnp' : devNodePlain false (efabOf P σ).efPlic :=
        devNodePlainNoPin _ (devPlainNode hpl.2.2) hnp
      obtain ⟨d', hdisk, -, -, rfl⟩ :=
        eplicGateStepPstepDisk P.epGen (efabOf P σ) m' P.epDp P.epDws σ σ' rfl hnp' hs
      have h := wpPfStepIntro pstepEv pclsEv nDisk (LDev .dev 0 [] [] []) (ecfgOf P σ) (ediskAg P) (.PDisk P.epDp) _
        (eagsDisk P σ) hdisk trivial
      have hag : plicAgent P.epPlic = nDisk := by
        cases hm : P.epPlic with
        | pure => rfl
        | op o k =>
          cases o with
          | setPin c mm b => exact absurd hm (hnp c mm b k)
          | _ => rfl
      rw [hag, ecfgOfPlicStep]
      exact h

theorem epfRunWpPfRun (ρ ρ' : Epool × WGState) :
    epPlain ρ.1 → epfRun ρ ρ' → wpPfRun pstepEv pclsEv (ecfgOf ρ.1 ρ.2) (ecfgOf ρ'.1 ρ'.2) := by
  rintro hp ⟨i, l, hs⟩
  exact epfStepWpPfStep i l ρ ρ' hp hs

theorem epfRtcWpPfRtc (ρ ρ' : Epool × WGState) :
    epPlain ρ.1 →
    rtc epfRun ρ ρ' → rtc (wpPfRun pstepEv pclsEv) (ecfgOf ρ.1 ρ.2) (ecfgOf ρ'.1 ρ'.2) := by
  intro hp h
  induction h with
  | refl => exact rtc_refl _
  | @tail b c hr hs ih => exact rtc_r ih (epfRunWpPfRun _ _ (epPlainRun _ _ hr hp) hs)

/-- ... and the run-level ⇒, under the fetch-view premise at every reachable state
(deviation 2). -/
theorem wpPfRtcEpfRtc (P : Epool) (σ : WGState) (c' : Wpcfg Pexv6 Efab) :
    ethreadLive σ P.epGen →
    (∀ ρ, rtc epfRun (P, σ) ρ → efetchItvOk ρ.1 ρ.2) →
    rtc (wpPfRun pstepEv pclsEv) (ecfgOf P σ) c' →
    ∃ P' σ', rtc epfRun (P, σ) (P', σ') ∧ ecfgOf P' σ' = c' := by
  intro hl hcov hrun
  induction hrun with
  | refl => exact ⟨P, σ, rtc_refl _, rfl⟩
  | tail _ hs ih =>
    obtain ⟨P1, σ1, hr1, rfl⟩ := ih
    obtain ⟨i, l, hst⟩ := hs
    have hl1 := epfRunLive P.epGen (P, σ) (P1, σ1) hl rfl hr1
    obtain ⟨P2, σ2, hs2, rfl⟩ :=
      wpPfStepEpfStep i l P1 σ1 _ (by rw [hl1.2]; exact hl1.1) (hcov (P1, σ1) hr1) hst
    exact ⟨P2, σ2, rtc_r hr1 ⟨i, l, hs2⟩, rfl⟩

/-! ## 4. The initial configuration -/

def epsInit (σ : WGState) : List Pexv6 :=
  cpus.map (fun c : CPU => .PHart c (FreeM.pure ()) (σ.wgregs c) none (σ.wgib c)) ++ [.PDisk none]

theorem mapIsFmap {A B : Type} (f : A → B) (l : List A) : List.map f l = f <$> l := rfl

theorem ecfgOfInit (gen : Nat) (σ : WGState) :
    σ.wglog = [] → (∀ c : CPU, σ.wgws c = wsInit) →
    ecfgOf (epInit gen) σ = wpInit (imgZ σ.wgimg) (efInit σ.wgdev) (epsInit σ) := by
  intro hlog hws
  simp only [ecfgOf, wpInit, eags, epsInit, hlog, List.map_append, List.map_map,
    List.map_cons, List.map_nil]
  congr 2
  apply List.map_congr_left
  intro c _
  simp only [Function.comp, ehartAg, epInit, ehartM, ehartFn, hws]

/-! ## 5. THE LAYER-1 SIDE CONDITIONS OF THE INSTANCE, AND THE TRANSPORT -/

theorem pstepEvLatFreeHalf (p : Pexv6) (d : Efab) (aq : Bool) (base : Int)
    (tvs : List (Nat × BitVec 8)) (asrc : List Dsrc) (p' : Pexv6) (d' : Efab) :
    ¬ pstepEv p d (LLoad aq true base tvs asrc) p' d' := by
  intro hs
  have hdf : asrc = [] := pstepEvLdepfree _ _ _ _ _ hs
  subst hdf
  exact pstepEvLatFree p d aq base tvs p' d' hs

theorem pstepEvLatFreeProg : latFreeProg pstepEv :=
  fun p d aq base tvs asrc p' d' => pstepEvLatFreeHalf p d aq base tvs asrc p' d'

theorem pstepEvTsOblivious : tsOblivious pstepEv := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p d aq lat base tvs tvs' asrc p' d' hts hs
    have hdf : asrc = [] := pstepEvLdepfree _ _ _ _ _ hs
    subst hdf
    cases lat
    · exact pstepEvTsLoad p d aq base tvs tvs' p' d' hs hts.symm
    · exact absurd hs (pstepEvLatFree p d aq base tvs p' d')
  · -- D3-2: at ARBITRARY operand lists
    intro p d aq rl base tvs tvs' data asrc vsrc p' d' hts hs
    exact pstepEvTsRmw p d aq rl base tvs tvs' data asrc vsrc p' d' hs hts.symm
  · -- THE RMW SPLIT (S4): the exclusive read
    intro p d aq base tvs tvs' asrc p' d' hts hs
    exact pstepEvTsExload p d aq base tvs tvs' asrc p' d' hs hts.symm
  · -- O2 (deviation 7): the fetch
    intro p d base tvs tvs' p' d' hts hs
    exact pstepEvTsIfetch p d base tvs tvs' p' d' hs hts.symm

theorem WeakEvCapstone.wmClassOfRelp (ak : AkInfo) (ws ws' : Wstate) :
    ws.wRelp = ws'.wRelp → wmClassOf ak ws = wmClassOf ak ws' := by
  intro h
  simp only [wmClassOf, h]

theorem pclsEvObl : pclsObl pclsEv := by
  refine ⟨?_, ?_, ?_⟩
  · intro p rl base data asrc vsrc ws ws' h
    cases p with
    | PHart _ m _ _ _ => exact pnodeWclassRelp m ws ws' h
    | PDisk _ => exact WeakEvCapstone.wmClassOfRelp ddevAk _ _ h
  · intros; rfl
  · intro p rl base data asrc vsrc ws ws' h
    cases p with
    | PHart _ m _ _ _ => exact pnodeWclassRelp m ws ws' h
    | PDisk _ => exact WeakEvCapstone.wmClassOfRelp ddevAk _ _ h

theorem pclsEvEqr : pclsEqr pclsEv := by
  intro p l w1 w2 he
  have h : w1.wRelp = w2.wRelp := wsEqrRelp w1 w2 he
  cases l <;> (try rfl) <;> cases p <;>
    first
    | rfl
    | exact pnodeWclassRelp _ _ _ h
    | exact WeakEvCapstone.wmClassOfRelp ddevAk _ _ h

/-- THE TRANSPORT: the event machine's violation-freedom IS Layer 1's (under the fetch-view
premise, deviation 2). -/
theorem epfPfViolationFree (gen : Nat) (σ : WGState) :
    ethreadLive σ gen → σ.wglog = [] → (∀ c : CPU, σ.wgws c = wsInit) →
    (∀ ρ, rtc epfRun (epInit gen, σ) ρ → efetchItvOk ρ.1 ρ.2) →
    epfViolationFreeHart (epInit gen, σ) →
    pfViolationFreeHart clsOf pubOf nDisk pstepEv pclsEv (imgZ σ.wgimg) (efInit σ.wgdev)
      (epsInit σ) := by
  intro hl hlog hws hcov hvf cf hrun
  rw [← ecfgOfInit gen σ hlog hws] at hrun
  obtain ⟨P', σ', hr, rfl⟩ := wpPfRtcEpfRtc (epInit gen) σ cf hl hcov hrun
  exact hvf (P', σ') hr

/-! ## 6. The retag plumbing -/

def efulfilAcct (mid : Wpcfg Pexv6 Efab) (TS : Ptraces Pexv6 Efab) : Prop :=
  ∀ (p : Nat) (m : Wmsg) (i : Nat), mid.pcLog[p]? = some m → m.wmTid = some i →
    ∃ T, TS.ptTrs[i]? = some T ∧
      (∃ (k : Nat) (ev : Aev Efab), T.atEvs[k]? = some ev ∧ ev.aeTs = some (p + 1)) ∧
      (∀ (k1 k2 : Nat) (ev1 ev2 : Aev Efab),
         T.atEvs[k1]? = some ev1 → ev1.aeTs = some (p + 1) →
         T.atEvs[k2]? = some ev2 → ev2.aeTs = some (p + 1) → k1 = k2)

theorem efulfilAcctRetag (f : Nat → WmClass) (mid : Wpcfg Pexv6 Efab)
    (TS : Ptraces Pexv6 Efab) :
    efulfilAcct mid TS → efulfilAcct (retagCfg f mid) (retagTraces f TS) := by
  intro hacct p m' i hp htid
  obtain ⟨m, hm, rfl⟩ := retagLogLookupInv f mid.pcLog p m' hp
  rw [retagMsgTid] at htid
  exact hacct p m i hm htid

/-! ## 7. THE CAPSTONE -/

section capstone

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- Rocq `xv6_ev_weak_robust`.  Its ledger (deviations 2, 4–6): (a) the fresh-era facts about
σ0; (b) THE WP PACKAGE, `weakEvPfViolationFree`'s verbatim; (b') THE FETCH-VIEW PREMISE at every
`epfRun`-reachable state (Lean-only; `efetchItvOkRunOfUnwritten` discharges it from "no
reachable log writes a fetched byte"); (c) the behavior; (d) THE ROBUSTNESS PACKAGE at canonical
bundles, with the fetch-source premise.  The fabric is `Efab`, starting at `efInit σ0.wgdev`
(every residual device program at `.pure ()`). -/
theorem xv6EvWeakRobust [MachGpreS hlc GF] [WeakGpreS GF]
    (gen : Nat) (σ0 : WGState) (D : CPU → List Register) (hD : ∀ c, (D c).Nodup)
    (c : Wpcfg Pexv6 Efab)
    (Hgen : gen = 0)
    (Hpow : σ0.wgpow = true) (Hgen0 : σ0.wggen = 0) (Hlog : σ0.wglog = [])
    (Hws : ∀ cc : CPU, σ0.wgws cc = wsInit) :
    -- (b) THE WP PACKAGE
    (∀ [MachGS hlc GF] [WeakGS GF],
      (([∗list] cc ∈ cpus, [∗list] r ∈ D cc, regPointsTo cc r (DFrac.own 1) (σ0.wgregs cc r)) ∗
        bigSepM (M := GMapF PAddr) (fun a b => wlatPointsto (paZ a) (DFrac.own 1) 0 b) σ0.wgimg ∗
        ([∗list] cc ∈ cpus, hartView cc) ∗
        wlogLb [] ∗
        ([∗list] d ∈ DevId.all, devFragAt (MachGS.era (hlc := hlc) (GF := GF)) d (σ0.wgdev.st d)))
      ⊢@{IProp GF} |={⊤}=> ([∗list] e ∈ epowerFork gen, ewpTriv (hlc := hlc) (GF := GF) ⊤ e)) →
    -- (b') THE FETCH-VIEW PREMISE (deviation 2)
    (∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    -- (c) the behavior
    wpBehavior pstepEv (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0) c →
    -- (d) THE ROBUSTNESS PACKAGE, at canonical bundles (deviation 5: plus `fetchSrcOk`)
    (∀ (cb mid : Wpcfg Pexv6 Efab) (TS : Ptraces Pexv6 Efab) (DS : Pdevs Efab),
      wpBehavior pstepEv (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0) cb →
      rtc (wpPromiseStep (P := Pexv6) (D := Efab))
        (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) mid →
      ptracesDevOf pstepEv pdevEv TS DS mid cb →
      clsCanonical pclsEv TS →
      mainPremises nDisk TS DS ∧ fetchSrcOk TS) →
    ∃ cf, rtc (wpPfRun pstepEv pclsEv) (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) cf ∧
      progOf cf = progOf c ∧ (∀ a, memOf cf a = memOf c a) ∧
      -- ... and the promise-free witness is a RUN OF THE EVENT LANGUAGE
      ∃ P' σ', rtc epfRun (epInit gen, σ0) (P', σ') ∧ ecfgOf P' σ' = cf := by
  intro Hwp Hcov Hbeh Hprem
  have hlive : ethreadLive σ0 gen := ⟨Hpow, by rw [Hgen0, Hgen]⟩
  -- (1)+(2): adequacy gives the event machine's violation-freedom
  have hvf0 : epfViolationFreeHart (epInit gen, σ0) :=
    weakEvPfViolationFree (hlc := hlc) (GF := GF) gen σ0 D hD Hgen Hpow Hgen0 Hlog Hws Hwp
  -- (3): ... which IS Layer 1's, through the instance
  have hvf := epfPfViolationFree gen σ0 hlive Hlog Hws Hcov hvf0
  -- THE TRACED DECOMPOSITION, and the canonical retag of it
  obtain ⟨mid, TS, DS, hprom, hofd, -, hacct⟩ :=
    wpBehaviorFulfilOnceDev pstepEv pdevEv (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0) c pdevEvOk
      pstepEvLatFreeProg Hbeh
  have hbeh' := wpBehaviorRetag pstepEv (canonF pclsEv TS) _ _ _ _ Hbeh
  have hprom' : rtc (wpPromiseStep (P := Pexv6) (D := Efab))
      (wpInit (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)) (retagCfg (canonF pclsEv TS) mid) := by
    have h := wpPromiseStepsRetag (canonF pclsEv TS) _ _ hprom
    rw [retagWpInit] at h
    exact h
  have hofd' := ptracesDevOfRetag pstepEv pdevEv (canonF pclsEv TS) TS DS mid c hofd
  have hcwf : cfgWf mid := cfgWfPromiseRun pstepEv _ _ (cfgWfInit _ _ _) hprom
  have hcanon : clsCanonical pclsEv (retagTraces (canonF pclsEv TS) TS) :=
    clsCanonicalCanon pstepEv pclsEv TS hofd.1.2.2.2.1 (tsPosOfPtraces pstepEv TS mid c hcwf hofd.1)
  obtain ⟨hpkg, hfetch⟩ := Hprem _ _ _ _ hbeh' hprom' hofd' hcanon
  -- THE LAYER-1 THEOREM, at the retagged bundle
  obtain ⟨cf, hrun, hpg, hmm⟩ :=
    robustMainBundle pstepEv pclsEv pdevEv nDisk (imgZ σ0.wgimg) (efInit σ0.wgdev) (epsInit σ0)
      (retagCfg (canonF pclsEv TS) c) (retagCfg (canonF pclsEv TS) mid)
      (retagTraces (canonF pclsEv TS) TS) DS pstepEvLatFreeProg pstepEvTsOblivious pclsEvObl
      hprom' hofd' (efulfilAcctRetag (canonF pclsEv TS) mid TS hacct) hpkg hcanon hvf hfetch
  -- ... and the conclusion comes back to `c`, with the language run attached
  have hrun0 : rtc (wpPfRun pstepEv pclsEv) (ecfgOf (epInit gen) σ0) cf := by
    rw [ecfgOfInit gen σ0 Hlog Hws]
    exact hrun
  obtain ⟨P', σ', hr, heq⟩ := wpPfRtcEpfRtc (epInit gen) σ0 cf hlive Hcov hrun0
  exact ⟨cf, hrun, by rw [hpg, progOfRetag], fun a => by rw [hmm, memOfRetag], P', σ', hr, heq⟩

end capstone

end Weak
