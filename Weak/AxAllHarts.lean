/-
Weak: **Tier A adequacy for the WHOLE MACHINE** — an indexed family of agents (every hart
`CPU = Fin NCPU`, plus optional device agents), one annotation interpretation, one protocol
allocation, per-agent FRAMED WPd obligations.

Rocq: `iris/AxAllHarts.v` @ xxvzwolszwmp.

## What this file proves (the Rocq header, in substance)

`AxTierA3.tierAAdequacyAnnGmo` and `AxTierA4.tierAAdequacyAnnRun` are ALREADY indexed-family
theorems (`harts : List Agent` + `Nodup` + `Hharts`); this file is the thin layer the top-level
theorem needs on top of them:
(a) `allHarts := List.range' 0 NCPU` (= `Fin.val <$> List.finRange NCPU`, `allHartsEnum`), and
    `tierAAdequacyAll` over `allHarts ++ devs` for device agents laid out at ids
    `NCPU, NCPU+1, …` (`devIds`); `Hharts` is DISCHARGED from graph well-formedness (`gwf`,
    implied by consistency) plus the row-count bound `GD.gdG.gxProg.length ≤ NCPU + nd`
    (`agentsOfGraphRows`); the no-device form is `tierAAdequacyAllHarts` with conclusion
    `∀ c : CPU, post c (sN c)`; the `Run` twins take AxTierA4's completed-scheduler premise
    `Hsched` instead of the gmo bounds on `sPol`/`lobp`;
(b) FRAMING: every theorem takes the per-agent obligation `framedWpd`
    (`∀ i ∈ agents, ⊢ init nm i -∗ WPd (s0 i) {{ post i }}`), not a joint `[∗list]` wand;
    `hwpOfFramed` is the (trivial) split;
(c) IDLE HARTS: a hart with no events left (`(grow GD i).length ≤ atK s`) has a TRIVIAL WPd
    (`wpdIdle`, a generic re-proof of `AxLock3Writer.wpdRowEndTriv` at any `axGA2` instance).
(d) USABILITY (§4): `epiReloadSound3ViaAgents` re-derives `AxEpiSound3.epiReloadSound3` (same
    statement) through the framed interface, and `epiReloadSound3AllHarts` derives it with
    agents := `allHarts` (all 8 harts, one allocation `epiHobAlloc3All`) given `Hidle` (harts
    2..7 have empty rows; they start at `s00`, take 0 steps, WPd by `wpdIdle`).

HONESTY (Rocq): everything here is plumbing over existing adequacy theorems; the device-agent
parameter is opaque (devices are just more agents with their own run/WPd obligations).

## Deviations from Rocq

1. NAMES: camelCase (map below).  Rocq names in `notes/weak-port-dupnames.json`
   (`astep_prog_row_end_shape'`, `wpd_skip_step_of_later'`, `lb_admin_wl_wdata_none'`) and the
   §4 local helpers are file-qualified `AxAllHarts.*`.
2. O2 STAGE C: the section parameter `T` is gone (AxTierA2 deviation 2); `astepProg` has no
   fetch constructor, so `AxAllHarts.astepProgRowEndShape'` has three cases.
3. `enum CPU` / `fin_to_nat` ↦ `List.finRange NCPU` / `Fin.val`; `seq` ↦ `List.range'`.
4. Rocq's `Local Instance AxGA2_idle` is not declared: §3 passes `axGA2 GD N obSt0 obStInterp0 nm`
   explicitly.  §3 is stated for `[InvGS_gen hlc GF]`, any `hlc` (Rocq: `HasNoLc`).
5. `framedWpd`'s quantification is `∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] nm i`, as AxTierA3's
   `Hwp`.  Wand chains are `⊢ A -∗ B`.
6. §4 (Stage C, as `AxEpiSound3` deviation 1): the epilogue premises are `epiReloadSound3`'s Lean
   forms — no `T`, no `Hnw_sd`/`Hnw_ld`/`Hntext`; `fetchImgOk GD 0 0`/`0 1`, `storeRowOk GD 0 0`,
   `sdWriteOk GD 0 0 a`, `loadRowOk GD 0 1`, `ldspOwnOk GD 0 1 (0,0)`, length 2,
   `Hlob_gmo (0,0) (0,1)`, conclusion `graphValue GD (0,1)` (Rocq `(0,3)`); `epiPol` passed
   explicitly.  `Hidle`'s `2 ≤ i < NCPU` is the conjunction `2 ≤ i ∧ i < NCPU`.  The per-hart
   framed obligations and the policy bounds, repeated verbatim in Rocq's two theorems, are
   factored into Lean-only `AxAllHarts.epiHart0Framed`/`epiHart1Framed`/`epiPolGmo`.

**Rocq → Lean name map.**  `all_harts` `allHarts`, `elem_of_all_harts` `elemOfAllHarts`,
`NoDup_all_harts` `nodupAllHarts`, `cpu_in_all_harts` `cpuInAllHarts`, `all_harts_cpu`
`allHartsCpu`, `fin_enum_to_nat` `finEnumToNat`, `all_harts_enum` `allHartsEnum`, `agents_with`
`agentsWith`, `NoDup_agents_with` `nodupAgentsWith`, `gmo_agent_lt_rows` `gmoAgentLtRows`,
`dev_ids` `devIds`, `agents_of_graph_rows` `agentsOfGraphRows`, `dev_ids_props` `devIdsProps`,
`harts_of_graph_rows` `hartsOfGraphRows`, `framed_wpd` `framedWpd`, `hwp_of_framed`
`hwpOfFramed`, `tierA_adequacy_agents` `tierAAdequacyAgents`, `tierA_adequacy_agents_run`
`tierAAdequacyAgentsRun`, `tierA_adequacy_all` `tierAAdequacyAll`, `tierA_adequacy_all_harts`
`tierAAdequacyAllHarts`, `tierA_adequacy_all_run` `tierAAdequacyAllRun`,
`tierA_adequacy_all_harts_run` `tierAAdequacyAllHartsRun`, `astep_prog_row_end_shape'`
`AxAllHarts.astepProgRowEndShape'`, `lb_admin_wl_wdata_none'` `AxAllHarts.lbAdminWlWdataNone'`,
`wpd_skip_step_of_later'` `AxAllHarts.wpdSkipStepOfLater'`, `wpd_idle` `wpdIdle`, `s00`
`AxAllHarts.s00`, `in01` `AxAllHarts.in01`, `epi_reload_sound3_via_agents`
`epiReloadSound3ViaAgents`, `epi_Hob_alloc3_all` `epiHobAlloc3All`, `epi_reload_sound3_all_harts`
`epiReloadSound3AllHarts`.  Lean-only (file-qualified): `AxAllHarts.epiHart0Framed`,
`AxAllHarts.epiHart1Framed`, `AxAllHarts.epiPolGmo`.

**Dropped:** the `Print Assumptions` lines (the lint's axiom check covers them); `AxGA2_idle`
(deviation 4).
-/
import Weak.AxTierA4
import Weak.AxEpiSound3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. The hart index set -/

def allHarts : List Agent := List.range' 0 NCPU

theorem elemOfAllHarts (i : Agent) : i ∈ allHarts ↔ i < NCPU := by
  simp [allHarts, List.mem_range'_1]

theorem nodupAllHarts : allHarts.Nodup := List.nodup_range' ..

theorem cpuInAllHarts (c : CPU) : (c.val : Agent) ∈ allHarts :=
  (elemOfAllHarts _).2 c.isLt

theorem allHartsCpu (i : Agent) : i ∈ allHarts → ∃ c : CPU, c.val = i :=
  fun Hi => ⟨⟨i, (elemOfAllHarts i).1 Hi⟩, rfl⟩

theorem finEnumToNat (n : Nat) : (List.finRange n).map Fin.val = List.range' 0 n := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp

/-- `allHarts` IS the enumeration of the finite hart type. -/
theorem allHartsEnum : allHarts = (List.finRange NCPU).map Fin.val :=
  (finEnumToNat NCPU).symm

/-- Agents of the machine: all harts, then the device agents. -/
def agentsWith (devs : List Agent) : List Agent := allHarts ++ devs

theorem nodupAgentsWith (devs : List Agent) (Hnd : devs.Nodup)
    (Hhi : ∀ d, d ∈ devs → NCPU ≤ d) : (agentsWith devs).Nodup := by
  unfold agentsWith
  refine List.nodup_append.2 ⟨nodupAllHarts, Hnd, ?_⟩
  intro a Ha b Hb Hab
  have h1 := (elemOfAllHarts a).1 Ha
  have h2 := Hhi b Hb
  subst Hab
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 h2)

/-- `Hharts` from graph well-formedness: every gmo event's agent indexes a row of `gxProg`. -/
theorem gmoAgentLtRows (G : Gexec) (Hwf : gwf G) (e : Geid) :
    e ∈ G.gxGmo → e.1 < G.gxProg.length := by
  intro He
  obtain ⟨l, Hl, -⟩ := gwfGmoMem G e Hwf He
  unfold gxLbl at Hl
  rcases Nat.lt_or_ge e.1 G.gxProg.length with h | h
  · exact h
  · rw [List.getElem?_eq_none h] at Hl
    cases Hl

/-- Devices laid out at ids `NCPU, NCPU+1, …, NCPU+nd-1`. -/
def devIds (nd : Nat) : List Agent := List.range' NCPU nd

theorem agentsOfGraphRows (GD : Gdexec) (nd : Nat) (Hwf : gwf GD.gdG)
    (Hrows : GD.gdG.gxProg.length ≤ NCPU + nd) :
    ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ agentsWith (devIds nd) := by
  intro e He
  have Hlt := gmoAgentLtRows _ Hwf e He
  unfold agentsWith devIds
  rw [List.mem_append, elemOfAllHarts, List.mem_range'_1]
  rcases Nat.lt_or_ge e.1 NCPU with h | h
  · exact .inl h
  · exact .inr ⟨h, Nat.lt_of_lt_of_le Hlt Hrows⟩

theorem devIdsProps (nd : Nat) : (devIds nd).Nodup ∧ ∀ d, d ∈ devIds nd → NCPU ≤ d := by
  refine ⟨List.nodup_range' .., fun d Hd => ?_⟩
  unfold devIds at Hd
  rw [List.mem_range'_1] at Hd
  omega

theorem hartsOfGraphRows (GD : Gdexec) (Hwf : gwf GD.gdG)
    (Hrows : GD.gdG.gxProg.length ≤ NCPU) :
    ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ allHarts := by
  intro e He
  have Hlt := gmoAgentLtRows _ Hwf e He
  rw [elemOfAllHarts]
  exact Nat.lt_of_lt_of_le Hlt Hrows

/-! # 2. Framed per-agent obligations and the agent-family theorems -/

section AllHarts
variable {GF : BundledGFunctors.{0,0,0}} [Axpol] (GD : Gdexec) (N obSt0 : Type)
  (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF) (init : N → Agent → IProp GF)

/-- The per-agent (FRAMED) WPd obligation: agent `i`'s proof only sees its own `init nm i`. -/
def framedWpd (agents : List Agent) (s0 : Agent → Athread) (post : Agent → Athread → Prop) :
    Prop :=
  ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N) (i : Agent), i ∈ agents →
    ⊢ init nm i -∗
      tierAWpd GD N obSt0 obStInterp0 nm (s0 i) .MaybeStuck i (fun s => iprop(⌜post i s⌝))

/-- (b) FRAMING: per-agent obligations assemble into the joint wand. -/
theorem hwpOfFramed (agents : List Agent) (s0 : Agent → Athread)
    (post : Agent → Athread → Prop)
    (Hwp1 : framedWpd GD N obSt0 obStInterp0 init agents s0 post) :
    ∀ [InvGS_gen .hasNoLC GF] [AxannotGS GF] (nm : N),
      ⊢ ([∗list] i ∈ agents, init nm i) -∗
        [∗list] i ∈ agents,
          tierAWpd GD N obSt0 obStInterp0 nm (s0 i) .MaybeStuck i (fun s => iprop(⌜post i s⌝)) := by
  intro _ _ nm
  refine entails_wand (BigSepL.bigSepL_mono fun {_ i} Hk => ?_)
  exact wand_entails (Hwp1 nm i (List.mem_of_getElem? Hk))

/-- Generic indexed family, gmo-bounded policies. -/
theorem tierAAdequacyAgents [InvGpreS GF] [AxannotG GF]
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (agents : List Agent) (Hnd : agents.Nodup)
    (Hagents : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ agents)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ agents →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ agents → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ agents → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp1 : framedWpd GD N obSt0 obStInterp0 init agents s0 post)
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ agents, init nm i)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e) :
    ∀ i, i ∈ agents → post i (sN i) :=
  tierAAdequacyAnnGmo GD N obSt0 obStInterp0 init Hwf Hcons agents Hnd Hagents s0 sN n Hrun Hk0
    Hend post (hwpOfFramed GD N obSt0 obStInterp0 init agents s0 post Hwp1) HobAlloc HsPolGmo
    HlobpGmo

/-- Generic indexed family, ANY completed scheduler run validating the policy
(`AxTierA4.tierAAdequacyAnnRun`). -/
theorem tierAAdequacyAgentsRun [InvGpreS GF] [AxannotG GF]
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (agents : List Agent) (Hnd : agents.Nodup)
    (Hagents : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ agents)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ agents →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ agents → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ agents → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp1 : framedWpd GD N obSt0 obStInterp0 init agents s0 post)
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ agents, init nm i)
    (Hsched : ∃ sst : Sstate, rtc (schedStep GD.gdG) sst0 sst ∧
      sst.sN = GD.gdG.gxGmo.length ∧ sst.sD = ∅ ∧ axpolWfL GD sst.sProc) :
    ∀ i, i ∈ agents → post i (sN i) :=
  tierAAdequacyAnnRun GD N obSt0 obStInterp0 init Hwf Hcons agents Hnd Hagents s0 sN n Hrun Hk0
    Hend post (hwpOfFramed GD N obSt0 obStInterp0 init agents s0 post Hwp1) HobAlloc Hsched

/-- (a) THE WHOLE MACHINE: every hart of `CPU` plus the device agents `devIds nd`; `Hharts`
discharged from `gwf` (via consistency) and the row-count bound `Hrows`. -/
theorem tierAAdequacyAll [InvGpreS GF] [AxannotG GF]
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (nd : Nat) (Hrows : GD.gdG.gxProg.length ≤ NCPU + nd)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ agentsWith (devIds nd) →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ agentsWith (devIds nd) → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ agentsWith (devIds nd) → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp1 : framedWpd GD N obSt0 obStInterp0 init (agentsWith (devIds nd)) s0 post)
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ agentsWith (devIds nd), init nm i)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e) :
    (∀ c : CPU, post c.val (sN c.val)) ∧ (∀ d, d ∈ devIds nd → post d (sN d)) := by
  obtain ⟨Hdnd, Hdhi⟩ := devIdsProps nd
  have Hall := tierAAdequacyAgents GD N obSt0 obStInterp0 init Hwf Hcons
    (agentsWith (devIds nd)) (nodupAgentsWith _ Hdnd Hdhi)
    (agentsOfGraphRows GD nd (schedHGwf GD Hcons) Hrows)
    s0 sN n Hrun Hk0 Hend post Hwp1 HobAlloc HsPolGmo HlobpGmo
  refine ⟨fun c => Hall _ ?_, fun d Hd => Hall _ ?_⟩
  · exact List.mem_append.2 (.inl (cpuInAllHarts c))
  · exact List.mem_append.2 (.inr Hd)

/-- The no-device form: the top-level shape
`(∀ i, ⊢ init nm i -∗ WPd (s0 i) {{post i}}) → … → ∀ c : CPU, post c (sN c)`. -/
theorem tierAAdequacyAllHarts [InvGpreS GF] [AxannotG GF]
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (Hrows : GD.gdG.gxProg.length ≤ NCPU)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ allHarts →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ allHarts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ allHarts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp1 : framedWpd GD N obSt0 obStInterp0 init allHarts s0 post)
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ allHarts, init nm i)
    (HsPolGmo : ∀ e e', e' ∈ Axpol.sPol GD e → gmoLt GD.gdG e' e)
    (HlobpGmo : ∀ e e', e' ∈ Axpol.lobp GD e → gmoLt GD.gdG e' e) :
    ∀ c : CPU, post c.val (sN c.val) := fun c =>
  tierAAdequacyAgents GD N obSt0 obStInterp0 init Hwf Hcons allHarts nodupAllHarts
    (hartsOfGraphRows GD (schedHGwf GD Hcons) Hrows)
    s0 sN n Hrun Hk0 Hend post Hwp1 HobAlloc HsPolGmo HlobpGmo c.val (cpuInAllHarts c)

/-- (a), scheduler-run form: the whole machine under AxTierA4's completed-scheduler premise
`Hsched` instead of the gmo bounds on `sPol`/`lobp`. -/
theorem tierAAdequacyAllRun [InvGpreS GF] [AxannotG GF]
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (nd : Nat) (Hrows : GD.gdG.gxProg.length ≤ NCPU + nd)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ agentsWith (devIds nd) →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ agentsWith (devIds nd) → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ agentsWith (devIds nd) → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp1 : framedWpd GD N obSt0 obStInterp0 init (agentsWith (devIds nd)) s0 post)
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ agentsWith (devIds nd), init nm i)
    (Hsched : ∃ sst : Sstate, rtc (schedStep GD.gdG) sst0 sst ∧
      sst.sN = GD.gdG.gxGmo.length ∧ sst.sD = ∅ ∧ axpolWfL GD sst.sProc) :
    (∀ c : CPU, post c.val (sN c.val)) ∧ (∀ d, d ∈ devIds nd → post d (sN d)) := by
  obtain ⟨Hdnd, Hdhi⟩ := devIdsProps nd
  have Hall := tierAAdequacyAgentsRun GD N obSt0 obStInterp0 init Hwf Hcons
    (agentsWith (devIds nd)) (nodupAgentsWith _ Hdnd Hdhi)
    (agentsOfGraphRows GD nd (schedHGwf GD Hcons) Hrows)
    s0 sN n Hrun Hk0 Hend post Hwp1 HobAlloc Hsched
  refine ⟨fun c => Hall _ ?_, fun d Hd => Hall _ ?_⟩
  · exact List.mem_append.2 (.inl (cpuInAllHarts c))
  · exact List.mem_append.2 (.inr Hd)

/-- No-device, scheduler-run form. -/
theorem tierAAdequacyAllHartsRun [InvGpreS GF] [AxannotG GF]
    (Hwf : axpolWf) (Hcons : rvwmoCatConsistent GD)
    (Hrows : GD.gdG.gxProg.length ≤ NCPU)
    (s0 sN : Agent → Athread) (n : Agent → Nat)
    (Hrun : ∀ (_ : AxannotGS GF) (nm : N) i, i ∈ allHarts →
      nsteps (tierAAstep GD nm i) (n i) (s0 i) (sN i))
    (Hk0 : ∀ i, i ∈ allHarts → (s0 i).atK = 0)
    (Hend : ∀ i, i ∈ allHarts → (sN i).atK = (AxOpsem.grow GD i).length)
    (post : Agent → Athread → Prop)
    (Hwp1 : framedWpd GD N obSt0 obStInterp0 init allHarts s0 post)
    (HobAlloc : ⊢ |==> ∃ (nm : N) (σ0 : obSt0),
      obStInterp0 nm GD σ0 ∅ ∗ [∗list] i ∈ allHarts, init nm i)
    (Hsched : ∃ sst : Sstate, rtc (schedStep GD.gdG) sst0 sst ∧
      sst.sN = GD.gdG.gxGmo.length ∧ sst.sD = ∅ ∧ axpolWfL GD sst.sProc) :
    ∀ c : CPU, post c.val (sN c.val) := fun c =>
  tierAAdequacyAgentsRun GD N obSt0 obStInterp0 init Hwf Hcons allHarts nodupAllHarts
    (hartsOfGraphRows GD (schedHGwf GD Hcons) Hrows)
    s0 sN n Hrun Hk0 Hend post Hwp1 HobAlloc Hsched c.val (cpuInAllHarts c)

end AllHarts

/-! # 3. Idle harts: past the row end, WPd {{True}} is free

Generic re-proof of `AxLock3Writer.wpdRowEndTriv` (whose type is tied to the lock3 instance) at an
arbitrary `axGA2`. -/

theorem AxAllHarts.astepProgRowEndShape' (row : List Lbl) (s : Athread) (l : Wlabel)
    (s' : Athread) (Hnone : row[s.atK]? = none) :
    AxOpsem.astepProg row s l s' →
    lbAdmin true l ∧ s'.atK = s.atK ∧ ∃ d d', pstepProg s.atP d l s'.atP d' := by
  intro h
  cases h with
  | AStepAdmin p k d l p' d' hadm hst => exact ⟨hadm, rfl, d, d', hst⟩
  | AStepWrite p k d l lb p' d' hlk _ _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone
  | AStepFence p k d l lb p' d' hlk _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone

theorem AxAllHarts.lbAdminWlWdataNone' (l : Wlabel) : lbAdmin true l → wlWdata l = none := by
  cases l <;> simp [lbAdmin, wlWdata]

section Idle
variable {GF : BundledGFunctors.{0,0,0}} {hlc : HasLC} [InvGS_gen hlc GF] [Axpol]
  (GD : Gdexec) (N obSt0 : Type) (obStInterp0 : N → Gdexec → obSt0 → GSet Geid → IProp GF)
  (nm : N) [AxannotGS GF]

theorem AxAllHarts.wpdSkipStepOfLater' (i : Agent) (k' : Nat) (Ψ : IProp GF) :
    ⊢ ▷ Ψ -∗ @wpSkipStep GF (axGA2 GD N obSt0 obStInterp0 nm) GD i k' Ψ := by
  iintro HΨ
  unfold wpSkipStep
  iintro %na Hna
  imodintro
  inext
  imodintro
  iexists ()
  isplitl [Hna]
  · iexact Hna
  isplitr
  · iapply (show ⊢ (iprop(True) : IProp GF) from true_intro)
  · iexact HΨ

theorem wpdIdle (i : Agent) (k0 : Nat) (Hend : (AxOpsem.grow GD i).length ≤ k0) (p : Pexv6) :
    ⊢ tierAWpd GD N obSt0 obStInterp0 nm ⟨p, k0⟩ .MaybeStuck i (fun _ => iprop(True)) := by
  have Hnone : (AxOpsem.grow GD i)[k0]? = none := List.getElem?_eq_none Hend
  have H : ⊢ ∀ p : Pexv6,
      tierAWpd GD N obSt0 obStInterp0 nm ⟨p, k0⟩ .MaybeStuck i (fun _ => iprop(True)) := by
    iloeb as IH
    iintro %p
    unfold tierAWpd
    iapply (@AxWpD.wpdMUnfoldStep hlc GF _ (axGA2 GD N obSt0 obStInterp0 nm) _
      rvwmoCatConsistent .MaybeStuck i _ _).2
    isplit
    · iapply (@progressOblMaybestuck GF (axGA2 GD N obSt0 obStInterp0 nm) _ i _).2
      itrivial
    unfold wpdMPreStepDef
    iintro %GD' %ls ⟨%Hc, #Hg, -⟩
    ihave %Hg := (show AxirisG.gconstInterp (self := axGA2 GD N obSt0 obStInterp0 nm) GD' ⊢
      iprop(⌜GD' = GD⌝) from .rfl) $$ Hg
    subst GD'
    isplit
    · iintro %id %K %Hst
      obtain ⟨lb, Hlb, -⟩ := Hst
      simp only at Hlb
      rw [Hnone] at Hlb
      cases Hlb
    isplit
    · iintro %l %s' %Hst %-
      obtain ⟨Hadm, Hk', -⟩ := AxAllHarts.astepProgRowEndShape' _ _ l s' Hnone Hst
      rw [AxAllHarts.lbAdminWlWdataNone' l Hadm]
      obtain ⟨p', k1⟩ := s'
      simp only at Hk'
      subst Hk'
      iapply AxAllHarts.wpdSkipStepOfLater' (GF := GF) GD N obSt0 obStInterp0 nm i
      inext
      iapply IH $$ %p'
    isplit
    · iintro %s' %Hw
      obtain ⟨p', k1⟩ := s'
      obtain ⟨Hk, -⟩ := Hw
      simp only at Hk
      subst Hk
      iapply AxAllHarts.wpdSkipStepOfLater' (GF := GF) GD N obSt0 obStInterp0 nm i
      inext
      iapply IH $$ %p'
    · iintro %-
      iapply (@postLiftingTrue GF (axGA2 GD N obSt0 obStInterp0 nm) _ _ i _ true_intro)
  iapply H $$ %p

end Idle

/-! # 4. USABILITY: `AxEpiSound3.epiReloadSound3` through this interface -/

/-- Rocq `Local Definition s00`: hart 0's probe start state. -/
noncomputable def AxAllHarts.s00 (cpu : CPU) : Athread :=
  ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩

theorem AxAllHarts.in01 (i : Agent) : i ∈ [0, 1] → i = 0 ∨ i = 1 := by
  intro Hi
  simpa using Hi

/-- Lean-only: hart 0's framed obligation at the epilogue instance (shared by both §4
theorems; Rocq repeats the script). -/
theorem AxAllHarts.epiHart0Framed (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName) :
    ⊢ epiInit3 a b nm 0 -∗
      @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (AxAllHarts.s00 cpu)
        .MaybeStuck 0 (fun s => iprop(⌜epiPost2 GD 0 s⌝)) := by
  have HA : ⊢ ([∗list] j ↦ H ∈ epiHs0, histAuth (GF := epiGF) nm (a + (j : Int)) 1 H) -∗
      @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm (AxAllHarts.s00 cpu)
        .MaybeStuck 0 (fun s => iprop(⌜epiPost2 GD 0 s⌝)) := by
    have h := wpdEpiGa2 (hlc := .hasNoLC) (GF := epiGF) (pol := epiPol) GD nm cpu ibNone a
      Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld Hlen
    unfold tierAWpd
    refine h.trans (wand_mono .rfl ?_)
    exact @wpdMono .hasNoLC epiGF _ (axGA2 GD GName Unit epiObInterp nm) epiPol _ _ _ _ _
      (fun _ => pure_mono (fun hp _ => hp))
  iintro Hi0
  ihave Hi0 := (AxEpiSound3.epiInit3Zero a b nm).1 $$ Hi0
  iapply HA $$ Hi0

/-- Lean-only: hart 1's framed obligation from `Hwp1` (post weakened to `epiPost2`). -/
theorem AxAllHarts.epiHart1Framed (GD : Gdexec) (a b : Int) (s0_1 : Athread)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True)))
    [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName) :
    ⊢ epiInit3 a b nm 1 -∗
      @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1
        .MaybeStuck 1 (fun s => iprop(⌜epiPost2 GD 1 s⌝)) := by
  have h := Hwp1 nm
  unfold tierAWpd at h
  unfold tierAWpd
  exact h.trans (wand_mono .rfl (@wpdMono .hasNoLC epiGF _
    (axGA2 GD GName Unit epiObInterp nm) epiPol _ _ _
    _ _ (fun _ => pure_intro (fun h => absurd h (by decide)))))

/-- Lean-only: the epilogue policy's handouts are gmo-earlier. -/
theorem AxAllHarts.epiPolGmo (GD : Gdexec) (Hcons : rvwmoCatConsistent GD)
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1)) :
    (∀ e e', e' ∈ Axpol.sPol (self := epiPol) GD e → gmoLt GD.gdG e' e) ∧
    (∀ e e', e' ∈ Axpol.lobp (self := epiPol) GD e → gmoLt GD.gdG e' e) := by
  refine ⟨fun e e' he' => gmoPrefixGmoLt _ Hcons.1 e e' (elemOfListToSet.1 he'), ?_⟩
  intro e e' he'
  change e' ∈ epiLobp GD e at he'
  unfold epiLobp at he'
  split at he'
  · rename_i heq
    subst heq
    have h1 := elemOfSingleton.1 (elemOfIntersection.1 he').1
    subst h1
    exact Hlob_gmo
  · exact absurd he' notElemOfEmpty

/-- Exactly `epiReloadSound3`'s statement, proved through the FRAMED agent-family theorem
`tierAAdequacyAgents` (each hart's obligation stated and discharged alone). -/
theorem epiReloadSound3ViaAgents (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    (sN : Athread) (n : Nat)
    (Hrun : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow GD 0).length)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    graphValue GD (0, 1) = some sdData := by
  let s0 : Agent → Athread := fun i => if i = 0 then AxAllHarts.s00 cpu else s0_1
  let sNf : Agent → Athread := fun i => if i = 0 then sN else sN1
  let nf : Agent → Nat := fun i => if i = 0 then n else n1
  have Hnd : ([0, 1] : List Agent).Nodup := by decide
  obtain ⟨Hs_pol, Hlobp⟩ := AxAllHarts.epiPolGmo GD Hcons Hlob_gmo
  have Hwpf : @framedWpd epiGF epiPol GD GName Unit epiObInterp (epiInit3 a b) [0, 1] s0
      (epiPost2 GD) := by
    intro _ _ nm i Hi
    rcases AxAllHarts.in01 i Hi with rfl | rfl
    · exact AxAllHarts.epiHart0Framed GD cpu a b Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld
        Hlen nm
    · exact AxAllHarts.epiHart1Framed GD a b s0_1 Hwp1 nm
  have HrunA : ∀ (Hann : AxannotGS epiGF) (nm : GName) i, i ∈ [0, 1] →
      nsteps (tierAAstep GD nm i) (nf i) (s0 i) (sNf i) := by
    intro Hann nm i Hi
    rcases AxAllHarts.in01 i Hi with rfl | rfl
    · exact Hrun Hann nm
    · exact Hrun1 Hann nm
  have Hk0 : ∀ i, i ∈ [0, 1] → (s0 i).atK = 0 := by
    intro i Hi
    rcases AxAllHarts.in01 i Hi with rfl | rfl
    · rfl
    · exact Hk1
  have HendA : ∀ i, i ∈ [0, 1] → (sNf i).atK = (AxOpsem.grow GD i).length := by
    intro i Hi
    rcases AxAllHarts.in01 i Hi with rfl | rfl
    · exact Hend
    · exact Hend1
  have Hagents : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ [0, 1] := by
    intro e He
    rcases Hharts e He with h | h <;> rw [h] <;> simp
  have Hfin := @tierAAdequacyAgents epiGF epiPol GD GName Unit epiObInterp (epiInit3 a b) _ _
    epiAxpolWf Hcons [0, 1] Hnd Hagents s0 sNf nf HrunA Hk0 HendA (epiPost2 GD) Hwpf
    (epiHobAlloc3 a b Hdisj GD) Hs_pol Hlobp 0 (by simp)
  exact Hfin rfl (by show sN.atK = 2; rw [Hend, Hlen])

/-- `HobAlloc` over ALL harts: `epiHobAlloc3`'s allocation, harts 2..7 get `emp`. -/
theorem epiHobAlloc3All {GF : BundledGFunctors} [AxlogG GF Hent] (a b : Int)
    (Hdisj : slotsDisjoint a b) (GD : Gdexec) :
    ⊢@{IProp GF} |==> ∃ (nm : GName) (σ0 : Unit),
      epiObInterp nm GD σ0 ∅ ∗ [∗list] i ∈ allHarts, epiInit3 a b nm i := by
  have Hsplit : allHarts = [0, 1] ++ List.range' 2 6 := rfl
  have Hidle : ∀ nm : GName, ⊢@{IProp GF} [∗list] i ∈ List.range' 2 6, epiInit3 a b nm i := by
    intro nm
    refine BigSepL.bigSepL_intro fun k x hx => ?_
    have hm := List.mem_of_getElem? hx
    rw [List.mem_range'_1] at hm
    have h0 : x ≠ 0 := fun h => by rw [h] at hm; exact absurd hm.1 (by decide)
    have h1 : x ≠ 1 := fun h => by rw [h] at hm; exact absurd hm.1 (by decide)
    unfold epiInit3
    rw [if_neg h0, if_neg h1]
  rw [Hsplit]
  ihave H := epiHobAlloc3 (GF := GF) a b Hdisj GD
  imod H with ⟨%nm, %σ0, Hob, Hi⟩
  imodintro
  iexists nm, σ0
  isplitl [Hob]
  · iexact Hob
  iapply BigSepL.bigSepL_append.2
  isplitl [Hi]
  · iexact Hi
  · ihave Hid := Hidle nm
    iexact Hid

/-- The 8-HART instance: `epiReloadSound3`'s conclusion through the all-harts family, with the
extra premise `Hidle` that harts 2..7 have empty rows.  Idle harts start at `s00 cpu`, take 0
steps, and their WPd is `wpdIdle`; only harts 0 and 1 carry real proofs. -/
theorem epiReloadSound3AllHarts (GD : Gdexec) (cpu : CPU) (a b : Int)
    (Hdisj : slotsDisjoint a b)
    (Hcons : rvwmoCatConsistent GD)
    (Hharts : ∀ e, e ∈ GD.gdG.gxGmo → e.1 = 0 ∨ e.1 = 1)
    (Hidle : ∀ i, 2 ≤ i ∧ i < NCPU → AxOpsem.grow GD i = [])
    (Hgd_sd : AxCjrWpd.fetchImgOk GD 0 0 pcSd sdVs)
    (Hrow_sd : storeRowOk GD 0 0)
    (Hw_sd : sdWriteOk GD 0 0 a)
    (Hgd_ld : AxCjrWpd.fetchImgOk GD 0 1 pcLd AxEpiLedger.ldVs)
    (Hrow_ld : loadRowOk GD 0 1)
    (Hok_ld : @ldspOwnOk epiPol GD 0 1 (0, 0) a (writenHist (0, 0) sdData epiHs0))
    (Hlen : (AxOpsem.grow GD 0).length = 2)
    (Hlob_gmo : gmoLt GD.gdG (0, 0) (0, 1))
    (sN : Athread) (n : Nat)
    (Hrun : ∀ (_ : AxannotGS epiGF) (nm : GName),
      nsteps (tierAAstep GD nm 0) n
        ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone, 0⟩ sN)
    (Hend : sN.atK = (AxOpsem.grow GD 0).length)
    (s0_1 sN1 : Athread) (n1 : Nat)
    (Hk1 : s0_1.atK = 0)
    (Hrun1 : ∀ (_ : AxannotGS epiGF) (nm : GName), nsteps (tierAAstep GD nm 1) n1 s0_1 sN1)
    (Hend1 : sN1.atK = (AxOpsem.grow GD 1).length)
    (Hwp1 : ∀ [InvGS_gen .hasNoLC epiGF] [AxannotGS epiGF] (nm : GName),
      ⊢ epiInit3 a b nm 1 -∗
        @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm s0_1 .MaybeStuck 1
          (fun _ => iprop(True))) :
    graphValue GD (0, 1) = some sdData := by
  let s0 : Agent → Athread := fun i => match i with
    | 0 => AxAllHarts.s00 cpu
    | 1 => s0_1
    | _ + 2 => AxAllHarts.s00 cpu
  let sNf : Agent → Athread := fun i => match i with
    | 0 => sN
    | 1 => sN1
    | _ + 2 => AxAllHarts.s00 cpu
  let nf : Agent → Nat := fun i => match i with
    | 0 => n
    | 1 => n1
    | _ + 2 => 0
  obtain ⟨Hs_pol, Hlobp⟩ := AxAllHarts.epiPolGmo GD Hcons Hlob_gmo
  have Hidle' : ∀ k, k + 2 ∈ allHarts → AxOpsem.grow GD (k + 2) = [] := by
    intro k Hk
    exact Hidle _ ⟨Nat.le_add_left 2 k, (elemOfAllHarts _).1 Hk⟩
  have Hwpf : @framedWpd epiGF epiPol GD GName Unit epiObInterp (epiInit3 a b) allHarts s0
      (epiPost2 GD) := by
    intro _ _ nm i Hi
    match i, Hi with
    | 0, _ =>
      exact AxAllHarts.epiHart0Framed GD cpu a b Hgd_sd Hrow_sd Hw_sd Hgd_ld Hrow_ld Hok_ld
        Hlen nm
    | 1, _ => exact AxAllHarts.epiHart1Framed GD a b s0_1 Hwp1 nm
    | k + 2, Hi =>
      have Hle : (AxOpsem.grow GD (k + 2)).length ≤ 0 := by rw [Hidle' k Hi]; exact .refl
      have h := @wpdIdle epiGF .hasNoLC _ epiPol GD GName Unit epiObInterp nm _ (k + 2) 0 Hle
        (.PHart cpu (riscvStep false) (probeRegs pcSd) none ibNone)
      have h' : ⊢ @tierAWpd epiGF .hasNoLC _ _ epiPol GD GName Unit epiObInterp nm
          (AxAllHarts.s00 cpu) .MaybeStuck (k + 2) (fun s => iprop(⌜epiPost2 GD (k + 2) s⌝)) := by
        unfold tierAWpd at h
        unfold tierAWpd
        exact h.trans (@wpdMono .hasNoLC epiGF _ (axGA2 GD GName Unit epiObInterp nm) epiPol
          _ _ _ _ _ (fun _ => pure_intro (fun h => absurd h (Nat.succ_ne_zero _))))
      iintro _
      ihave H := h'
      iexact H
  have HrunA : ∀ (Hann : AxannotGS epiGF) (nm : GName) i, i ∈ allHarts →
      nsteps (tierAAstep GD nm i) (nf i) (s0 i) (sNf i) := by
    intro Hann nm i Hi
    match i with
    | 0 => exact Hrun Hann nm
    | 1 => exact Hrun1 Hann nm
    | _ + 2 => exact nsteps_O _
  have Hk0 : ∀ i, i ∈ allHarts → (s0 i).atK = 0 := by
    intro i Hi
    match i with
    | 0 => rfl
    | 1 => exact Hk1
    | _ + 2 => rfl
  have HendA : ∀ i, i ∈ allHarts → (sNf i).atK = (AxOpsem.grow GD i).length := by
    intro i Hi
    match i, Hi with
    | 0, _ => exact Hend
    | 1, _ => exact Hend1
    | k + 2, Hi => rw [Hidle' k Hi]; rfl
  have Hagents : ∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ allHarts := by
    intro e He
    rw [elemOfAllHarts]
    rcases Hharts e He with h | h <;> rw [h] <;> decide
  have Hfin := @tierAAdequacyAgents epiGF epiPol GD GName Unit epiObInterp (epiInit3 a b) _ _
    epiAxpolWf Hcons allHarts nodupAllHarts Hagents s0 sNf nf HrunA Hk0 HendA (epiPost2 GD) Hwpf
    (epiHobAlloc3All a b Hdisj GD) Hs_pol Hlobp 0 (cpuInAllHarts ⟨0, by decide⟩)
  exact Hfin rfl (by show sN.atK = 2; rw [Hend, Hlen])

end Weak
