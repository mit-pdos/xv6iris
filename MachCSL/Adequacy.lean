/-
MachCSL: ADEQUACY of the power thread (Rocq `RiscvAdequacy.v` :1213–2154).

Iris's `wp_strong_adequacy_gen` applied to the one-thread program
`[Expr.power]`, over `wp_power` (`MachCSL/Power.lean`).  The conclusion is
CSL-free: every configuration reachable from a powered-off, never-booted
machine, under ANY schedule of power cycles, hart steps and device steps, has
only reducible threads, and the client's pure trace predicate `phi` holds of the
reached state and of the run's observable trace.

Three stages.

1. `powerAdequacyCore`: the part of Rocq's `riscv_power_adequacy` proof that
   is Iris's own (the `wp_strong_adequacy` application, the `obsTotal` trick
   that pins the history ghost to the run's trace at the end, the final
   observation at `⊤ ⇛ ∅`).  It is stated over an ARBITRARY fixed record
   `F : MachFixedGS` the client builds under the given invariant world.  It
   does not name one field of the record beyond `obsTotal` and does not
   destructure `powerInterp`, so it is unchanged by any field or
   `powerInterp` conjunct added later (the crash layer's, below).
2. `bootFixedGS` (Rocq `boot_fixedGS` :1229) and `riscvPowerAdequacy` (Rocq
   `riscv_power_adequacy` :1593): the record literal filled from `MachGpreS`,
   the fixed ghosts allocated at the initial machine, and the client's hooks.
   `riscvTraceAdequacy` (Rocq `riscv_trace_adequacy` :2037) is its corollary
   at the ledger and the trivial application.
3. The trace hook's helpers (Rocq :1342–1591): `powerInterp_era`
   (`power_interp_era`), `powerInterp_mmOk` (`power_interp_resv_ok`: Lean's
   `mmOk` carries `resv_ok`), `obsPredAt`/`obsLedgerAt` and their
   alloc/step/phi lemmas (`obs_pred_at*`, `obs_ledger_at*`).

## Parameters, against Rocq's

In Rocq order: `CT`/`Cl`/`Hbirth` (the application's birth step, run first),
`Pc`/`HPc` (the crash predicate, allocated ONCE into its fixed-layer
invariant at `crashN`), [`Ppure`/`Hproj`/`Mof`/`Rb`/`Hswap`: see CRASH
below], `Pt`/`HPt`/`Hobs` (the trace predicate and its power hook), `Tg`,
`Kc`, `Cres` (record slots at the application's fixed part), `phi`/`Hphi`
(consumptive, at the raw gnames, over `powerInterp` at the literal, the
machine's history half, `obsWf`, `▷ Pc`, `▷ Pt`), `Hgen0`/`Hpow`, and
`Hboot`, which is handed the record's SHAPE as an equation
`F = bootFixedGS …` (Rocq :264–270; `rfl` here).

Deviations from Rocq (all inherited from the current MachCSL record, none
introduced here):
* no `D`/`nproc`/`ndisk` (Lean's `bootFacts` fixes the geometry);
* `Ores`/`Ires` are gone (Lean has the merged console resource `consRes`,
  Rocq's redesign R2 `Cres`); the echo window token `Wres` and the init turn
  `Tn` are not ported (`wp_power`'s header), so `Hobs`'s on-arm yields
  `Cres c (obsBoots h + 1) [] ⟨[],[],[],none⟩` only;
* the record has no application fields (`riscv_client_T`/`riscv_client`):
  the value `c` is named by the hooks and the slots, not by the record.

## CRASH: what this file assumes about the C-M additions (crash_layer.md D39)

Stage 1 is final: it needs nothing from C-M.  Stage 2 already allocates the
crash predicate the Rocq way -- swap counter at 0 (`γswap`), then
`Pc γswap γreg γstart c` from `HPc`, sealed into `inv powerCrashN (Pc …)`
(`powerCrashN` = Rocq `crashN` = `nroot .@ "crash"`), and consumed at the end
of the run by `Hphi` beside `▷ Pt`.  What C-M's merge adds, all additive:
* `MachFixedGS` fields `diskName`/`diskSize`/`crashPred`/`swapName`:
  `bootFixedGS` gains `(γdisk : GName) (ndisk : Nat) (γswap : GName)
  (Pcp : IProp GF)` in Rocq's positions and sets `crashPred := Pcp`,
  `swapName := γswap`; `riscvPowerAdequacy` passes
  `(Pc γdisk γswap γreg γstart c)`.  The invariant allocated here is then
  C-M's `crashInv` at the literal, PROVIDED C-M's `crashN` is
  `ndot nroot "crash"` and `crashInv := inv crashN crashPred` (replace
  `powerCrashN` by it).
* the durable-disk camera (C-M's `DiskImg`): allocate
  `diskImgSizedAlloc (g.m.devs virtio disk) ndisk` first; its fragments join
  `HPc`'s premise (Rocq :20–23), its auth joins the initial `powerInterp`.
* `diskFixedInterp`, appended LAST to `powerInterp`: the initial
  `powerInterp` proof below frames one more conjunct; nothing else here
  destructures `powerInterp`.
* `wp_power`'s new hooks (`Hproj`/`Mof`/`Rb`/`Hswap`, the `Hobs` disk lend)
  and its crash-invariant premise: `riscvPowerAdequacy` takes Rocq's
  `Ppure`/`Hproj`/`Mof`/`Rb`/`Hswap` at the raw gnames (as `HPc`) and passes
  them through; `Hobs`/`Hphi` take the lent disk auth; `Hboot` gains the
  `Ppure` premise and receives `crashInv`/`Rb c gen` inside `powerBootRes`.
  UNTIL THEN `Hboot` does not see the crash invariant (the current
  `wp_power` has no channel for it).
-/
import MachCSL.Power
import Iris.ProgramLogic.Adequacy

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std Std
open Language.Notation PrimStep

variable {hlc : HasLC} {GF : BundledGFunctors}

/-- The record `F` with its invariant world replaced by `Hinv`.  The core
quantifies over the record EXISTENTIALLY, so it cannot ask that the client's
record be built over the adequacy's invariant world; it forces it instead.  A
record built as a literal over `Hinv` is convertible with this. -/
@[reducible] def MachFixedGS.withInv (F : MachFixedGS hlc GF) (Hinv : InvGS_gen hlc GF) :
    MachFixedGS hlc GF :=
  { F with invGS := Hinv }

/-- What the core asks of the client at the record `F` (the body of Rocq's
`wp_strong_adequacy` premise, as `riscv_power_adequacy`'s proof fills it):
the record's whole-run trace is the run's, the initial state
interpretation, the power thread's WP, and the FINAL OBSERVATION -- at the
last state of the run, with the machine's half of the history (which is then
the run's trace) and its well-formedness, a fancy update to `∅` into the pure
`phi`, so every invariant may be opened and never closed. -/
def adeqBirth [MachFixedGS hlc GF] (g : GState) (κs : List Obs)
    (phi : GState → List Obs → Prop) : IProp GF := iprop%
  ⌜MachFixedGS.obsTotal (hlc := hlc) (GF := GF) = κs⌝ ∗
  (powerInterp g ∗ obsInterp g κs) ∗
  WP Expr.power @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
  (∀ (g2 : GState) (h : List Obs), powerInterp g2 -∗ obsHalf h -∗ ⌜obsWf h g2⌝ -∗
    |={⊤,∅}=> ⌜phi g2 h⌝)

/-- THE GENERIC CORE of `riscv_power_adequacy`: whatever the fixed record,
if the client can build it with its birth obligations, the run is safe and
`phi` holds of its last state and trace.  Independent of the record's fields
beyond `obsTotal` (see the header, CRASH). -/
theorem powerAdequacyCore [MachGpreS hlc GF] (g : GState) (phi : GState → List Obs → Prop)
    (Hwp : ∀ [Hinv : InvGS_gen hlc GF] (κs : List Obs),
      ⊢@{IProp GF} |={⊤}=> ∃ F : MachFixedGS hlc GF, @adeqBirth hlc GF (F.withInv Hinv) g κs phi)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ phi g2 κs := by
  suffices h : (∀ e2, e2 ∈ t2 → NotStuck (Val := Val) (e2, g2)) ∧ phi g2 κs by
    refine ⟨fun e2 he => ?_, h.2⟩
    rcases h.1 e2 he with hv | hr
    · exact absurd hv (by simp [ToVal.toVal])
    · exact hr
  refine wp_strong_adequacy_gen (hlc := hlc) (GF := GF) Stuckness.NotStuck [Expr.power] g n κs t2 g2
    _ (fun _ => 0) ?_ hsteps
  intro Hinv
  have H := @Hwp Hinv κs
  unfold adeqBirth at H
  imod H with ⟨%F, %htot, HSI, Hwp, Hfin⟩
  imodintro
  iexists (fun σ ns κs' nt => @stateInterp GState Obs GF (@instIrisGS hlc GF (F.withInv Hinv)).toStateInterp σ ns κs' nt),
    [fun _ => iprop(True)], (fun _ => iprop(True)),
    (@instIrisGS hlc GF (F.withInv Hinv)).stateInterp_mono
  dsimp only
  simp only [@stateInterp_eq hlc GF (F.withInv Hinv)]
  isplitl [HSI]
  · iexact HSI
  isplitl [Hwp]
  · iapply BigSepL2.bigSepL2_singleton
    iexact Hwp
  iintro %es' %t2' %Heq %Hlen %Hns ⟨Hpi, Hoi⟩ _ _
  unfold obsInterp
  icases Hoi with ⟨%h, %htot', %hwf, Ha⟩
  have hh : h = κs := by rw [List.append_nil] at htot'; exact htot'.trans htot
  subst hh
  unfold obsAuth
  icases Ha with ⟨Hhalf, _⟩
  imod Hfin $$ %g2 %h Hpi Hhalf %hwf with %hphi
  imodintro
  ipureintro
  exact ⟨fun e2 he => Hns e2 trivial he, hphi⟩

/-! ## Stage 2: the power adequacy -/

/-- THE FIXED RECORD the adequacy builds (Rocq `boot_fixedGS` :1229), named
so that `Hboot` can be told its shape: every functor instance from
`MachGpreS`, the invariant world, the fixed gnames, the run's trace `T`, the
trace predicate `Ptp`, and the application's slots. -/
@[reducible] def bootFixedGS [MachGpreS hlc GF] (Hinv : InvGS_gen hlc GF)
    (γgen γstart γreg γobs : GName) (T : List Obs) (Ptp : IProp GF) (γhist : GName)
    (Tg : List Obs → IProp GF) (HTg : ∀ h, Persistent (Tg h)) (HTgt : ∀ h, Timeless (Tg h))
    (Kc : IProp GF) (HKc : Persistent Kc) (HKct : Timeless Kc)
    (Cres : Nat → List Obs → ConsHist → IProp GF) (HCrest : ∀ k h H, Timeless (Cres k h H)) :
    MachFixedGS hlc GF where
  invGS := Hinv
  reg := MachGpreS.reg_pre
  memPre := MachGpreS.mem_pre
  mono := MachGpreS.mono_pre
  registry := MachGpreS.registry_pre
  authG := MachGpreS.auth_pre
  resvG := MachGpreS.resv_pre
  dirtyG := MachGpreS.dirty_pre
  lockSetG := MachGpreS.lockset_pre
  lockG := MachGpreS.lock_pre
  kmapG := MachGpreS.kmap_pre
  kptRootG := MachGpreS.kptroot_pre
  devG := MachGpreS.dev_pre
  genName := γgen
  startName := γstart
  registryName := γreg
  obsVarG := MachGpreS.obsVar_pre
  obsName := γobs
  obsTotal := T
  obsPred := Ptp
  obsHistG := MachGpreS.obsHist_pre
  obsHist := γhist
  rxTag := Tg
  rxTag_persistent := HTg
  rxTag_timeless := HTgt
  killCred := Kc
  killCred_persistent := HKc
  killCred_timeless := HKct
  consRes := Cres
  consRes_timeless := HCrest

/-- The crash invariant's namespace (Rocq `crashN`; C-M's `crashN` replaces
it, see the header). -/
def powerCrashN : Namespace := ndot nroot "crash"

theorem powerCrashN_obsN : (↑obsN : CoPset) ⊆ ⊤ \ ↑powerCrashN := by
  have hd : (↑obsN : CoPset) ## ↑powerCrashN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  rw [CoPset.in_diff]
  exact ⟨CoPset.subseteq_top p hp, fun hc => hd p ⟨hp, hc⟩⟩

/-- THE POWER ADEQUACY (Rocq `riscv_power_adequacy` :1593): the machine
starts POWERED OFF with nothing ever run; if the client can boot ANY era from
ANY reset state, every configuration reachable under any schedule is
reducible and satisfies `phi` of the run's observable trace.

The hooks, in Rocq's order (the header lists the crash ones C-M adds):
* `Hbirth` -- the application's birth step, run FIRST, so the slots can name
  its value `c`;
* `Pc`/`HPc` -- the crash predicate at the swap counter (at 0), the registry
  and the started counter, allocated ONCE into a fixed-layer invariant;
* `Pt`/`HPt` -- the trace predicate, born from the birth's yield and the
  client's half of the empty history, sealed into `obsInv`;
* `Hobs` -- the power hook: the client moves its half by the power event and,
  on a power-on, founds the era's console claim;
* `Tg`/`Kc`/`Cres` -- the record's application slots;
* `phi`/`Hphi` -- the trace invariant, read off `powerInterp` at the literal,
  the machine's history half, `obsWf`, and the two fixed-layer predicates;
* `Hboot` -- the client's whole system, told the record's shape. -/
theorem riscvPowerAdequacy [MachGpreS hlc GF] [KernelMap] (g : GState)
    (CT : Type) (Cl : CT → IProp GF)
    (Hbirth : ⊢@{IProp GF} |==> ∃ c : CT, Cl c)
    (Pc : GName → GName → GName → CT → IProp GF)
    (HPc : ∀ (γsw γreg γst : GName) (c : CT),
      MonoNat.auth_own γsw (DFrac.own 1) (.ofNat 0) ⊢@{IProp GF} |==> Pc γsw γreg γst c)
    (Pt : GName → CT → IProp GF)
    (Tg : CT → List Obs → IProp GF) (HTg : ∀ c h, Persistent (Tg c h))
    (HTgt : ∀ c h, Timeless (Tg c h))
    (Kc : CT → IProp GF) (HKc : ∀ c, Persistent (Kc c)) (HKct : ∀ c, Timeless (Kc c))
    (Cres : CT → Nat → List Obs → ConsHist → IProp GF)
    (HCrest : ∀ c k h H, Timeless (Cres c k h H))
    (HPt : ∀ (γobs : GName) (c : CT),
      Cl c ∗ (γobs ↪VAR{.own (1 : Qp).half} ([] : List Obs)) ⊢@{IProp GF} |==> Pt γobs c)
    (Hobs : ∀ (γobs : GName) (c : CT) (h : List Obs) (on : Bool), traceShape h on →
      ▷ Pt γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} h) ⊢@{IProp GF}
        |==> ◇ (▷ Pt γobs c ∗ (γobs ↪VAR{.own (1 : Qp).half} (h ++ [powerEv on])) ∗
          (if on then iprop(emp) else Cres c (obsBoots h + 1) [] ⟨[], [], [], none⟩)))
    (phi : GState → List Obs → Prop)
    (Hphi : ∀ (Hinv : InvGS_gen hlc GF) (γgen γstart γreg γswap γobs γhist : GName) (c : CT)
        (T : List Obs) (g' : GState) (h : List Obs),
      @powerInterp hlc GF (bootFixedGS Hinv γgen γstart γreg γobs T (Pt γobs c) γhist
          (Tg c) (HTg c) (HTgt c) (Kc c) (HKc c) (HKct c) (Cres c) (HCrest c)) g' ∗
        (γobs ↪VAR{.own (1 : Qp).half} h) ∗ ⌜obsWf h g'⌝ ∗
        ▷ Pc γswap γreg γstart c ∗ ▷ Pt γobs c ⊢@{IProp GF} ◇ ⌜phi g' h⌝)
    (Hgen0 : g.gen = 0) (Hpow : g.pow = false)
    (Hboot : ∀ [F : MachFixedGS hlc GF] (Hinv : InvGS_gen hlc GF)
        (γgen γstart γreg γobs γhist : GName) (c : CT) (T : List Obs),
      F = bootFixedGS Hinv γgen γstart γreg γobs T (Pt γobs c) γhist
          (Tg c) (HTg c) (HTgt c) (Kc c) (HKc c) (HKct c) (Cres c) (HCrest c) →
      ∀ (E : EraGS GF) (gen : Nat) (σ : MState) (image : Mem), bootFacts σ image →
        obsInv ∗ powerBootRes E gen σ ⊢@{IProp GF} |={⊤}=>
          ([∗list] cpu ∈ cpus, hartWP gen cpu (pure ())) ∗
          ([∗list] d ∈ DevId.all, devWP gen d rootTask (pure ())))
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ phi g2 κs := by
  refine powerAdequacyCore (hlc := hlc) (GF := GF) g phi ?_ n κs t2 g2 hsteps
  intro Hinv T
  imod (MonoNat.own_alloc (GF := GF) (.ofNat g.gen)) with ⟨%γgen, Hgauth, _⟩
  imod (MonoNat.own_alloc (GF := GF) (.ofNat (startCount g))) with ⟨%γstart, Hsauth, _⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := Nat) (V := EraGS GF) (H := RegMapF)) with ⟨%γreg, HRauth⟩
  imod (MonoNat.own_alloc (GF := GF) (.ofNat 0)) with ⟨%γswap, Hswap, _⟩
  imod Hbirth with ⟨%c, Hcl⟩
  imod (HPc γswap γreg γstart c) $$ Hswap with HPc0
  imod (inv_alloc powerCrashN ⊤ (Pc γswap γreg γstart c)) $$ [HPc0] with #Hcinv
  · inext; iexact HPc0
  imod (ghost_var_alloc (GF := GF) ([] : List Obs)) with ⟨%γobs, Hob⟩
  have hsplit := (ghost_var_fractional (GF := GF) γobs ([] : List Obs)).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hsplit
  icases hsplit.1 $$ Hob with ⟨HobA, HobF⟩
  imod (MonoList.own_alloc (GF := GF) ([] : List Obs)) with ⟨%γhist, HobH, _⟩
  imod (HPt γobs c) $$ [Hcl HobF] with HPt0
  · iframe Hcl HobF
  imod (inv_alloc obsN ⊤ (Pt γobs c)) $$ [HPt0] with #Hoinv
  · inext; iexact HPt0
  imodintro
  iexists (bootFixedGS Hinv γgen γstart γreg γobs T (Pt γobs c) γhist
    (Tg c) (HTg c) (HTgt c) (Kc c) (HKc c) (HKct c) (Cres c) (HCrest c))
  unfold adeqBirth
  isplitr
  · ipureintro; rfl
  isplitl [Hgauth Hsauth HRauth HobA HobH]
  · isplitl [Hgauth Hsauth HRauth]
    · unfold powerInterp genAuth startAuth eraCur
      iframe Hgauth Hsauth
      iexists ∅
      iframe HRauth
      rw [Hpow]
      isplit
      · ipureintro
        intro k
        simp [LawfulPartialMap.get?_empty, startCount, Hpow, Hgen0]
      · ipureintro; trivial
    · unfold obsInterp obsAuth obsHalf obsHistAuth
      iexists []
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact obsWf_init g Hpow Hgen0
      iframe HobA HobH
  isplitl []
  · iapply (@wp_power hlc GF ((bootFixedGS Hinv γgen γstart γreg γobs T (Pt γobs c) γhist
      (Tg c) (HTg c) (HTgt c) (Kc c) (HKc c) (HKct c) (Cres c) (HCrest c)).withInv Hinv) _
      (fun h on hs => Hobs γobs c h on hs)
      (fun E gen σ image hbf => @Hboot ((bootFixedGS Hinv γgen γstart γreg γobs T (Pt γobs c) γhist
        (Tg c) (HTg c) (HTgt c) (Kc c) (HKc c) (HKct c) (Cres c) (HCrest c)).withInv Hinv)
        Hinv γgen γstart γreg γobs γhist c T rfl E gen σ image hbf))
    unfold obsInv
    iexact Hoinv
  unfold obsHalf
  iintro %g2' %h Hpi Hhalf %hwf
  imod (inv_acc (E := ⊤) (N := powerCrashN) (P := Pc γswap γreg γstart c) CoPset.subseteq_top)
    $$ Hcinv with ⟨HP, _⟩
  imod (inv_acc (E := ⊤ \ ↑powerCrashN) (N := obsN) (P := Pt γobs c) powerCrashN_obsN)
    $$ Hoinv with ⟨HPt, _⟩
  imod (Hphi Hinv γgen γstart γreg γswap γobs γhist c T g2' h) $$ [Hpi Hhalf HP HPt] with %hphi
  · iframe Hpi Hhalf HP HPt
    ipureintro; exact hwf
  iapply fupd_mask_intro_discard LawfulSet.empty_subset
  ipureintro; exact hphi

/-! ## Stage 3: the trace hook's helpers -/

section helpers
variable [MachFixedGS hlc GF]

/-- The era conjunct at the client's own era (Rocq `power_interp_era`). -/
theorem powerInterp_era (g : GState) (E : EraGS GF) (hpw : g.pow = true) :
    powerInterp g ∗ eraRegistered g.gen E ⊢@{IProp GF} eraInterp E g.m := by
  unfold powerInterp eraCur
  simp only [hpw]
  iintro ⟨⟨_, _, %R, HR, _, %E', %hE', Hera⟩, #Hreg⟩
  ihave %hE := eraRegistered_lookup R g.gen E $$ HR Hreg
  rw [hE'] at hE
  cases hE
  iexact Hera

/-- A fact already pure in the state interpretation (Rocq
`power_interp_resv_ok`; Lean's `mmOk` carries `resv_ok`). -/
theorem powerInterp_mmOk (g : GState) :
    powerInterp g ⊢@{IProp GF} ⌜g.pow = true → mmOk g.m⌝ := by
  unfold powerInterp eraCur
  cases hpw : g.pow
  · iintro _
    ipureintro
    intro h; cases h
  · iintro ⟨_, _, %R, _, _, %E, _, Hera⟩
    unfold eraInterp memModelAt
    icases Hera with ⟨_, _, ⟨_, _, _, _, %hok⟩, _⟩
    ipureintro
    exact fun _ => hok

end helpers

section raw
variable [MachGpreS hlc GF]

/-- The trivial trace predicate at a raw gname (Rocq `obs_pred_at`);
convertible with `obsPredTriv` at the literal (`bootFixedGS_obsPredTriv`). -/
def obsPredAt (γ : GName) : IProp GF := iprop% ∃ h : List Obs, γ ↪VAR{.own (1 : Qp).half} h

theorem obsPredAt_alloc (γ : GName) :
    (γ ↪VAR{.own (1 : Qp).half} ([] : List Obs)) ⊢@{IProp GF} |==> obsPredAt γ := by
  unfold obsPredAt
  iintro H
  imodintro
  iexists []
  iexact H

theorem obsPredAt_alloc_cl {CT : Type} (Cl : CT → IProp GF) (γ : GName) (c : CT) :
    Cl c ∗ (γ ↪VAR{.own (1 : Qp).half} ([] : List Obs)) ⊢@{IProp GF} |==> obsPredAt γ := by
  iintro ⟨_, H⟩
  iapply obsPredAt_alloc γ $$ H

theorem obsPredAt_step (C : Nat → List Obs → ConsHist → IProp GF)
    (HC : ∀ k : Nat, ⊢@{IProp GF} C k [] ⟨[], [], [], none⟩)
    (γ : GName) (h : List Obs) (on : Bool) (_ : traceShape h on) :
    ▷ obsPredAt γ ∗ (γ ↪VAR{.own (1 : Qp).half} h) ⊢@{IProp GF}
      |==> ◇ (▷ obsPredAt γ ∗ (γ ↪VAR{.own (1 : Qp).half} (h ++ [powerEv on])) ∗
        (if on then iprop(emp) else C (obsBoots h + 1) [] ⟨[], [], [], none⟩)) := by
  unfold obsPredAt
  iintro ⟨⟨%h', >Hfrag⟩, Hauth⟩
  ihave %he := ghost_var_agree γ h' _ h _ $$ Hfrag Hauth
  subst he
  imod ghost_var_update_halves (h' ++ [powerEv on]) γ h' h' $$ Hauth Hfrag with ⟨Hauth, Hfrag⟩
  imodintro
  imodintro
  isplitl [Hfrag]
  · inext; iexists _; iexact Hfrag
  iframe Hauth
  cases on
  · simp only [Bool.false_eq_true, ↓reduceIte]; iapply HC
  · simp only [↓reduceIte]; itrivial

/-- The ledger at a raw gname (Rocq `obs_ledger_at`); convertible with
`obsLedger R` at the literal (`bootFixedGS_obsLedger`). -/
def obsLedgerAt (R : List Obs → IProp GF) (γ : GName) : IProp GF :=
  iprop% ∃ h : List Obs, (γ ↪VAR{.own (1 : Qp).half} h) ∗ R h

theorem obsLedgerAt_alloc_cl (R : List Obs → IProp GF) (γ : GName) (P : IProp GF)
    (HR0 : P ⊢@{IProp GF} |==> R []) :
    P ∗ (γ ↪VAR{.own (1 : Qp).half} ([] : List Obs)) ⊢@{IProp GF} |==> obsLedgerAt R γ := by
  unfold obsLedgerAt
  iintro ⟨Hc, H⟩
  imod HR0 $$ Hc with HR
  imodintro
  iexists []
  iframe H HR

theorem obsLedgerAt_step (R : List Obs → IProp GF) [∀ h, Timeless (R h)]
    (C : Nat → List Obs → ConsHist → IProp GF)
    (Hpow : ∀ (h : List Obs) (on : Bool), traceShape h on →
      R h ⊢@{IProp GF} |==> (R (h ++ [powerEv on]) ∗
        (if on then iprop(emp) else C (obsBoots h + 1) [] ⟨[], [], [], none⟩)))
    (γ : GName) (h : List Obs) (on : Bool) (hs : traceShape h on) :
    ▷ obsLedgerAt R γ ∗ (γ ↪VAR{.own (1 : Qp).half} h) ⊢@{IProp GF}
      |==> ◇ (▷ obsLedgerAt R γ ∗ (γ ↪VAR{.own (1 : Qp).half} (h ++ [powerEv on])) ∗
        (if on then iprop(emp) else C (obsBoots h + 1) [] ⟨[], [], [], none⟩)) := by
  unfold obsLedgerAt
  iintro ⟨⟨%h', >Hfrag, >HR⟩, Hauth⟩
  ihave %he := ghost_var_agree γ h' _ h _ $$ Hfrag Hauth
  subst he
  imod ghost_var_update_halves (h' ++ [powerEv on]) γ h' h' $$ Hauth Hfrag with ⟨Hauth, Hfrag⟩
  imod Hpow h' on hs $$ HR with ⟨HR, Hfound⟩
  imodintro
  imodintro
  isplitl [Hfrag HR]
  · inext
    iexists _
    iframe Hfrag HR
  iframe Hauth Hfound

theorem obsLedgerAt_phi (R : List Obs → IProp GF) [∀ h, Timeless (R h)]
    (P : List Obs → Prop) (HR : ∀ h, R h ⊢@{IProp GF} ⌜P h⌝) (γ : GName) (h : List Obs) :
    (γ ↪VAR{.own (1 : Qp).half} h) ∗ ▷ obsLedgerAt R γ ⊢@{IProp GF} ◇ ⌜P h⌝ := by
  unfold obsLedgerAt
  iintro ⟨Hauth, ⟨%h', >Hfrag, >Hr⟩⟩
  ihave %he := ghost_var_agree γ h _ h' _ $$ Hauth Hfrag
  subst he
  ihave %hp := HR h $$ Hr
  imodintro
  ipureintro
  exact hp

/-- At the literal, the trivial trace predicate IS `obsPredAt`. -/
theorem bootFixedGS_obsPredTriv (Hinv : InvGS_gen hlc GF)
    (γgen γstart γreg γobs : GName) (T : List Obs) (γhist : GName)
    (Tg : List Obs → IProp GF) (HTg : ∀ h, Persistent (Tg h)) (HTgt : ∀ h, Timeless (Tg h))
    (Kc : IProp GF) (HKc : Persistent Kc) (HKct : Timeless Kc)
    (Cres : Nat → List Obs → ConsHist → IProp GF) (HCrest : ∀ k h H, Timeless (Cres k h H)) :
    @MachFixedGS.obsPred hlc GF (bootFixedGS Hinv γgen γstart γreg γobs T (obsPredAt γobs) γhist
        Tg HTg HTgt Kc HKc HKct Cres HCrest) =
      @obsPredTriv hlc GF (bootFixedGS Hinv γgen γstart γreg γobs T (obsPredAt γobs) γhist
        Tg HTg HTgt Kc HKc HKct Cres HCrest) := rfl

/-- ...and the ledger IS `obsLedger`. -/
theorem bootFixedGS_obsLedger (R : List Obs → IProp GF)
    (Hinv : InvGS_gen hlc GF)
    (γgen γstart γreg γobs : GName) (T : List Obs) (γhist : GName)
    (Tg : List Obs → IProp GF) (HTg : ∀ h, Persistent (Tg h)) (HTgt : ∀ h, Timeless (Tg h))
    (Kc : IProp GF) (HKc : Persistent Kc) (HKct : Timeless Kc)
    (Cres : Nat → List Obs → ConsHist → IProp GF) (HCrest : ∀ k h H, Timeless (Cres k h H)) :
    @MachFixedGS.obsPred hlc GF (bootFixedGS Hinv γgen γstart γreg γobs T (obsLedgerAt R γobs) γhist
        Tg HTg HTgt Kc HKc HKct Cres HCrest) =
      @obsLedger hlc GF (bootFixedGS Hinv γgen γstart γreg γobs T (obsLedgerAt R γobs) γhist
        Tg HTg HTgt Kc HKc HKct Cres HCrest) R := rfl

/-- THE PACKAGED TRACE THEOREM (Rocq `riscv_trace_adequacy` :2037):
`riscvPowerAdequacy` at the ledger, the trivial application (`CT := Unit`)
and the trivial slots; the client gets `P` of the run's observable trace. -/
theorem riscvTraceAdequacy [KernelMap] (g : GState)
    (Pc : GName → GName → GName → IProp GF)
    (HPc : ∀ (γsw γreg γst : GName),
      MonoNat.auth_own γsw (DFrac.own 1) (.ofNat 0) ⊢@{IProp GF} |==> Pc γsw γreg γst)
    (R : List Obs → IProp GF) [HRt : ∀ h, Timeless (R h)]
    (HR0 : ⊢@{IProp GF} |==> R [])
    (Hpow : ∀ (h : List Obs) (on : Bool), traceShape h on →
      R h ⊢@{IProp GF} |==> R (h ++ [powerEv on]))
    (P : List Obs → Prop) (HR : ∀ h, R h ⊢@{IProp GF} ⌜P h⌝)
    (Hgen0 : g.gen = 0) (Hpow0 : g.pow = false)
    (Hboot : ∀ [F : MachFixedGS hlc GF] (Hinv : InvGS_gen hlc GF)
        (γgen γstart γreg γobs γhist : GName) (T : List Obs),
      F = bootFixedGS Hinv γgen γstart γreg γobs T (obsLedgerAt R γobs) γhist
          rxTagTriv (fun _ => inferInstance) (fun _ => inferInstance)
          killCredTriv inferInstance inferInstance
          consResTriv (fun _ _ _ => inferInstance) →
      ∀ (E : EraGS GF) (gen : Nat) (σ : MState) (image : Mem), bootFacts σ image →
        obsInv ∗ powerBootRes E gen σ ⊢@{IProp GF} |={⊤}=>
          ([∗list] cpu ∈ cpus, hartWP gen cpu (pure ())) ∗
          ([∗list] d ∈ DevId.all, devWP gen d rootTask (pure ())))
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ P κs :=
  riscvPowerAdequacy (hlc := hlc) (GF := GF) g Unit (fun _ => iprop(True))
    (by imodintro; iexists (); itrivial)
    (fun γsw γreg γst _ => Pc γsw γreg γst) (fun γsw γreg γst _ => HPc γsw γreg γst)
    (fun γobs _ => obsLedgerAt R γobs)
    (fun _ => rxTagTriv) (fun _ _ => inferInstance) (fun _ _ => inferInstance)
    (fun _ => killCredTriv) (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => consResTriv) (fun _ _ _ _ => inferInstance)
    (fun γobs _ => obsLedgerAt_alloc_cl R γobs iprop(True) (by iintro _; iapply HR0))
    (fun γobs _ h on hs => obsLedgerAt_step R consResTriv
      (fun h on hs => by
        iintro Hr
        imod Hpow h on hs $$ Hr with Hr
        imodintro
        iframe Hr
        cases on
        · simp only [Bool.false_eq_true, ↓reduceIte, consResTriv]; itrivial
        · simp only [↓reduceIte]; itrivial)
      γobs h on hs)
    (fun _ h => P h)
    (fun _ _ _ _ _ γobs _ _ _ _ h => by
      iintro ⟨_, Hauth, _, _, HPt⟩
      iapply obsLedgerAt_phi R P HR γobs h $$ [Hauth HPt]
      iframe Hauth HPt)
    Hgen0 Hpow0
    (fun Hinv γgen γstart γreg γobs γhist _ T heq => Hboot Hinv γgen γstart γreg γobs γhist T heq)
    n κs t2 g2 hsteps

end raw

end MachCSL
