/-
Weak: **the one-hart `wpd` for the whole J0 program `c.sdsp ; c.ldsp`**, by chaining the green
per-instruction lemmas (`wpdCsdspConcrete'`, the `.pure ()` junction, `wpdCldspAfterSd`, and
the past-the-row-end tail).

Rocq: `iris/AxEpiChainSdLd.v` @ xxvzwolszwmp.

## The Rocq header, in substance

Row (Lean, Stage C): `[sd @kk; ld @kk + 1]`, and the row ends EXACTLY at `kk + 2` (`Hlen`).

* §1 `wpdOfClosedRunG`: `AxWpdLift.wpdOfClosedRun` (`MaybeStuck`) whose closure premises may use
  a per-`GD` fact `G GD` read off `gconstInterp GD` (the row length) and the step's boot-image
  pin (Q12), and whose row-end obligation is owed only under `G GD` (model-generic
  `wpdOfClosedRunGM`).
* §2 THE `.pure ()` JUNCTION `wpdRetBoundary`: from any state `aeqv` to `.pure ()` at registers
  `rs` (position `k`, not the row end), the only program step is the boundary `LInstr` tick to
  `riscvStep tick` with the same registers, `ibNone`, same `k` (`RetNext`); the wire stays in
  the `aeqv` class.  No row-end obligation (`k ≠ kend`).
* §3 PAST THE ROW END `wpdPastRowEnd`: from a set `E` at position `k0 ≥ length row`, every step
  is administrative and position-keeping; the row-end obligation is owed only on `pastEnd E`
  (the `k`-keeping closure of `E`).
* §4 `wpdEpiSdLd`.

## Deviations from Rocq

1. O2 STAGE C (`AxEpiLedgerSd` deviation 3, `AxEpiLedgerTick` deviation 3): the fetches are
   pinned admin steps with no row item.  The row is `[sd @kk; ld @kk + 1]`, so `Hlen` is
   `length = kk + 2` (Rocq `kk + 4`); the junction sits at `kk + 1` (Rocq `S (S kk)`), the load's
   `Hgd_ld`/`Hrow_ld`/flow at `kk + 1` (Rocq fetch `S (S kk)`, load `S (S (S kk))`), `RetLd` and
   `pastEnd` at `kk + 2` (Rocq `S (S (S (S kk)))`); the store's `Hrow_sd` and flow at `kk` (Rocq
   `S kk`).  `Hgd_sd`/`Hgd_ld` state `AxCjrWpd.fetchImgOk` (Rocq `fetch_gd_ok`) at the
   instruction's data position; `Hflow_sd`, `Hloc_sd`, `Hflow_ld`, `Hloc_ld` and `Hntext` are
   DROPPED (the callees no longer take them).  `astep_prog` has three constructors (no fetch
   arm) and no `T`/`img` parameters: `astepProgRetShape`,
   `AxEpiChainSdLd.astepProgRowEndShape'` and `kstep` drop them (`kstep`'s program arm is
   `∃ row l, AxOpsem.astepProg row s1 l s2`).
2. THE TWO-PIN BOUNDARY (`AxEpiLedger` deviation 1): the store's exit is indexed by the two
   boundary answers `v' v` (`wpdCsdspConcrete'`), so `epiSdLdInv`'s load disjunct is
   `∃ tick v' v, ldAfterSdInv tick v' v cpu (kk + 1) s1` (Rocq `∃ tick v`).
3. THE PINS (`AxRunClose` deviation 1): `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`
   (`RetNext`, `retxShape`).
4. TYPES / SHAPES: `Interface.Ret tt` ↦ `.pure ()`, `ib_none` ↦ `ibNone`, `S k` ↦ `k + 1`,
   `lookup_ge_None` ↦ `List.getElem?_eq_none`; `WPd s @ MaybeStuck; i {{ Φ }}` ↦
   `wpd .MaybeStuck i s Φ` (`wpdM M .MaybeStuck i s Φ` in §1); `A -∗ B` ↦ `⊢ A -∗ B`;
   `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]`.  `wpd_of_closed_run_g` (a Rocq `Definition`
   alias) is a theorem.  Rocq's `section chainM` notations are not needed (`wpdM M` is explicit).

5. Q12 (owner, THE FETCH PIN): `wpdOfClosedRunGM` / `wpdOfClosedRunG`'s closure premise `Hclos`
   takes the program step's boot-image pin `WeakAxRealize.fetchPin GD.gdG.gxImg l` (as the WPd
   step clause supplies it, Q8; Rocq: none — its fetches were row reads), so an administrative
   fetch step need only be closed when it returns image bytes (`AxSpinRow.wpdMStuck`).  The
   in-file closures (`wpdRetBoundary`, `wpdPastRowEnd`) ignore it.

**Rocq → Lean name map.**  `ret_pstep_inv` `retPstepInv`, `astep_prog_ret_shape`
`astepProgRetShape`, `astep_prog_row_end_shape'` `AxEpiChainSdLd.astepProgRowEndShape'`
(duplicated name), `RetNext` `RetNext`, `retx_shape` `retxShape`, `kstep` `kstep`, `past_end`
`pastEnd`, `kstep_rtc_k` `kstepRtcK`, `past_end_k` `pastEndK`, `epi_sd_ld_inv` `epiSdLdInv`,
`wpd_of_closed_run_gM` `wpdOfClosedRunGM`, `wpd_of_closed_run_g` `wpdOfClosedRunG`,
`wpd_ret_boundary` `wpdRetBoundary`, `wpd_past_row_end` `wpdPastRowEnd`, `wpd_epi_sd_ld`
`wpdEpiSdLd`.

**Dropped:** nothing (Rocq 15 definitions/lemmas; Lean 15).  **Not ported:** the
`Print Assumptions` block (the lint's axiom check covers it).
-/
import Weak.AxEpiLedgerTick2
import Weak.AxWpdLift

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-! # 0. Pure step facts -/

/-- The boundary `.pure ()` node's only program step. -/
theorem retPstepInv (c : CPU) (rs : RegFile) (ib : Ibch) (d : Efab) (l : Wlabel) (p' : Pexv6)
    (d' : Efab) :
    pstepProg (.PHart c (.pure ()) rs none ib) d l p' d' →
    l = .LInstr ∧ ∃ tick : Bool, p' = .PHart c (riscvStep tick) rs none ibNone := by
  cases p' with
  | PHart c' m' rs' fn' ib' =>
    rintro ⟨rfl, ors, oib, obar, rfl, rfl, Hn, -⟩
    dsimp only [pstepNode, pnodeStep] at Hn
    obtain ⟨tick, rfl, rfl, rfl, rfl, -, rfl, -⟩ := Hn
    exact ⟨rfl, tick, rfl⟩
  | PDisk _ => intro h; exact h.elim

theorem astepProgRetShape (row : List Lbl) (c : CPU) (rs : RegFile) (ib : Ibch) (k : Nat)
    (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row ⟨.PHart c (.pure ()) rs none ib, k⟩ l s' →
    ∃ tick : Bool, s' = ⟨.PHart c (riscvStep tick) rs none ibNone, k⟩ := by
  intro h
  cases h with
  | AStepAdmin _ _ d _ p' d' _ hps =>
    obtain ⟨-, tick, rfl⟩ := retPstepInv c rs ib d l p' d' hps
    exact ⟨tick, rfl⟩
  | AStepWrite _ _ d _ _ p' d' _ hwr _ _ hps =>
    obtain ⟨rfl, -⟩ := retPstepInv c rs ib d l p' d' hps
    simp [wlWr] at hwr
  | AStepFence _ _ d _ _ p' d' _ hf _ hps =>
    obtain ⟨rfl, -⟩ := retPstepInv c rs ib d l p' d' hps
    simp [wlFence] at hf

/-- Local copy of the row-end shape lemma (Rocq's copy of `AxLock3Writer`'s; duplicated name):
past the row end, every program step is administrative and keeps the position. -/
theorem AxEpiChainSdLd.astepProgRowEndShape' (row : List Lbl) (s : Athread) (l : Wlabel)
    (s' : Athread) (Hnone : row[s.atK]? = none) :
    AxOpsem.astepProg row s l s' → AxOpsem.lbAdminAx true l ∧ s'.atK = s.atK := by
  intro h
  cases h with
  | AStepAdmin p k d l p' d' hadm _ => exact ⟨hadm, rfl⟩
  | AStepWrite p k d l lb p' d' hlk _ _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone
  | AStepFence p k d l lb p' d' hlk _ _ _ =>
    simp only at Hnone
    rw [hlk] at Hnone
    cases Hnone

/-- The exit of the `.pure ()` junction: the tick, same registers (up to the pins), `ibNone`,
same position. -/
def RetNext (cpu : CPU) (rs : RegFile) (k : Nat) (s : Athread) : Prop :=
  ∃ (tick : Bool) (rs' : RegFile), regsAgree AxRunClose.pinReg rs rs' ∧
    s = ⟨.PHart cpu (riscvStep tick) rs' none ibNone, k⟩

theorem retxShape (cpu : CPU) (rs : RegFile) (k : Nat) (s : Athread) :
    RetX cpu rs k s →
    ∃ (rs1 : RegFile) (ib1 : Ibch), s = ⟨.PHart cpu (.pure ()) rs1 none ib1, k⟩ ∧
      regsAgree AxRunClose.pinReg rs1 rs := by
  rcases s with ⟨p, k1⟩
  rintro ⟨ib', Hk, Hp⟩
  cases p with
  | PHart c m rs1 fn ib1 =>
    obtain rfl : k1 = k := Hk
    obtain ⟨rfl, rfl, rfl, rfl, Hag⟩ := Hp
    exact ⟨rs1, ib1, rfl, Hag⟩
  | PDisk _ => exact Hp.elim

/-- The `k`-keeping closure step (any row, or the wire). -/
def kstep (s1 s2 : Athread) : Prop :=
  s2.atK = s1.atK ∧ ((∃ row l, AxOpsem.astepProg row s1 l s2) ∨ awire s1 s2)

def pastEnd (E : Athread → Prop) (s : Athread) : Prop :=
  ∃ s0, E s0 ∧ rtc kstep s0 s

theorem kstepRtcK (s0 s : Athread) : rtc kstep s0 s → s.atK = s0.atK := by
  intro h
  induction h with
  | refl => rfl
  | tail _ hst ih => exact hst.1.trans ih

theorem pastEndK (E : Athread → Prop) (k0 : Nat) (HE : ∀ s0, E s0 → s0.atK = k0) (s : Athread) :
    pastEnd E s → s.atK = k0 := by
  rintro ⟨s0, H0, Hr⟩
  rw [kstepRtcK _ _ Hr]
  exact HE s0 H0

/-- The union of the reachable row-end sets of the two-instruction program. -/
noncomputable def epiSdLdInv (cpu : CPU) (kk : Nat) (s1 : Athread) : Prop :=
  ledgerSdInv (tAt pcSd) AxEpiProbe.drNopin DwAll DPost sdVs cpu kk s1 ∨
  (∃ (tick : Bool) (v' v : BitVec 1), ldAfterSdInv tick v' v cpu (kk + 1) s1) ∨
  pastEnd (RetLd cpu ldPost (kk + 2)) s1

/-! # 1. The closed-run lift with a per-`GD` fact -/

section chainM
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdOfClosedRunGM (M : Gdexec → Prop) (i : Agent) (G : Gdexec → Prop)
    (P Q : Athread → Prop) (Φ : Athread → IProp GF)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Hnord : ∀ GD s1 id K, G GD → P s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K)
    (Hclos : ∀ GD s1 l s2, G GD → P s1 → AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
       WeakAxRealize.fetchPin GD.gdG.gxImg l →
       wlWdata l = none ∧ s2.atK = s1.atK ∧ (P s2 ∨ Q s2))
    (Hwire : ∀ s1 s2, P s1 → awire s1 s2 → P s2 ∨ Q s2) :
    ⊢ ∀ s, ⌜P s⌝ -∗
      ((∀ s2, ⌜Q s2⌝ -∗ wpdM M .MaybeStuck i s2 Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜G GD⌝ -∗ ⌜P s1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i s1)) -∗
      wpdM M .MaybeStuck i s Φ := by
  iloeb as IH
  iintro %s %HP R
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i s Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i s).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  isplit
  · iintro %id %K %Hst
    exact (Hnord GD s id K HGD HP Hst).elim
  isplit
  · iintro %l %s' %Hst %Hfp
    obtain ⟨Hw, Hk, HPQ⟩ := Hclos GD s l s' HGD HP Hst Hfp
    simp only [Hw]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    rw [Hk]
    iframe Hna Hloc
    cases HPQ with
    | inl HP' => iapply IH $$ %s' %HP' R
    | inr HQ' =>
      icases R with ⟨R, -⟩
      iapply R $$ %s' %HQ'
  isplit
  · iintro %s' %Hst
    have HPQ := Hwire s s' HP Hst
    have Hk : s'.atK = s.atK := Hst.1
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    rw [Hk]
    iframe Hna Hloc
    cases HPQ with
    | inl HP' => iapply IH $$ %s' %HP' R
    | inr HQ' =>
      icases R with ⟨R, -⟩
      iapply R $$ %s' %HQ'
  · iintro %Heq
    icases R with ⟨-, R⟩
    iapply R $$ %GD %s %HGD %HP %Heq

end chainM

section chain
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdOfClosedRunG (i : Agent) (G : Gdexec → Prop) (P Q : Athread → Prop)
    (Φ : Athread → IProp GF)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Hnord : ∀ GD s1 id K, G GD → P s1 → ¬ areadStep (AxOpsem.grow GD i) s1 id K)
    (Hclos : ∀ GD s1 l s2, G GD → P s1 → AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 →
       WeakAxRealize.fetchPin GD.gdG.gxImg l →
       wlWdata l = none ∧ s2.atK = s1.atK ∧ (P s2 ∨ Q s2))
    (Hwire : ∀ s1 s2, P s1 → awire s1 s2 → P s2 ∨ Q s2) :
    ⊢ ∀ s, ⌜P s⌝ -∗
      ((∀ s2, ⌜Q s2⌝ -∗ wpd .MaybeStuck i s2 Φ) ∧
       (∀ (GD : Gdexec) s1, ⌜G GD⌝ -∗ ⌜P s1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
          postLifting Φ i s1)) -∗
      wpd .MaybeStuck i s Φ :=
  wpdOfClosedRunGM rvwmoCatConsistent i G P Q Φ HG Hnord Hclos Hwire

/-! # 2. THE `.pure ()` JUNCTION -/

theorem wpdRetBoundary (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (rs : RegFile)
    (k kend : Nat) (s : Athread) (Hs : RetX cpu rs k s)
    (Hlen : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length = kend⌝)
    (Hne : k ≠ kend) :
    ⊢ (∀ s2, ⌜RetNext cpu rs k s2⌝ -∗ wpd .MaybeStuck i s2 Φ) -∗
      wpd .MaybeStuck i s Φ := by
  have Hnord : ∀ GD s1 id K, (AxOpsem.grow GD i).length = kend → RetX cpu rs k s1 →
      ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    rintro GD s1 id K - HP ⟨lb, -, -, Hrd, HK⟩
    obtain ⟨rs1, ib1, rfl, -⟩ := retxShape cpu rs k s1 HP
    obtain ⟨l, d, d', Hl, -, Hps, -⟩ := HK (List.replicate (aidentN id) 0) List.length_replicate
    obtain ⟨rfl, -⟩ := retPstepInv _ _ _ _ _ _ _ Hps
    rw [← Hl] at Hrd
    simp [wlRd] at Hrd
  have Hclos : ∀ GD s1 l s2, (AxOpsem.grow GD i).length = kend → RetX cpu rs k s1 →
      AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 → WeakAxRealize.fetchPin GD.gdG.gxImg l →
      wlWdata l = none ∧ s2.atK = s1.atK ∧ (RetX cpu rs k s2 ∨ RetNext cpu rs k s2) := by
    rintro GD s1 l s2 - HP Hst -
    obtain ⟨rs1, ib1, rfl, Hag⟩ := retxShape cpu rs k s1 HP
    obtain ⟨d, d', Hps⟩ := astepProgPstep _ _ _ _ Hst
    obtain ⟨tick, rfl⟩ := astepProgRetShape _ cpu rs1 ib1 k l s2 Hst
    obtain ⟨rfl, -⟩ := retPstepInv _ _ _ _ _ _ _ Hps
    exact ⟨rfl, rfl, .inr ⟨tick, rs1, regsAgreeSym _ _ _ Hag, rfl⟩⟩
  have Hwire : ∀ s1 s2, RetX cpu rs k s1 → awire s1 s2 →
      RetX cpu rs k s2 ∨ RetNext cpu rs k s2 := by
    rintro s1 s2 ⟨ib', Hq⟩ Hw
    exact .inl ⟨ib', aeqvTrans _ _ _ (awireAeqv _ _ Hw) Hq⟩
  iintro Hcont
  iapply (wpdOfClosedRunG i (fun GD => (AxOpsem.grow GD i).length = kend) (RetX cpu rs k)
    (RetNext cpu rs k) Φ Hlen Hnord Hclos Hwire) $$ %s %Hs
  isplit
  · iexact Hcont
  · iintro %GD %s1 %HGD %HP %Heq
    obtain ⟨rs1, ib1, rfl, -⟩ := retxShape cpu rs k s1 HP
    exact absurd (Heq.trans HGD) Hne

/-! # 3. PAST THE ROW END -/

theorem wpdPastRowEnd (i : Agent) (Φ : Athread → IProp GF) (E : Athread → Prop) (k0 : Nat)
    (s : Athread) (Hs : E s) (HE : ∀ s0, E s0 → s0.atK = k0)
    (Hlen : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length ≤ k0⌝) :
    ⊢ (∀ (GD : Gdexec) s1, ⌜pastEnd E s1⌝ -∗ ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗
        postLifting Φ i s1) -∗
      wpd .MaybeStuck i s Φ := by
  have Hnord : ∀ GD s1 id K, (AxOpsem.grow GD i).length ≤ k0 → pastEnd E s1 →
      ¬ areadStep (AxOpsem.grow GD i) s1 id K := by
    rintro GD s1 id K Hle HP ⟨lb, Hlk, -⟩
    rw [pastEndK E k0 HE s1 HP, List.getElem?_eq_none Hle] at Hlk
    cases Hlk
  have Hclos : ∀ GD s1 l s2, (AxOpsem.grow GD i).length ≤ k0 → pastEnd E s1 →
      AxOpsem.astepProg (AxOpsem.grow GD i) s1 l s2 → WeakAxRealize.fetchPin GD.gdG.gxImg l →
      wlWdata l = none ∧ s2.atK = s1.atK ∧ (pastEnd E s2 ∨ (fun _ => False) s2) := by
    rintro GD s1 l s2 Hle HP Hst -
    have Hnone : (AxOpsem.grow GD i)[s1.atK]? = none := by
      rw [pastEndK E k0 HE s1 HP]
      exact List.getElem?_eq_none Hle
    obtain ⟨Hadm, Hk⟩ := AxEpiChainSdLd.astepProgRowEndShape' _ s1 l s2 Hnone Hst
    refine ⟨AxRunClose.lbAdminWdata _ Hadm, Hk, .inl ?_⟩
    obtain ⟨s0, H0, Hr⟩ := HP
    exact ⟨s0, H0, rtc_r Hr ⟨Hk, .inl ⟨_, _, Hst⟩⟩⟩
  have Hwire : ∀ s1 s2, pastEnd E s1 → awire s1 s2 → pastEnd E s2 ∨ (fun _ => False) s2 := by
    rintro s1 s2 ⟨s0, H0, Hr⟩ Hw
    exact .inl ⟨s0, H0, rtc_r Hr ⟨Hw.1, .inr Hw⟩⟩
  iintro R
  iapply (wpdOfClosedRunG i (fun GD => (AxOpsem.grow GD i).length ≤ k0) (pastEnd E)
    (fun _ => False) Φ Hlen Hnord Hclos Hwire) $$ %s %⟨s, Hs, rtc_refl _⟩
  isplit
  · iintro %s2 %H
    exact H.elim
  · iintro %GD %s1 %_ %HP %Heq
    iapply R $$ %GD %s1 %HP %Heq

/-! # 4. THE WHOLE PROGRAM c.sdsp ; c.ldsp -/

theorem wpdEpiSdLd (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU) (ib : Ibch) (kk : Nat)
    (Rv : Gdexec → List (BitVec 8) → IProp GF)
    -- c.sdsp: the store at `kk`
    (Hgd_sd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜AxCjrWpd.fetchImgOk GD i kk (pcSd : Int) sdVs⌝)
    (Hrow_sd : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜storeRowOk GD i kk⌝)
    -- c.ldsp: the load at `kk + 1`
    (Hgd_ld : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜AxCjrWpd.fetchImgOk GD i (kk + 1) (pcLd : Int) AxEpiLedger.ldVs⌝)
    (Hrow_ld : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜loadRowOk GD i (kk + 1)⌝)
    -- the row is EXACTLY these two events
    (Hlen : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length = kk + 2⌝) :
    ⊢ (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i kk ls -∗
         storeFlow GD i kk sdData) -∗
      (∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (w : List (BitVec 8)),
         ⌜rvwmoCatConsistent GD⌝ -∗ □ AxirisG.gconstInterp GD -∗
         AxirisG.localInterp GD i (kk + 1) ls -∗
         ⌜graphValue GD (i, kk + 1) = some w⌝ -∗ loadFlow GD i (kk + 1) (Rv GD w)) -∗
      (∀ (GD : Gdexec) s1, ⌜epiSdLdInv cpu kk s1⌝ -∗
         ⌜s1.atK = (AxOpsem.grow GD i).length⌝ -∗ postLifting Φ i s1) -∗
      wpd .MaybeStuck i ⟨.PHart cpu (riscvStep false) (probeRegs pcSd) none ib, kk⟩ Φ := by
  have HlenLe : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length ≤ kk + 2⌝ := by
    intro GD Hc
    refine (Hlen GD Hc).trans ?_
    iintro %h
    ipureintro
    omega
  have HE : ∀ s0, RetLd cpu ldPost (kk + 2) s0 → s0.atK = kk + 2 := by
    rintro s0 ⟨x, rs3, ib', -, Hk, -⟩
    exact Hk
  iintro Fs Fl R
  iapply (wpdCsdspConcrete' i Φ cpu ib kk Hgd_sd Hrow_sd) $$ Fs
  isplit
  · iintro %v' %v %s' %Hs'
    iapply (wpdRetBoundary i Φ cpu _ (kk + 1) (kk + 2) s' Hs' Hlen (by omega))
    iintro %s2 %Hs2
    obtain ⟨tick, rs', Hag, rfl⟩ := Hs2
    iapply (wpdCldspAfterSd i Φ cpu ibNone (kk + 1) v' v Rv Hgd_ld Hrow_ld tick rs' Hag) $$ Fl
    isplit
    · iintro %s3 %Hs3
      iapply (wpdPastRowEnd i Φ (RetLd cpu ldPost (kk + 2)) (kk + 2) s3 Hs3 HE HlenLe)
      iintro %GD %s1 %Hp %Heq
      iapply R $$ %GD %s1 %(Or.inr (Or.inr Hp)) %Heq
    · iintro %GD %s1 %Hs1 %Heq
      iapply R $$ %GD %s1 %(Or.inr (Or.inl ⟨tick, v', v, Hs1⟩)) %Heq
  · iintro %GD %s1 %Hs1 %Heq
    iapply R $$ %GD %s1 %(Or.inl Hs1) %Heq

end chain

end Weak
