/-
Weak: **(c) [OWN.100], increment 5a — the SILENT agreement and the REALIZED member**
(`PROGRESS-W10N2p.md`).  Lean-only, no Rocq twin.

The twin of CertZ24's padded agreement, with NO padding: the realized member is the member of the
projection of a twin candidate (`CertZ3.member N (SilCand.proj c)`), whose slots are the graph's slots; at
a failed acquire it carries the READ of the silent AMO (`LLoad`), elsewhere a re-indexed copy of `GF`'s label.

  §1  `SilAgree.lblRelS`, `SilAgree.lblAgreeS`, **`SilAgree.agreeRPS`** and **`SilAgree.agreeW4OfRPS`**
      (the silent agreement gives CertZ24's `agreeW4`, which every CertZ24/25 consumer uses);
  §2  **`SilAgree.RunDataS`** (the twin run datum: valid twin candidate, twin program data from the boot
      states), `SilAgree.agBound` (agents are below `N`, from the program data), the realized member
      `SilAgree.memberS` / its log `SilAgree.logS`, and its facts **`SilAgree.memberFacts`** (gwf,
      gwrowGmo, logOf, rmwLatest — PROVED, no longer supplied);
  §3  **`SilAgree.runErasedS`** (`runErasedZ`'s twin at `RunDataS`).

Spec: FAITHFUL (proof organisation; the failed acquire is realized, silently).
-/
import Weak.SilReplay
import Weak.CertZ25

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open TsoShadow

/-! # 1. The silent agreement -/

/-- The per-slot relation of the realized member to `GF`: a re-index of a non-failed label, or, at a
failed acquire (an `LRmw`), the LOAD of its read (the silent AMO's projection). -/
def SilAgree.lblRelS (L : Int → Prop) (pi : Nat → Nat) (l l' : Lbl) : Prop :=
  (¬ CertZ24.lblFail L l ∧ lblReidxW (lblRen pi l) l') ∨
  (CertZ24.lblFail L l ∧ ∃ (aq rl : Bool) (base : Int) (ts ts' : List Nat) (rvs wvs : List (BitVec 8))
      (k : WmClass), l = .LRmw aq rl base ts rvs wvs k ∧ l' = .LLoad aq base ts' rvs ∧
      ts'.length = ts.length)

/-- **THE SILENT LABEL AGREEMENT.** -/
def SilAgree.lblAgreeS (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) : Prop :=
  ∀ e, (gxLbl G e = none ∧ gxLbl GR e = none) ∨
    ∃ l l', gxLbl G e = some l ∧ gxLbl GR e = some l' ∧ SilAgree.lblRelS L pi l l'

def SilAgree.agreeRPS (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) : Prop :=
  GR.gxImg = G.gxImg ∧ SilAgree.lblAgreeS G GR pi L ∧ CertZ18.lockCoSP G GR L

/-- The per-event facts of the silent agreement: CertZ24's `agreeW4`. -/
theorem SilAgree.agreeW4OfRPS (G GR : Gexec) (pi : Nat → Nat) (L : Int → Prop) :
    SilAgree.agreeRPS G GR pi L → CertZ24.agreeW4 G GR L := by
  rintro ⟨himg, hlbl, hco⟩
  have hwrR : ∀ e l', gxLbl GR e = some l' → lbIsW l' = true →
      ∃ l, gxLbl G e = some l ∧ ¬ CertZ24.lblFail L l ∧ lblReidxW (lblRen pi l) l' := by
    intro e l' hl' hW
    rcases hlbl e with ⟨-, h2⟩ | ⟨l, l'', h1, h2, hrel⟩
    · rw [h2] at hl'; cases hl'
    · rw [hl', Option.some.injEq] at h2
      subst h2
      rcases hrel with ⟨hnf, hre⟩ | ⟨-, _, _, _, _, _, _, _, _, -, rfl, -⟩
      · exact ⟨l, h1, hnf, hre⟩
      · simp [lbIsW] at hW
  have hnfG : ∀ e l, gxLbl G e = some l → CertZ24.nf G L e →
      ∃ l', gxLbl GR e = some l' ∧ lblReidxW (lblRen pi l) l' := by
    intro e l hl hnf
    rcases hlbl e with ⟨h1, -⟩ | ⟨l0, l', h1, h2, hrel⟩
    · rw [h1] at hl; cases hl
    · rw [hl, Option.some.injEq] at h1
      subst h1
      rcases hrel with ⟨-, hre⟩ | ⟨hf, -⟩
      · exact ⟨l', h2, hre⟩
      · exact absurd ((CertZ24.failIff G L e _ hl).1 hf) hnf
  refine ⟨himg, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, hco⟩
  · rintro e a v ⟨l', base, vs, j, hl', hwr, hv, ha⟩
    obtain ⟨l, hl, -, hre⟩ := hwrR e l' hl' (lbWrIsW _ _ hwr)
    refine ⟨l, base, vs, j, hl, ?_, hv, ha⟩
    rw [← lblRenWr pi l, ← CertZ22.wrEq _ _ hre, hwr]
  · rintro e a v ⟨l', base, vs, j, hl', hwr, -, -⟩
    obtain ⟨l, hl, hnf, -⟩ := hwrR e l' hl' (lbWrIsW _ _ hwr)
    exact fun hf => hnf ((CertZ24.failIff G L e l hl).2 hf)
  · rintro e a v hnf ⟨l, base, vs, j, hl, hwr, hv, ha⟩
    obtain ⟨l', hl', hre⟩ := hnfG e l hl hnf
    refine ⟨l', base, vs, j, hl', ?_, hv, ha⟩
    rw [CertZ22.wrEq _ _ hre, lblRenWr, hwr]
  · rintro e k hnf ⟨l0, hl0, hk⟩ ⟨l1, hl1, hW⟩
    rw [hl0, Option.some.injEq] at hl1
    subst hl1
    obtain ⟨l', hl', hre⟩ := hnfG e l0 hl0 hnf
    have hW' : lbIsW (lblRen pi l0) = true := by rw [lblRenIsW]; exact hW
    obtain ⟨-, hcl'⟩ := GraphFetchWalkZ.lblReidxWWr _ _ hre hW'
    exact ⟨l', hl', by rw [hcl', lblRenCls]; exact hk⟩
  · rintro e a t v hnf ⟨l1, hl1, hW⟩ ⟨l0, base, ts, vs, j, hl0, hrd, ht, hv, ha⟩
    rw [hl1, Option.some.injEq] at hl0
    subst hl0
    obtain ⟨l', hl', hre⟩ := hnfG e l1 hl1 hnf
    obtain ⟨ts', hrd', hlen⟩ := CertZ18.reidxRd _ _ base (ts.map pi) vs hre
      (by rw [lblRenIsW]; exact hW) (lblRenRd pi _ base ts vs hrd)
    have hj : j < ts'.length := by rw [hlen, List.length_map]; exact lookup_lt_Some ht
    exact ⟨ts'[j], l', base, ts', vs, j, hl', hrd', List.getElem?_eq_getElem hj, hv, ha⟩
  · rintro e a t v ⟨l1, hl1, hW⟩ ⟨l0, base, ts', vs, j, hl0, hrd, ht, hv, ha⟩
    rw [hl1, Option.some.injEq] at hl0
    subst hl0
    obtain ⟨l, hl, -, hre⟩ := hwrR e l1 hl1 hW
    have hWl : lbIsW (lblRen pi l) = true := by rw [← lblReidxWIsw _ _ hre]; exact hW
    obtain ⟨ts1, hrd1, hlen1⟩ := CertZ18.reidxRdInv _ _ base ts' vs hre hWl hrd
    obtain ⟨ts, hrd0, hlen0⟩ := CertZ18.renRdInv pi l base ts1 vs hrd1
    have hj : j < ts.length := by rw [← hlen0, ← hlen1]; exact lookup_lt_Some ht
    exact ⟨ts[j], l, base, ts, vs, j, hl, hrd0, List.getElem?_eq_getElem hj, hv, ha⟩

/-! # 2. The twin run datum and the realized member -/

/-- **THE TWIN RUN DATUM**: a valid twin candidate at `G`'s image, supplied by the twin program data
from the boot program states and fabric. -/
structure SilAgree.RunDataS (boot : Nat → Pexv6) (d0 : Efab) (N : Nat) (G : Gexec)
    (c : SilCand.CandS) (pst : Nat → List Pexv6) (dv : Nat → Efab) : Prop where
  rdValid : SilCand.validS c
  rdImg : c.img = G.gxImg
  rdPst0 : pst 0 = (List.range' 0 N).map boot
  rdDv0 : dv 0 = d0
  rdProg : SilReplay.progOk pstepEv pclsEv pst dv c

/-- The program data keep the number of agents. -/
theorem SilAgree.pstLen {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (pst : Nat → List P) (dv : Nat → D)
    (c : SilCand.CandS) (N : Nat) :
    SilReplay.progOk pstep pcls pst dv c → (pst 0).length = N →
    ∀ k, k ≤ c.tr.length → (pst k).length = N := by
  intro hpr h0 k
  induction k with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hk
    obtain ⟨s, hs⟩ : ∃ s, c.tr[k]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨_, _, _, _, _, _, hn, _⟩ := hpr k s hs
    rw [hn, List.length_set]
    exact ih (by omega)

/-- Every step's agent is below `N`. -/
theorem SilAgree.agBound {P D : Type} (pstep : P → D → Wlabel → P → D → Prop)
    (pcls : P → Wlabel → Wstate → WmClass) (pst : Nat → List P) (dv : Nat → D)
    (c : SilCand.CandS) (N : Nat) :
    SilReplay.progOk pstep pcls pst dv c → (pst 0).length = N →
    ∀ s, s ∈ c.tr → s.esAg < N := by
  intro hpr h0 s hs
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hs
  have hkl : k < c.tr.length := lookup_lt_Some hk
  obtain ⟨_, _, _, _, _, hp, _⟩ := hpr k s hk
  have := lookup_lt_Some hp
  rw [SilAgree.pstLen pstep pcls pst dv c N hpr h0 k (by omega)] at this
  exact this

/-- **THE REALIZED MEMBER** of a twin candidate over `N` agents, and its log. -/
def SilAgree.memberS (N : Nat) (c : SilCand.CandS) : Gexec := CertZ3.member N (SilCand.proj c)

def SilAgree.logS (c : SilCand.CandS) : List Wmsg :=
  cdLog (SilCand.proj c) (SilCand.proj c).cdTr.length

theorem SilAgree.runAg {boot : Nat → Pexv6} {d0 : Efab} {N : Nat} {G : Gexec} {c : SilCand.CandS}
    {pst : Nat → List Pexv6} {dv : Nat → Efab} (h : SilAgree.RunDataS boot d0 N G c pst dv) :
    ∀ s, s ∈ c.tr → s.esAg < N :=
  SilAgree.agBound pstepEv pclsEv pst dv c N h.rdProg (by rw [h.rdPst0]; simp)

/-- **THE REALIZED MEMBER'S FACTS** (proved from the run datum). -/
theorem SilAgree.memberFacts {boot : Nat → Pexv6} {d0 : Efab} {N : Nat} {G : Gexec}
    {c : SilCand.CandS} {pst : Nat → List Pexv6} {dv : Nat → Efab}
    (h : SilAgree.RunDataS boot d0 N G c pst dv) :
    gwf (SilAgree.memberS N c) ∧ gwrowGmo (SilAgree.memberS N c) ∧
    logOf (SilAgree.memberS N c) (SilAgree.logS c) ∧
    CertZ18.rmwLatest (SilAgree.memberS N c) (SilAgree.logS c) ∧
    (SilAgree.memberS N c).gxImg = G.gxImg :=
  ⟨SilMember.twinGwf N c h.rdValid (SilAgree.runAg h),
   SilMember.twinGwrowGmo N c (SilAgree.runAg h),
   SilMember.twinLogOf N c (SilAgree.runAg h),
   SilMember.twinRmwLatest N c h.rdValid (SilAgree.runAg h),
   h.rdImg⟩

/-! # 3. The twin erased run at a run datum -/

section run

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode
open Language.Notation PrimStep
open LeanRV64D

/-- **`runErasedS`** (`runErasedZ`'s twin): a twin run datum at the booted state is an erased run of the
TWIN thread pool ending at the realized member's log. -/
theorem SilAgree.runErasedS (gen : Nat) (σ0 : WGState) (boot : Nat → Pexv6) (d0 : Efab) (N : Nat)
    (G : Gexec) (c : SilCand.CandS) (pst : Nat → List Pexv6) (dv : Nat → Efab) :
    freshEra gen σ0 →
    (∀ ρ, rtc SilEpf.epfRunS (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2) →
    (List.range' 0 N).map boot = epsInit σ0 →
    d0 = efInit σ0.wgdev →
    G.gxImg = imgZ σ0.wgimg →
    SilAgree.RunDataS boot d0 N G c pst dv →
    ∃ (t2 : List SilLang.EExprS) (σ2 : WGState),
      (SilLang.epowerForkS gen, σ0) -·->ₜₚ* (t2, σ2) ∧ σ2.wglog = SilAgree.logS c := by
  intro hfr hcov hb1 hb2 hb3 h
  have hlen : c.tr.length = (SilCand.proj c).cdTr.length := (SilCand.projLen c).symm
  obtain ⟨t2, σ2, hr, hl⟩ := SilReplay.runErased gen σ0 c pst dv hfr hcov (h.rdImg.trans hb3)
    (h.rdPst0.trans hb1) (h.rdDv0.trans hb2) h.rdValid h.rdProg
  refine ⟨t2, σ2, hr, ?_⟩
  rw [hl, SilAgree.logS, hlen]

end run

end Weak
