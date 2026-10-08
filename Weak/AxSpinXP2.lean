/-
Weak: **`AxSpinXP`'s positional X leaf and load leaf over the WINDOW-RESTRICTED flow resource**
(`AxCertP3.FldMW`).

Rocq: `iris/AxSpinXP2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`XBkW` is `AxSpinXP.XBkP` over `AxCertP3.wpdInstrOfCertW`: the pending data resource is
`CResW … k hi` — for a load, a flow only at the row positions of the instruction's window.
`XxLdW` is `AxSpinXP.XxLdP` consuming `FldMW … k hi` instead of the position-generic `FldM`: a
client needs to supply the load's flow only inside the load's window — so a row containing an
RMW on the same bytes elsewhere (acquire's `amoswap.w.aq lk`) no longer blocks building the flow
resource.  Proofs are AxSpinXP's with the resource swapped.

## Deviations from Rocq

1. O2 STAGE C COUNT SHIFT (as `AxSpinXP` deviation 1): the instruction's fetch consumes NO row
   item, so an instruction consumes exactly `e` items (Rocq `e + 1`).
   * `XBkW`: the window premises `HnoRmwX` / `HnoSplitX` range over `k ≤ k' ∧ k' < k + e`
     (Rocq `k ≤ k' < k + e + 1`); the resource window is `CResW … k (k + e)` (Rocq
     `k (k + e + 1)`); the continuation is at `k + e` (Rocq `k + e + 1`); the arithmetic
     premise `k + e + 1 ≤ L` becomes `k < L` and `k + e ≤ L` (as `AxSpinXP.XBkP`).  The
     bridge's `Hhi` (`length ≤ hi + c`, with `hi = k + e`, `c = L - (k + e)`) is discharged
     from `HL` and `k + e ≤ L`.
   * `XxLdW` (`e = 1`): the load's data event is EXACTLY at `k` (Rocq `k + 1`), so the flow
     resource is `FldMW … k (k + 1)` (Rocq `k (k + 2)`: the fetch slot `k` and the data slot
     `k + 1`), `Hnormw1` is stated at position `k` (Rocq `S k`), and the conclusion is
     `AxSpinXP.XLdP … k … (Out k)` (Rocq `XLdP … (Out (S k))`).  Rocq's fetch premise `Hnrk`
     is DROPPED (as in `AxSpinXP.XxLdP`): row item `k` IS the load's own data read, so the
     premise would be unsatisfiable; its two Rocq uses are discharged by arithmetic.
   * Rocq's section premise `Hntext` of `XBkW` is DROPPED (`AxCertP3` deviation 1).  `XxLdW`
     keeps the premise `¬ L.xlText (paZ pa)` for caller compatibility; it is unused.
2. TYPES as `AxSpinXP` deviation 2: `[InvGS_gen hlc GF]` (any `hlc`), `[AxSpinX.Xv6G GF]`; the
   local instances `xp_pol` / `xp_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`,
   passed with `@`.  `Z` widths ↦ `Nat`, `uint pa` ↦ `paZ pa`, `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`.
   Section variables are explicit arguments: `XBkW` takes the `xBkW` section's
   `σi T satp0 hmode hasid hppn i cpu G HG L HL HGex Φ Hmid Htext Hflow Hloc dok kind Out`;
   `FldMWRowW` takes `L GT nm i pa n Out lo hi`; `XxLdW` takes
   `L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid` first.
3. The trailing `Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `XBkW` `XBkW`, `FldMW_rowW` `FldMWRowW`, `Xx_ldW` `XxLdW`.  None is
in the duplicated-name table; no Lean-only helpers.

**Dropped:** nothing (Rocq 3 lemmas + the 2 local instances `xp_pol` / `xp_G`, inlined; Lean 3).
-/
import Weak.AxSpinXP
import Weak.AxCertP3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! # 1. The POSITIONAL X LEAF, window premises -/

section xBkW
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
variable (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
variable (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (G : Gdexec → Prop)
variable (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (L : Nat) (HL : ∀ GD, G GD → (AxOpsem.grow GD i).length = L) (HGex : ∃ GD, G GD)
variable (Φ : Athread → IProp GF)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (dok : Int → Nat → Prop) (kind : Dkind)
variable (Out : Nat → List (BitVec 8) → IProp GF)

include hmode hasid hppn HG HL HGex Hmid Htext Hflow Hloc in
/-- Rocq `XBkW`: `AxSpinXP.XBkP` over the window-restricted resource `CResW … k (k + e)`
(deviation 1; Rocq `k (k + e + 1)`). -/
theorem XBkW (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (e : Nat) (ot : Option (BitVec 64))
    (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop)
    (HnoRmwX : kind = .DKLd → ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat), k ≤ k' ∧ k' < k + e →
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)
    (HnoSplitX : kind = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat), k ≤ k' ∧ k' < k + e →
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)
    (HPXr : ∀ d r, PX d r → ∀ aq vs, d ≠ .CRmwR aq vs) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc ins → (∀ d r, PX d r → owOk (ow d)) →
    CertB σi T satp0 dok kind rs pc is_rvc ins e ot ow d0 r0 PX →
    k < L → k + e ≤ L →
    ⊢ CResW dok kind i Out k (k + e) d0 k -∗
      (∀ d r rs' ib', ⌜PX d r⌝ -∗ ⌜GoodB T satp0 rs pc is_rvc ot (ow d) rs'⌝ -∗
          CResW dok kind i Out k (k + e) d (k + e) -∗
          wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k + e⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  intro HRet Hc HPC Hhit Htx How Hcert Hk Hle
  have HnoRmwW : kind = .DKLd → ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat), k ≤ k' →
        k' + (L - (k + e)) < (AxOpsem.grow GD i).length →
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝ := by
    intro Hkd GD Hc'
    refine (BI.and_intro (HG GD Hc') (HnoRmwX Hkd GD Hc')).trans ?_
    iintro ⟨%HGD, %Hw⟩
    ipureintro
    intro k' lb aq rl base n H1 H2 Hlb Hid
    rw [HL GD HGD] at H2
    exact Hw k' lb aq rl base n ⟨H1, by omega⟩ Hlb Hid
  have HnoSplitW : kind = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat), k ≤ k' →
        k' + (L - (k + e)) < (AxOpsem.grow GD i).length →
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝ := by
    intro Hkd GD Hc'
    refine (BI.and_intro (HG GD Hc') (HnoSplitX Hkd GD Hc')).trans ?_
    iintro ⟨%HGD, %Hw⟩
    ipureintro
    intro k' lb aq base n H1 H2 Hlb Hid
    rw [HL GD HGD] at H2
    exact Hw k' lb aq base n ⟨H1, by omega⟩ Hlb Hid
  have Hhi : ∀ GD, G GD → (AxOpsem.grow GD i).length ≤ (k + e) + (L - (k + e)) := by
    intro GD HGD
    rw [HL GD HGD]
    omega
  have Hbp : AxCert2.bpos G i k (Cst.csB ⟨d0, .BFin (e + (L - (k + e))), r0⟩) := by
    intro GD HGD
    rw [HL GD HGD]
    omega
  have Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1 := by
    intro GD s1 HGD HR1 Hat
    exfalso
    obtain ⟨_, _, rfl, -⟩ := retxShape _ _ _ _ HR1
    rw [HL GD HGD] at Hat
    dsimp only at Hat
    omega
  have HPF : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      PF (imgS σi) dok kind (L - (k + e)) ⟨d0, .BFin (e + (L - (k + e))), r0⟩
        (riscvStep tick) t := by
    intro tick t Hag _
    refine ⟨e + (L - (k + e)), rfl, fun j => ⟨d0, r0, trivial, ?_⟩⟩
    have Hs := AxSpinE.spineCertB σi T satp0 hmode hasid hppn dok kind rs pc is_rvc ins e ot ow
      d0 r0 PX Hc HPC Hhit Htx How Hcert tick t Hag (L - (k + e) + j)
    rw [← Nat.add_assoc] at Hs
    refine CertMono (imgS σi) dok kind _ _ _ _ _ _ _ (fun _ _ _ h => h) ?_ Hs
    rintro s' x t' ⟨d, r, rfl, HP, -⟩
    exact ⟨rfl, HPXr d r HP⟩
  have H := wpdInstrOfCertW (hlc := hlc) (GF := GF) (imgS σi) dok kind i Φ cpu G HG
    Hmid Htext Hflow Hloc Out k (L - (k + e)) (k + e) Hhi HnoRmwW HnoSplitW
    (fun s' _ t' => ∃ d r, s' = ⟨d, .BFin (L - (k + e)), r⟩ ∧ PX d r ∧
      GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
    ⟨d0, .BFin (e + (L - (k + e))), r0⟩ rs s HRet Hbp Hb
    (fun tick t Hag => AxSpinE.spineCertB σi T satp0 hmode hasid hppn dok kind rs pc is_rvc ins e
      ot ow d0 r0 PX Hc HPC Hhit Htx How Hcert tick t Hag (L - (k + e))) HPF
  iintro D C
  iapply H $$ D
  iintro %s' %t' %rs' %ib' %k' %HQ %Hag' %Hbp' D
  obtain ⟨d, r, rfl, HPX, HGB⟩ := HQ
  obtain ⟨GD, HGD⟩ := HGex
  have E : (AxOpsem.grow GD i).length = k' + (L - (k + e)) := Hbp' GD HGD
  rw [HL GD HGD] at E
  obtain rfl : k' = k + e := by omega
  iapply C $$ %d %r %rs' %ib' %HPX %(GoodBAgree σi T satp0 hmode hasid hppn rs pc is_rvc ot (ow d)
    _ rs' HGB Hag') D

end xBkW

/-! # 2. The POSITIONAL LOAD LEAF -/

section ldW
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- Rocq `FldMW_rowW`: `AxSpinXP.FldMRowP` over the window-restricted `FldMW`. -/
theorem FldMWRowW (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (pa : Int) (n : Nat)
    (Out : Nat → List (BitVec 8) → IProp GF) (lo hi : Nat) :
    ⊢ @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa n) i Out
        lo hi -∗
      @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa n) i
        (OutRP GT i pa n Out) lo hi := by
  iintro F
  unfold FldMW
  iintro %GD %ls %k %v %base %n' %Hc #Hg Hloc %Hgv %Hd %Hw
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrd⟩ := Hd
  ihave F2 := F $$ %(gtAdGd GT) %ls %k %v %base %n' %Hc Hg Hloc %Hgv %⟨⟨rfl, rfl⟩, Hrd⟩ %Hw
  iapply (dflowOMonoP L GT nm i (gtAdGd GT) k _ _) $$ [] F2
  iintro HO
  unfold OutRP
  isplitr
  · ipureintro
    exact ⟨Hgv, Hrd⟩
  · iexact HO

/-- Rocq `Xx_ldW`: THE POSITIONAL LOAD LEAF over `FldMW … k (k + 1)` (deviation 1; Rocq
`k (k + 2)`, and Rocq's fetch premise `Hnrk` is dropped). -/
theorem XxLdW (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (i : Agent) (cpu : CPU) (Hfix : textFixed (gtAdGd GT) i (imgS σi))
    (Ψ : Athread → IProp GF)
    (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
      ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)
    (k : Nat) (pc : BitVec 64) (imm : BitVec 12) (rs1 rd : BitVec 5) (w : Nat)
    (vb pa : BitVec 64) (Out : Nat → List (BitVec 8) → IProp GF) :
    textOkB σi T satp0 pc true (.LOAD (imm, .Regidx rs1, .Regidx rd, false, w)) →
    rd.toNat ≠ 0 → vmemWidth w → 1 ≤ w → w ≤ 8 →
    dataAtS σi T (.Load .Data) (vb + sign_extend (m := 64) imm) w pa →
    ¬ L.xlText (paZ pa) →
    (∀ (lb : Lbl) (aq rl : Bool) (n : Nat), (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb →
      aident lb = .IRmw aq rl (paZ pa) n → n ≠ w) →
    ⊢ @FldMW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP (paZ pa) w) i
        Out k (k + 1) -∗
      XLdP (hlc := hlc) L GT nm T satp0 i cpu Ψ k pc rs1 rd imm w vb (Out k) := by
  intro Htx hrd hvw hw1 hw8 hda _ Hnormw1
  have HnoRmwX : Dkind.DKLd = .DKLd → ∀ GD, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat), k ≤ k' ∧ k' < k + 1 →
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRmw aq rl base n →
        ¬ dokAtP (paZ pa) w base n⌝ := by
    intro _ GD Hc'
    iintro Hg
    ihave %Heq := (HGX L GT nm GD Hc') $$ Hg
    subst Heq
    ipureintro
    rintro k' lb aq rl base n ⟨H1, H2⟩ Hlb Hid ⟨rfl, rfl⟩
    obtain rfl : k' = k := by omega
    exact Hnormw1 lb aq rl _ Hlb Hid rfl
  have HnoSplitX : Dkind.DKLd = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat), k ≤ k' ∧ k' < k + 1 →
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRead aq base n →
        ¬ dokAtP (paZ pa) w base n⌝ := by
    intro h
    cases h
  iintro F
  unfold XLdP
  iintro %s %rs %Hpre C
  obtain ⟨HRet, Hc, HPC, Hhit, Hvb, Hhv, Hle⟩ := Hpre
  have H := @XBkW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0P GT i)
    ⟨_, rfl⟩ Ψ (Hmid0P L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i)
    (dokAtP (paZ pa) w) .DKLd (OutRP GT i (paZ pa) w Out)
    s rs k pc true _ 1 none (owLdB rd false w) .CPend false
    (fun d r' => ∃ vs, d = .CLd vs ∧ vs.length = w ∧ r' = false)
    HnoRmwX HnoSplitX (by rintro d r ⟨vs, rfl, -⟩ aq vs' h; cases h)
    HRet Hc HPC Hhit Htx (by rintro d r ⟨vs, rfl, -, -⟩; exact hrd)
    (CertBLoadS σi T satp0 hmode hasid hppn (dokAtP (paZ pa) w) rs pc true imm rs1 rd false w
      (vb + sign_extend (m := 64) imm) pa false hrd hvw hw1 hw8 (by rw [Hvb]) hda Hhv ⟨rfl, rfl⟩)
    (by omega) (by omega)
  iapply H $$ [F] [C]
  · simp only [CResW, CFkW]
    iapply (FldMWRowW L GT nm i (paZ pa) w Out k (k + 1))
    iexact F
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨vs, rfl, Hvs, rfl⟩ := HPX
    simp only [CResW]
    icases HO with ⟨%kd, %Hkd, HO⟩
    obtain rfl : kd = k := by omega
    unfold OutRP
    icases HO with ⟨%Hgv, HO⟩
    iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv.1 HO

end ldW

end Weak
