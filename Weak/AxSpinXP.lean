/-
Weak: **THE POSITIONAL X LEAF `XBkP` and the positional load leaf `XxLdP`**: the data read's
no-RMW / no-split premises restricted to the instruction's window.

Rocq: `iris/AxSpinXP.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`XBkP` is `AxSpinE4.XBk` over the window-bounded bridge `AxCertP2.wpdInstrOfCertP`: its
`HnoRmwX` / `HnoSplitX` quantify only over the row positions of the instruction's own window.
The family invariant `PF` is built from `AxSpinE.spineCertB` at EVERY final budget `b + j` (the
`CertB` of a leaf already holds for all `b`); the one new side condition is `HPXr`: the final
data states `PX` are never an RMW half (`CRmwR`) — true for every leaf (`CLd` / `CSt` / `CRmw` /
`CPend`).

`XxLdP` is `AxSpinHd7.Xx_ldO` over `XBkP`: the whole-row premise `Hnormw` (no RMW row item of
hart `i` at ANY position on the load's bytes — FALSE for holding's lock-word load on any row with
acquire's `amoswap.w.aq lk`) is replaced by `Hnormw1`: no such RMW item AT the load's own data
slot.  AxSpinHd7's leaf interface `XLd`, `dok_at`, `OutR`, `FldM_row`, `dflowO_mono` is restated
here under primed names (`XLdP`, `dokAtP`, …), with the same bodies.

## Deviations from Rocq

1. O2 STAGE C COUNT SHIFT (`AxSpinE` deviation 1, `AxSpinE4` deviation 1): the instruction's
   fetch consumes NO row item, so an instruction consumes exactly `e` items (Rocq `e + 1`).
   * `XBkP`: the window premises `HnoRmwX` / `HnoSplitX` range over `k ≤ k' ∧ k' < k + e`
     (Rocq `k ≤ k' < k + e + 1`); the continuation is at `k + e` (Rocq `k + e + 1`); the
     arithmetic premise `k + e + 1 ≤ L` becomes `k < L` and `k + e ≤ L` (as `AxSpinE4.XBk`).
   * `XxLdP` / `XLdP` (`e = 1`): the load's data event is EXACTLY at `k` (Rocq `k + 1`), so
     `Hnormw1` is stated at position `k` (Rocq `S k`), the continuation gets
     `graphValue GD0 (i, k)` and `Out k` and is at `k + 1` (Rocq `k + 2`), and `XLdP`'s premise
     is `k + 1 ≤ LEN` (Rocq `k + 2 ≤ LEN`).  Rocq's fetch premise `Hnrk` (the row item at `k`,
     the fetch, is not a read of `w` bytes) is DROPPED: under Stage C row item `k` IS the load's
     own data read, so the premise would be unsatisfiable; its two Rocq uses (ruling out the
     fetch slot from the window and from the event position) are discharged by arithmetic.
   * Rocq's section premise `Hntext` of `XBkP` is DROPPED (`AxCert2` deviation 1; neither
     `AxCertP2.wpdInstrOfCertP` nor `XBk` takes it).  `XxLdP` keeps the premise
     `¬ L.xlText (paZ pa)` (it only fed `Hntext` in Rocq) for caller compatibility; it is unused.
2. TYPES as `AxSpinE4` deviation 3 / `AxSpinE5` deviation 2: `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]` (any `hlc`); `xv6G Σ` ↦ `[AxSpinX.Xv6G GF]`; the local instances
   `xp_pol` / `xp_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`, passed with `@`.
   `Z` widths ↦ `Nat` (`Z.to_nat w` ↦ `w`, `(1 ≤ w ≤ 8)%Z` ↦ `1 ≤ w → w ≤ 8`), `uint pa` ↦
   `paZ pa`, `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`, `add_vec vb (sign_extend' 64 imm)` ↦
   `vb + sign_extend (m := 64) imm`, `register_lookup PC rs` ↦ `rs .PC`, `l !! k` ↦ `l[k]?`.
   Section variables are explicit arguments: `XBkP` takes the `xBkP` section's
   `σi T satp0 hmode hasid hppn i cpu G HG L HL HGex Φ Hmid Htext Hflow Hloc dok kind Out`;
   `HL0P GT i`; `Hmid0P L GT nm i Ψ HΨmid`; `XLdP L GT nm T satp0 i cpu Ψ`; `dflowOMonoP L GT nm
   i`; `OutRP GT i`; `FldMRowP L GT nm i`; `XxLdP` takes
   `L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid` first.
3. The trailing `Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `XBkP` `XBkP`, `dok_atP` `dokAtP`, `HL0P` `HL0P`, `Hmid0P`
`Hmid0P`, `XLdP` `XLdP`, `dflowO_monoP` `dflowOMonoP`, `OutRP` `OutRP`, `FldM_rowP`
`FldMRowP`, `Xx_ldP` `XxLdP`.  None is in the duplicated-name table; no Lean-only helpers.

**Dropped:** nothing (Rocq 9 definitions/lemmas + the 2 local instances `xp_pol` / `xp_G`,
inlined; Lean 9).
-/
import Weak.AxCertP2
import Weak.AxSpinE2
import Weak.AxSpinE5

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! # 1. The POSITIONAL X LEAF, window premises -/

section xBkP
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
/-- Rocq `XBkP`: the positional leaf whose no-RMW / no-split premises range over the
instruction's window `[k, k + e)` only (deviation 1; Rocq `[k, k + e + 1)`). -/
theorem XBkP (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
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
    ⊢ CResK dok kind i Out k d0 k -∗
      (∀ d r rs' ib', ⌜PX d r⌝ -∗ ⌜GoodB T satp0 rs pc is_rvc ot (ow d) rs'⌝ -∗
          CResK dok kind i Out k d (k + e) -∗
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
  have H := AxCertP2.wpdInstrOfCertP (hlc := hlc) (GF := GF) (imgS σi) dok kind i Φ cpu G HG
    Hmid Htext Hflow Hloc Out k (L - (k + e)) HnoRmwW HnoSplitW
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

end xBkP

/-- Rocq `dok_atP` (verbatim copy of `AxSpinHd7.dok_at`). -/
def dokAtP (pa : Int) (n : Nat) : Int → Nat → Prop := fun b m => b = pa ∧ m = n

/-- Rocq `HL0P`. -/
theorem HL0P (GT : GdexecT) (i : Agent) :
    ∀ GD, GD = gtAdGd GT → (AxOpsem.grow GD i).length = (AxOpsem.grow (gtAdGd GT) i).length := by
  rintro GD rfl
  rfl

/-! # 2. The POSITIONAL LOAD LEAF -/

section ldP
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- Rocq `Hmid0P`. -/
theorem Hmid0P (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (Ψ : Athread → IProp GF)
    (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
      ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s) :
    ∀ GD s, GD = gtAdGd GT → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s := by
  rintro GD s rfl Hm Hk
  exact HΨmid s Hm Hk

/-- Rocq `XLdP` (verbatim copy of `AxSpinHd7.XLd`; deviation 1: data slot `k`, continuation at
`k + 1`). -/
def XLdP (L : Xlay) (GT : GdexecT) (nm : Xv6N) (T : PTree) (satp0 : BitVec 64) (i : Agent)
    (cpu : CPU) (Ψ : Athread → IProp GF) (k : Nat) (pc : BitVec 64) (rs1 rd : BitVec 5)
    (imm : BitVec 12) (w : Nat) (vb : BitVec 64) (Out : List (BitVec 8) → IProp GF) :
    IProp GF :=
  iprop(∀ (s : Athread) (rs : RegFile),
    ⌜RetX cpu rs k s ∧ ctrlOkSW T satp0 rs ∧ rs .PC = pc ∧ hitW rs pc ∧
      gprVal rs rs1 = vb ∧ hitW rs (vb + sign_extend (m := 64) imm) ∧
      k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length⌝ -∗
    (∀ (vs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜vs.length = w⌝ -∗
      ⌜GoodB T satp0 rs pc true none (some (rd, ldRes false w vs)) rs'⌝ -∗
      ⌜graphValue (gtAdGd GT) (i, k) = some vs⌝ -∗ Out vs -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
    @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ)

/-- Rocq `dflowO_monoP`. -/
theorem dflowOMonoP (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (GD : Gdexec) (k : Nat)
    (O O' : IProp GF) :
    ⊢ (O -∗ O') -∗ @dflowO hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) i GD k O -∗
      @dflowO hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) i GD k O' := by
  iintro HOO F
  unfold dflowO
  iintro %na Hna
  imod F $$ %na Hna with F
  imodintro
  inext
  imod F with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl, HO⟩
  imodintro
  iexists R, nu, nuu, ls'
  isplitl [Hs]
  · iexact Hs
  isplitl [Hfe]
  · iexact Hfe
  isplitl [Hna]
  · iexact Hna
  isplitl [Hl]
  · iexact Hl
  iapply HOO $$ HO

/-- Rocq `OutRP` (verbatim copy of `AxSpinHd7.OutR`). -/
def OutRP (GT : GdexecT) (i : Agent) (pa : Int) (n : Nat)
    (Out : Nat → List (BitVec 8) → IProp GF) (k : Nat) (v : List (BitVec 8)) : IProp GF :=
  iprop(⌜graphValue (gtAdGd GT) (i, k) = some v ∧
    ∃ lb aq, (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb ∧
      aidentRd (aident lb) = some (aq, pa, n)⌝ ∗ Out k v)

/-- Rocq `FldM_rowP`. -/
theorem FldMRowP (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (pa : Int) (n : Nat)
    (Out : Nat → List (BitVec 8) → IProp GF) :
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa n) i Out -∗
      @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa n) i
        (OutRP GT i pa n Out) := by
  iintro F
  unfold FldM
  iintro %GD %ls %k %v %base %n' %Hc #Hg Hloc %Hgv %Hd
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hrd⟩ := Hd
  ihave F2 := F $$ %(gtAdGd GT) %ls %k %v %base %n' %Hc Hg Hloc %Hgv %⟨⟨rfl, rfl⟩, Hrd⟩
  iapply (dflowOMonoP L GT nm i (gtAdGd GT) k _ _) $$ [] F2
  iintro HO
  unfold OutRP
  isplitr
  · ipureintro
    exact ⟨Hgv, Hrd⟩
  · iexact HO

/-- Rocq `Xx_ldP`: THE POSITIONAL LOAD LEAF, the no-RMW premise only at the data slot `k`
(deviation 1; Rocq `k + 1`, and Rocq's fetch premise `Hnrk` is dropped). -/
theorem XxLdP (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
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
    ⊢ @FldM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP (paZ pa) w) i
        Out -∗
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
  have H := @XBkP hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
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
  · simp only [CResK, CFkM]
    iapply (FldMRowP L GT nm i (paZ pa) w Out)
    iexact F
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨vs, rfl, Hvs, rfl⟩ := HPX
    simp only [CResK]
    icases HO with ⟨%kd, %Hkd, HO⟩
    obtain rfl : kd = k := by omega
    unfold OutRP
    icases HO with ⟨%Hgv, HO⟩
    iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hgv.1 HO

end ldP

end Weak
