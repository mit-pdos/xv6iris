/-
Weak: **acquire's AMOSWAP on the POSITIONAL ENGINE, part 3**: the X leaf over the pinned bridge
(`XBkWP`) and THE AMOSWAP LEAF `XxAmoswap` at the joint instance Ixv6
(`AxSpinX2.xG L GT nm` / `xv6Pol GT`).

Rocq: `iris/AxSpinAm3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

PUBLISHED INTERFACE (one lemma, Lean form — see deviation 1 for the positions):

    XxAmoswap … k pc rs2 rs1 rd vb pa Out :
      textOkB σi T satp0 pc false (.AMO (.AMOSWAP, true, false, rs2, rs1, 4, rd)) →
      rd.toNat ≠ 0 → dataAtS σi T (accAmo true) vb 4 pa → ¬ L.xlText (paZ pa) →
      (row item k: no PLAIN read at paZ pa) →
      ⊢ FstRmwW rvwmoCatConsistent (dokAtP (paZ pa) 4) i Out k (k + 1) -∗
        AxSpinAm3.XAmo … k pc rs2 rs1 rd vb pa Out

`AxSpinAm3.XAmo k …` = from a `.pure ()` boundary `RetX cpu rs k s` (S-mode data regime
`ctrlOkSW`, `PC = pc`, warm TLB for the fetch page and the lock page, `gprVal rs rs1 = vb`,
`k + 1 ≤ LEN`), for every read value `rvs` (4 bytes) the continuation gets `GoodB … (rd ↦ amoLdv 4
rvs)`, the ROW FACT `grow GD0 i [k]? = LRmw aq rl (paZ pa) ts rvs wvs cls` with `wvs` = rs2's low
word (the READ VALUE is the graph value of the fused RMW item — pinned), and the write flow's
output `Out k wvs` at the RMW event, and continues at `k + 1`.

Rocq's forced deviations from step3-plan §2 [ID-4] carry over: `XAmo` takes `pa`; the window
premise is split (Rocq: the `aidentRd` form at the fetch slot, the plain-`IRead` form at the RMW
slot — here only the latter survives, deviation 1); the label's aq / rl bits are existential;
`Out` is applied to the WRITTEN bytes at the RMW's position.

PREMISES / HONESTY (as Rocq): the layout `L`, graph tuple `GT` (the graph is PINNED: `HGX`), the
S-mode data regime, a warm TLB for both pages (`hitW`), `textFixed GD0 i img` and the post's
mid-state lifting `HΨmid` are hypotheses, as for `AxSpinXP2.XxLdW`.  Like every positional leaf
this one is stated at a row POSITION `k` of the pinned graph `GD0`; it proves nothing about a hart
whose control flow or addresses are diverted; ownership is load-bearing for data values (OWNER
DECISION 2026-10-03).  The written bytes are rs2's low word (symbolic: `gprVal rs rs2`).

## Deviations from Rocq

1. O2 STAGE C COUNT SHIFT (as `AxSpinXP2` deviation 1): the instruction's fetch consumes NO row
   item, so an instruction consumes exactly `e` items (Rocq `e + 1`).
   * `XBkWP`: the window premise `HnoSplitX` ranges over `k ≤ k' ∧ k' < k + e` (Rocq
     `k ≤ k' < k + e + 1`); the resource window is `CResWP … k (k + e)` (Rocq `k (k + e + 1)`);
     the continuation is at `k + e`; the premise `k + e + 1 ≤ L` becomes `k < L` and `k + e ≤ L`.
     The bridge's `Hhi` (`length ≤ hi + c`, `hi = k + e`, `c = L - (k + e)`) is discharged from
     `HL`.
   * `XxAmoswap` / `XAmo` (`e = 1`): the fused RMW is EXACTLY row item `k` (Rocq `k + 1`), so the
     flow resource is `FstRmwW … k (k + 1)` (Rocq `k (k + 2)`), the row fact and `Out` are at `k`
     (Rocq `S k`), the continuation at `k + 1` (Rocq `k + 2`), `XAmo`'s length premise is
     `k + 1 ≤ LEN` (Rocq `k + 2 ≤ LEN`), and the plain-read premise `Hns1` is stated at `k`
     (Rocq `S k`).  Rocq's fetch-slot premise `Hnk` (no `aidentRd` read of `uint pa` at `k`) is
     DROPPED: row item `k` IS the amoswap's own `IRmw`, whose `aidentRd` is `some`, so the premise
     would be unsatisfiable; its two Rocq uses (the window at `k' = k`; `kd ≠ k`) are discharged
     by arithmetic.
   * Rocq's section premise `Hntext` does not exist in the Lean bridge (`AxCertP3` deviation 1).
     `XxAmoswap` keeps `¬ L.xlText (paZ pa)` for caller compatibility; it is unused (as Rocq).
2. TYPES as `AxSpinXP2` deviation 2: `[InvGS_gen hlc GF]` (any `hlc`), `[AxSpinX.Xv6G GF]`; the
   local instances `xa_pol` / `xa_G` are inlined as `xv6Pol GT` / `AxSpinX2.xG L GT nm`, passed
   with `@`.  `uint pa` ↦ `paZ pa`, `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`, `add_vec v (zeros' 64)` ↦
   `v + zeros (n := 64)`, `Interface.Ret tt` ↦ `.pure ()`, `register_lookup PC rs` ↦ `rs .PC`.
   Section variables are explicit arguments: `XBkWP` takes the `xBkWP` section's
   `σi T satp0 hmode hasid hppn i cpu G HG L HL HGex Φ Hmid Htext Hflow Hloc Hagree dok Out`
   (the bridge `AxSpinAm2.wpdInstrOfCertWP` has no `kind`: it is fixed to `DKRmw`);
   `HagreeX` / `FstRmwWRow` take `L GT nm` (+ `i pa n Out lo hi`); `OutWR` takes `GT i` first;
   `XAmo` takes `L GT nm T satp0 i cpu Ψ` first; `XxAmoswap` takes
   `L GT nm HL Hcons σi T satp0 hmode hasid hppn i cpu Hfix Ψ HΨmid` first.  `Hagree_x` is in
   the bridge's `⊢ … -∗ … -∗ ⌜GD = GD'⌝` form (`AxSpinAm2` deviation 2).
3. The trailing `Print Assumptions` lines are not ported (the lint's axiom check covers them).

**Rocq → Lean name map.**  `XBkWP` `XBkWP`, `Hagree_x` `HagreeX`, `add_vec_zeros64`
`addVecZeros64`, `OutWR` `OutWR`, `FstRmwW_row` `FstRmwWRow`, `XAmo` `AxSpinAm3.XAmo`
(file-qualified: `AxCert4.lean` declares `Weak.XAmo`), `Xx_amoswap` `XxAmoswap`.  None is in the
duplicated-name table; no Lean-only helpers.

**Dropped:** nothing (Rocq 7 definitions/lemmas + the 2 local instances `xa_pol` / `xa_G`,
inlined; Lean 7).
-/
import Weak.AxSpinAm
import Weak.AxSpinAm2
import Weak.AxSpinXP

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! # 1. The positional X leaf over the pinned bridge (kind `DKRmw`) -/

section xBkWP
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
variable (Hagree : ∀ GD GD', rvwmoCatConsistent GD → rvwmoCatConsistent GD' →
  ⊢ AxirisG.gconstInterp (GF := GF) GD -∗ AxirisG.gconstInterp GD' -∗ ⌜GD = GD'⌝)
variable (dok : Int → Nat → Prop)
variable (Out : Nat → List (BitVec 8) → IProp GF)

include hmode hasid hppn HG HL HGex Hmid Htext Hflow Hloc Hagree in
/-- Rocq `XBkWP`: the positional X leaf over the pinned, window-restricted bridge
`AxSpinAm2.wpdInstrOfCertWP` (deviation 1: window `CResWP … k (k + e)`, Rocq `k (k + e + 1)`). -/
theorem XBkWP (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (e : Nat) (ot : Option (BitVec 64))
    (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop)
    (HnoSplitX : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat), k ≤ k' ∧ k' < k + e →
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)
    (HPXr : ∀ d r, PX d r → ∀ aq vs, d ≠ .CRmwR aq vs) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc ins → (∀ d r, PX d r → owOk (ow d)) →
    CertB σi T satp0 dok .DKRmw rs pc is_rvc ins e ot ow d0 r0 PX →
    k < L → k + e ≤ L →
    ⊢ CResWP dok i Out k (k + e) d0 k -∗
      (∀ d r rs' ib', ⌜PX d r⌝ -∗ ⌜GoodB T satp0 rs pc is_rvc ot (ow d) rs'⌝ -∗
          CResWP dok i Out k (k + e) d (k + e) -∗
          wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k + e⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  intro HRet Hc HPC Hhit Htx How Hcert Hk Hle
  have HnoSplitW : ∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat), k ≤ k' →
        k' + (L - (k + e)) < (AxOpsem.grow GD i).length →
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝ := by
    intro GD Hc'
    refine (BI.and_intro (HG GD Hc') (HnoSplitX GD Hc')).trans ?_
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
      PF (imgS σi) dok .DKRmw (L - (k + e)) ⟨d0, .BFin (e + (L - (k + e))), r0⟩
        (riscvStep tick) t := by
    intro tick t Hag _
    refine ⟨e + (L - (k + e)), rfl, fun j => ⟨d0, r0, trivial, ?_⟩⟩
    have Hs := AxSpinE.spineCertB σi T satp0 hmode hasid hppn dok .DKRmw rs pc is_rvc ins e ot ow
      d0 r0 PX Hc HPC Hhit Htx How Hcert tick t Hag (L - (k + e) + j)
    rw [← Nat.add_assoc] at Hs
    refine CertMono (imgS σi) dok .DKRmw _ _ _ _ _ _ _ (fun _ _ _ h => h) ?_ Hs
    rintro s' x t' ⟨d, r, rfl, HP, -⟩
    exact ⟨rfl, HPXr d r HP⟩
  have H := AxSpinAm2.wpdInstrOfCertWP (hlc := hlc) (GF := GF) (imgS σi) dok i Φ cpu G HG HGex
    Hmid Htext Hflow Hloc Hagree Out k (L - (k + e)) (k + e) Hhi HnoSplitW
    (fun s' _ t' => ∃ d r, s' = ⟨d, .BFin (L - (k + e)), r⟩ ∧ PX d r ∧
      GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
    ⟨d0, .BFin (e + (L - (k + e))), r0⟩ rs s HRet Hbp Hb
    (fun tick t Hag => AxSpinE.spineCertB σi T satp0 hmode hasid hppn dok .DKRmw rs pc is_rvc ins
      e ot ow d0 r0 PX Hc HPC Hhit Htx How Hcert tick t Hag (L - (k + e))) HPF
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

end xBkWP

/-! # 2. THE AMOSWAP LEAF at Ixv6 -/

/-- Rocq `add_vec_zeros64`. -/
theorem addVecZeros64 (v : BitVec 64) : v + zeros (n := 64) = v := by
  show v + 0#64 = v
  exact BitVec.add_zero v

section amoW
variable {hlc : HasLC} {GF : BundledGFunctors.{0,0,0}} [InvGS_gen hlc GF] [AxannotGS GF]
  [AxSpinX.Xv6G GF]

/-- Rocq `Hagree_x`: graph agreement at Ixv6 (the graph is pinned). -/
theorem HagreeX (L : Xlay) (GT : GdexecT) (nm : Xv6N) :
    ∀ GD GD', rvwmoCatConsistent GD → rvwmoCatConsistent GD' →
      ⊢ @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD -∗
        @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD' -∗ ⌜GD = GD'⌝ := by
  intro GD GD' Hc Hc'
  iintro H1 H2
  ihave %h1 := (HGX L GT nm GD Hc) $$ H1
  ihave %h2 := (HGX L GT nm GD' Hc') $$ H2
  ipureintro
  rw [h1, h2]

/-- Rocq `OutWR`: the write flow's output, with the RMW event's row facts. -/
def OutWR (GT : GdexecT) (i : Agent) (pa : Int) (_n : Nat)
    (Out : Nat → List (BitVec 8) → IProp GF) (k : Nat) (data : List (BitVec 8)) : IProp GF :=
  iprop(⌜graphData (gtAdGd GT) (i, k) = some data ∧
    rowWr i (gtAdGd GT) k pa data.length⌝ ∗ Out k data)

/-- Rocq `FstRmwW_row`. -/
theorem FstRmwWRow (L : Xlay) (GT : GdexecT) (nm : Xv6N) (i : Agent) (pa : Int) (n : Nat)
    (Out : Nat → List (BitVec 8) → IProp GF) (lo hi : Nat) :
    ⊢ @FstRmwW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa n) i Out
        lo hi -∗
      @FstRmwW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent (dokAtP pa n) i
        (OutWR GT i pa n Out) lo hi := by
  iintro F
  unfold FstRmwW
  iintro %GD %ls %k %data %base %n' %Hc #Hg Hloc %Hgd %Hd %Hw
  ihave %Heq := (HGX L GT nm GD Hc) $$ Hg
  subst Heq
  obtain ⟨⟨rfl, rfl⟩, Hwr⟩ := Hd
  ihave F2 := F $$ %(gtAdGd GT) %ls %k %data %base %n' %Hc Hg Hloc %Hgd %⟨⟨rfl, rfl⟩, Hwr⟩ %Hw
  iapply (dflowOMonoP L GT nm i (gtAdGd GT) k _ _) $$ [] F2
  iintro HO
  unfold OutWR
  isplitr
  · ipureintro
    exact ⟨Hgd, Hwr⟩
  · iexact HO

/-- Rocq `XAmo`: the leaf's shape (deviation 1: the RMW at `k`, continuation at `k + 1`). -/
def AxSpinAm3.XAmo (L : Xlay) (GT : GdexecT) (nm : Xv6N) (T : PTree) (satp0 : BitVec 64)
    (i : Agent) (cpu : CPU) (Ψ : Athread → IProp GF) (k : Nat) (pc : BitVec 64)
    (rs2 rs1 rd : BitVec 5) (vb pa : BitVec 64) (Out : Nat → List (BitVec 8) → IProp GF) :
    IProp GF :=
  iprop(∀ (s : Athread) (rs : RegFile),
    ⌜RetX cpu rs k s ∧ ctrlOkSW T satp0 rs ∧ rs .PC = pc ∧ hitW rs pc ∧
      gprVal rs rs1 = vb ∧ hitW rs vb ∧ k + 1 ≤ (AxOpsem.grow (gtAdGd GT) i).length⌝ -∗
    (∀ (rvs : List (BitVec 8)) (rs' : RegFile) (ib' : Ibch), ⌜rvs.length = 4⌝ -∗
      ⌜GoodB T satp0 rs pc false none (some (rd, amoLdv 4 rvs)) rs'⌝ -∗
      ⌜∃ (aq rl : Bool) (ts : List Nat) (wvs : List (BitVec 8)) (cls : WmClass),
        (AxOpsem.grow (gtAdGd GT) i)[k]? = some (Lbl.LRmw aq rl (paZ pa) ts rvs wvs cls) ∧
        wvs = AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2))⌝ -∗
      Out k (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2))) -∗
      @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i
        ⟨.PHart cpu (.pure ()) rs' none ib', k + 1⟩ Ψ) -∗
    @wpdM hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent .MaybeStuck i s Ψ)

/-- Rocq `Xx_amoswap`: THE POSITIONAL AMOSWAP LEAF (`amoswap.w.aq`) (deviation 1: the RMW at
`k`, the flow window `[k, k + 1)`, Rocq's fetch-slot premise `Hnk` dropped). -/
theorem XxAmoswap (L : Xlay) (GT : GdexecT) (nm : Xv6N) (HL : xlayOk L)
    (Hcons : rvwmoCatConsistent (gtAdGd GT)) (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (i : Agent) (cpu : CPU) (Hfix : textFixed (gtAdGd GT) i (imgS σi))
    (Ψ : Athread → IProp GF)
    (HΨmid : ∀ s, midState s → s.atK = (AxOpsem.grow (gtAdGd GT) i).length →
      ⊢ @postLifting GF (AxSpinX2.xG L GT nm) Ψ i s)
    (k : Nat) (pc : BitVec 64) (rs2 rs1 rd : BitVec 5) (vb pa : BitVec 64)
    (Out : Nat → List (BitVec 8) → IProp GF) :
    textOkB σi T satp0 pc false (.AMO (.AMOSWAP, true, false, .Regidx rs2, .Regidx rs1, 4,
      .Regidx rd)) →
    rd.toNat ≠ 0 →
    dataAtS σi T (accAmo true) vb 4 pa → ¬ L.xlText (paZ pa) →
    (∀ (lb : Lbl) (aq : Bool) (m : Nat), (AxOpsem.grow (gtAdGd GT) i)[k]? = some lb →
      aident lb = .IRead aq (paZ pa) m → False) →
    ⊢ @FstRmwW hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) rvwmoCatConsistent
        (dokAtP (paZ pa) 4) i Out k (k + 1) -∗
      AxSpinAm3.XAmo (hlc := hlc) L GT nm T satp0 i cpu Ψ k pc rs2 rs1 rd vb pa Out := by
  intro Htx hrd hda _ Hns
  have HnoSplitX : ∀ GD, rvwmoCatConsistent GD →
      @AxirisG.gconstInterp GF (AxSpinX2.xG L GT nm) GD ⊢
      ⌜∀ (k' : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat), k ≤ k' ∧ k' < k + 1 →
        (AxOpsem.grow GD i)[k']? = some lb → aident lb = .IRead aq base n →
        ¬ dokAtP (paZ pa) 4 base n⌝ := by
    intro GD Hc'
    iintro Hg
    ihave %Heq := (HGX L GT nm GD Hc') $$ Hg
    subst Heq
    ipureintro
    rintro k' lb aq base n ⟨H1, H2⟩ Hlb Hid ⟨rfl, rfl⟩
    obtain rfl : k' = k := by omega
    exact Hns lb aq 4 Hlb Hid
  iintro F
  unfold AxSpinAm3.XAmo
  iintro %s %rs %Hpre C
  obtain ⟨HRet, Hc, HPC, Hhit, Hvb, Hhv, Hle⟩ := Hpre
  have H := @XBkWP hlc GF _ (AxSpinX2.xG L GT nm) (xv6Pol GT) σi T satp0 hmode hasid hppn i cpu
    (fun GD => GD = gtAdGd GT) (HGX L GT nm) (AxOpsem.grow (gtAdGd GT) i).length (HL0P GT i)
    ⟨_, rfl⟩ Ψ (Hmid0P L GT nm i Ψ HΨmid) (HtextX L GT nm (imgS σi) i Hfix)
    (HflowX L GT nm HL Hcons (imgS σi) i) (HlocX L GT nm i) (HagreeX L GT nm)
    (dokAtP (paZ pa) 4) (OutWR GT i (paZ pa) 4 Out)
    s rs k pc false _ 1 none (owAmoB rd) .CPend false (PXamo true rs rs2 false)
    HnoSplitX (by rintro d r ⟨vs, rfl, -⟩ aq vs' h; cases h)
    HRet Hc HPC Hhit Htx (by rintro d r ⟨vs, rfl, -, -⟩; exact hrd)
    (CertBAmoswapS σi T satp0 hmode hasid hppn (dokAtP (paZ pa) 4) rs pc false true rs2 rs1 rd
      (vb + zeros (n := 64)) pa false hrd (by rw [Hvb]) (by rw [addVecZeros64]; exact hda)
      (by rw [addVecZeros64]; exact Hhv) ⟨rfl, rfl⟩)
    (by omega) (by omega)
  iapply H $$ [F] [C]
  · simp only [CResWP]
    iapply (FstRmwWRow L GT nm i (paZ pa) 4 Out k (k + 1))
    iexact F
  · iintro %d %r %rs' %ib' %HPX %HGB HO
    obtain ⟨vs, rfl, Hvs, rfl⟩ := HPX
    simp only [CResWP, OutWR]
    icases HO with ⟨%kd, %Hkd, ⟨%Hgd, HO⟩, #P⟩
    obtain rfl : kd = k := by omega
    unfold Pin
    icases P with ⟨%GD, %Hc', #Hg, %Hgv, %Hrmw⟩
    ihave %Heq := (HGX L GT nm GD Hc') $$ Hg
    subst Heq
    have Hrow : ∃ (aq rl : Bool) (ts : List Nat) (wvs : List (BitVec 8)) (cls : WmClass),
        (AxOpsem.grow (gtAdGd GT) i)[kd]? = some (Lbl.LRmw aq rl (paZ pa) ts vs wvs cls) ∧
        wvs = AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)) := by
      obtain ⟨lb, aq1, rl1, b1, n1, Hlb, Hid⟩ := Hrmw
      obtain ⟨Hgd, lb', rl', Hlb', Hw'⟩ := Hgd
      rw [Hlb] at Hlb'
      obtain rfl := Option.some.inj Hlb'
      have Hl := lblOfRow _ _ _ _ Hlb
      cases lb with
      | LRmw aq2 rl2 b2 ts2 rv2 wv2 cls2 =>
        unfold graphValue at Hgv
        unfold graphData at Hgd
        rw [Hl] at Hgv Hgd
        simp only [Option.bind_some, lblValue, lblData, Option.some.injEq] at Hgv Hgd
        simp only [aident, aidentWr, Option.some.injEq, Prod.mk.injEq] at Hw'
        obtain ⟨-, rfl, -⟩ := Hw'
        subst Hgv
        subst Hgd
        exact ⟨aq2, rl2, ts2, _, cls2, Hlb, rfl⟩
      | LLoad _ _ _ _ => simp [aident] at Hid
      | LStore _ _ _ _ => simp [aident] at Hid
      | LFence _ _ _ _ => simp [aident] at Hid
    iapply C $$ %vs %rs' %ib' %Hvs %HGB %Hrow HO

end amoW

end Weak
