/-
Weak: **PHASE 5 POSITIONAL ENGINE, part 4: the `Cert` ⇒ `WPd` bridge with a POSITIONED data
event, and the leaf `XBk`.**

Rocq: `iris/AxSpinE4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

WHY.  `AxCert2.wpdOfCertM` hands the continuation the data event's resource as `∃ k, Out k vs` —
the event's row position is forgotten.  A row-pinned client needs it: the spill's flow output is
`graphData (i, kd)`, and to link the spilled bytes to the row item that `Row_mycpu` pins, `kd`
must be KNOWN.  `wpdOfCertK` is `wpdOfCertM` (same node lemmas, same induction) whose data
resource `CResK d kc` additionally records `k0 ≤ kd < kc` — the event happened at or after the
instruction's start `k0` and before the current position `kc`.  `XBk` = `AxSpinE3.XB` over it.

## Deviations from Rocq

1. O2 STAGE C COUNT SHIFT (`AxSpinE` deviation 1, `AxSpinE3` deviation 1): the instruction's
   fetch consumes NO row item, so an instruction consumes exactly `e` items (Rocq `e + 1`).
   `XBk`'s data event is positioned in `[k, k + e)` (Rocq `[k, k + e + 1)`), its continuation is
   at `k + e` (Rocq `k + e + 1`), and the arithmetic premise `k + e + 1 ≤ L` becomes the two
   premises `k < L` (the boundary's row-end obligation) and `k + e ≤ L`, as `AxSpinE3.XB`.
   Consequence for callers: for a load / store (`e = 1`) the data event is EXACTLY at `k`
   (Rocq: at `k` or `k + 1`, the caller excluding `k` — the fetch — from its row facts).
   In `wpdOfCertK` the Lean-only `Cert.cIf` arm (an image-answered fetch) keeps the position;
   `Cert.cEnd` is the Lean form of Rocq's stuck-read arm.  Rocq's section premise `Hntext` is
   DROPPED (`AxCert2` deviation 1).
2. THE PINS: `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`.
3. TYPES as `AxCert2` deviation 4 / `AxSpinE3` deviation 5: `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]` (any `hlc`); Rocq's `Mc` is `rvwmoCatConsistent`, so the node lemmas are
   the `…M` forms at `rvwmoCatConsistent`.  Section variables are explicit arguments:
   `CResK dok kind i Out k0 d kc`; `wpdOfCertK`/`wpdInstrOfCertK` take
   `img dok kind i Φ cpu G HG Hmid Htext Hflow Hloc HnoRmw HnoSplit Out k0` first; `XBk` takes
   the `xB` section's `σi T satp0 hmode hasid hppn i cpu G HG L HL HGex Φ Hmid Htext Hflow Hloc
   dok kind HnoRmw HnoSplit Out` (as `AxSpinE3.XB`).  `MState rs ∅ dev0_state` ↦
   `⟨rs, fun _ => none, testDevs⟩`, `Interface.Ret tt` ↦ `.pure ()`.
4. The Ltac `silent_psK` is replaced by inline inversions (as `AxCert2.wpdOfCertM`).
5. Q19 (provisional): `wpdOfCertK` has the case of the Lean-only `Cert.cSf` (an SFENCE.VMA
   announce, one row item), by `AxCert2.wpdSfNodeM` as the fence.

**Rocq → Lean name map.**  `CResK` `CResK`, `CResK_succ` `cResKSucc`, `wpd_of_CertK`
`wpdOfCertK`, `wpd_instr_of_CertK` `wpdInstrOfCertK`, `XBk` `XBk`.

**Dropped:** nothing (Rocq 5 definitions/lemmas + 1 Ltac; Lean 5).
**Not ported:** the Ltac `silent_psK` (deviation 4); the `Print Assumptions` lines (the lint's
axiom check covers them).
-/
import Weak.AxSpinE3

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! # 1. The positioned data resource -/

section bridgeKDefs
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The data event's resource, POSITIONED in `[k0, kc)`. -/
def CResK (dok : Int → Nat → Prop) (kind : Dkind) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (k0 : Nat) (d : Cdata) (kc : Nat) : IProp GF :=
  match d with
  | .CPend => CFkM rvwmoCatConsistent dok kind i Out
  | .CRmwR _ _ => FstM rvwmoCatConsistent dok i Out
  | .CLd vs | .CSt vs _ | .CRmw _ _ _ vs _ => iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kc⌝ ∗ Out kd vs)

theorem cResKSucc (dok : Int → Nat → Prop) (kind : Dkind) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (k0 : Nat) (d : Cdata) (kc : Nat) :
    CResK dok kind i Out k0 d kc ⊢ CResK dok kind i Out k0 d (kc + 1) := by
  cases d with
  | CPend => exact .rfl
  | CRmwR _ _ => exact .rfl
  | CLd vs | CSt vs _ | CRmw _ _ _ vs _ =>
    simp only [CResK]
    iintro ⟨%kd, %Hk, H⟩
    iexists kd
    isplitr
    · ipureintro
      omega
    iexact H

end bridgeKDefs

/-! # 2. THE BRIDGE with a positioned data event -/

section bridgeK
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop)
variable (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (HnoRmw : kind = .DKLd → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)
variable (HnoSplit : kind = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)
variable (Out : Nat → List (BitVec 8) → IProp GF) (k0 : Nat)

include HG Hmid Htext Hflow Hloc HnoRmw HnoSplit in
theorem wpdOfCertK (Q : Cst → Unit → ExecSt → Prop) (m : SailM Unit) (s : Cst) (t : ExecSt) :
    AxCert.Cert img dok kind (fun _ _ _ => False) Q s m t →
    ∀ rs ib kk, regsAgree AxRunClose.pinReg rs t.regs → AxCert2.bpos G i kk s.csB → k0 ≤ kk →
    ⊢ CResK dok kind i Out k0 s.csD kk -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ ⌜k0 ≤ k'⌝ -∗ CResK dok kind i Out k0 s'.csD k' -∗
         wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu m rs none ib, kk⟩ Φ := by
  intro H
  induction H with
  | cRet s x t HQ =>
    intro rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply C $$ %s %t %rs %ib %kk %HQ %Hag %Hb %Hk0 Hd
  | cExt s e k t he => exact he.elim
  | cRd s r k t _ _ IHs IHn =>
    intro rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (wpdAdminNode3M rvwmoCatConsistent i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k (rs1 r)) rs1 none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨rfl, rfl⟩ := pstepRdInv cpu r k rs1 ib1 d l p' d' Hp
      exact ⟨trivial, rs1, _, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      by_cases Hs : AxRunClose.pinReg r
      · iapply (IHs Hs (rs1 r) rs1 ib1 kk HA1 Hb Hk0) $$ Hd C
      · have h := IHn Hs rs1 ib1 kk HA1 Hb Hk0
        rw [← HA1 r Hs] at h
        iapply h $$ Hd C
  | cWr s r v k t Hr _ IH =>
    intro rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (wpdAdminNode3M rvwmoCatConsistent i Φ cpu G HG Hmid _ ?_ kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (k PUnit.unit) (rs1.set r v) none ib1, kk⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨Hl, rfl⟩ := pstepWrInv cpu r v k rs1 ib1 d l p' d' Hp
      exact ⟨Hl, rs1, ib1, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      iapply (IH (rs1.set r v) ib1 kk (regsAgreeSet _ _ _ r v HA1) Hb Hk0) $$ Hd C
  | cMrd d b r n va req k t vs Hdev Hlat Hnf Hvs _ IH =>
    intro rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdImgRead3M rvwmoCatConsistent img i Φ cpu G HG Hmid Htext Hflow n va
      req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    ihave Hd := (cResKSucc dok kind i Out k0 d kk) $$ Hd
    iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega)) $$ Hd C
  | cIf s n va req k t vs Hdev Hlat Hfe Hvs _ IH =>
    intro rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdImgFetch3M rvwmoCatConsistent img i Φ cpu G HG Hmid Htext n va req k
      ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hfe Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib kk HA' Hb Hk0) $$ Hd C
  | cEnd d r n va req k t Hdev Hlat Hnf =>
    intro rs ib kk Hag Hb _
    have Hb' : ∀ GD, G GD → (AxOpsem.grow GD i).length = kk + 0 := Hb
    iintro - -
    iapply (wpdStuckReadM rvwmoCatConsistent i Φ cpu G HG Hmid kk (fun GD h => Hb' GD h) n va req
      k ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf rs Hag)
  | cWrEnd d r n va req k t Hdev Hlat =>
    intro rs ib kk Hag Hb _
    have Hb' : ∀ GD, G GD → (AxOpsem.grow GD i).length = kk + 0 := Hb
    iintro - -
    iapply (AxCert2.wpdStuckWriteM rvwmoCatConsistent i Φ cpu G HG Hmid kk (fun GD h => Hb' GD h) n va req k ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat rs Hag)
  | cDrd b r n va req k t Hkd Hdev Hlat Hnf Hdok _ IH =>
    intro rs ib kk Hag Hb Hk0
    have hconv : CResK dok kind i Out k0 .CPend kk ⊢ FldM rvwmoCatConsistent dok i Out := by
      subst Hkd
      exact .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdDrdNodeM rvwmoCatConsistent dok kind i Φ cpu G HG Hmid HnoRmw Out n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hkd Hdev Hlat Hnf Hdok) $$ %rs %Hag Hd
    iintro %vs %rs' %Hlen %HA' HO
    have hdone : iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kk + 1⌝ ∗ Out kd vs) ⊢
        CResK dok kind i Out k0 (.CLd vs) (kk + 1) := .rfl
    iapply (IH vs Hlen rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega)) $$ [HO] C
    iapply hdone
    iexists kk
    isplitr
    · ipureintro
      omega
    iexact HO
  | cDwr b r n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    intro rs ib kk Hag Hb Hk0
    have hconv : CResK dok kind i Out k0 .CPend kk ⊢ FstM rvwmoCatConsistent dok i Out := by
      subst Hkd
      exact .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdDwrNodeM rvwmoCatConsistent dok i Φ cpu G HG Hmid Out n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %HA' HO
    have hdone : iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kk + 1⌝ ∗ Out kd (WeakInterpProj.wbytes n v)) ⊢
        CResK dok kind i Out k0 (.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind r))
          (kk + 1) := .rfl
    iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega)) $$ [HO] C
    iapply hdone
    iexists kk
    isplitr
    · ipureintro
      omega
    iexact HO
  | cFence d b r bk k t Hpark _ IH =>
    intro rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (wpdFenceNodeM rvwmoCatConsistent i Φ cpu G HG Hmid Hloc bk k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hpark) $$ %rs %Hag
    iintro %rs' %HA'
    ihave Hd := (cResKSucc dok kind i Out k0 d kk) $$ Hd
    iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega)) $$ Hd C
  | cXrd b r n va req k t Hkd Hdev Hlat Hdok _ IH =>
    intro rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (wpdXrdNodeM rvwmoCatConsistent dok kind i Φ cpu G HG Hmid HnoSplit n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hkd Hdev Hlat Hdok) $$ %rs %Hag
    iintro %vs %rs' %Hlen %HA'
    have hconv : CResK dok kind i Out k0 .CPend kk ⊢
        CResK dok kind i Out k0 (.CRmwR (classify req.access_kind).akSync vs) kk := by
      subst Hkd
      exact .rfl
    ihave Hd := hconv $$ Hd
    iapply (IH vs Hlen rs' ib kk HA' Hb Hk0) $$ Hd C
  | cXwr aq rvs b r n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    intro rs ib kk Hag Hb Hk0
    have hconv : CResK dok kind i Out k0 (.CRmwR aq rvs) kk ⊢
        FstM rvwmoCatConsistent dok i Out := .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdXwrNodeM rvwmoCatConsistent dok i Φ cpu G HG Hmid Out n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %HA' HO
    have hdone : iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kk + 1⌝ ∗ Out kd (WeakInterpProj.wbytes n v)) ⊢
        CResK dok kind i Out k0 (.CRmw aq (classify req.access_kind).akSync rvs
          (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) (kk + 1) := .rfl
    iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega)) $$ [HO] C
    iapply hdone
    iexists kk
    isplitr
    · ipureintro
      omega
    iexact HO
  | cIa s n w k t Hsf _ IH =>
    intro rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M rvwmoCatConsistent i Φ cpu G HG Hmid _ (k ()) ?_ kk t ?_
      rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      rw [annLabelNot Hsf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1 Hb Hk0) $$ Hd C
  | cSf d b r n w k t Hsf _ IH =>
    intro rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxCert2.wpdSfNodeM rvwmoCatConsistent i Φ cpu G HG Hmid Hloc n w k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hsf) $$ %rs %Hag
    iintro %rs' %ib' %HA'
    ihave Hd := (cResKSucc dok kind i Out k0 d kk) $$ Hd
    iapply (IH rs' ib' (kk + 1) HA' (bposSucc G i kk b Hb) (by omega)) $$ Hd C
  | cBa s _ _ k t _ IH | cCo s _ k t _ IH | cTl s _ k t _ IH | cTe s _ k t _ IH
  | cRx s _ k t _ IH | cTs s _ k t _ IH | cTx s _ k t _ IH | cCc s k t _ IH
  | cMsg s _ k t _ IH | cGcc s k t _ IH =>
    intro rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M rvwmoCatConsistent i Φ cpu G HG Hmid _ _ ?_ kk t ?_
      rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      exact ⟨trivial, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1 Hb Hk0) $$ Hd C

include HG Hmid Htext Hflow Hloc HnoRmw HnoSplit in
theorem wpdInstrOfCertK (Q : Cst → Unit → ExecSt → Prop) (s0 : Cst) (rs : RegFile)
    (s : Athread) (Hs : RetX cpu rs k0 s)
    (Hbp : AxCert2.bpos G i k0 s0.csB)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k0 s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       AxCert.Cert img dok kind (fun _ _ _ => False) Q s0 (riscvStep tick) t) :
    ⊢ CResK dok kind i Out k0 s0.csD k0 -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResK dok kind i Out k0 s'.csD k' -∗
         wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  iintro Hd C
  iapply (wpdRetNode3M rvwmoCatConsistent i Φ cpu G HG rs k0 s Hs Hb)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  iapply (wpdOfCertK img dok kind i Φ cpu G HG Hmid Htext Hflow Hloc HnoRmw HnoSplit Out k0 Q _
    s0 ⟨rs', fun _ => none, testDevs⟩
    (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone k0
    (regsAgreeRefl _ _) Hbp (Nat.le_refl _)) $$ Hd
  iintro %s' %t' %rs1 %ib' %k' %HQ %Hag' %Hbp' %_ Hd
  iapply C $$ %s' %t' %rs1 %ib' %k' %HQ %Hag' %Hbp' Hd

end bridgeK

/-! # 3. THE POSITIONAL X LEAF with a positioned data event -/

section xBk
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
variable (HnoRmw : kind = .DKLd → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)
variable (HnoSplit : kind = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)
variable (Out : Nat → List (BitVec 8) → IProp GF)

include hmode hasid hppn HG HL HGex Hmid Htext Hflow Hloc HnoRmw HnoSplit in
/-- THE POSITIONAL LEAF, data event positioned in `[k, k + e)`, continuation at `k + e`
(deviation 1; Rocq `[k, k + e + 1)` / `k + e + 1`). -/
theorem XBk (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (e : Nat) (ot : Option (BitVec 64))
    (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop) :
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
  have H := wpdInstrOfCertK (hlc := hlc) (GF := GF) (imgS σi) dok kind i Φ cpu G HG Hmid Htext
    Hflow Hloc HnoRmw HnoSplit Out k
    (fun s' _ t' => ∃ d r, s' = ⟨d, .BFin (L - (k + e)), r⟩ ∧ PX d r ∧
      GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
    ⟨d0, .BFin (e + (L - (k + e))), r0⟩ rs s HRet Hbp Hb
    (fun tick t Hag => AxSpinE.spineCertB σi T satp0 hmode hasid hppn dok kind rs pc is_rvc ins e
      ot ow d0 r0 PX Hc HPC Hhit Htx How Hcert tick t Hag (L - (k + e)))
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

end xBk

end Weak
