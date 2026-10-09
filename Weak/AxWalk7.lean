/-
Weak: **the POSITIONAL variant of the main bridge for the one-event certificate** (task item 2):
`AxCert.Cert` embeds into `AxWalk.CertWP` (no walker events) with the positional side conditions
required only on the INSTRUCTION'S OWN row span.

Rocq: `iris/AxWalk7.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxCert.Cert` embeds into `CertWP` (no walker events) with the positional side conditions
required only on the instruction's own row span — at `BFin n` the `n` positions `k .. k+n-1` the
certificate consumes, at `BInf` the row suffix from `k` — instead of `AxCert2`'s region-wide
`HnoRmw` / `HnoSplit` over the whole row (`CertWPOfCertPos`); composed with
`AxWalk2.wpdOfCertWPM` at an empty PT region this is `wpdOfCertPosM`: `AxCert2.wpdOfCertM`
without `HnoRmw` / `HnoSplit`.  (`okFrom` at `BFin n` includes `k + n`, one past the row end under
`AxCert2.bpos`: there the positional facts hold vacuously and a fused read half may sit there
before the certificate ends.)

## Deviations from Rocq

1. AS `AxCert` / `AxWalk` deviation 1: `Cert` / `CertWP` are on `SailM X`, Rocq's extra-outcome
   type `E` ↦ `Sail.Error exception` (no `E` binder); `regs_agree seip_reg` ↦
   `regsAgree AxRunClose.pinReg`; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`);
   `Interface.Ret tt` ↦ `.pure ()`; `CRes` ↦ `CResM M dok kind i Out`; `cs_b`/`cs_d` ↦
   `csB`/`csD`; `S k` ↦ `k + 1`; `(k ≤ k' ≤ k + n)%nat` ↦ `k ≤ k' ∧ k' ≤ k + n`.
2. O2 STAGE C (as `AxWalk2` deviation 1): Rocq's section premise `Hntext` is DROPPED (Lean's
   `AxWalk2.wpdOfCertWPM` no longer takes it; data reads carry `akIfetch = false`).  The Lean-only
   fetch arm `cIf` maps to `CertWP.pIf` (position and budget kept).  Q19 (provisional): the
   Lean-only sfence-announce arm `cSf` maps to `CertWP.pSf` (one row item, as `cFence`).
3. Section variables `M img dok kind i Φ cpu G HG Hmid Htext Hflow Hloc Out` (Rocq additionally
   `Hntext`, deviation 2).  The empty-PT-region walker flows and the empty initial walker
   resource (Rocq's inline `iModIntro …` / `by rewrite /WRes` bullets) are the Lean-only lemmas
   `AxWalk7.wfrEmpty` / `AxWalk7.wfwEmpty` (and AxWalk2's `AxWalk2.wResNil`).
4. The riscv.cat instance `wpd_of_Cert_pos` (Rocq `Definition`) is a theorem typed
   `type_of% (wpdOfCertPosM rvwmoCatConsistent)`.

**Rocq → Lean name map.**  `ok_from` `okFrom`, `ok_from_succ` `okFromSucc`, `CertWP_of_Cert_pos`
`CertWPOfCertPos`, `wpd_of_Cert_posM` `wpdOfCertPosM`, `wpd_of_Cert_pos` `wpdOfCertPos`.  None is
in the duplicated-name table.  Lean-only: `AxWalk7.wfrEmpty`, `AxWalk7.wfwEmpty`.

**Dropped:** nothing (Rocq 5 definitions/lemmas; Lean 5, + 2 Lean-only helpers).  **Not ported:**
the local notations and the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxWalk2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D

/-- The positions the certificate still consumes from `k` at budget `b`. -/
def okFrom (P : Nat → Prop) (k : Nat) (b : Bud) : Prop :=
  match b with
  | .BInf => ∀ k', k ≤ k' → P k'
  | .BFin n => ∀ k', k ≤ k' ∧ k' ≤ k + n → P k'

theorem okFromSucc (P : Nat → Prop) (k : Nat) (b : Bud) :
    okFrom P k (bsucc b) → P k ∧ okFrom P (k + 1) b := by
  cases b with
  | BInf =>
    intro H
    dsimp only [okFrom, bsucc] at H ⊢
    exact ⟨H k (Nat.le_refl _), fun k' hk => H k' (by omega)⟩
  | BFin n =>
    intro H
    dsimp only [okFrom, bsucc] at H ⊢
    exact ⟨H k ⟨Nat.le_refl _, by omega⟩, fun k' hk => H k' ⟨by omega, by omega⟩⟩

/-- `Cert` embeds into `CertWP` with the positional obligations on the certificate's own span. -/
theorem CertWPOfCertPos (img : Image) (dok wok : Int → Nat → Prop) (kind : Dkind)
    (pR pX : (Int → Nat → Prop) → Nat → Prop) (wpin xpin : Nat → Int → List (BitVec 8) → Prop)
    {X : Type} (QE : Cst → Sail.Error exception → ExecSt → Prop) (Q : Cst → X → ExecSt → Prop)
    (s : Cst) (m : SailM X) (t : ExecSt) :
    AxCert.Cert img dok kind QE Q s m t →
    ∀ (ws : List (Nat × Wev)) (k : Nat), okFrom (pR dok) k s.csB → okFrom (pX dok) k s.csB →
    CertWP img dok wok kind pR pX wpin xpin (fun ws' s' _ e t' => ws' = ws ∧ QE s' e t')
      (fun ws' s' _ x t' => ws' = ws ∧ Q s' x t') ws s k m t := by
  intro h
  induction h with
  | cRet s x t HQ => intro ws k _ _; exact .pRet ws s k x t ⟨rfl, HQ⟩
  | cExt s e kk t he => intro ws k _ _; exact .pExt ws s k e kk t ⟨rfl, he⟩
  | cRd s r kk t _ _ ihs ihn =>
    intro ws k HR HX
    exact .pRd ws s k r kk t (fun hp v => ihs hp v ws k HR HX) (fun hp => ihn hp ws k HR HX)
  | cWr s r v kk t hr _ ih => intro ws k HR HX; exact .pWr ws s k r v kk t hr (ih ws k HR HX)
  | cMrd d b r n va req kk t vs h1 h2 h3 h4 _ ih =>
    intro ws k HR HX
    have HR' := (okFromSucc _ _ _ HR).2
    have HX' := (okFromSucc _ _ _ HX).2
    exact .pMrd ws d b r k n va req kk t vs h1 h2 h3 h4 (ih ws (k + 1) HR' HX')
  | cIf s n va req kk t vs h1 h2 h3 h4 _ ih =>
    intro ws k HR HX
    exact .pIf ws s k n va req kk t vs h1 h2 h3 h4 (ih ws k HR HX)
  | cEnd d r n va req kk t h1 h2 h3 =>
    intro ws k _ _; exact .pEnd ws d r k n va req kk t h1 h2 h3
  | cWrEnd d r n va req kk t h1 h2 =>
    intro ws k _ _; exact .pWrEnd ws d r k n va req kk t h1 h2
  | cDrd b r n va req kk t h1 h2 h3 h4 h5 _ ih =>
    intro ws k HR HX
    obtain ⟨HR0, HR'⟩ := okFromSucc _ _ _ HR
    have HX' := (okFromSucc _ _ _ HX).2
    exact .pDrd ws b r k n va req kk t h1 h2 h3 h4 h5 HR0
      (fun vs hl => ih vs hl ws (k + 1) HR' HX')
  | cDwr b r n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    intro ws k HR HX
    have HR' := (okFromSucc _ _ _ HR).2
    have HX' := (okFromSucc _ _ _ HX).2
    exact .pDwr ws b r k n va req kk t v h1 h2 h3 h4 h5 (ih ws (k + 1) HR' HX')
  | cFence d b r bk kk t h1 _ ih =>
    intro ws k HR HX
    have HR' := (okFromSucc _ _ _ HR).2
    have HX' := (okFromSucc _ _ _ HX).2
    exact .pFence ws d b r k bk kk t h1 (ih ws (k + 1) HR' HX')
  | cXrd b r n va req kk t h1 h2 h3 h4 _ ih =>
    intro ws k HR HX
    have HX0 : pX dok k := by
      cases b with
      | BInf => exact HX k (Nat.le_refl _)
      | BFin n0 => exact HX k ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
    exact .pXrd ws b r k n va req kk t h1 h2 h3 h4 HX0 (fun vs hl => ih vs hl ws k HR HX)
  | cXwr aq rvs b r n va req kk t v h1 h2 h3 h4 h5 _ ih =>
    intro ws k HR HX
    have HR' := (okFromSucc _ _ _ HR).2
    have HX' := (okFromSucc _ _ _ HX).2
    exact .pXwr ws aq rvs b r k n va req kk t v h1 h2 h3 h4 h5 (ih ws (k + 1) HR' HX')
  | cIa s n w kk t hs _ ih => intro ws k HR HX; exact .pIa ws s k n w kk t hs (ih ws k HR HX)
  | cSf d b r n w kk t hs _ ih =>
    intro ws k HR HX
    have HR' := (okFromSucc _ _ _ HR).2
    have HX' := (okFromSucc _ _ _ HX).2
    exact .pSf ws d b r k n w kk t hs (ih ws (k + 1) HR' HX')
  | cBa s n a kk t _ ih => intro ws k HR HX; exact .pBa ws s k n a kk t (ih ws k HR HX)
  | cCo s c kk t _ ih => intro ws k HR HX; exact .pCo ws s k c kk t (ih ws k HR HX)
  | cTl s c kk t _ ih => intro ws k HR HX; exact .pTl ws s k c kk t (ih ws k HR HX)
  | cTe s f kk t _ ih => intro ws k HR HX; exact .pTe ws s k f kk t (ih ws k HR HX)
  | cRx s a kk t _ ih => intro ws k HR HX; exact .pRx ws s k a kk t (ih ws k HR HX)
  | cTs s a kk t _ ih => intro ws k HR HX; exact .pTs ws s k a kk t (ih ws k HR HX)
  | cTx s a kk t _ ih => intro ws k HR HX; exact .pTx ws s k a kk t (ih ws k HR HX)
  | cCc s kk t _ ih => intro ws k HR HX; exact .pCc ws s k kk t (ih ws k HR HX)
  | cMsg s a kk t _ ih => intro ws k HR HX; exact .pMsg ws s k a kk t (ih ws k HR HX)
  | cGcc s kk t _ ih => intro ws k HR HX; exact .pGcc ws s k kk t (ih ws k HR HX)

section bridgeP
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- (Lean-only) the walker READ flows at the empty PT region. -/
theorem AxWalk7.wfrEmpty (M : Gdexec → Prop) (i : Agent) :
    ⊢ □ WFrM (GF := GF) M (fun _ _ => False) i (fun _ _ _ => True) (fun _ _ _ => iprop(True)) := by
  unfold WFrM FldM
  imodintro
  iintro %a %GD %ls %k %v %base %n _ _ _ _ %Hr
  exact Hr.1.2.elim

/-- (Lean-only) the walker WRITE-BACK flows at the empty PT region. -/
theorem AxWalk7.wfwEmpty (M : Gdexec → Prop) (i : Agent) :
    ⊢ □ WFwM (GF := GF) M (fun _ _ => False) i (fun _ _ _ => iprop(True)) := by
  unfold WFwM FstM
  imodintro
  iintro %a %GD %ls %k %v %base %n _ _ _ _ %Hr
  exact Hr.1.2.elim

variable (M : Gdexec → Prop)
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Htext : ∀ GD, M GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, M GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, M GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (Out : Nat → List (BitVec 8) → IProp GF)

include HG Hmid Htext Hflow Hloc in
/-- `AxCert2.wpdOfCertM` with the positional obligations on the instruction's own span only —
NO `HnoRmw` / `HnoSplit`. -/
theorem wpdOfCertPosM (Q : Cst → Unit → ExecSt → Prop) (m : SailM Unit) (s : Cst) (t : ExecSt) :
    AxCert.Cert img dok kind (fun _ _ _ => False) Q s m t →
    ∀ rs ib k, regsAgree AxRunClose.pinReg rs t.regs → AxCert2.bpos G i k s.csB →
    okFrom (posR G i dok) k s.csB → okFrom (posX G i dok) k s.csB →
    ⊢ CResM M dok kind i Out s.csD -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResM M dok kind i Out s'.csD -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ := by
  intro HC rs ib k Hag Hb HR HX
  have HP0 := CertWPOfCertPos img dok (fun _ _ => False) kind (posR G i) (posX G i)
    (fun _ _ _ => True) (fun _ _ _ => True) _ _ s m t HC [] k HR HX
  have HP : CertWP img dok (fun _ _ => False) kind (posR G i) (posX G i) (fun _ _ _ => True)
      (fun _ _ _ => True) (fun _ _ _ _ _ => False) (fun ws' s' _ x t' => ws' = [] ∧ Q s' x t')
      [] s k m t :=
    CertWPMono img dok (fun _ _ => False) kind (posR G i) (posX G i) (fun _ _ _ => True)
      (fun _ _ _ => True) _ _ _ _ [] s k m t (fun _ _ _ _ _ h => h.2) (fun _ _ _ _ _ h => h) HP0
  iintro Hd C
  ihave #WFr := AxWalk7.wfrEmpty (GF := GF) M i
  ihave #WFw := AxWalk7.wfwEmpty (GF := GF) M i
  ihave Hw := AxWalk2.wResNil (GF := GF) (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(True))
  ihave H := (wpdOfCertWPM M img dok (fun _ _ => False) kind i Φ cpu G HG Hmid Htext Hflow Hloc
    (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ _ hw _ => hw.elim) Out
    (fun _ _ _ => iprop(True)) (fun _ _ _ => iprop(True)) _ m [] s k t HP rs ib Hag Hb)
    $$ WFr WFw Hd Hw
  iapply H
  iintro %ws' %s' %k' %t' %rs' %ib' %HQ %Hag' %Hb' Hd' _
  iapply C $$ %s' %t' %rs' %ib' %k' %HQ.2 %Hag' %Hb' Hd'

end bridgeP

/-! ### The riscv.cat instance under the Rocq name -/

section bridgePCat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdOfCertPos :
    type_of% (wpdOfCertPosM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdOfCertPosM rvwmoCatConsistent

end bridgePCat

end Weak
