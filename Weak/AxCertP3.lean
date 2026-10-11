/-
Weak: **THE WINDOW-RESTRICTED flow resource** `FldMW` threaded through the window-bounded
`Cert` bridge.

Rocq: `iris/AxCertP3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

WHY.  `AxCertP2.wpdOfCertP` bounds the data read's position inside the instruction's window for
its no-RMW premise, but its pending data resource is still `FldM`: a flow at EVERY row position
that reads the data bytes.  For holding's lock-word load the row also holds acquire's
`amoswap.w.aq lk`, where no flow rule applies, so a client cannot supply `FldM`.  The data read
happens at a position `kk` with `k0 ≤ kk` and `kk + c < length` (AxCertP2's `FamDrd` + `bpos`),
so the flow is only ever demanded INSIDE the window.

WHAT.  `FldMW M dok i Out lo hi` = `FldM` restricted to positions `lo ≤ k < hi` (one extra pure
premise); `FldMToW : FldM ⊢ FldMW`.  `wpdDrdNodeW` = `AxCertP.wpdDrdNodeP` consuming `FldMW`
with a positional premise `Hwin`.  `CResW` = `CResK` whose `CPend` load arm is `FldMW k0 hi`.
`wpdOfCertW` / `wpdInstrOfCertW` = `AxCertP2.wpdOfCertP` / `wpdInstrOfCertP` over `CResW`, with
one new premise `Hhi`: every `G`-graph's row has `length ≤ hi + c` (so `kk + c < length` gives
`kk < hi`).  Proofs are the originals' (the Lean ones) with the data-read arm changed.

## Deviations from Rocq

1. O2 STAGE C (as `AxCertP` / `AxCertP2` deviation 1): Rocq's section premise `Hntext` is
   DROPPED (in the node rule and in the bridge); `wpdDrdNodeW` takes `Hnf : akIfetch = false`
   after `Hlat`.  The bridge has the `cIf` (image fetch) arm of `AxCertP2.wpdOfCertP`.
   Q19: the bridge has the `cSf` (sfence.vma announce) arm of `AxCertP2.wpdOfCertP`
   (`AxCert2.wpdSfNodeM`, `cResWSucc`, `AxCertP2.PFSf`); Rocq has no such constructor.
2. As `AxCertP2` deviations 2–4: lean-sail outcomes (read answers
   `.Ok (wordOfBytes n vs, none)`), `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`,
   `[InvGS_gen hlc GF]` (any `hlc`), `Interface.Ret tt` ↦ `.pure ()`, `S n` ↦ `n + 1`,
   `(lo ≤ k < hi)` ↦ `lo ≤ k ∧ k < hi`.  Section variables are explicit arguments: the node rule
   takes `M dok i Φ cpu G HG Hmid Out lo hi` then Rocq's lemma arguments (+ `Hnf`); the bridge
   takes `img dok kind i Φ cpu G HG Hmid Htext Hflow Hloc Out k0 c hi Hhi HnoRmwW HnoSplitW`.
   `CFkW`/`CResW` take `dok kind i Out k0 hi` (Rocq's section order).
3. The Ltac `silent_psP` is replaced by inline inversions (as `AxCertP2.wpdOfCertP`).

**Rocq → Lean name map.**  `FldMW` `FldMW`, `FldM_W` `FldMToW` (the camelCase `FldMW` is the
definition), `wpd_drd_nodeW` `wpdDrdNodeW`, `CFkW` `CFkW`, `CResW` `CResW`, `CResW_succ`
`cResWSucc`, `wpd_of_CertW` `wpdOfCertW`, `wpd_instr_of_CertW` `wpdInstrOfCertW`.

**Dropped:** nothing (Rocq 8 definitions/lemmas; Lean 8).  **Not ported:** the Ltac `silent_psP`
(deviation 3), the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxCertP2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! # 1. The window-restricted flow resource and its node rule -/

section fldW
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `FldM` restricted to the row positions `lo ≤ k < hi`. -/
def FldMW (M : Gdexec → Prop) (dok : Int → Nat → Prop) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (lo hi : Nat) : IProp GF :=
  iprop(∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (k : Nat) (v : List (BitVec 8)) (base : Int)
      (n : Nat),
    ⌜M GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
    ⌜graphValue GD (i, k) = some v⌝ -∗ ⌜dok base n ∧ rowRd i GD k base n⌝ -∗
    ⌜lo ≤ k ∧ k < hi⌝ -∗ dflowO i GD k (Out k v))

theorem FldMToW (M : Gdexec → Prop) (dok : Int → Nat → Prop) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (lo hi : Nat) :
    FldM M dok i Out ⊢ FldMW M dok i Out lo hi := by
  unfold FldM FldMW
  iintro F %GD %ls %k %v %base %n %Hc #Hg Hl %Hv %Hd %_
  iapply F $$ %GD %ls %k %v %base %n %Hc Hg Hl %Hv %Hd

end fldW

section drdW
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (dok : Int → Nat → Prop)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Out : Nat → List (BitVec 8) → IProp GF) (lo hi : Nat)

include HG Hmid in
/-- `AxCertP.wpdDrdNodeP` consuming the WINDOW-RESTRICTED `FldMW` with the positional premise
`Hwin` (the node's `k` is in the window `[lo, hi)`). -/
theorem wpdDrdNodeW (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (HnoRmwK : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (lb : Lbl) (aq rl : Bool) (base : Int) (n' : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n' → ¬ dok base n'⌝)
    (Hwin : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜lo ≤ k ∧ k < hi⌝)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hdok : dok (paZ req.pa) n) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗ FldMW M dok i Out lo hi -∗
      (∀ (vs : List (BitVec 8)) (rs' : RegFile), ⌜vs.length = n⌝ -∗ ⌜A rs'⌝ -∗ Out k vs -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k + 1⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  unfold FldMW dflowO
  iloeb as IH
  iintro %rs %HP F C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  ihave Hnr := (HnoRmwK GD Hc) $$ Hg
  icases Hnr with %Hnr
  ihave Hw := (Hwin GD Hc) $$ Hg
  icases Hw with %Hw
  isplit
  · -- (a) THE DATA READ, demonic
    iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    subst Hid
    obtain ⟨l0, d0, d0', Hl0, -, Hps0, -⟩ :=
      HK (List.replicate (aidentN (aident lb)) 0) List.length_replicate
    obtain ⟨tvs0, Htl0, rfl, -⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d0 _ _ d0' Hdev Hlat Hnf Hps0
    simp only [wlRd, Htl0] at Hl0
    have Hadv0 : aidentAdvRd (aident lb) = 1 := by
      cases hid : aident lb with
      | IRmw aq rl base n' =>
        exfalso
        rw [hid] at Hl0
        simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hl0
        obtain ⟨-, hb, hn⟩ := Hl0
        subst hb
        subst hn
        exact Hnr lb aq rl _ _ Hlb hid Hdok
      | IRead _ _ _ => rfl
      | IWrite _ _ _ => rfl
      | IFence _ _ _ _ => rfl
      | IIo _ _ _ => rfl
    simp only [Hadv0, ↓reduceIte]
    iintro %v %Hv %Hlenv
    obtain ⟨l, d, d', -, Hrv, Hps, Hk'⟩ := HK v Hlenv
    obtain ⟨tvs, Htl, rfl, Hp'⟩ :=
      AxLdspWpd.loadStepInv cpu n va req KK rs ib d _ _ d' Hdev Hlat Hnf Hps
    simp only [wlRvals] at Hrv
    subst Hrv
    rw [Hadv0] at Hk'
    have hKv : K (tvs.map Prod.snd) =
        ⟨.PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib, k + 1⟩ := by
      cases hK : K (tvs.map Prod.snd) with
      | AThread p' k' =>
        rw [hK] at Hp' Hk'
        simp only at Hp' Hk'
        rw [Hp', Hk']
    rw [hKv]
    unfold wpEvStep
    iintro %na Hpg
    ihave Hf := F $$ %GD %ls %k %(tvs.map Prod.snd) %(paZ req.pa) %n %Hc Hg Hloc %Hv
      %⟨Hdok, lb, _, Hlb, Hl0.symm⟩ %Hw
    imod Hf $$ %na Hpg with Hf
    imodintro
    inext
    imod Hf with ⟨%R, %nu, %nuu, %ls', Hs, Hfe, Hna, Hl, HO⟩
    imodintro
    iexists (), R, nu, nuu, ls'
    isplitr
    · ipureintro
      trivial
    iframe Hs Hna Hl
    isplitl [Hfe]
    · iapply (flowEqDynMono GD (i, k) _ nu R
        iprop(R ∗ ⌜graphValue GD (i, k) = some (tvs.map Prod.snd)⌝))
      · inext
        iintro HR
        iframe HR
        ipureintro
        exact Hv
      · iexact Hfe
    · iapply C $$ %(tvs.map Prod.snd) %rs
      · ipureintro
        rw [List.length_map]
        exact Htl
      · ipureintro
        exact HP
      · iexact HO
  isplit
  · -- (b) no program step at a data read (`akIfetch = false`: no admin fetch)
    iintro %l %s' %Hst %Hpin
    have hfalse : False := by
      obtain ⟨d, d', hps⟩ := astepProgPstep _ _ _ _ Hst
      obtain ⟨tvs, -, hl, -⟩ :=
        AxLdspWpd.loadStepInv cpu n va req KK rs ib d l _ d' Hdev Hlat Hnf hps
      subst hl
      cases Hst with
      | AStepAdmin _ _ _ _ _ _ hadm _ => exact hadm
      | AStepWrite _ _ _ _ _ _ _ _ hwr _ _ _ => simp [wlWr] at hwr
      | AStepFence _ _ _ _ _ _ _ _ hf _ _ => simp [wlFence] at hf
    exact hfalse.elim
  isplit
  · -- (c) the PLIC wire
    iintro %s' %Hw
    obtain ⟨hk, hp⟩ := awireAeqv _ _ Hw
    obtain ⟨p', k'⟩ := s'
    simp only at hk hp
    subst hk
    match p', hp with
    | .PHart c m' rs' fn' ib', hp =>
      obtain ⟨rfl, rfl, rfl, rfl, hag⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' %(HA rs rs' HP hag) F C
  · iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

end drdW

/-! # 2. The data resource and the bridge -/

section resW
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The pending data resource: a load's flow only inside the window `[k0, hi)`. -/
def CFkW (dok : Int → Nat → Prop) (kind : Dkind) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (k0 hi : Nat) : IProp GF :=
  match kind with
  | .DKLd => FldMW rvwmoCatConsistent dok i Out k0 hi
  | _ => FstM rvwmoCatConsistent dok i Out

/-- `CResK` with the window-restricted pending load resource. -/
def CResW (dok : Int → Nat → Prop) (kind : Dkind) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (k0 hi : Nat) (d : Cdata) (kc : Nat) : IProp GF :=
  match d with
  | .CPend => CFkW dok kind i Out k0 hi
  | .CRmwR _ _ => FstM rvwmoCatConsistent dok i Out
  | .CLd vs | .CSt vs _ | .CRmw _ _ _ vs _ => iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kc⌝ ∗ Out kd vs)

theorem cResWSucc (dok : Int → Nat → Prop) (kind : Dkind) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (k0 hi : Nat) (d : Cdata) (kc : Nat) :
    CResW dok kind i Out k0 hi d kc ⊢ CResW dok kind i Out k0 hi d (kc + 1) := by
  cases d with
  | CPend => exact .rfl
  | CRmwR _ _ => exact .rfl
  | CLd vs | CSt vs _ | CRmw _ _ _ vs _ =>
    simp only [CResW]
    iintro ⟨%kd, %Hk, H⟩
    iexists kd
    isplitr
    · ipureintro
      omega
    iexact H

end resW

section bridgeW
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
variable (Out : Nat → List (BitVec 8) → IProp GF) (k0 c hi : Nat)
/- the window's upper end: every `G`-row has length at most `hi + c`. -/
variable (Hhi : ∀ GD, G GD → (AxOpsem.grow GD i).length ≤ hi + c)
/- THE WINDOW PREMISES: only positions `k0 ≤ k < length − c`. -/
variable (HnoRmwW : kind = .DKLd → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat), k0 ≤ k →
    k + c < (AxOpsem.grow GD i).length →
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)
variable (HnoSplitW : kind = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat), k0 ≤ k →
    k + c < (AxOpsem.grow GD i).length →
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)

include HG Hmid Htext Hflow Hloc Hhi HnoRmwW HnoSplitW in
/-- `AxCertP2.wpdOfCertP` over `CResW`; only the data-read arm changes (`wpdDrdNodeW`). -/
theorem wpdOfCertW (Q : Cst → Unit → ExecSt → Prop) (m : SailM Unit) (s : Cst)
    (t : ExecSt) :
    AxCert.Cert img dok kind (fun _ _ _ => False) Q s m t → PF img dok kind c s m t →
    ∀ rs ib kk, regsAgree AxRunClose.pinReg rs t.regs → AxCert2.bpos G i kk s.csB → k0 ≤ kk →
    ⊢ CResW dok kind i Out k0 hi s.csD kk -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ ⌜k0 ≤ k'⌝ -∗ CResW dok kind i Out k0 hi s'.csD k' -∗
         wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu m rs none ib, kk⟩ Φ := by
  intro H
  induction H with
  | cRet s x t HQ =>
    intro _ rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply C $$ %s %t %rs %ib %kk %HQ %Hag %Hb %Hk0 Hd
  | cExt s e k t he => exact he.elim
  | cRd s r k t _ _ IHs IHn =>
    intro HPF rs ib kk Hag Hb Hk0
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
      · iapply (IHs Hs (rs1 r) (PFRds img dok kind (rs1 r) Hs HPF) rs1 ib1 kk HA1 Hb Hk0) $$ Hd C
      · have h := IHn Hs (PFRdn img dok kind Hs HPF) rs1 ib1 kk HA1 Hb Hk0
        rw [← HA1 r Hs] at h
        iapply h $$ Hd C
  | cWr s r v k t Hr _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
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
      iapply (IH (PFWr img dok kind HPF) (rs1.set r v) ib1 kk (regsAgreeSet _ _ _ r v HA1) Hb
        Hk0) $$ Hd C
  | cMrd d b r n va req k t vs Hdev Hlat Hnf Hvs _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdImgRead3M rvwmoCatConsistent img i Φ cpu G HG Hmid Htext Hflow n va
      req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    ihave Hd := (cResWSucc dok kind i Out k0 hi d kk) $$ Hd
    iapply (IH (PFMrd img dok kind Hlat Hnf Hvs HPF) rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)
      (by omega)) $$ Hd C
  | cIf s n va req k t vs Hdev Hlat Hfe Hvs _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdImgFetch3M rvwmoCatConsistent img i Φ cpu G HG Hmid Htext n va req k
      ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hfe Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH (AxCertP2.PFIf img dok kind Hfe Hvs HPF) rs' ib kk HA' Hb Hk0) $$ Hd C
  | cEnd d r n va req k t Hdev Hlat Hnf =>
    intro _ rs ib kk Hag Hb _
    have Hb' : ∀ GD, G GD → (AxOpsem.grow GD i).length = kk + 0 := Hb
    iintro - -
    iapply (wpdStuckReadM rvwmoCatConsistent i Φ cpu G HG Hmid kk (fun GD h => Hb' GD h) n va req
      k ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf rs Hag)
  | cWrEnd d r n va req k t Hdev Hlat =>
    intro _ rs ib kk Hag Hb _
    have Hb' : ∀ GD, G GD → (AxOpsem.grow GD i).length = kk + 0 := Hb
    iintro - -
    iapply (AxCert2.wpdStuckWriteM rvwmoCatConsistent i Φ cpu G HG Hmid kk (fun GD h => Hb' GD h) n va req k ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat rs Hag)
  | cDrd b r n va req k t Hkd Hdev Hlat Hnf Hdok _ IH =>
    -- THE DATA READ: positioned inside the window
    intro HPF rs ib kk Hag Hb Hk0
    obtain ⟨a, Ha, HF⟩ := HPF rfl
    obtain ⟨b', rfl⟩ : ∃ b', b = .BFin b' := by
      cases b with
      | BInf => cases Ha
      | BFin b' => exact ⟨b', rfl⟩
    simp only [bsucc, Bud.BFin.injEq] at Ha
    subst Ha
    have Hca := FamDrd img dok kind HF Hlat Hnf
    have HnoRmwK : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜∀ (lb : Lbl) (aq rl : Bool) (base : Int) (n' : Nat),
          (AxOpsem.grow GD i)[kk]? = some lb → aident lb = .IRmw aq rl base n' → ¬ dok base n'⌝ := by
      intro GD Hc
      refine (BI.and_intro (HG GD Hc) (HnoRmwW Hkd GD Hc)).trans ?_
      iintro ⟨%HGD, %Hw⟩
      ipureintro
      intro lb aq rl base n' Hlb Hid
      have E : (AxOpsem.grow GD i).length = kk + (b' + 1) := Hb GD HGD
      exact Hw kk lb aq rl base n' Hk0 (by omega) Hlb Hid
    have HwinK : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜k0 ≤ kk ∧ kk < hi⌝ := by
      intro GD Hc
      refine (HG GD Hc).trans ?_
      iintro %HGD
      ipureintro
      have E : (AxOpsem.grow GD i).length = kk + (b' + 1) := Hb GD HGD
      have := Hhi GD HGD
      omega
    have hconv : CResW dok kind i Out k0 hi .CPend kk ⊢
        FldMW rvwmoCatConsistent dok i Out k0 hi := by
      subst Hkd
      exact .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdDrdNodeW rvwmoCatConsistent dok i Φ cpu G HG Hmid Out k0 hi n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) HnoRmwK HwinK Hdev Hlat Hnf Hdok)
      $$ %rs %Hag Hd
    iintro %vs %rs' %Hlen %HA' HO
    have hdone : iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kk + 1⌝ ∗ Out kd vs) ⊢
        CResW dok kind i Out k0 hi (.CLd vs) (kk + 1) := .rfl
    iapply (IH vs Hlen (fun h => by cases h) rs' ib (kk + 1) HA' (bposSucc G i kk (.BFin b') Hb)
      (by omega)) $$ [HO] C
    iapply hdone
    iexists kk
    isplitr
    · ipureintro
      omega
    iexact HO
  | cDwr b r n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    intro _ rs ib kk Hag Hb Hk0
    have hconv : CResW dok kind i Out k0 hi .CPend kk ⊢ FstM rvwmoCatConsistent dok i Out := by
      subst Hkd
      exact .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdDwrNodeM rvwmoCatConsistent dok i Φ cpu G HG Hmid Out n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %HA' HO
    have hdone : iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kk + 1⌝ ∗ Out kd (WeakInterpProj.wbytes n v)) ⊢
        CResW dok kind i Out k0 hi (.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind r))
          (kk + 1) := .rfl
    iapply (IH (fun h => by cases h) rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega))
      $$ [HO] C
    iapply hdone
    iexists kk
    isplitr
    · ipureintro
      omega
    iexact HO
  | cFence d b r bk k t Hpark _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (wpdFenceNodeM rvwmoCatConsistent i Φ cpu G HG Hmid Hloc bk k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hpark) $$ %rs %Hag
    iintro %rs' %HA'
    ihave Hd := (cResWSucc dok kind i Out k0 hi d kk) $$ Hd
    iapply (IH (PFFence img dok kind HPF) rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega))
      $$ Hd C
  | cXrd b r n va req k t Hkd Hdev Hlat Hdok _ IH =>
    -- THE EXCLUSIVE READ: positioned inside the window
    intro HPF rs ib kk Hag Hb Hk0
    obtain ⟨a, Ha, HF⟩ := HPF rfl
    simp only at Ha
    subst Ha
    have Hca := FamXrd img dok kind HF Hlat
    have HnoSplitK : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜∀ (lb : Lbl) (aq : Bool) (base : Int) (n' : Nat),
          (AxOpsem.grow GD i)[kk]? = some lb → aident lb = .IRead aq base n' → ¬ dok base n'⌝ := by
      intro GD Hc
      refine (BI.and_intro (HG GD Hc) (HnoSplitW Hkd GD Hc)).trans ?_
      iintro ⟨%HGD, %Hw⟩
      ipureintro
      intro lb aq base n' Hlb Hid
      have E : (AxOpsem.grow GD i).length = kk + a := Hb GD HGD
      exact Hw kk lb aq base n' Hk0 (by omega) Hlb Hid
    iintro Hd C
    iapply (wpdXrdNodeP rvwmoCatConsistent dok i Φ cpu G HG Hmid n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) HnoSplitK Hdev Hlat Hdok) $$ %rs %Hag
    iintro %vs %rs' %Hlen %HA'
    have hconv : CResW dok kind i Out k0 hi .CPend kk ⊢
        CResW dok kind i Out k0 hi (.CRmwR (classify req.access_kind).akSync vs) kk := by
      subst Hkd
      exact .rfl
    ihave Hd := hconv $$ Hd
    iapply (IH vs Hlen (fun h => by cases h) rs' ib kk HA' Hb Hk0) $$ Hd C
  | cXwr aq rvs b r n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    intro _ rs ib kk Hag Hb Hk0
    have hconv : CResW dok kind i Out k0 hi (.CRmwR aq rvs) kk ⊢
        FstM rvwmoCatConsistent dok i Out := .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdXwrNodeM rvwmoCatConsistent dok i Φ cpu G HG Hmid Out n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %HA' HO
    have hdone : iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kk + 1⌝ ∗ Out kd (WeakInterpProj.wbytes n v)) ⊢
        CResW dok kind i Out k0 hi (.CRmw aq (classify req.access_kind).akSync rvs
          (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) (kk + 1) := .rfl
    iapply (IH (fun h => by cases h) rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega))
      $$ [HO] C
    iapply hdone
    iexists kk
    isplitr
    · ipureintro
      omega
    iexact HO
  | cIa s n w k t Hsf _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M rvwmoCatConsistent i Φ cpu G HG Hmid _ (k ()) ?_ kk t ?_
      rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      rw [annLabelNot Hsf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH (PFSil' img dok kind HPF (fun _ _ H => Or.elim H And.right
        (fun h => absurd (Hsf.symm.trans h.1) Bool.false_ne_true))) rs1 ib1 kk HA1 Hb Hk0) $$ Hd C
  | cSf d b r n w k t Hsf _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxCert2.wpdSfNodeM rvwmoCatConsistent i Φ cpu G HG Hmid Hloc n w k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hsf) $$ %rs %Hag
    iintro %rs' %ib' %HA'
    ihave Hd := (cResWSucc dok kind i Out k0 hi d kk) $$ Hd
    iapply (IH (AxCertP2.PFSf img dok kind Hsf HPF) rs' ib' (kk + 1) HA' (bposSucc G i kk b Hb)
      (by omega)) $$ Hd C
  | cBa s _ _ k t _ IH | cCo s _ k t _ IH | cTl s _ k t _ IH | cTe s _ k t _ IH
  | cRx s _ k t _ IH | cTs s _ k t _ IH | cTx s _ k t _ IH | cCc s k t _ IH
  | cMsg s _ k t _ IH | cGcc s k t _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M rvwmoCatConsistent i Φ cpu G HG Hmid _ _ ?_ kk t ?_
      rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      exact ⟨trivial, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH (PFSil' img dok kind HPF (fun _ _ H => H)) rs1 ib1 kk HA1 Hb Hk0) $$ Hd C

include HG Hmid Htext Hflow Hloc Hhi HnoRmwW HnoSplitW in
/-- `AxCertP2.wpdInstrOfCertP` over `CResW`. -/
theorem wpdInstrOfCertW (Q : Cst → Unit → ExecSt → Prop) (s0 : Cst) (rs : RegFile)
    (s : Athread) (Hs : RetX cpu rs k0 s)
    (Hbp : AxCert2.bpos G i k0 s0.csB)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k0 s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       AxCert.Cert img dok kind (fun _ _ _ => False) Q s0 (riscvStep tick) t)
    (HPF : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       PF img dok kind c s0 (riscvStep tick) t) :
    ⊢ CResW dok kind i Out k0 hi s0.csD k0 -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResW dok kind i Out k0 hi s'.csD k' -∗
         wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  iintro Hd C
  iapply (wpdRetNode3M rvwmoCatConsistent i Φ cpu G HG rs k0 s Hs Hb)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  iapply (wpdOfCertW img dok kind i Φ cpu G HG Hmid Htext Hflow Hloc Out k0 c hi Hhi HnoRmwW
    HnoSplitW Q _ s0 ⟨rs', fun _ => none, testDevs⟩
    (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag))
    (HPF tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone k0
    (regsAgreeRefl _ _) Hbp (Nat.le_refl _)) $$ Hd
  iintro %s' %t' %rs1 %ib' %k' %HQ %Hag' %Hbp' %_ Hd
  iapply C $$ %s' %t' %rs1 %ib' %k' %HQ %Hag' %Hbp' Hd

end bridgeW

end Weak
