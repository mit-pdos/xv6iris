/-
Weak: **POSITIONAL SIDE CONDITIONS** for the data-read and RMW-read nodes.

Rocq: `iris/AxDataX10.v` @ xxvzwolszwmp.

## The Rocq header, in substance

The region premises `HnoRmw` / `HnoSplit` of `AxCert2` ("no fused RMW row item of hart `i`
ANYWHERE at a data-load address"; "no plain `IRead` row item ANYWHERE at an RMW target") are
FALSE for whole-kernel use (xv6's `holding()` reads the lock word plainly, and the same word is
an amoswap target elsewhere in the row).  The node lemmas only use the premise at the CURRENT row
position `k`, so `wpdDrdNodePosM` restates `AxCert2.wpdDrdNodeM` with the POSITIONAL premise
`Hpos` ("the row item at `k` is not a fused RMW at a `dok` address"), and `wpdXrdNodePosM` the
same for `wpdXrdNodeM` ("the row item at `k` is not a plain read at an RMW target").
`posOfRegionM` recovers the positional form from the region form; `posOfBfinM` derives it under
`Cert`'s `BFin` budget mode, where the position is determined by the row length
(`AxCert2.bpos`: length = `k + n`), from an instance-level fact about the row SUFFIX of length
`n`.  The walker read of `AxDataX9.CertW` (`wWrd`) is meant to be this lemma at `dok := wok`
(with mutable PTs the A/D write-back IS a fused RMW at a `wok` address, so the positional form
is REQUIRED there).

## Deviations from Rocq

1. O2 STAGE C (as `AxCert2` deviation 1): Rocq's section premise `Hntext` is DROPPED (Rocq used
   it only to refute `AStepFetch` at a data read); `wpdDrdNodePosM` instead takes
   `Hnf : (classify req.access_kind).akIfetch = false` (after `Hlat`), exactly as
   `AxCert2.wpdDrdNodeM`.  `Hkind` is kept (unused, as Rocq's `wpd_xrd_node_posM`).
2. AS `AxCert2` deviations 2–4: read answers `.Ok (wordOfBytes n vs, none)`; `regs_agree
   seip_reg` ↦ `regsAgree AxRunClose.pinReg`; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]`
   (any `hlc`); `Interface.ReadReq.t n` ↦ `Mem_read_request n va …` (extra `va`); `N.to_nat n`
   ↦ `n : Nat`; `grow GD i !! k` ↦ `(AxOpsem.grow GD i)[k]?`; `BFin (S n)` ↦ `.BFin (n + 1)`.
   Section variables are `M dok kind i Φ cpu G HG Hmid Out` (Rocq `Mc` … `Hntext` `Out`).
   `posOfRegionM` / `posOfBfinM` drop Rocq's unused `invGS_gen HasNoLc Σ` context (only
   `[AxirisG GF]` is needed).  The riscv.cat instances (Rocq `Definition … := …M rvwmo_cat_consistent`) are theorems typed
   `type_of% (…M rvwmoCatConsistent)`.

**Rocq → Lean name map.**  `wpd_drd_node_posM` `wpdDrdNodePosM`, `wpd_xrd_node_posM`
`wpdXrdNodePosM`, `wpd_drd_node_pos` `wpdDrdNodePos`, `wpd_xrd_node_pos` `wpdXrdNodePos`,
`pos_of_regionM` `posOfRegionM`, `pos_of_bfinM` `posOfBfinM`, `pos_of_region` `posOfRegion`,
`pos_of_bfin` `posOfBfin`.  None is in the duplicated-name table.

**Dropped:** nothing (Rocq 8 definitions/lemmas; Lean 8).  **Not ported:** the `Print
Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxCert2
import Weak.AxDataX9

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

section posC
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (dok : Int → Nat → Prop) (kind : Dkind)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Out : Nat → List (BitVec 8) → IProp GF)

include HG Hmid in
/-- EvD's data read with the POSITIONAL no-fused-RMW premise at `k` (deviation 1: `Hnf`). -/
theorem wpdDrdNodePosM (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (_Hkind : kind = .DKLd)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hdok : dok (paZ req.pa) n)
    (Hpos : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (lb : Lbl) (aq rl : Bool) (base : Int) (m : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base m → ¬ dok base m⌝) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗ FldM M dok i Out -∗
      (∀ (vs : List (BitVec 8)) (rs' : RegFile), ⌜vs.length = n⌝ -∗ ⌜A rs'⌝ -∗ Out k vs -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k + 1⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  unfold FldM dflowO
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
  ihave Hnr := (Hpos GD Hc) $$ Hg
  icases Hnr with %Hnr
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
      %⟨Hdok, lb, _, Hlb, Hl0.symm⟩
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

include HG Hmid in
/-- The RMW read half with the POSITIONAL no-split premise at `k`. -/
theorem wpdXrdNodePosM (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (_Hkind : kind = .DKRmw)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = true)
    (Hdok : dok (paZ req.pa) n)
    (Hpos : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (lb : Lbl) (aq : Bool) (base : Int) (m : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base m → ¬ dok base m⌝) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ (vs : List (BitVec 8)) (rs' : RegFile), ⌜vs.length = n⌝ -∗ ⌜A rs'⌝ -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (wordOfBytes n vs, none))) rs' none ib, k⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  iloeb as IH
  iintro %rs %HP C
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  ihave Hns := (Hpos GD Hc) $$ Hg
  icases Hns with %Hns
  isplit
  · -- (a) the exclusive read
    iintro %id %K %Hst
    obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
    simp only at Hlb
    subst Hid
    obtain ⟨l0, d0, d0', Hl0, -, Hps0, -⟩ :=
      HK (List.replicate (aidentN (aident lb)) 0) List.length_replicate
    obtain ⟨tvs0, Htl0, rfl, -⟩ := xreadPstep cpu n va req KK rs ib d0 _ _ d0' Hdev Hlat Hps0
    simp only [wlRd, Htl0] at Hl0
    -- the SPLIT matching (a plain `IRead` row item) is refuted
    have Had : aidentAdvRd (aident lb) = 0 := by
      cases hid : aident lb with
      | IRead aq base n' =>
        exfalso
        rw [hid] at Hl0
        simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hl0
        obtain ⟨-, hb, hn⟩ := Hl0
        subst hb
        subst hn
        exact Hns lb aq _ _ Hlb hid Hdok
      | IRmw _ _ _ _ => rfl
      | IWrite _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
      | IFence _ _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
    simp only [Had, Nat.zero_ne_one, ↓reduceIte]
    -- the FUSED matching: a skip step at the same position
    iintro %v %Hv %Hlenv
    obtain ⟨l, d, d', -, Hrv, Hps, Hk'⟩ := HK v Hlenv
    obtain ⟨tvs, Htl, rfl, Hp'⟩ := xreadPstep cpu n va req KK rs ib d _ _ d' Hdev Hlat Hps
    simp only [wlRvals] at Hrv
    subst Hrv
    rw [Had] at Hk'
    have hKv : K (tvs.map Prod.snd) =
        ⟨.PHart cpu (KK (.Ok (wordOfBytes n (tvs.map Prod.snd), none))) rs none ib, k⟩ := by
      cases hK : K (tvs.map Prod.snd) with
      | AThread p' k' =>
        rw [hK] at Hp' Hk'
        simp only [Nat.add_zero] at Hp' Hk'
        rw [Hp', Hk']
    rw [hKv]
    unfold wpSkipStep
    iintro %na Hna
    imodintro
    inext
    imodintro
    iexists ls
    iframe Hna Hloc
    iapply C $$ %(tvs.map Prod.snd) %rs
    · ipureintro
      rw [List.length_map]
      exact Htl
    · ipureintro
      exact HP
  isplit
  · -- (b) no program step at an exclusive read
    iintro %l %s' %Hst %Hpin
    exact (AxCert2.xreadAstepFalse _ cpu n va req KK rs ib k l s' Hdev Hlat Hst).elim
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
      iapply IH $$ %rs' %(HA rs rs' HP hag) C
  · iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

end posC

/-! riscv.cat instances under the OLD NAMES -/
section posCCat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdDrdNodePos :
    type_of% (wpdDrdNodePosM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdDrdNodePosM rvwmoCatConsistent

theorem wpdXrdNodePos :
    type_of% (wpdXrdNodePosM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdXrdNodePosM rvwmoCatConsistent

end posCCat

section posLemmas
variable {GF : BundledGFunctors} [AxirisG GF]

/-- The region form implies the positional one at every `k`. -/
theorem posOfRegionM (M : Gdexec → Prop) (dok : Int → Nat → Prop) (i : Agent) (k : Nat) :
    (∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝) →
    ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (lb : Lbl) (aq rl : Bool) (base : Int) (m : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base m → ¬ dok base m⌝ := by
  intro H GD Hc
  iintro Hg
  ihave Hr := (H GD Hc) $$ Hg
  icases Hr with %Hr
  ipureintro
  exact Hr k

/-- Under `BFin`: the position of the node is `length row - (n + 1)`. -/
theorem posOfBfinM (M : Gdexec → Prop) (dok : Int → Nat → Prop) (i : Agent)
    (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (k n : Nat) :
    AxCert2.bpos G i k (.BFin (n + 1)) →
    (∀ GD, G GD → ∀ (lb : Lbl) (aq rl : Bool) (base : Int) (m : Nat),
      (AxOpsem.grow GD i)[(AxOpsem.grow GD i).length - (n + 1)]? = some lb →
      aident lb = .IRmw aq rl base m → ¬ dok base m) →
    ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (lb : Lbl) (aq rl : Bool) (base : Int) (m : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base m → ¬ dok base m⌝ := by
  intro Hb Hsuf GD Hc
  iintro Hg
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  ipureintro
  intro lb aq rl base m Hlb Hid
  refine Hsuf GD HGD lb aq rl base m ?_ Hid
  have hlen : (AxOpsem.grow GD i).length = k + (n + 1) := Hb GD HGD
  rw [hlen, show k + (n + 1) - (n + 1) = k by omega]
  exact Hlb

theorem posOfRegion :
    type_of% (posOfRegionM (GF := GF) rvwmoCatConsistent) :=
  posOfRegionM rvwmoCatConsistent

theorem posOfBfin :
    type_of% (posOfBfinM (GF := GF) rvwmoCatConsistent) :=
  posOfBfinM rvwmoCatConsistent

end posLemmas

end Weak
