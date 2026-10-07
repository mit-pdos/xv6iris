/-
Weak: **THE POSITIONAL node rules** — `AxCert2`'s RMW read half and EvD data read with the
whole-row no-RMW / no-split premises replaced by their instance at the node's own row position.

Rocq: `iris/AxCertP.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`AxCert2.wpdDrdNodeM` takes its no-RMW refutation from the section premise `HnoRmw` (no fused
`IRmw` row item of hart `i` on the read's bytes AT ANY row position), but the proof uses it at
exactly ONE place: the degenerate matching of the plain read's label against the row item at the
node's own position `k` with `aidentAdvRd = 0`.  Nothing else (rf/co, consistency, RMW atomicity
elsewhere) is used: the whole-row form is an artefact of the `Cert` bridge sharing one premise,
not a soundness requirement — a row with acquire's `amoswap.w.aq lk` at `kA ≠ k` is harmless for
a plain read at `k`.
- `wpdDrdNodeP` = `wpdDrdNodeM` with `HnoRmw` replaced by the POSITIONAL `HnoRmwK` (no fused
  `IRmw` row item on the read's bytes AT `k`);
- `wpdXrdNodeP` = the same fix for the RMW arm's read half (`AxCert2.wpdXrdNodeM`): its whole-row
  `HnoSplit` (false on a row where `holding()` plainly reads `lk->locked`) is used only at `k`;
  `HnoSplitK` states exactly that instance.
NOT HERE (Rocq's open step): the `Cert` bridge still threads the whole-row `HnoRmw`, since a
generic `Cert` does not bound the position of its data read (`cEnd` lets a path run past the
instruction's window).

## Deviations from Rocq

1. O2 STAGE C (as `AxCert2` deviation 1): Rocq's section premise `Hntext` is DROPPED (it only
   refuted `AStepFetch` at a data read); `wpdDrdNodeP` takes `Hnf : akIfetch = false` after
   `Hlat`, as `AxCert2.wpdDrdNodeM`.  `wpdXrdNodeP` needs nothing (an `akLatest` access is not a
   fetch, `AxCert2.nfOfLatest`).
2. As `AxCert2` deviations 2–4: read answers `.Ok (wordOfBytes n vs, none)`; `regs_agree seip_reg`
   ↦ `regsAgree AxRunClose.pinReg`; `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`);
   Lean read requests `Mem_read_request n va …` (extra `va`); `grow GD i !! k` ↦
   `(AxOpsem.grow GD i)[k]?`.  The positional premises are lemma arguments after `HA` (as in
   Rocq).  Section variables: `M dok i Φ cpu G HG Hmid Out` (Rocq's order minus `Hntext`).

**Rocq → Lean name map.**  `wpd_xrd_nodeP` `wpdXrdNodeP`, `wpd_drd_nodeP` `wpdDrdNodeP`.

**Dropped:** nothing (Rocq 2 lemmas; Lean 2).  **Not ported:** the `Print Assumptions` lines (the
lint's axiom check covers them).
-/
import Weak.AxCert2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

section drdP
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (dok : Int → Nat → Prop)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Out : Nat → List (BitVec 8) → IProp GF)

include HG Hmid in
/-- THE RMW ARM, read half, POSITIONAL no-split premise (at `k` only). -/
theorem wpdXrdNodeP (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (HnoSplitK : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (lb : Lbl) (aq : Bool) (base : Int) (n' : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n' → ¬ dok base n'⌝)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = true)
    (Hdok : dok (paZ req.pa) n) :
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
  ihave Hns := (HnoSplitK GD Hc) $$ Hg
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

include HG Hmid in
/-- EvD's data read at row position `k`, POSITIONAL no-RMW premise (deviation 1: `Hnf`). -/
theorem wpdDrdNodeP (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (HnoRmwK : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (lb : Lbl) (aq rl : Bool) (base : Int) (n' : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n' → ¬ dok base n'⌝)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hdok : dok (paZ req.pa) n) :
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
  ihave Hnr := (HnoRmwK GD Hc) $$ Hg
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

end drdP

end Weak
