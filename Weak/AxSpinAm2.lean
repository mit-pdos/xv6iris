/-
Weak: **acquire's AMOSWAP on the POSITIONAL ENGINE, part 2**: the PINNED, WINDOW-RESTRICTED
`Cert` bridge for an RMW instruction.

Rocq: `iris/AxSpinAm2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

WHY.  `wpdOfCertW` (AxCertP3, the positional bridge the load leaf `AxSpinXP2.XxLdW` runs on) has
two defects for acquire's `amoswap.w.aq`:
(1) its RMW data resource is the position-GENERIC `FstM`: a write flow at EVERY row position that
    writes the lock word — on a row that also runs release's `sw zero, (lk)` (WCrel, needs
    `locked` and the protected resources) no client can supply it;
(2) the exclusive read half is answered demonically and the equation "read bytes = the graph
    value of the fused RMW item" is FORGOTTEN, so the continuation's `rd = amoLdv 4 vs` says
    nothing about the lock word the graph read.
`AxCondM2` fixed (2) for the BInf bridge with a PIN; this file ports that pin to the positional
bridge and fixes (1) the way AxCertP3 fixed loads: the write flow `FstRmwW … lo hi` is demanded
only at positions `lo ≤ k < hi`.  The write's position is in the window because the PIN fixes it:
the exclusive read at `kk` has `kk < hi` (`FamXrd` + `bpos` + `Hhi`); the pin says row item `kk`
IS the fused `IRmw`, which refutes an image read or a fence at `kk` (`wpdPinMread` /
`wpdPinFence`), so the write half happens at the same `kk`.

§1 `FstRmwW` (+ `FstMToW`); node lemmas `wpdXwrNodeW` (`wpdXwrNodeM` consuming `FstRmwW` at a
   node inside the window) and `wpdXrdPinP` (`wpdXrdPin` with its whole-row `HnoSplit` replaced
   by the instance at the node's own position, as `AxCertP.wpdXrdNodeP`).
§2 the bridge, kind fixed to `DKRmw`: data resource `CResWP d kc` (`CPend ↦ FstRmwW`,
   `CRmwR aq rvs ↦ FstRmwW ∗ Pin kc rvs ∗ ⌜k0 ≤ kc < hi⌝`,
   `CRmw … rvs wvs … ↦ ∃ kd, ⌜k0 ≤ kd < kc⌝ ∗ Out kd wvs ∗ Pin kd rvs`);
   `AxSpinAm2.wpdOfCertWP` / `AxSpinAm2.wpdInstrOfCertWP` = AxCertP3's with that resource; new
   premises `Hagree` (graph agreement — AxCondM2's) and `HGex` (some graph satisfies `G`: the
   window bound is a pure fact).

## Deviations from Rocq

1. O2 STAGE C (as `AxCertP3` deviation 1): no `Hntext`; `Cert.cMrd` is a graph image read with
   `akIfetch = false` (`wpdPinMread` / `AxSymEngine3.wpdImgRead3M` take `Hnf`).  The Lean-only
   `Cert.cIf` arm (an image FETCH: an admin step at the SAME row position) is
   `AxSymEngine3.wpdImgFetch3M` in every data state — the pin stays valid at the same `kk`.
   Q19: the `Cert.cSf` arm (an SFENCE.VMA announce, one row item) is `AxCert2.wpdSfNodeM` +
   `cResWPSucc` off the pinned state and `AxCondM2.wpdPinSf` at a pinned state (twin of the
   fence arm); Rocq has no such constructor.
2. As `AxCertP3` deviation 2 / `AxCondM2` deviations 2–3: lean-sail outcomes (read answers
   `.Ok (wordOfBytes n vs, none)`, write values `req.value = some v`, written bytes
   `WeakInterpProj.wbytes n v`, write answer `.Ok (some true)`), `regs_agree seip_reg` ↦
   `regsAgree AxRunClose.pinReg`, `[InvGS_gen hlc GF]` (any `hlc`), `Interface.Ret tt` ↦
   `.pure ()`, `S n` ↦ `n + 1`, `(lo ≤ k < hi)` ↦ `lo ≤ k ∧ k < hi`, `Hagree` in the
   `⊢ gconstInterp GD -∗ gconstInterp GD' -∗ ⌜GD = GD'⌝` form.  Section variables are explicit
   arguments: the node rules take `M dok i Φ cpu G HG Hmid` (+ `Out` for the write rule) then
   Rocq's lemma arguments (`wpdXwrNodeW`: `lo hi` first, `Hwin` after `HA`, `Hval` after
   `Hlat`); the bridge takes `img dok i Φ cpu G HG HGex Hmid Htext Hflow Hloc Hagree Out k0 c hi
   Hhi HnoSplitW` (Rocq's section order).  `CResWP` takes `dok i Out k0 hi`.
3. `CResWP_succ`'s premise `∀ aq vs, d ≠ CRmwR aq vs` is kept; the Ltac `silent_psWP` is replaced
   by inline inversions (as `AxCertP3.wpdOfCertW`).

**Rocq → Lean name map.**  `FstRmwW` `FstRmwW`, `FstM_W` `FstMToW` (as AxCertP3's `FldMToW`),
`wpd_xwr_nodeW` `wpdXwrNodeW`, `wpd_xrd_pinP` `wpdXrdPinP`, `CResWP` `CResWP`, `CResWP_succ`
`cResWPSucc`, `wpd_of_CertWP` `AxSpinAm2.wpdOfCertWP`, `wpd_instr_of_CertWP`
`AxSpinAm2.wpdInstrOfCertWP` (the last two collide with AxWalk2's camelCase names:
file-qualified).

**Dropped:** nothing (Rocq 8 definitions/lemmas; Lean 8).  **Not ported:** the Ltac
`silent_psWP` (deviation 3), the section notations (written out), and the `Print Assumptions`
lines (the lint's axiom check covers them).
-/
import Weak.AxCertP3
import Weak.AxCondM2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! # 1. The window-restricted write flow and the node lemmas -/

section fstW
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- `FstM` restricted to the row positions `lo ≤ k < hi`. -/
def FstRmwW (M : Gdexec → Prop) (dok : Int → Nat → Prop) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (lo hi : Nat) : IProp GF :=
  iprop(∀ (GD : Gdexec) (ls : AxirisG.logTsT GF) (k : Nat) (data : List (BitVec 8)) (base : Int)
      (n : Nat),
    ⌜M GD⌝ -∗ □ AxirisG.gconstInterp GD -∗ AxirisG.localInterp GD i k ls -∗
    ⌜graphData GD (i, k) = some data⌝ -∗ ⌜dok base n ∧ rowWr i GD k base data.length⌝ -∗
    ⌜lo ≤ k ∧ k < hi⌝ -∗ dflowO i GD k (Out k data))

theorem FstMToW (M : Gdexec → Prop) (dok : Int → Nat → Prop) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (lo hi : Nat) :
    FstM M dok i Out ⊢ FstRmwW M dok i Out lo hi := by
  unfold FstM FstRmwW
  iintro F %GD %ls %k %v %base %n %Hc #Hg Hl %Hv %Hd %_
  iapply F $$ %GD %ls %k %v %base %n %Hc Hg Hl %Hv %Hd

end fstW

section nodesW
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (dok : Int → Nat → Prop)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (Out : Nat → List (BitVec 8) → IProp GF)

include HG Hmid in
/-- THE RMW ARM, write half, the flow demanded only inside `[lo, hi)`. -/
theorem wpdXwrNodeW (lo hi : Nat) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat) (v : BitVec (8 * n))
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hwin : lo ≤ k ∧ k < hi)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = true)
    (Hval : req.value = some v)
    (Hdok : dok (paZ req.pa) n) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗ FstRmwW M dok i Out lo hi -∗
      (∀ rs', ⌜A rs'⌝ -∗ Out k (WeakInterpProj.wbytes n v) -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (KK (.Ok (some true))) rs' none ib, k + 1⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ Φ := by
  unfold FstRmwW dflowO
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
  isplit
  · -- (a) no read at a write node
    iintro %id %K %Hst
    have hfalse : False := by
      obtain ⟨lb, -, -, Hsome, HK⟩ := Hst
      obtain ⟨l, d, d', Hrd, -, Hps, -⟩ := HK (List.replicate (aidentN id) 0) List.length_replicate
      obtain ⟨v', -, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := xwritePstep cpu n va req KK rs ib d l _ d' Hdev Hlat Hps
      · simp only [wlRd] at Hrd
        simp [← Hrd] at Hsome
      · simp only [wlRd] at Hrd
        simp [← Hrd] at Hsome
    exact hfalse.elim
  isplit
  · -- (b) THE EXCLUSIVE STORE (inside the window), or the retry self-loop
    iintro %l %s' %Hst %Hpin
    obtain ⟨v', hv', hcase⟩ := AxCert2.xwriteAstepInv _ cpu n va req KK rs ib k l s' Hdev Hlat Hst
    have hvv : v' = v := by
      rw [Hval] at hv'
      exact (Option.some.inj hv').symm
    subst hvv
    rcases hcase with ⟨lb, hrow, hwr, hwd, hl, hs'⟩ | ⟨hl, hs'⟩
    · have Hgd : graphData GD (i, k) = some (WeakInterpProj.wbytes n v') ∧
          rowWr i GD k (paZ req.pa) (WeakInterpProj.wbytes n v').length := by
        rw [hl] at hwr hwd
        simp only [wlWr] at hwr
        simp only [wlWdata] at hwd
        refine ⟨?_, lb, _, hrow, hwr.symm⟩
        unfold graphData
        rw [AxWp.growLookup _ _ _ _ hrow, Option.bind_some, ← hwd]
      rw [hl, hs']
      simp only [wlWdata]
      unfold wpEvStep
      iintro %na Hpg
      ihave Hf := F $$ %GD %ls %k %(WeakInterpProj.wbytes n v') %(paZ req.pa) %n %Hc Hg Hloc
        %Hgd.1 %⟨Hdok, Hgd.2⟩ %Hwin
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
          iprop(R ∗ ⌜graphData GD (i, k) = some (WeakInterpProj.wbytes n v')⌝))
        · inext
          iintro HR
          iframe HR
          ipureintro
          exact Hgd.1
        · iexact Hfe
      · iapply C $$ %rs
        · ipureintro
          exact HP
        · iexact HO
    · -- the retry self-loop
      rw [hl, hs']
      simp only [wlWdata]
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs %HP F C
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
/-- THE RMW ARM, read half, KEEPING the graph-value equation (the pin); the no-split premise
only at the node's own position. -/
theorem wpdXrdPinP (n va : Nat)
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
         Pin M i k vs -∗
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
    -- the SPLIT matching (a plain `IRead` row item at `k`) is refuted
    have Hrmw : ∃ (aq rl : Bool) (base : Int) (n' : Nat), aident lb = .IRmw aq rl base n' := by
      cases hid : aident lb with
      | IRead aq base n' =>
        exfalso
        rw [hid] at Hl0
        simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hl0
        obtain ⟨-, hb, hn⟩ := Hl0
        subst hb
        subst hn
        exact Hns lb aq _ _ Hlb hid Hdok
      | IRmw aq rl base n' => exact ⟨aq, rl, base, n', rfl⟩
      | IWrite _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
      | IFence _ _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
      | IIo _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
    obtain ⟨aq1, rl1, base1, n1, Hidr⟩ := Hrmw
    have Had : aidentAdvRd (aident lb) = 0 := by rw [Hidr]; rfl
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
    · unfold Pin
      iexists GD
      isplitr
      · ipureintro
        exact Hc
      isplitr
      · imodintro
        iexact Hg
      isplitr
      · ipureintro
        exact Hv
      · ipureintro
        exact ⟨lb, aq1, rl1, base1, n1, Hlb, Hidr⟩
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

end nodesW

/-! # 2. The pinned, window-restricted bridge (kind `DKRmw`) -/

section resWP
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The RMW data resource: the write flow only inside `[k0, hi)`; the read half's pin. -/
def CResWP (dok : Int → Nat → Prop) (i : Agent) (Out : Nat → List (BitVec 8) → IProp GF)
    (k0 hi : Nat) (d : Cdata) (kc : Nat) : IProp GF :=
  match d with
  | .CPend => FstRmwW rvwmoCatConsistent dok i Out k0 hi
  | .CRmwR _ rvs => iprop(FstRmwW rvwmoCatConsistent dok i Out k0 hi ∗
      Pin rvwmoCatConsistent i kc rvs ∗ ⌜k0 ≤ kc ∧ kc < hi⌝)
  | .CRmw _ _ rvs wvs _ => iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kc⌝ ∗ Out kd wvs ∗
      Pin rvwmoCatConsistent i kd rvs)
  | .CLd vs | .CSt vs _ => iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kc⌝ ∗ Out kd vs)

theorem cResWPSucc (dok : Int → Nat → Prop) (i : Agent) (Out : Nat → List (BitVec 8) → IProp GF)
    (k0 hi : Nat) (d : Cdata) (kc : Nat) (hd : ∀ aq vs, d ≠ .CRmwR aq vs) :
    CResWP dok i Out k0 hi d kc ⊢ CResWP dok i Out k0 hi d (kc + 1) := by
  cases d with
  | CPend => exact .rfl
  | CRmwR aq vs => exact (hd aq vs rfl).elim
  | CRmw _ _ rvs vs _ =>
    simp only [CResWP]
    iintro ⟨%kd, %Hk, H⟩
    iexists kd
    isplitr
    · ipureintro
      omega
    iexact H
  | CLd vs | CSt vs _ =>
    simp only [CResWP]
    iintro ⟨%kd, %Hk, H⟩
    iexists kd
    isplitr
    · ipureintro
      omega
    iexact H

end resWP

section bridgeWP
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (dok : Int → Nat → Prop)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop)
variable (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (HGex : ∃ GD, G GD)
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
/- GRAPH AGREEMENT: two graphs both agreed by `gconstInterp` are equal. -/
variable (Hagree : ∀ GD GD', rvwmoCatConsistent GD → rvwmoCatConsistent GD' →
  ⊢ AxirisG.gconstInterp (GF := GF) GD -∗ AxirisG.gconstInterp GD' -∗ ⌜GD = GD'⌝)
variable (Out : Nat → List (BitVec 8) → IProp GF) (k0 c hi : Nat)
/- the window's upper end: every `G`-row has length at most `hi + c`. -/
variable (Hhi : ∀ GD, G GD → (AxOpsem.grow GD i).length ≤ hi + c)
/- THE WINDOW PREMISE: no plain read of the RMW's bytes at `k0 ≤ k < length − c`. -/
variable (HnoSplitW : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat), k0 ≤ k →
    k + c < (AxOpsem.grow GD i).length →
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)

include HG HGex Hmid Htext Hflow Hloc Hagree Hhi HnoSplitW in
/-- Rocq `wpd_of_CertWP`: `wpdOfCertW` over the pinned, window-restricted `CResWP`. -/
theorem AxSpinAm2.wpdOfCertWP (Q : Cst → Unit → ExecSt → Prop) (m : SailM Unit) (s : Cst)
    (t : ExecSt) :
    AxCert.Cert img dok .DKRmw (fun _ _ _ => False) Q s m t → PF img dok .DKRmw c s m t →
    ∀ rs ib kk, regsAgree AxRunClose.pinReg rs t.regs → AxCert2.bpos G i kk s.csB → k0 ≤ kk →
    ⊢ CResWP dok i Out k0 hi s.csD kk -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ ⌜k0 ≤ k'⌝ -∗ CResWP dok i Out k0 hi s'.csD k' -∗
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
      · iapply (IHs Hs (rs1 r) (PFRds img dok .DKRmw (rs1 r) Hs HPF) rs1 ib1 kk HA1 Hb Hk0)
          $$ Hd C
      · have h := IHn Hs (PFRdn img dok .DKRmw Hs HPF) rs1 ib1 kk HA1 Hb Hk0
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
      iapply (IH (PFWr img dok .DKRmw HPF) (rs1.set r v) ib1 kk (regsAgreeSet _ _ _ r v HA1) Hb
        Hk0) $$ Hd C
  | cMrd d b r n va req k t vs Hdev Hlat Hnf Hvs _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    by_cases hR : ∃ aq rvs, d = .CRmwR aq rvs
    · -- a pinned position refutes the image read
      obtain ⟨aq, rvs, rfl⟩ := hR
      have hconv : CResWP dok i Out k0 hi (.CRmwR aq rvs) kk ⊢
          iprop(FstRmwW rvwmoCatConsistent dok i Out k0 hi ∗
            Pin rvwmoCatConsistent i kk rvs ∗ ⌜k0 ≤ kk ∧ kk < hi⌝) := .rfl
      iintro Hd -
      ihave Hd := hconv $$ Hd
      icases Hd with ⟨-, #P, -⟩
      iapply (wpdPinMread rvwmoCatConsistent img i Φ cpu G HG Hmid Htext Hagree n va req k ib kk
        vs rvs Hdev Hlat Hnf Hvs) $$ %rs P
    · iintro Hd C
      ihave Hd := (cResWPSucc dok i Out k0 hi d kk (fun aq rvs h => hR ⟨aq, rvs, h⟩)) $$ Hd
      iapply (AxSymEngine3.wpdImgRead3M rvwmoCatConsistent img i Φ cpu G HG Hmid Htext Hflow n va
        req k ib kk vs
        (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
        (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf Hvs) $$ %rs %Hag
      iintro %rs' %HA'
      iapply (IH (PFMrd img dok .DKRmw Hlat Hnf Hvs HPF) rs' ib (kk + 1) HA'
        (bposSucc G i kk b Hb) (by omega)) $$ Hd C
  | cIf s n va req k t vs Hdev Hlat Hfe Hvs _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    iintro Hd C
    iapply (AxSymEngine3.wpdImgFetch3M rvwmoCatConsistent img i Φ cpu G HG Hmid Htext n va req k
      ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hfe Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH (AxCertP2.PFIf img dok .DKRmw Hfe Hvs HPF) rs' ib kk HA' Hb Hk0) $$ Hd C
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
  | cDrd b r n va req k t Hkd => cases Hkd
  | cDwr b r n va req k t v Hkd => cases Hkd
  | cFence d b r bk k t Hpark _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    by_cases hR : ∃ aq rvs, d = .CRmwR aq rvs
    · -- a pinned position refutes the fence
      obtain ⟨aq, rvs, rfl⟩ := hR
      have hconv : CResWP dok i Out k0 hi (.CRmwR aq rvs) kk ⊢
          iprop(FstRmwW rvwmoCatConsistent dok i Out k0 hi ∗
            Pin rvwmoCatConsistent i kk rvs ∗ ⌜k0 ≤ kk ∧ kk < hi⌝) := .rfl
      iintro Hd -
      ihave Hd := hconv $$ Hd
      icases Hd with ⟨-, #P, -⟩
      iapply (wpdPinFence rvwmoCatConsistent i Φ cpu G HG Hmid Hagree bk k ib kk rvs) $$ %rs P
    · iintro Hd C
      ihave Hd := (cResWPSucc dok i Out k0 hi d kk (fun aq rvs h => hR ⟨aq, rvs, h⟩)) $$ Hd
      iapply (wpdFenceNodeM rvwmoCatConsistent i Φ cpu G HG Hmid Hloc bk k ib kk
        (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
        (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hpark) $$ %rs %Hag
      iintro %rs' %HA'
      iapply (IH (PFFence img dok .DKRmw HPF) rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)
        (by omega)) $$ Hd C
  | cXrd b r n va req k t Hkd Hdev Hlat Hdok _ IH =>
    -- THE EXCLUSIVE READ: positioned inside the window, pinned
    intro HPF rs ib kk Hag Hb Hk0
    obtain ⟨a, Ha, HF⟩ := HPF rfl
    simp only at Ha
    subst Ha
    have Hca := FamXrd img dok .DKRmw HF Hlat
    have Hwin : kk < hi := by
      obtain ⟨GD, HGD⟩ := HGex
      have E : (AxOpsem.grow GD i).length = kk + a := Hb GD HGD
      have := Hhi GD HGD
      omega
    have HnoSplitK : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜∀ (lb : Lbl) (aq : Bool) (base : Int) (n' : Nat),
          (AxOpsem.grow GD i)[kk]? = some lb → aident lb = .IRead aq base n' → ¬ dok base n'⌝ := by
      intro GD Hc
      refine (BI.and_intro (HG GD Hc) (HnoSplitW GD Hc)).trans ?_
      iintro ⟨%HGD, %Hw⟩
      ipureintro
      intro lb aq base n' Hlb Hid
      have E : (AxOpsem.grow GD i).length = kk + a := Hb GD HGD
      exact Hw kk lb aq base n' Hk0 (by omega) Hlb Hid
    iintro Hd C
    iapply (wpdXrdPinP rvwmoCatConsistent dok i Φ cpu G HG Hmid n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) HnoSplitK Hdev Hlat Hdok) $$ %rs %Hag
    iintro %vs %rs' %Hlen %HA' #P
    have hconv : CResWP dok i Out k0 hi .CPend kk ⊢ FstRmwW rvwmoCatConsistent dok i Out k0 hi :=
      .rfl
    have hbuild : iprop(FstRmwW rvwmoCatConsistent dok i Out k0 hi ∗
        Pin rvwmoCatConsistent i kk vs ∗ ⌜k0 ≤ kk ∧ kk < hi⌝) ⊢
        CResWP dok i Out k0 hi (.CRmwR (classify req.access_kind).akSync vs) kk := .rfl
    ihave Hd := hconv $$ Hd
    iapply (IH vs Hlen (fun h => by cases h) rs' ib kk HA' Hb Hk0) $$ [Hd] C
    iapply hbuild
    isplitl [Hd]
    · iexact Hd
    isplitr
    · iexact P
    · ipureintro
      exact ⟨Hk0, Hwin⟩
  | cXwr aq rvs b r n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    -- THE EXCLUSIVE WRITE: at the pinned position
    intro _ rs ib kk Hag Hb Hk0
    have hconv : CResWP dok i Out k0 hi (.CRmwR aq rvs) kk ⊢
        iprop(FstRmwW rvwmoCatConsistent dok i Out k0 hi ∗
          Pin rvwmoCatConsistent i kk rvs ∗ ⌜k0 ≤ kk ∧ kk < hi⌝) := .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    icases Hd with ⟨F, #P, %Hw⟩
    iapply (wpdXwrNodeW rvwmoCatConsistent dok i Φ cpu G HG Hmid Out k0 hi n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hw Hdev Hlat Hval Hdok) $$ %rs %Hag F
    iintro %rs' %HA' HO
    have hdone : iprop(∃ kd, ⌜k0 ≤ kd ∧ kd < kk + 1⌝ ∗ Out kd (WeakInterpProj.wbytes n v) ∗
        Pin rvwmoCatConsistent i kd rvs) ⊢
        CResWP dok i Out k0 hi (.CRmw aq (classify req.access_kind).akSync rvs
          (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) (kk + 1) := .rfl
    iapply (IH (fun h => by cases h) rs' ib (kk + 1) HA' (bposSucc G i kk b Hb) (by omega))
      $$ [HO] C
    iapply hdone
    iexists kk
    isplitr
    · ipureintro
      omega
    isplitl [HO]
    · iexact HO
    · iexact P
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
      iapply (IH (PFSil' img dok .DKRmw HPF (fun _ _ H => Or.elim H And.right
        (fun h => absurd (Hsf.symm.trans h.1) Bool.false_ne_true))) rs1 ib1 kk HA1 Hb Hk0) $$ Hd C
  | cSf d b r n w k t Hsf _ IH =>
    intro HPF rs ib kk Hag Hb Hk0
    by_cases hR : ∃ aq rvs, d = .CRmwR aq rvs
    · -- a pinned position refutes the marker
      obtain ⟨aq, rvs, rfl⟩ := hR
      have hconv : CResWP dok i Out k0 hi (.CRmwR aq rvs) kk ⊢
          iprop(FstRmwW rvwmoCatConsistent dok i Out k0 hi ∗
            Pin rvwmoCatConsistent i kk rvs ∗ ⌜k0 ≤ kk ∧ kk < hi⌝) := .rfl
      iintro Hd -
      ihave Hd := hconv $$ Hd
      icases Hd with ⟨-, #P, -⟩
      iapply (AxCondM2.wpdPinSf rvwmoCatConsistent i Φ cpu G HG Hmid Hagree n w k ib kk rvs Hsf)
        $$ %rs P
    · iintro Hd C
      ihave Hd := (cResWPSucc dok i Out k0 hi d kk (fun aq rvs h => hR ⟨aq, rvs, h⟩)) $$ Hd
      iapply (AxCert2.wpdSfNodeM rvwmoCatConsistent i Φ cpu G HG Hmid Hloc n w k ib kk
        (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
        (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hsf) $$ %rs %Hag
      iintro %rs' %ib' %HA'
      iapply (IH (AxCertP2.PFSf img dok .DKRmw Hsf HPF) rs' ib' (kk + 1) HA'
        (bposSucc G i kk b Hb) (by omega)) $$ Hd C
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
      iapply (IH (PFSil' img dok .DKRmw HPF (fun _ _ H => H)) rs1 ib1 kk HA1 Hb Hk0) $$ Hd C

include HG HGex Hmid Htext Hflow Hloc Hagree Hhi HnoSplitW in
/-- Rocq `wpd_instr_of_CertWP`: one RMW instruction from a `.pure ()` boundary at `k0`. -/
theorem AxSpinAm2.wpdInstrOfCertWP (Q : Cst → Unit → ExecSt → Prop) (s0 : Cst) (rs : RegFile)
    (s : Athread) (Hs : RetX cpu rs k0 s)
    (Hbp : AxCert2.bpos G i k0 s0.csB)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k0 s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       AxCert.Cert img dok .DKRmw (fun _ _ _ => False) Q s0 (riscvStep tick) t)
    (HPF : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       PF img dok .DKRmw c s0 (riscvStep tick) t) :
    ⊢ CResWP dok i Out k0 hi s0.csD k0 -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResWP dok i Out k0 hi s'.csD k' -∗
         wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  iintro Hd C
  iapply (wpdRetNode3M rvwmoCatConsistent i Φ cpu G HG rs k0 s Hs Hb)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  iapply (AxSpinAm2.wpdOfCertWP img dok i Φ cpu G HG HGex Hmid Htext Hflow Hloc Hagree Out k0 c
    hi Hhi HnoSplitW Q _ s0 ⟨rs', fun _ => none, testDevs⟩
    (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag))
    (HPF tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone k0
    (regsAgreeRefl _ _) Hbp (Nat.le_refl _)) $$ Hd
  iintro %s' %t' %rs1 %ib' %k' %HQ %Hag' %Hbp' %_ Hd
  iapply C $$ %s' %t' %rs1 %ib' %k' %HQ %Hag' %Hbp' Hd

end bridgeWP

end Weak
