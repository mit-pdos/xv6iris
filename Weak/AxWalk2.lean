/-
Weak: **THE BRIDGE `CertWP` ⇒ WPd** (constraint A, engine side): walker reads as DEMONIC reads
at their exact row positions with a PERSISTENT walker flow, the fused A/D RMW through the RMW
node lemmas at the PT region, and POSITIONAL premises everywhere — for the data accesses too
(no region-wide `HnoRmw` / `HnoSplit`).

Rocq: `iris/AxWalk2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

PREMISES (`AxCert2`'s bridge premises minus `HnoRmw` / `HnoSplit`): `HG`/`Hmid`/`Htext`/
`Hflow`/`Hloc` as there; `HxPin`: every fused RMW row item of hart `i` at a PT (`wok`) address
reads a value satisfying `xpin` at its row position — the RMW read half is a SKIP step (no flow
is run there, WPd clause (a)'s `aidentAdvRd = 0` arm), so the pin of Sail's exclusive RE-READ can
only be a graph-level fact (protocol: H5'.3 + `pt_disc` ⇒ the read half is the token's last
word, AxPtProt3); the WALKER FLOWS are persistent caller resources: `WFrM` = for every PT slot
`a`, `FldM` at the one-slot region `Wa wok a` with OUTPUT `⌜wpin k a vs⌝ ∗ WOr a k vs` (the pin
of the plain walk read is delivered BY THE FLOW — positional by construction: the walker flow
runs only at `pWrd` nodes, the explicit loads' flow only at `pDrd`); `WFwM` = for every slot
`a`, `FstM` at `Wa wok a` with output `WOw a`.  POSITIONAL obligations are carried BY THE
CERTIFICATE (instantiated at `pR := posR G i`, `pX := posX G i`).  THE CONTINUATION learns the
final walker list `ws'` (every walker event WITH ITS ROW POSITION), the final row position `k'`,
the certificate state, the data resource and `WRes ws'` (each walker read's flow output
`WOr a k vs`, each write-back's `WOw a k wvs`).  §1 the walker RMW read half with its graph-level
pin (`wpdWxrdNodeM`); §2 THE BRIDGE `wpdOfCertWPM`, one instruction `wpdInstrOfCertWPM`, and the
region-form corollary `wpdOfCertWRegionM` (`AxDataX9.CertW` through `CertWPOfCertW`).

## Deviations from Rocq

1. O2 STAGE C (as `AxCert2` / `AxDataX10` deviation 1): Rocq's section premises `Hntext` (data
   reads are not fetch text) and `Hwtext` (walker addresses are not fetch text) are DROPPED —
   Rocq used them only to refute `AStepFetch` at a data / walker read; Lean's `CertWP.pDrd` and
   `pWrd` carry `akIfetch = false`, which `wpdDrdNodePosM` takes as `Hnf`.  `CertWP.pMrd` runs
   through `AxSymEngine3.wpdImgRead3M` (to `k + 1`), the Lean-only `CertWP.pIf` through
   `AxSymEngine3.wpdImgFetch3M` (at `k`, budget and walker list kept); `pEnd` through
   `wpdStuckReadM`.  `wpdWxrdNodeM`'s inversion has one case less (Lean `astepProg` has no
   fetch arm; `AxCert2.xreadAstepFalse`).
2. AS `AxCert2` deviations 2–4: read answers `.Ok (wordOfBytes n vs, none)`; writes take `v` with
   `req.value = some v` (`pDwr`/`pXwr`/`pWxwr`), continuing at `.Ok (some true)`;
   `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg`; `invGS_gen HasNoLc Σ` ↦
   `[InvGS_gen hlc GF]` (any `hlc`); `Interface.ReadReq.t n` ↦ `Mem_read_request n va …`;
   `N.to_nat n` ↦ `n : Nat`; `Interface.Ret tt` ↦ `.pure ()`; `MState rs' ∅ dev0_state` ↦
   `⟨rs', fun _ => none, testDevs⟩`; `ib_none` ↦ `ibNone`; `CRes` ↦ `CResM M dok kind i Out`.
3. Section variables `M img dok wok kind i Φ cpu G HG Hmid Htext Hflow Hloc wpin xpin HxPin Out
   WOr WOw` (Rocq additionally `Hntext Hwtext`, deviation 1).  The defs `WFrM`/`WFwM`/`wres`/
   `WRes` and the lemmas `posRIpropM`/`posXIpropM`/`WResSnoc` take their arguments explicitly
   (the defs: `WFrM M wok i wpin WOr`, `WFwM M wok i WOw`, `wres WOr WOw kw`, `WRes WOr WOw ws`;
   the pos lemmas: `M i G HG D k`, without Rocq's unused `invGS_gen`).  `wpdWxrdNodeM` takes
   `dok` after the section variables `M i Φ cpu G HG Hmid` (Rocq: the same).
4. The riscv.cat instances (Rocq `Definition … := …M rvwmo_cat_consistent`): `WFr`/`WFw` are
   abbrevs, the rest theorems typed `type_of% (…M rvwmoCatConsistent)`.
5. Q19 (provisional): `wpdOfCertWPM` has the case of the Lean-only `CertWP.pSf` (an SFENCE.VMA
   announce, one row item), by `AxCert2.wpdSfNodeM` as the fence.

**Rocq → Lean name map.**  `Wa` `Wa`, `wpd_wxrd_nodeM` `wpdWxrdNodeM`, `wpd_wxrd_node`
`wpdWxrdNode`, `WFrM` `WFrM`, `WFwM` `WFwM`, `wres` `wres`, `WRes` `WRes`, `WRes_snoc`
`WResSnoc`, `posR_ipropM` `posRIpropM`, `posX_ipropM` `posXIpropM`, `wpd_of_CertWPM`
`wpdOfCertWPM`, `wpd_instr_of_CertWPM` `wpdInstrOfCertWPM`, `wpd_of_CertW_regionM`
`wpdOfCertWRegionM`, and the riscv.cat instances `WFr` `WFr`, `WFw` `WFw`, `posR_iprop`
`posRIprop`, `posX_iprop` `posXIprop`, `wpd_of_CertWP` `AxWalk2.wpdOfCertWP`,
`wpd_instr_of_CertWP` `AxWalk2.wpdInstrOfCertWP` (both duplicated with AxSpinAm2: file-qualified),
`wpd_of_CertW_region` `wpdOfCertWRegion`.

**Dropped:** nothing (Rocq 20 definitions/lemmas; Lean 20, + the Lean-only
`AxWalk2.wResNil` (`WRes []`, Rocq `by rewrite /WRes`)).  **Not ported:** the section-local
Ltac `silent_psW` (↦ `AxSymEngine3.wpdSilentNode3M`), the local notation `CR`, and the
`Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxWalk
import Weak.AxDataX10

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-- The one-slot walker region. -/
def Wa (wok : Int → Nat → Prop) (a : Int) : Int → Nat → Prop := fun b m => b = a ∧ wok b m

/-! # 1. The walker RMW read half with its graph-level pin -/

section wxrd
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (i : Agent) (Φ : Athread → IProp GF) (cpu : CPU)
variable (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)

include HG Hmid in
/-- The walker's exclusive RE-READ: a skip step at the fused row item, its value pinned by the
graph-level fact `Hpin`. -/
theorem wpdWxrdNodeM (dok : Int → Nat → Prop) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop) (P : List (BitVec 8) → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = true)
    (Hdok : dok (paZ req.pa) n)
    (Hpos : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (lb : Lbl) (aq : Bool) (base : Int) (m : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base m → ¬ dok base m⌝)
    (Hpin : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (lb : Lbl) (aq rl : Bool) (v : List (BitVec 8)),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl (paZ req.pa) n →
        graphValue GD (i, k) = some v → P v⌝) :
    ⊢ ∀ rs, ⌜A rs⌝ -∗
      (∀ (vs : List (BitVec 8)) (rs' : RegFile), ⌜vs.length = n⌝ -∗ ⌜P vs⌝ -∗ ⌜A rs'⌝ -∗
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
    ihave Hns := (Hpos GD Hc) $$ Hg
    icases Hns with %Hns
    -- the SPLIT matching (a plain `IRead` row item) is refuted; the fused one is at the address
    have Hrmw : ∃ aq rl, aident lb = .IRmw aq rl (paZ req.pa) n := by
      cases hid : aident lb with
      | IRead aq base n' =>
        exfalso
        rw [hid] at Hl0
        simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hl0
        obtain ⟨-, hb, hn⟩ := Hl0
        subst hb
        subst hn
        exact Hns lb aq _ _ Hlb hid Hdok
      | IRmw aq rl base n' =>
        rw [hid] at Hl0
        simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hl0
        obtain ⟨-, hb, hn⟩ := Hl0
        subst hb
        subst hn
        exact ⟨aq, rl, rfl⟩
      | IWrite _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
      | IFence _ _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
      | IIo _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
    obtain ⟨aq0, rl0, Hid0⟩ := Hrmw
    have Had : aidentAdvRd (aident lb) = 0 := by rw [Hid0]; rfl
    simp only [Had, Nat.zero_ne_one, ↓reduceIte]
    -- the FUSED matching: a skip step at the same position, the value pinned
    ihave Hpn := (Hpin GD Hc) $$ Hg
    icases Hpn with %Hpn
    iintro %v %Hv %Hlenv
    obtain ⟨l, d, d', -, Hrv, Hps, Hk'⟩ := HK v Hlenv
    obtain ⟨tvs, Htl, rfl, Hp'⟩ := xreadPstep cpu n va req KK rs ib d _ _ d' Hdev Hlat Hps
    simp only [wlRvals] at Hrv
    subst Hrv
    have HPv := Hpn lb aq0 rl0 _ Hlb Hid0 Hv
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
      exact HPv
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

end wxrd

section wxrdCat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem wpdWxrdNode :
    type_of% (wpdWxrdNodeM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdWxrdNodeM rvwmoCatConsistent

end wxrdCat

/-! # 2. THE BRIDGE -/

section bridgeWDefs
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The persistent walker READ flows: every slot `a`, the one-slot region `Wa wok a`, output
`⌜wpin k a vs⌝ ∗ WOr a k vs`. -/
def WFrM (M : Gdexec → Prop) (wok : Int → Nat → Prop) (i : Agent)
    (wpin : Nat → Int → List (BitVec 8) → Prop)
    (WOr : Int → Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  iprop(∀ a, FldM M (Wa wok a) i (fun k vs => iprop(⌜wpin k a vs⌝ ∗ WOr a k vs)))

/-- The persistent walker WRITE-BACK flows. -/
def WFwM (M : Gdexec → Prop) (wok : Int → Nat → Prop) (i : Agent)
    (WOw : Int → Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  iprop(∀ a, FstM M (Wa wok a) i (WOw a))

/-- A walker event's output. -/
def wres (WOr WOw : Int → Nat → List (BitVec 8) → IProp GF) (kw : Nat × Wev) : IProp GF :=
  match kw with
  | (k, .WRd a vs) => WOr a k vs
  | (k, .WRmw a _ wvs) => WOw a k wvs
  | (_, .WRmwR _ _) => iprop(True)

/-- The walker events' outputs. -/
def WRes (WOr WOw : Int → Nat → List (BitVec 8) → IProp GF) (ws : List (Nat × Wev)) :
    IProp GF :=
  iprop([∗list] kw ∈ ws, wres WOr WOw kw)

theorem WResSnoc (WOr WOw : Int → Nat → List (BitVec 8) → IProp GF) (ws : List (Nat × Wev))
    (kw : Nat × Wev) :
    ⊢ WRes WOr WOw ws -∗ wres WOr WOw kw -∗ WRes WOr WOw (ws ++ [kw]) := by
  unfold WRes
  iintro H1 H2
  iapply BigSepL.bigSepL_append.2
  isplitl [H1]
  · iexact H1
  · iapply BigSepL.bigSepL_singleton.2
    iexact H2

theorem AxWalk2.wResNil (WOr WOw : Int → Nat → List (BitVec 8) → IProp GF) :
    ⊢ WRes WOr WOw [] := by
  unfold WRes
  iapply BigSepL.bigSepL_nil.2
  itrivial

end bridgeWDefs

section posIprop
variable {GF : BundledGFunctors} [AxirisG GF]

theorem posRIpropM (M : Gdexec → Prop) (i : Agent) (G : Gdexec → Prop)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (D : Int → Nat → Prop) (k : Nat) :
    posR G i D k → ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (lb : Lbl) (aq rl : Bool) (base : Int) (m : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base m → ¬ D base m⌝ := by
  intro Hq GD Hc
  iintro Hg
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  ipureintro
  exact Hq GD HGD

theorem posXIpropM (M : Gdexec → Prop) (i : Agent) (G : Gdexec → Prop)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (D : Int → Nat → Prop) (k : Nat) :
    posX G i D k → ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
      ⌜∀ (lb : Lbl) (aq : Bool) (base : Int) (m : Nat),
        (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base m → ¬ D base m⌝ := by
  intro Hq GD Hc
  iintro Hg
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  ipureintro
  exact Hq GD HGD

theorem posRIprop :
    type_of% (posRIpropM (GF := GF) rvwmoCatConsistent) :=
  posRIpropM rvwmoCatConsistent

theorem posXIprop :
    type_of% (posXIpropM (GF := GF) rvwmoCatConsistent) :=
  posXIpropM rvwmoCatConsistent

end posIprop

section bridgeW
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (img : Image) (dok wok : Int → Nat → Prop) (kind : Dkind)
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
variable (wpin xpin : Nat → Int → List (BitVec 8) → Prop)
variable (HxPin : ∀ GD, G GD → ∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (m : Nat)
  (v : List (BitVec 8)), (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base m →
  wok base m → graphValue GD (i, k) = some v → xpin k base v)
variable (Out : Nat → List (BitVec 8) → IProp GF)
variable (WOr WOw : Int → Nat → List (BitVec 8) → IProp GF)

include HG Hmid Htext Hflow Hloc HxPin in
/-- THE BRIDGE: a `CertWP` of the thread's tree at any state agreeing off the pins with the
thread's registers gives its WPd, with continuation at every `.pure ()` reached. -/
theorem wpdOfCertWPM (Q : List (Nat × Wev) → Cst → Nat → Unit → ExecSt → Prop)
    (m : SailM Unit) (ws : List (Nat × Wev)) (s : Cst) (k : Nat) (t : ExecSt) :
    CertWP img dok wok kind (posR G i) (posX G i) wpin xpin (fun _ _ _ _ _ => False) Q ws s k m t →
    ∀ rs ib, regsAgree AxRunClose.pinReg rs t.regs → AxCert2.bpos G i k s.csB →
    ⊢ □ WFrM M wok i wpin WOr -∗ □ WFwM M wok i WOw -∗ CResM M dok kind i Out s.csD -∗
      WRes WOr WOw ws -∗
      (∀ ws' s' k' t' rs' ib', ⌜Q ws' s' k' () t'⌝ -∗
         ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResM M dok kind i Out s'.csD -∗ WRes WOr WOw ws' -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ := by
  intro H
  induction H with
  | pRet ws s k x t HQ =>
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    iapply C $$ %ws %s %k %t %rs %ib %HQ %Hag %Hb Hd Hw
  | pExt ws s k e kk t he => exact he.elim
  | pRd ws s k r kk t _ _ ihs ihn =>
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ k
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (kk (rs1 r)) rs1 none ib1, k⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨rfl, rfl⟩ := pstepRdInv cpu r kk rs1 ib1 d l p' d' Hp
      exact ⟨trivial, rs1, _, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      by_cases Hs : AxRunClose.pinReg r
      · iapply (ihs Hs (rs1 r) rs1 ib1 HA1 Hb) $$ WFr WFw Hd Hw C
      · have h := ihn Hs rs1 ib1 HA1 Hb
        rw [← HA1 r Hs] at h
        iapply h $$ WFr WFw Hd Hw C
  | pWr ws s k r v kk t Hr _ ih =>
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ k
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun s2 => ∃ rs1 ib1, s2 = ⟨.PHart cpu (kk PUnit.unit) (rs1.set r v) none ib1, k⟩ ∧
        regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs1 ib1 d l p' d' HA1 Hp
      obtain ⟨Hl, rfl⟩ := pstepWrInv cpu r v kk rs1 ib1 d l p' d' Hp
      exact ⟨Hl, rs1, ib1, rfl, HA1⟩
    · iintro %s2 %HN
      obtain ⟨rs1, ib1, rfl, HA1⟩ := HN
      iapply (ih (rs1.set r v) ib1 (regsAgreeSet _ _ _ r v HA1) Hb) $$ WFr WFw Hd Hw C
  | pMrd ws d b r k n va req kk t vs Hdev Hlat Hnf Hvs _ ih =>
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    iapply (AxSymEngine3.wpdImgRead3M M img i Φ cpu G HG Hmid Htext Hflow n va req kk ib k vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (ih rs' ib HA' (bposSucc G i k b Hb)) $$ WFr WFw Hd Hw C
  | pIf ws s k n va req kk t vs Hdev Hlat Hfe Hvs _ ih =>
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    iapply (AxSymEngine3.wpdImgFetch3M M img i Φ cpu G HG Hmid Htext n va req kk ib k vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hfe Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (ih rs' ib HA' Hb) $$ WFr WFw Hd Hw C
  | pEnd ws d r k n va req kk t Hdev Hlat Hnf =>
    intro rs ib Hag Hb
    have Hb' : ∀ GD, G GD → (AxOpsem.grow GD i).length = k + 0 := Hb
    iintro - - - - -
    iapply (wpdStuckReadM M i Φ cpu G HG Hmid k (fun GD h => Hb' GD h) n va req kk ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf rs Hag)
  | pWrEnd ws d r k n va req kk t Hdev Hlat =>
    intro rs ib Hag Hb
    have Hb' : ∀ GD, G GD → (AxOpsem.grow GD i).length = k + 0 := Hb
    iintro - - - - -
    iapply (AxCert2.wpdStuckWriteM M i Φ cpu G HG Hmid k (fun GD h => Hb' GD h) n va req kk ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat rs Hag)
  | pDrd ws b r k n va req kk t Hkd Hdev Hlat Hnf Hdok Hp _ ih =>
    intro rs ib Hag Hb
    have hconv : CResM M dok kind i Out .CPend ⊢ FldM M dok i Out := by
      subst Hkd
      exact .rfl
    iintro #WFr #WFw Hd Hw C
    ihave Hd := hconv $$ Hd
    iapply (wpdDrdNodePosM M dok kind i Φ cpu G HG Hmid Out n va req kk ib k
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hkd Hdev Hlat Hnf Hdok
      (posRIpropM M i G HG dok k Hp)) $$ %rs %Hag Hd
    iintro %vs %rs' %Hlen %HA' HO
    have hdone : iprop(∃ k, Out k vs) ⊢ CResM M dok kind i Out (.CLd vs) := .rfl
    iapply (ih vs Hlen rs' ib HA' (bposSucc G i k b Hb)) $$ WFr WFw [HO] Hw C
    iapply hdone
    iexists k
    iexact HO
  | pDwr ws b r k n va req kk t v Hkd Hdev Hlat Hval Hdok _ ih =>
    intro rs ib Hag Hb
    have hconv : CResM M dok kind i Out .CPend ⊢ FstM M dok i Out := by
      subst Hkd
      exact .rfl
    iintro #WFr #WFw Hd Hw C
    ihave Hd := hconv $$ Hd
    iapply (wpdDwrNodeM M dok i Φ cpu G HG Hmid Out n va req kk ib k v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %HA' HO
    have hdone : iprop(∃ k, Out k (WeakInterpProj.wbytes n v)) ⊢
        CResM M dok kind i Out (.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) := .rfl
    iapply (ih rs' ib HA' (bposSucc G i k b Hb)) $$ WFr WFw [HO] Hw C
    iapply hdone
    iexists k
    iexact HO
  | pFence ws d b r k bk kk t Hpark _ ih =>
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    iapply (wpdFenceNodeM M i Φ cpu G HG Hmid Hloc bk kk ib k
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hpark) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (ih rs' ib HA' (bposSucc G i k b Hb)) $$ WFr WFw Hd Hw C
  | pXrd ws b r k n va req kk t Hkd Hdev Hlat Hdok Hp _ ih =>
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    iapply (wpdXrdNodePosM M dok kind i Φ cpu G HG Hmid n va req kk ib k
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hkd Hdev Hlat Hdok
      (posXIpropM M i G HG dok k Hp)) $$ %rs %Hag
    iintro %vs %rs' %Hlen %HA'
    have hconv : CResM M dok kind i Out .CPend ⊢
        CResM M dok kind i Out (.CRmwR (classify req.access_kind).akSync vs) := by
      subst Hkd
      exact .rfl
    ihave Hd := hconv $$ Hd
    iapply (ih vs Hlen rs' ib HA' Hb) $$ WFr WFw Hd Hw C
  | pXwr ws aq rvs b r k n va req kk t v Hkd Hdev Hlat Hval Hdok _ ih =>
    intro rs ib Hag Hb
    have hconv : CResM M dok kind i Out (.CRmwR aq rvs) ⊢ FstM M dok i Out := .rfl
    iintro #WFr #WFw Hd Hw C
    ihave Hd := hconv $$ Hd
    iapply (wpdXwrNodeM M dok i Φ cpu G HG Hmid Out n va req kk ib k v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %HA' HO
    have hdone : iprop(∃ k, Out k (WeakInterpProj.wbytes n v)) ⊢
        CResM M dok kind i Out (.CRmw aq (classify req.access_kind).akSync rvs
          (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) := .rfl
    iapply (ih rs' ib HA' (bposSucc G i k b Hb)) $$ WFr WFw [HO] Hw C
    iapply hdone
    iexists k
    iexact HO
  | pIa ws s k n w kk t Hsf _ ih =>
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ (kk ()) ?_ k t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      rw [annLabelNot Hsf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (ih rs1 ib1 HA1 Hb) $$ WFr WFw Hd Hw C
  | pSf ws d b r k n w kk t Hsf _ ih =>
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    iapply (AxCert2.wpdSfNodeM M i Φ cpu G HG Hmid Hloc n w kk ib k
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hsf) $$ %rs %Hag
    iintro %rs' %ib' %HA'
    iapply (ih rs' ib' HA' (bposSucc G i k b Hb)) $$ WFr WFw Hd Hw C
  | pBa ws s k _ _ kk t _ ih | pCo ws s k _ kk t _ ih | pTl ws s k _ kk t _ ih
  | pTe ws s k _ kk t _ ih | pRx ws s k _ kk t _ ih | pTs ws s k _ kk t _ ih
  | pTx ws s k _ kk t _ ih | pCc ws s k kk t _ ih | pMsg ws s k _ kk t _ ih
  | pGcc ws s k kk t _ ih =>
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ _ ?_ k t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      exact ⟨trivial, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (ih rs1 ib1 HA1 Hb) $$ WFr WFw Hd Hw C
  | pWrd ws d b r k n va req kk t Hdev Hlat Hnf Hwok Hp _ ih =>
    -- THE WALKER READ: demonic, positional, pinned by the walker flow
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    have hF : WFrM M wok i wpin WOr ⊢
        FldM M (Wa wok (paZ req.pa)) i
          (fun k vs => iprop(⌜wpin k (paZ req.pa) vs⌝ ∗ WOr (paZ req.pa) k vs)) := by
      unfold WFrM
      iintro H
      iapply H
    ihave F := hF $$ WFr
    iapply (wpdDrdNodePosM M (Wa wok (paZ req.pa)) .DKLd i Φ cpu G HG Hmid
      (fun k vs => iprop(⌜wpin k (paZ req.pa) vs⌝ ∗ WOr (paZ req.pa) k vs)) n va req kk ib k
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) rfl Hdev Hlat Hnf ⟨rfl, Hwok⟩
      (posRIpropM M i G HG _ k (posRAnti G i wok _ k (fun _ _ H => H.2) Hp))) $$ %rs %Hag F
    iintro %vs %rs' %Hlen %HA' HO
    icases HO with ⟨%Hpin, HO⟩
    have hw : WOr (paZ req.pa) k vs ⊢ wres WOr WOw (k, .WRd (paZ req.pa) vs) := .rfl
    ihave HO := hw $$ HO
    ihave Hw := (WResSnoc WOr WOw ws (k, .WRd (paZ req.pa) vs)) $$ Hw HO
    iapply (ih vs Hlen Hpin rs' ib HA' (bposSucc G i k b Hb)) $$ WFr WFw Hd Hw C
  | pWxrd ws d b r k n va req kk t Hdev Hlat Hwok Hp _ ih =>
    -- THE WALKER A/D RMW, read half: fused (skip step), pinned by `HxPin`
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    have Hpn : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
        ⌜∀ (lb : Lbl) (aq rl : Bool) (v : List (BitVec 8)),
          (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl (paZ req.pa) n →
          graphValue GD (i, k) = some v → xpin k (paZ req.pa) v⌝ := by
      intro GD Hc
      iintro Hg
      ihave HGD := (HG GD Hc) $$ Hg
      icases HGD with %HGD
      ipureintro
      intro lb aq rl v Hlb Hid Hv
      exact HxPin GD HGD k lb aq rl _ _ v Hlb Hid Hwok Hv
    iapply (wpdWxrdNodeM M i Φ cpu G HG Hmid (Wa wok (paZ req.pa)) n va req kk ib k
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs) (xpin k (paZ req.pa))
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat ⟨rfl, Hwok⟩
      (posXIpropM M i G HG _ k (posXAnti G i wok _ k (fun _ _ H => H.2) Hp)) Hpn) $$ %rs %Hag
    iintro %vs %rs' %Hlen %Hpin %HA'
    have ht : ⊢ wres WOr WOw (k, .WRmwR (paZ req.pa) vs) := by
      unfold wres
      itrivial
    ihave Ht := ht
    ihave Hw := (WResSnoc WOr WOw ws (k, .WRmwR (paZ req.pa) vs)) $$ Hw Ht
    iapply (ih vs Hlen Hpin rs' ib HA' Hb) $$ WFr WFw Hd Hw C
  | pWxwr ws rvs d b r k n va req kk t v Hdev Hlat Hval Hwok _ _ ih =>
    -- THE WALKER A/D RMW, write half
    intro rs ib Hag Hb
    iintro #WFr #WFw Hd Hw C
    have hF : WFwM M wok i WOw ⊢ FstM M (Wa wok (paZ req.pa)) i (WOw (paZ req.pa)) := by
      unfold WFwM
      iintro H
      iapply H
    ihave F := hF $$ WFw
    iapply (wpdXwrNodeM M (Wa wok (paZ req.pa)) i Φ cpu G HG Hmid (WOw (paZ req.pa)) n va req kk
      ib k v (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval ⟨rfl, Hwok⟩) $$ %rs %Hag F
    iintro %rs' %HA' HO
    have hw : WOw (paZ req.pa) k (WeakInterpProj.wbytes n v) ⊢
        wres WOr WOw (k, .WRmw (paZ req.pa) rvs (WeakInterpProj.wbytes n v)) := .rfl
    ihave HO := hw $$ HO
    ihave Hw := (WResSnoc WOr WOw ws (k, .WRmw (paZ req.pa) rvs (WeakInterpProj.wbytes n v)))
      $$ Hw HO
    iapply (ih rs' ib HA' (bposSucc G i k b Hb)) $$ WFr WFw Hd Hw C

include HG Hmid Htext Hflow Hloc HxPin in
/-- ONE INSTRUCTION from a `.pure ()` boundary at position `k`. -/
theorem wpdInstrOfCertWPM (Q : List (Nat × Wev) → Cst → Nat → Unit → ExecSt → Prop) (s0 : Cst)
    (rs : RegFile) (k : Nat) (s : Athread) (Hs : RetX cpu rs k s)
    (Hbp : AxCert2.bpos G i k s0.csB)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       CertWP img dok wok kind (posR G i) (posX G i) wpin xpin (fun _ _ _ _ _ => False) Q [] s0 k
         (riscvStep tick) t) :
    ⊢ □ WFrM M wok i wpin WOr -∗ □ WFwM M wok i WOw -∗ CResM M dok kind i Out s0.csD -∗
      (∀ ws' s' k' t' rs' ib', ⌜Q ws' s' k' () t'⌝ -∗
         ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResM M dok kind i Out s'.csD -∗ WRes WOr WOw ws' -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i s Φ := by
  iintro #WFr #WFw Hd C
  iapply (wpdRetNode3M M i Φ cpu G HG rs k s Hs Hb)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  ihave Hw := AxWalk2.wResNil (GF := GF) WOr WOw
  iapply (wpdOfCertWPM M img dok wok kind i Φ cpu G HG Hmid Htext Hflow Hloc wpin xpin HxPin Out
    WOr WOw Q _ [] s0 k ⟨rs', fun _ => none, testDevs⟩
    (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone
    (regsAgreeRefl _ _) Hbp) $$ WFr WFw Hd Hw C

include HG Hmid Htext Hflow Hloc HxPin in
/-- REGION-FORM corollary: `AxDataX9.CertW` (no positions, no pins) bridges when the positional
premises hold at EVERY position. -/
theorem wpdOfCertWRegionM (Q : List Wev → Cst → Unit → ExecSt → Prop) (m : SailM Unit) (s : Cst)
    (t : ExecSt) (k : Nat)
    (HR : ∀ k, posR G i dok k ∧ posR G i wok k) (HX : ∀ k, posX G i dok k ∧ posX G i wok k) :
    CertW img dok wok kind (fun _ _ _ _ => False) Q [] s m t →
    ∀ rs ib, regsAgree AxRunClose.pinReg rs t.regs → AxCert2.bpos G i k s.csB →
    ⊢ □ WFrM M wok i wpin WOr -∗ □ WFwM M wok i WOw -∗ CResM M dok kind i Out s.csD -∗
      (∀ ws' s' k' t' rs' ib', ⌜Q (ws'.map Prod.snd) s' () t'⌝ -∗
         ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResM M dok kind i Out s'.csD -∗ WRes WOr WOw ws' -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ := by
  intro HC rs ib Hag Hb
  have HP := CertWPOfCertW img dok wok kind (posR G i) (posX G i) wpin xpin HR HX _ _ [] s m t HC
    [] k rfl
  have HP' : CertWP img dok wok kind (posR G i) (posX G i) wpin xpin (fun _ _ _ _ _ => False)
      (fun wsp' s' _ x t' => Q (wsp'.map Prod.snd) s' x t') [] s k m t :=
    CertWPMono img dok wok kind (posR G i) (posX G i) wpin xpin _ _ _ _ [] s k m t
      (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h) HP
  iintro #WFr #WFw Hd C
  ihave Hw := AxWalk2.wResNil (GF := GF) WOr WOw
  iapply (wpdOfCertWPM M img dok wok kind i Φ cpu G HG Hmid Htext Hflow Hloc wpin xpin HxPin Out
    WOr WOw _ m [] s k t HP' rs ib Hag Hb) $$ WFr WFw Hd Hw C

end bridgeW

/-! ### The riscv.cat instances under the Rocq names (`…M` at `rvwmoCatConsistent`) -/

section bridgeWCat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- (Rocq `WFr`) -/
abbrev WFr (wok : Int → Nat → Prop) (i : Agent) (wpin : Nat → Int → List (BitVec 8) → Prop)
    (WOr : Int → Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  WFrM rvwmoCatConsistent wok i wpin WOr

/-- (Rocq `WFw`) -/
abbrev WFw (wok : Int → Nat → Prop) (i : Agent)
    (WOw : Int → Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  WFwM rvwmoCatConsistent wok i WOw

theorem AxWalk2.wpdOfCertWP :
    type_of% (wpdOfCertWPM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdOfCertWPM rvwmoCatConsistent

theorem AxWalk2.wpdInstrOfCertWP :
    type_of% (wpdInstrOfCertWPM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdInstrOfCertWPM rvwmoCatConsistent

theorem wpdOfCertWRegion :
    type_of% (wpdOfCertWRegionM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  wpdOfCertWRegionM rvwmoCatConsistent

end bridgeWCat

end Weak
