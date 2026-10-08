/-
Weak: **the AMO READ VALUE reaches the WRITE FLOW** — a PINNED variant of the certificate bridge
(`AxCert2.wpdOfCertM`) in which the RMW's exclusive read half records, as a persistent PIN, the
graph value it was answered with at the fused row item, and the continuation after the write half
gets that pin AT THE WRITE'S ROW POSITION.

Rocq: `iris/AxCondM2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

WHY.  `wpdXrdNodeM` answers the read half demonically at `graphValue GD (i, k)` (WPd's read
clause) but forgets the equation; the write half's flow `FstM` then hands its output only the
WRITTEN bytes.  A protocol that hands the lock over on the value amoswap READ needs the read value
in the flow AND the hart's register to be that value.  The fused RMW is ONE event `(i, k)`; what is
missing is that the hart's `rvs` equals its graph value.  `Pin M i k rvs` (§1) says exactly that,
under a graph `GD0` the read step was given; `Hagree` (graph agreement; trivial at `axGA2`, see
`AxCondM.hagreeGa2`) identifies `GD0` with any later step's graph.

§1 `Pin` and the three node lemmas: `wpdXrdPin` (the read half, keeping the equation),
   `wpdPinMread` / `wpdPinFence` (a pinned state — row item `k` IS the fused `IRmw` — refutes an
   image graph read or a fence at `k`: the certificate allows those nodes between the two halves,
   the opax row does not; this keeps the pin at the write's position).
§2 THE PINNED BRIDGE `AxCondM2.wpdOfCertP` / `AxCondM2.wpdInstrOfCertP`: as AxCert2's, with the
   data resource `CResP … d k` position-indexed only in the RMW states:
   `CRmwR aq rvs ↦ FstM ∗ Pin k rvs`, `CRmw aq rl rvs wvs c ↦ ∃ kd, Out kd wvs ∗ Pin kd rvs`.
§3 `XCertTP` (`AxLeafS2.XCertT` on the pinned bridge) and the S-mode AMO leaf `XAmoswapSP`
   (`XAmoswapS` whose continuation also gets `Pin kd vs` for the SAME `kd` as the write's output).
§4 `OutOfV`: a write flow output indexed by the event's own graph read value; `amoOutPin`: with
   the pin, that output is the one at `some vs`, the hart's own bytes.

## Deviations from Rocq

1. O2 STAGE C (as `AxCert2` deviation 1).  The section premise `Hntext` is DROPPED (sections
   `pinC` and `xTP`).  `Cert.cMrd` is a graph image read with `akIfetch = false`, so
   `wpdPinMread` takes `Hnf : (classify req.access_kind).akIfetch = false` after `Hlat`; its
   program-step clause has no fetch arm (Lean's `astepProg` has none), so the refutation of a
   program step needs no pin (only the read clause uses `Hagree`).  The Lean-only `Cert.cIf`
   (an image FETCH: admin step at the SAME row position) is bridged by
   `AxSymEngine3.wpdImgFetch3M` in every data state — the pin stays valid at the same `k`.
2. LEAN-SAIL VALUES as AxCert2 deviation 2 (`req.value = some v`, read answers
   `.Ok (wordOfBytes n vs, none)`, `WeakInterpProj.wbytes n v` as write bytes); the pins
   `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg` (AxRunClose deviation 1).
3. TYPES as AxCert2 deviation 4: `[InvGS_gen hlc GF]` (any `hlc`); `Pin`, `CFkP`, `CResP` take
   their section variables explicitly (`Pin M i k rvs`, `CResP M dok kind i Out d k`).  Rocq's
   `Hagree` (`gconst_interp GD -∗ gconst_interp GD' -∗ ⌜GD = GD'⌝`) is
   `⊢ gconstInterp GD -∗ gconstInterp GD' -∗ ⌜GD = GD'⌝` (the form of `AxCondM.hagreeGa2`).
   `Pin_pers` is an `instance pinPers`.  Section variables are explicit arguments of each
   declaration that uses them (Lean `include … in`).
4. SPELLING as AxLeafS2 deviation 3 (`rs .PC = pc`, `rd.toNat ≠ 0`, `gprVal rs rs1 + zeros`,
   `⟨d, b, r⟩` for `CS d b r`, `.pure ()` for `Interface.Ret tt`); XAmoswapSP takes
   `Hsf : sfAnnB 32 w32 = false` after `Htx` (Q7, as `XAmoswapS`), and so does `XCertTP`.
5. Lean-only helpers (file-qualified): `AxCondM2.pinAt` (Rocq's inline
   `iDestruct "P" … Hagree … subst` step: under the current graph the pin's facts hold) and
   `AxCondM2.cresPShift` (Rocq's `destruct d; simpl`: off `CRmwR`, `CResP` does not depend on
   the position).

**Rocq → Lean name map.**  `Pin` `Pin`, `Pin_pers` `pinPers`, `wpd_xrd_pin` `wpdXrdPin`,
`wpd_pin_mread` `wpdPinMread`, `wpd_pin_fence` `wpdPinFence`, `CFkP` `CFkP`, `CResP` `CResP`,
`wpd_of_CertP` `AxCondM2.wpdOfCertP`, `wpd_instr_of_CertP` `AxCondM2.wpdInstrOfCertP` (both
duplicated with AxCertP2), `X_certTP` `XCertTP`, `X_amoswap_SP` `XAmoswapSP`, `OutOfV`
`OutOfV`, `amo_out_pin` `amoOutPin`.

**Dropped:** nothing (Rocq 13 definitions/lemmas/instances; Lean 13 + 2 Lean-only).  **Not
ported:** the Ltac `silent_psC` (↦ `AxSymEngine3.wpdSilentNode3M`, as AxCert2), the section
notations (written out), and the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxLeafS2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! # 1. The pin and the node lemmas -/

section pinDefs
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

/-- The read half's pin: row item `k` is the fused RMW and its graph value is `rvs`. -/
def Pin (M : Gdexec → Prop) (i : Agent) (k : Nat) (rvs : List (BitVec 8)) : IProp GF :=
  iprop(∃ GD, ⌜M GD⌝ ∗ □ AxirisG.gconstInterp (GF := GF) GD ∗
    ⌜graphValue GD (i, k) = some rvs⌝ ∗
    ⌜∃ (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
      (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRmw aq rl base n⌝)

instance pinPers (M : Gdexec → Prop) (i : Agent) (k : Nat) (rvs : List (BitVec 8)) :
    Persistent (Pin (GF := GF) M i k rvs) := by
  unfold Pin; infer_instance

/-- The data event's resource while it is pending (as `CFkM`). -/
def CFkP (M : Gdexec → Prop) (dok : Int → Nat → Prop) (kind : Dkind) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) : IProp GF :=
  match kind with
  | .DKLd => FldM M dok i Out
  | _ => FstM M dok i Out

/-- The data resource, position-indexed in the RMW states. -/
def CResP (M : Gdexec → Prop) (dok : Int → Nat → Prop) (kind : Dkind) (i : Agent)
    (Out : Nat → List (BitVec 8) → IProp GF) (d : Cdata) (k : Nat) : IProp GF :=
  match d with
  | .CPend => CFkP M dok kind i Out
  | .CRmwR _ rvs => iprop(FstM M dok i Out ∗ Pin M i k rvs)
  | .CRmw _ _ rvs wvs _ => iprop(∃ kd, Out kd wvs ∗ Pin M i kd rvs)
  | .CLd vs | .CSt vs _ => iprop(∃ kd, Out kd vs)

/-- (Lean-only) Off `CRmwR`, `CResP` does not depend on the position. -/
theorem AxCondM2.cresPShift (M : Gdexec → Prop) (dok : Int → Nat → Prop) (kind : Dkind)
    (i : Agent) (Out : Nat → List (BitVec 8) → IProp GF) (d : Cdata)
    (hd : ∀ aq rvs, d ≠ .CRmwR aq rvs) (k k' : Nat) :
    CResP M dok kind i Out d k ⊢ CResP M dok kind i Out d k' := by
  cases d with
  | CPend => exact .rfl
  | CLd _ => exact .rfl
  | CSt _ _ => exact .rfl
  | CRmwR aq rvs => exact (hd aq rvs rfl).elim
  | CRmw _ _ _ _ _ => exact .rfl

end pinDefs

section pinC
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
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
variable (HnoRmw : kind = .DKLd → ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)
variable (HnoSplit : kind = .DKRmw → ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)
/- GRAPH AGREEMENT: two graphs both agreed by `gconstInterp` are equal. -/
variable (Hagree : ∀ GD GD', M GD → M GD' →
  ⊢ AxirisG.gconstInterp (GF := GF) GD -∗ AxirisG.gconstInterp GD' -∗ ⌜GD = GD'⌝)
variable (Out : Nat → List (BitVec 8) → IProp GF)

include Hagree in
/-- (Lean-only) Under the current graph `GD`, the pin's facts hold. -/
theorem AxCondM2.pinAt (GD : Gdexec) (k : Nat) (rvs : List (BitVec 8)) (Hc : M GD) :
    ⊢ AxirisG.gconstInterp (GF := GF) GD -∗ Pin M i k rvs -∗
      ⌜graphValue GD (i, k) = some rvs ∧
        ∃ (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
          (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRmw aq rl base n⌝ := by
  unfold Pin
  iintro Hg ⟨%GD0, %Hc0, #Hg0, %Hgv0, %Hrmw⟩
  ihave Heq := (Hagree GD0 GD Hc0 Hc) $$ Hg0 Hg
  icases Heq with %Heq
  subst Heq
  ipureintro
  exact ⟨Hgv0, Hrmw⟩

include HG Hmid HnoSplit in
/-- THE RMW ARM, read half, KEEPING the graph-value equation. -/
theorem wpdXrdPin (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (A : RegFile → Prop)
    (HA : ∀ rs rs', A rs → regsAgree AxRunClose.pinReg rs' rs → A rs')
    (Hkind : kind = .DKRmw)
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
  ihave Hns := (HnoSplit Hkind GD Hc) $$ Hg
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
    -- the SPLIT matching (a plain `IRead` row item) is refuted; the row item is the fused RMW
    have Hrmw : ∃ (aq rl : Bool) (base : Int) (n' : Nat), aident lb = .IRmw aq rl base n' := by
      cases hid : aident lb with
      | IRead aq base n' =>
        exfalso
        rw [hid] at Hl0
        simp only [aidentRd, Option.some.injEq, Prod.mk.injEq] at Hl0
        obtain ⟨-, hb, hn⟩ := Hl0
        subst hb
        subst hn
        exact Hns k lb aq _ _ Hlb hid Hdok
      | IRmw aq rl base n' => exact ⟨aq, rl, base, n', rfl⟩
      | IWrite _ _ _ =>
        rw [hid] at Hl0
        simp [aidentRd] at Hl0
      | IFence _ _ _ _ =>
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

include HG Hmid Htext Hagree in
/-- A pinned position refutes an IMAGE graph read there (deviation 1: `Hnf`). -/
theorem wpdPinMread (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (ib : Ibch) (k : Nat)
    (vs rvs : List (BitVec 8))
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hvs : imgBytes img (paZ req.pa) n = some vs) :
    ⊢ ∀ rs, Pin M i k rvs -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  iloeb as IH
  iintro %rs #P
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave Hok := (Htext GD Hc) $$ Hg
  icases Hok with %Hok
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  ihave Hpf := (AxCondM2.pinAt M i Hagree GD k rvs Hc) $$ Hg P
  icases Hpf with %Hpf
  obtain ⟨-, lb0, aq0, rl0, base0, n0, Hlb0, Hid0⟩ := Hpf
  isplit
  · -- (a) the read would match the fused RMW row item as an image `IRead`
    iintro %id %K %Hst
    have hfalse : False := by
      obtain ⟨lb, Hlb, Hid, -, HK⟩ := Hst
      simp only at Hlb
      subst Hid
      obtain ⟨l0, d0, d0', Hl0, -, Hps0, -⟩ :=
        HK (List.replicate (aidentN (aident lb)) 0) List.length_replicate
      obtain ⟨tvs0, Htl0, rfl, -⟩ :=
        AxLdspWpd.loadStepInv cpu n va req KK rs ib d0 _ _ d0' Hdev Hlat Hnf Hps0
      simp only [wlRd, Htl0] at Hl0
      obtain ⟨Hidlb, -⟩ := Hok.2 k lb _ _ _ vs Hlb Hl0.symm Hvs
      rw [Hlb0] at Hlb
      cases Hlb
      rw [Hid0] at Hidlb
      cases Hidlb
    exact hfalse.elim
  isplit
  · -- (b) no program step at a plain non-fetch read
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
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' P
  · iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

include HG Hmid Hagree in
/-- A pinned position refutes a FENCE there. -/
theorem wpdPinFence (bk : barrier_kind) (KK : Unit → SailM Unit) (ib : Ibch) (k : Nat)
    (rvs : List (BitVec 8)) :
    ⊢ ∀ rs, Pin M i k rvs -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.barrier bk)) KK) rs none ib, k⟩ Φ := by
  obtain ⟨pr, pw, sr, sw, Hlab⟩ := ebarLabelFence bk
  iloeb as IH
  iintro %rs #P
  iapply (AxWpD.wpdMUnfoldStep M .MaybeStuck i _ Φ).2
  isplit
  · iapply (progressOblMaybestuck (GF := GF) i _).2
    itrivial
  unfold wpdMPreStepDef
  iintro %GD %ls ⟨%Hc, #Hg, Hloc⟩
  ihave HGD := (HG GD Hc) $$ Hg
  icases HGD with %HGD
  ihave Hpf := (AxCondM2.pinAt M i Hagree GD k rvs Hc) $$ Hg P
  icases Hpf with %Hpf
  obtain ⟨-, lb0, aq0, rl0, base0, n0, Hlb0, Hid0⟩ := Hpf
  isplit
  · -- (a) no read at a barrier node
    iintro %id %K %Hst
    have hfalse : False := by
      obtain ⟨lb, -, -, Hsome, HK⟩ := Hst
      obtain ⟨l, d, d', Hrd, -, Hps, -⟩ := HK (List.replicate (aidentN id) 0) List.length_replicate
      obtain ⟨rfl, -⟩ := barrierPstep cpu bk KK rs ib d l _ d' Hps
      rw [Hlab] at Hrd
      simp only [wlRd] at Hrd
      simp [← Hrd] at Hsome
    exact hfalse.elim
  isplit
  · -- (b) the fence would match the fused RMW row item
    iintro %l %s' %Hst %Hpin
    have hfalse : False := by
      cases Hst with
      | AStepAdmin _ _ d _ p' d' hadm hps =>
        obtain ⟨rfl, -⟩ := barrierPstep cpu bk KK rs ib d l p' d' hps
        rw [Hlab] at hadm
        exact (hadm : False).elim
      | AStepWrite _ _ d _ lb p' d' _ hsome _ _ hps =>
        obtain ⟨rfl, -⟩ := barrierPstep cpu bk KK rs ib d l p' d' hps
        rw [Hlab] at hsome
        simp [wlWr] at hsome
      | AStepFence _ _ d _ lb p' d' hrow hsome hf hps =>
        rw [Hlb0] at hrow
        cases hrow
        rw [Hid0] at hf
        simp only [aidentFence] at hf
        rw [hf] at hsome
        exact Bool.noConfusion hsome
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
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
      unfold wpSkipStep
      iintro %na Hna
      imodintro
      inext
      imodintro
      iexists ls
      iframe Hna Hloc
      iapply IH $$ %rs' P
  · iintro %Heq
    iapply (Hmid GD _ HGD (by exact trivial) Heq)

/-! # 2. THE PINNED BRIDGE -/

include HG Hmid Htext Hflow Hloc HnoRmw HnoSplit Hagree in
/-- Rocq `wpd_of_CertP`. -/
theorem AxCondM2.wpdOfCertP (Q : Cst → Unit → ExecSt → Prop) (m : SailM Unit) (s : Cst)
    (t : ExecSt) :
    AxCert.Cert img dok kind (fun _ _ _ => False) Q s m t →
    ∀ rs ib k, regsAgree AxRunClose.pinReg rs t.regs → AxCert2.bpos G i k s.csB →
    ⊢ CResP M dok kind i Out s.csD k -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResP M dok kind i Out s'.csD k' -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu m rs none ib, k⟩ Φ := by
  intro H
  induction H with
  | cRet s x t HQ =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply C $$ %s %t %rs %ib %kk %HQ %Hag %Hb Hd
  | cExt s e k t he => exact he.elim
  | cRd s r k t _ _ IHs IHn =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
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
      · iapply (IHs Hs (rs1 r) rs1 ib1 kk HA1 Hb) $$ Hd C
      · have h := IHn Hs rs1 ib1 kk HA1 Hb
        rw [← HA1 r Hs] at h
        iapply h $$ Hd C
  | cWr s r v k t Hr _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (wpdAdminNode3M M i Φ cpu G HG Hmid _ ?_ kk
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
      iapply (IH (rs1.set r v) ib1 kk (regsAgreeSet _ _ _ r v HA1) Hb) $$ Hd C
  | cMrd d b r n va req k t vs Hdev Hlat Hnf Hvs _ IH =>
    intro rs ib kk Hag Hb
    by_cases hR : ∃ aq rvs, d = .CRmwR aq rvs
    · -- a pinned state: the image read is refuted
      obtain ⟨aq, rvs, rfl⟩ := hR
      have hconv : CResP M dok kind i Out (.CRmwR aq rvs) kk ⊢
          iprop(FstM M dok i Out ∗ Pin M i kk rvs) := .rfl
      iintro Hd -
      ihave Hd := hconv $$ Hd
      icases Hd with ⟨-, #P⟩
      iapply (wpdPinMread M img i Φ cpu G HG Hmid Htext Hagree n va req k ib kk vs rvs
        Hdev Hlat Hnf Hvs) $$ %rs P
    · have hsh := AxCondM2.cresPShift M dok kind i Out d
        (fun aq rvs h => hR ⟨aq, rvs, h⟩) kk (kk + 1)
      iintro Hd C
      ihave Hd := hsh $$ Hd
      iapply (AxSymEngine3.wpdImgRead3M M img i Φ cpu G HG Hmid Htext Hflow n va req k ib kk vs
        (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
        (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf Hvs) $$ %rs %Hag
      iintro %rs' %HA'
      iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)) $$ Hd C
  | cIf s n va req k t vs Hdev Hlat Hfe Hvs _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (AxSymEngine3.wpdImgFetch3M M img i Φ cpu G HG Hmid Htext n va req k ib kk vs
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hfe Hvs) $$ %rs %Hag
    iintro %rs' %HA'
    iapply (IH rs' ib kk HA' Hb) $$ Hd C
  | cEnd d r n va req k t Hdev Hlat Hnf =>
    intro rs ib kk Hag Hb
    have Hb' : ∀ GD, G GD → (AxOpsem.grow GD i).length = kk + 0 := Hb
    iintro - -
    iapply (wpdStuckReadM M i Φ cpu G HG Hmid kk (fun GD h => Hb' GD h) n va req k ib
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hnf rs Hag)
  | cDrd b r n va req k t Hkd Hdev Hlat Hnf Hdok _ IH =>
    intro rs ib kk Hag Hb
    have hconv : CResP M dok kind i Out .CPend kk ⊢ FldM M dok i Out := by
      subst Hkd
      exact .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdDrdNodeM M dok kind i Φ cpu G HG Hmid HnoRmw Out n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hkd Hdev Hlat Hnf Hdok) $$ %rs %Hag Hd
    iintro %vs %rs' %Hlen %HA' HO
    have hdone : iprop(∃ kd, Out kd vs) ⊢ CResP M dok kind i Out (.CLd vs) (kk + 1) :=
      .rfl
    iapply (IH vs Hlen rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)) $$ [HO] C
    iapply hdone
    iexists kk
    iexact HO
  | cDwr b r n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    intro rs ib kk Hag Hb
    have hconv : CResP M dok kind i Out .CPend kk ⊢ FstM M dok i Out := by
      subst Hkd
      exact .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdDwrNodeM M dok i Φ cpu G HG Hmid Out n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag Hd
    iintro %rs' %HA' HO
    have hdone : iprop(∃ kd, Out kd (WeakInterpProj.wbytes n v)) ⊢
        CResP M dok kind i Out
          (.CSt (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) (kk + 1) := .rfl
    iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)) $$ [HO] C
    iapply hdone
    iexists kk
    iexact HO
  | cFence d b r bk k t Hpark _ IH =>
    intro rs ib kk Hag Hb
    by_cases hR : ∃ aq rvs, d = .CRmwR aq rvs
    · -- a pinned state: the fence is refuted
      obtain ⟨aq, rvs, rfl⟩ := hR
      have hconv : CResP M dok kind i Out (.CRmwR aq rvs) kk ⊢
          iprop(FstM M dok i Out ∗ Pin M i kk rvs) := .rfl
      iintro Hd -
      ihave Hd := hconv $$ Hd
      icases Hd with ⟨-, #P⟩
      iapply (wpdPinFence M i Φ cpu G HG Hmid Hagree bk k ib kk rvs) $$ %rs P
    · have hsh := AxCondM2.cresPShift M dok kind i Out d
        (fun aq rvs h => hR ⟨aq, rvs, h⟩) kk (kk + 1)
      iintro Hd C
      ihave Hd := hsh $$ Hd
      iapply (wpdFenceNodeM M i Φ cpu G HG Hmid Hloc bk k ib kk
        (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
        (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hpark) $$ %rs %Hag
      iintro %rs' %HA'
      iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)) $$ Hd C
  | cXrd b r n va req k t Hkd Hdev Hlat Hdok _ IH =>
    intro rs ib kk Hag Hb
    have hconv : CResP M dok kind i Out .CPend kk ⊢ FstM M dok i Out := by
      subst Hkd
      exact .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    iapply (wpdXrdPin M dok kind i Φ cpu G HG Hmid HnoSplit n va req k ib kk
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hkd Hdev Hlat Hdok) $$ %rs %Hag
    iintro %vs %rs' %Hlen %HA' #P
    have hbuild : iprop(FstM M dok i Out ∗ Pin M i kk vs) ⊢
        CResP M dok kind i Out (.CRmwR (classify req.access_kind).akSync vs) kk :=
      .rfl
    iapply (IH vs Hlen rs' ib kk HA' Hb) $$ [Hd] C
    iapply hbuild
    isplitl [Hd]
    · iexact Hd
    · iexact P
  | cXwr aq rvs b r n va req k t v Hkd Hdev Hlat Hval Hdok _ IH =>
    intro rs ib kk Hag Hb
    have hconv : CResP M dok kind i Out (.CRmwR aq rvs) kk ⊢
        iprop(FstM M dok i Out ∗ Pin M i kk rvs) := .rfl
    iintro Hd C
    ihave Hd := hconv $$ Hd
    icases Hd with ⟨F, #P⟩
    iapply (wpdXwrNodeM M dok i Φ cpu G HG Hmid Out n va req k ib kk v
      (fun rs1 => regsAgree AxRunClose.pinReg rs1 t.regs)
      (fun _ _ h1 h2 => regsAgreeTrans _ _ _ _ h2 h1) Hdev Hlat Hval Hdok) $$ %rs %Hag F
    iintro %rs' %HA' HO
    have hdone : iprop(∃ kd, Out kd (WeakInterpProj.wbytes n v) ∗ Pin M i kd rvs) ⊢
        CResP M dok kind i Out (.CRmw aq (classify req.access_kind).akSync rvs
          (WeakInterpProj.wbytes n v) (wcls req.access_kind r)) (kk + 1) := .rfl
    iapply (IH rs' ib (kk + 1) HA' (bposSucc G i kk b Hb)) $$ [HO] C
    iapply hdone
    iexists kk
    isplitl [HO]
    · iexact HO
    · iexact P
  | cIa s n w k t Hsf _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ (k ()) ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      rw [annLabelNot Hsf]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1 Hb) $$ Hd C
  | cBa s _ _ k t _ IH | cCo s _ k t _ IH | cTl s _ k t _ IH | cTe s _ k t _ IH
  | cRx s _ k t _ IH | cTs s _ k t _ IH | cTx s _ k t _ IH | cCc s k t _ IH
  | cMsg s _ k t _ IH | cGcc s k t _ IH =>
    intro rs ib kk Hag Hb
    iintro Hd C
    iapply (AxSymEngine3.wpdSilentNode3M M i Φ cpu G HG Hmid _ _ ?_ kk t ?_ rs ib Hag)
    all_goals try exact trivial
    · intro rs ib d l m' ors fn' d' oib obar h
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := h
      exact ⟨trivial, rfl, rfl, rfl⟩
    · iintro %rs1 %ib1 %HA1
      iapply (IH rs1 ib1 kk HA1 Hb) $$ Hd C

include HG Hmid Htext Hflow Hloc HnoRmw HnoSplit Hagree in
/-- Rocq `wpd_instr_of_CertP`: one instruction from a `.pure ()` boundary at position `k`. -/
theorem AxCondM2.wpdInstrOfCertP (Q : Cst → Unit → ExecSt → Prop) (s0 : Cst) (rs : RegFile)
    (k : Nat) (s : Athread) (Hs : RetX cpu rs k s)
    (Hbp : AxCert2.bpos G i k s0.csB)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1)
    (Hcert : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
       AxCert.Cert img dok kind (fun _ _ _ => False) Q s0 (riscvStep tick) t) :
    ⊢ CResP M dok kind i Out s0.csD k -∗
      (∀ s' t' rs' ib' k', ⌜Q s' () t'⌝ -∗ ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
         ⌜AxCert2.bpos G i k' s'.csB⌝ -∗ CResP M dok kind i Out s'.csD k' -∗
         wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i s Φ := by
  iintro Hd C
  iapply (wpdRetNode3M M i Φ cpu G HG rs k s Hs Hb)
  iintro %s2 %HN
  obtain ⟨tick, rs', Hag, rfl⟩ := HN
  iapply (AxCondM2.wpdOfCertP M img dok kind i Φ cpu G HG Hmid Htext Hflow Hloc HnoRmw HnoSplit
    Hagree Out Q _ s0 ⟨rs', fun _ => none, testDevs⟩
    (Hcert tick ⟨rs', fun _ => none, testDevs⟩ (regsAgreeSym _ _ _ Hag)) rs' ibNone k
    (regsAgreeRefl _ _) Hbp) $$ Hd C

end pinC

/-! # 3. The pinned X bridge and the S-mode AMO leaf -/

section xTP
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (textAt4 : BitVec 64 → BitVec 32 → Prop)
variable (Hsp : SpineOkT img ctrlOk textAt) (Hf4 : SpineFetch4T img ctrlOk textAt4)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Φ : Athread → IProp GF)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (dok : Int → Nat → Prop) (kind : Dkind) (Out : Nat → List (BitVec 8) → IProp GF)
variable (HnoRmw : kind = .DKLd → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)
variable (HnoSplit : kind = .DKRmw → ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)
variable (Hagree : ∀ GD GD', rvwmoCatConsistent GD → rvwmoCatConsistent GD' →
  ⊢ AxirisG.gconstInterp (GF := GF) GD -∗ AxirisG.gconstInterp GD' -∗ ⌜GD = GD'⌝)

include Hsp Hf4 Htext Hflow Hloc HG Hmid HnoRmw HnoSplit Hagree in
/-- Rocq `X_certTP`: `XCertT` on the pinned bridge. -/
theorem XCertTP (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w : BitVec 32)
    (ins : instruction) (ow : Cst → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cst → Prop)
    (HRet : RetX cpu rs k s) (Hctrl : ctrlOk rs) (HPC : rs .PC = pc) (Htx : textAt4 pc w)
    (Hsf : sfAnnB 32 w = false)
    (Hdec : ∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w) t)
    (How : ∀ s', PX s' → owOk (ow s')) (HPXb : ∀ s', PX s' → s'.csB = .BInf)
    (Hcert : CertXT img dok kind ctrlOk rs pc ins ow ⟨d0, .BInf, r0⟩ PX)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ CResP rvwmoCatConsistent dok kind i Out d0 k -∗
      (∀ (s' : Cst) (t' : ExecSt) (rs' : RegFile) (ib' : Ibch) (k' : Nat), ⌜PX s'⌝ -∗
        ⌜GoodC ctrlOk false rs pc none (ow s') t'.regs⌝ -∗
        ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
        CResP rvwmoCatConsistent dok kind i Out s'.csD k' -∗
        wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  have Hc : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      AxCert.Cert img dok kind (fun _ _ _ => False)
        (fun s' _ t' => PX s' ∧ GoodC ctrlOk false rs pc none (ow s') t'.regs)
        ⟨d0, .BInf, r0⟩ (riscvStep tick) t :=
    fun tick t Hag => spineCertXT img dok kind ctrlOk textAt textAt4 Hsp Hf4 rs pc w ins ow d0
      r0 PX Hctrl HPC Htx Hsf Hdec How HPXb Hcert tick t Hag
  have Hbr : CResP rvwmoCatConsistent dok kind i Out d0 k ⊢
      CResP rvwmoCatConsistent dok kind i Out (⟨d0, .BInf, r0⟩ : Cst).csD k := .rfl
  iintro D C
  ihave D := Hbr $$ D
  iapply (AxCondM2.wpdInstrOfCertP rvwmoCatConsistent img dok kind i Φ cpu G HG Hmid Htext Hflow
    Hloc HnoRmw HnoSplit Hagree Out _ ⟨d0, .BInf, r0⟩ rs k s HRet trivial Hb Hc) $$ D
  iintro %s' %t' %rs' %ib' %k' %HQ %Hag %_ HD
  obtain ⟨HP, HG'⟩ := HQ
  iapply C $$ %s' %t' %rs' %ib' %k' %HP %HG' %Hag HD

end xTP

section xSP
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
variable (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
  (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
  (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
variable (i : Agent) (cpu : CPU)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i (imgS σi)⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes (imgS σi) base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Φ : Athread → IProp GF)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)
variable (dok : Int → Nat → Prop) (Out : Nat → List (BitVec 8) → IProp GF)
variable (Hagree : ∀ GD GD', rvwmoCatConsistent GD → rvwmoCatConsistent GD' →
  ⊢ AxirisG.gconstInterp (GF := GF) GD -∗ AxirisG.gconstInterp GD' -∗ ⌜GD = GD'⌝)
variable (HnoSplit : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)

include hmode hasid hppn Htext Hflow Hloc HG Hmid HnoSplit Hagree in
/-- Rocq `X_amoswap_SP`: THE AMO LEAF WITH THE PIN — the write's output and the read's pin at
the SAME row position `kd`. -/
theorem XAmoswapSP (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w32 : BitVec 32)
    (aq : Bool) (rs2 rs1 rd : BitVec 5) (va pa : BitVec 64)
    (HRet : RetX cpu rs k s) (Hctrl : ctrlOkSW T satp0 rs) (HPC : rs .PC = pc)
    (Htx : textAt4S σi T pc w32) (Hsf : sfAnnB 32 w32 = false)
    (Hdec : ∀ t : ExecSt, ctrlOkSW T satp0 t.regs →
      EvA (imgS σi) (fun _ _ => False)
        (fun x t' => x = .AMO (.AMOSWAP, aq, false, .Regidx rs2, .Regidx rs1, 4, .Regidx rd) ∧
          t' = t) (ext_decode w32) t)
    (Hrd : rd.toNat ≠ 0)
    (Hva : va = gprVal rs rs1 + zeros (n := 64))
    (Hda : dataAtS σi T (accAmo aq) va 4 pa) (Hdok : dok (paZ pa) 4)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ FstM rvwmoCatConsistent dok i Out -∗
      (∀ (vs : List (BitVec 8)) (t' : ExecSt) (rs' : RegFile) (ib' : Ibch) (k' : Nat),
        ⌜vs.length = 4⌝ -∗
        ⌜GoodC (ctrlOkSW T satp0) false rs pc none (some (rd, amoLdv 4 vs)) t'.regs⌝ -∗
        ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
        (∃ kd, Out kd (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2))) ∗
          Pin rvwmoCatConsistent i kd vs) -∗
        wpdM rvwmoCatConsistent .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM rvwmoCatConsistent .MaybeStuck i s Φ := by
  have Hcert := CertXTAmoswapS σi T satp0 hmode hasid hppn dok rs pc aq rs2 rs1 rd va pa false
    Hrd Hva Hda Hdok
  have How : ∀ s', (∃ vs, s' = (⟨.CRmw aq false vs (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)))
      (wcls akXc false), .BInf, false⟩ : Cst) ∧ vs.length = 4) → owOk (owAmo rd s') := by
    rintro _ ⟨_, rfl, _⟩
    exact Hrd
  have HPXb : ∀ s', (∃ vs, s' = (⟨.CRmw aq false vs (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)))
      (wcls akXc false), .BInf, false⟩ : Cst) ∧ vs.length = 4) → s'.csB = .BInf := by
    rintro _ ⟨_, rfl, _⟩
    rfl
  have Hbr : FstM rvwmoCatConsistent dok i Out ⊢
      CResP rvwmoCatConsistent dok .DKRmw i Out .CPend k := .rfl
  iintro F C
  ihave F := Hbr $$ F
  iapply (XCertTP (imgS σi) i cpu (ctrlOkSW T satp0) (textAtS σi T) (textAt4S σi T)
    (SpineOkTSW σi T satp0 hmode hasid hppn) (SpineFetch4TSW σi T satp0 hmode hasid hppn)
    Htext Hflow Hloc G HG Φ Hmid dok .DKRmw Out (fun h => nomatch h) (fun _ => HnoSplit) Hagree
    s rs k pc w32 _ (owAmo rd) .CPend false _ HRet Hctrl HPC Htx Hsf Hdec How HPXb Hcert
    Hb) $$ F
  iintro %s' %t' %rs' %ib' %k' %HP %HG' %Hag HD
  obtain ⟨vs, rfl, Hlen⟩ := HP
  have Hbr2 : CResP rvwmoCatConsistent dok .DKRmw i Out
      (⟨.CRmw aq false vs (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2)))
        (wcls akXc false), .BInf, false⟩ : Cst).csD k' ⊢
      iprop(∃ kd, Out kd (AxDataX.wrb 4 (amoStv 4 (gprVal rs rs2))) ∗
        Pin rvwmoCatConsistent i kd vs) := .rfl
  ihave HD := Hbr2 $$ HD
  iapply C $$ %vs %t' %rs' %ib' %k' %Hlen %HG' %Hag HD

end xSP

/-! # 4. The flow side: an output indexed by the event's own READ value -/

section outv
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (i : Agent)
variable (Hagree : ∀ GD GD', rvwmoCatConsistent GD → rvwmoCatConsistent GD' →
  ⊢ AxirisG.gconstInterp (GF := GF) GD -∗ AxirisG.gconstInterp GD' -∗ ⌜GD = GD'⌝)

/-- A write flow's output may depend on the graph value of the SAME fused event: the flow is
given `GD`, so it can produce `OutV k (graphValue GD (i, k)) data` (keeping `GD`'s agreement as
a witness). -/
def OutOfV (OutV : Nat → Option (List (BitVec 8)) → List (BitVec 8) → IProp GF) :
    Nat → List (BitVec 8) → IProp GF :=
  fun k data => iprop(∃ GD, ⌜rvwmoCatConsistent GD⌝ ∗ □ AxirisG.gconstInterp (GF := GF) GD ∗
    OutV k (graphValue GD (i, k)) data)

include Hagree in
/-- With the pin, that output is the one at the hart's OWN bytes. -/
theorem amoOutPin (OutV : Nat → Option (List (BitVec 8)) → List (BitVec 8) → IProp GF)
    (k : Nat) (vs data : List (BitVec 8)) :
    ⊢ Pin rvwmoCatConsistent i k vs -∗ OutOfV i OutV k data -∗
      OutV k (some vs) data := by
  unfold OutOfV
  iintro #P ⟨%GD, %Hc, #Hg, HO⟩
  ihave Hpf := (AxCondM2.pinAt rvwmoCatConsistent i Hagree GD k vs Hc) $$ Hg P
  icases Hpf with %Hpf
  rw [← Hpf.1]
  iexact HO

end outv

end Weak
