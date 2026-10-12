/-
Weak: **PHASE 5 POSITIONAL ENGINE, part 3: the WPd-level plumbing.**

Rocq: `iris/AxSpinE3.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 FIT-OR-STUCK at a RAM node (`wpdRdFitOrStuckM` / write / fence): at a plain RAM read (write,
   fence) node at row position `k` of a PINNED graph (`gconstInterp GD ⊢ ⌜GD = GD0⌝`): EITHER the
   physically emitted label fits `row[k]?` (the caller's continuation gets that as a pure ROW
   fact) OR the hart is row-stuck — `rowStuckOfFirst` with `F` = {this node's labels} and
   `firstEv` TRIVIAL (a RAM node has no administrative step, a wire keeps the node) — so `wpdM`
   holds for EVERY postcondition (`wpdMStuck`).
§2 THE OFF-ROW RETURN, from ONE named Sail premise.  `FirstRd img P Q m t`: every path of the
   tree `m` from `t` (both answers of every pin read) either reaches a plain RAM read whose
   (address, width) satisfies `P`, or returns with `Q`.  THE PREMISE (a section variable `HVA`,
   instantiated in AxSpinE5): for every regime state `rs`, `riscvStep tick` (both ticks) is
   `FirstRd img (P (rs .PC)) (fun t' => C t'.regs ∧ t'.regs .PC = stv)`.  `firstEvOffrow` /
   `offrowRowStuck`: from such a boundary whose PC is in an OFF set `Off` (no first read of an
   `Off` address fits the row item at `k`; `stv ∈ Off`) the hart is row-stuck — every run stays
   at `k`, through any number of trap round trips — hence `wpdOffrowM`: `wpdM` for EVERY
   postcondition, with no `Hmid` premise.
§3 THE POSITIONAL X LEAF `XB`: `wpdInstrOfCert` at budget `BFin` + `AxSpinE.spineCertB`: from a
   boundary at row position `k` (row length `L` pinned by the graph fact `G`), an instruction
   whose `execute` consumes `e` items hands its continuation the boundary AT POSITION `k + e`
   (exact; Stage C, Rocq `k + e + 1`), with `GoodB` (regime, PC, GPRs, TLB) and the data event's
   resource; the boundary's own row-end obligation is discharged by arithmetic (`k < L`).

## Deviations from Rocq

1. O2 STAGE C (fetches are administrative `LIFetch` steps, not row reads; `AxSpinE` deviation 1).
   * §1: the read-node lemmas `kreachRdNode`, `wpdRdStuckM`, `wpdRdFitOrStuckM` take
     `Hnf : (classify req.access_kind).akIfetch = false` after `Hlat` (an `akIfetch` node steps by
     an administrative fetch, so it is not stuck).
   * §2: `FirstRd` takes the image `img` first.  Its first-read constructor `frMrd` takes
     `akIfetch = false`; a FETCH no longer is a first read: the Lean-only constructors `frIf`
     (an image-answered fetch CONTINUES with the image bytes, as `AxSpinVA.FEC.fcIf`) and `frNf`
     (a fetch with no image bytes: no pinned step at all, as `fcNf`).  Hence the off-row runs are
     the IMAGE-PINNED runs (Q12): `firstEvOffrow` is `firstEv (WeakAxRealize.fetchPin img) …`,
     `frsClosed` is over `kstep0 (fetchPin img)`, `FirstRdStep`'s administrative half takes
     `fetchPin img l`, `offrowRowStuck` concludes `rowStuckR (fetchPin img) row …` (Rocq's
     `row_stuck_r row Tt img`; its `Tt img` parameters are dropped) and `wpdOffrowM` takes
     `HGimg : ∀ GD, G GD → GD.gdG.gxImg = img` after `HG`.  §1 uses `pin := fun _ => True`;
     the `kreach*` lemmas are generic in `pin`.
   * §3: the instruction consumes EXACTLY `e` row items (Rocq `e + 1`): `XB`'s continuation is at
     `k + e` and its arithmetic premise `k + e + 1 ≤ L` becomes the two premises `k < L` (the
     boundary's row-end obligation) and `k + e ≤ L`.
2. Q7 (sfence.vma announce is a fence marker): `FirstRd.frIa` takes `sfAnnB n w = false`
   (a non-sfence announce is administrative; there is no sfence constructor — its label is a
   fence, not a first read).  Lean-only `frExt`: a failure node `.impure (.error e) _` has no
   step (Rocq's `M` has no such node in `FirstRd`).
3. THE PINS: `regs_agree seip_reg` ↦ `regsAgree AxRunClose.pinReg` (`AxRunClose` deviation 1);
   `FirstRd.frRd` branches on `AxRunClose.pinReg r`, `frWr` takes `¬ AxRunClose.pinReg r`.
4. LEAN-SAIL WRITE VALUES ARE `Option`: the write-node lemmas state the row width as `n` (Rocq
   `length (wbytes n value)`, equal by `wbytesLength`).
5. TYPES as `AxSpinE` deviation 3: `register_lookup r s.(sregs)` ↦ `s.regs r`, `set_reg` ↦
   `setReg`, `mstate` ↦ `ExecSt`, `MState rs ∅ dev0_state` ↦ `⟨rs, fun _ => none, testDevs⟩`,
   `Interface.Ret tt` ↦ `.pure ()`, `Interface.Next (o) k` ↦ `.impure (.ok o) k`, `row !! k` ↦
   `row[k]?`.  `invGS_gen HasNoLc Σ` ↦ `[InvGS_gen hlc GF]` (any `hlc`) in §1 and `wpdOffrowM`.
   Section variables are explicit arguments (the `xB` section's `Hmode Hasid Hppn` are
   `hmode hasid hppn`); Rocq's `Hntext` (xB) is DROPPED (`AxCert2` deviation 1).  The section
   notations `img`/`ctrl_ok` are unfolded (`imgS σi`, `ctrlOkSW T satp0`).
6. The Ltac `ps_silentE` is replaced by the Lean-only `AxSpinE3.nodeStepInv` (a hart program
   step, inverted to its `pnodeStep`).  The wires are inverted by `pstepWireInv` (Rocq
   `pstep_wire_inv` / `awire_aeqv`).

**Rocq → Lean name map.**  `kreach_rd_node` `kreachRdNode`, `kreach_wr_node` `kreachWrNode`,
`kreach_fence_node` `kreachFenceNode`, `wpd_rd_stuckM` `wpdRdStuckM`, `wpd_wr_stuckM`
`wpdWrStuckM`, `wpd_fence_stuckM` `wpdFenceStuckM`, `wpd_rd_fit_or_stuckM` `wpdRdFitOrStuckM`,
`wpd_wr_fit_or_stuckM` `wpdWrFitOrStuckM`, `wpd_fence_fit_or_stuckM` `wpdFenceFitOrStuckM`,
`FirstRd` `FirstRd` (constructors `fr_ret` `frRet`, `fr_rd` `frRd`, `fr_wr` `frWr`, `fr_mrd`
`frMrd`, `fr_ia` `frIa`, `fr_ba` `frBa`, `fr_co` `frCo`, `fr_tl` `frTl`, `fr_te` `frTe`, `fr_rx`
`frRx`, `fr_ts` `frTs`, `fr_tx` `frTx`, `fr_cc` `frCc`, `fr_msg` `frMsg`, `fr_gcc` `frGcc`;
Lean-only `frIf`, `frNf`, `frExt`), `Qv` `Qv`, `FRS` `FRS`, `Foff` `Foff`, `frs_of_boundary`
`frsOfBoundary`, `FirstRd_step` `FirstRdStep`, `frs_closed` `frsClosed`, `first_ev_offrow`
`firstEvOffrow`, `offrow_row_stuck` `offrowRowStuck`, `wpd_offrowM` `wpdOffrowM`, `GoodB_agree`
`GoodBAgree`, `XB` `XB`.  Lean-only (file-qualified): `AxSpinE3.nodeStepInv`.

**Dropped:** nothing (Rocq 21 definitions/lemmas + 1 Ltac; Lean 21 + 1 Lean-only).
**Not ported:** the Ltac `ps_silentE` (deviation 6); the `Print Assumptions` lines (the lint's
axiom check covers them).
-/
import Weak.AxSpinE
import Weak.AxSpinVA
import Weak.AxEpiLedgerSd

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions
open Wlabel

/-! # 0. A hart program step, inverted -/

/-- (Lean-only, Rocq Ltac `ps_silentE`) A program step of a hart thread (no parked fence) is a
`pnodeStep` of its monad, landing at the step's continuation. -/
theorem AxSpinE3.nodeStepInv (cpu : CPU) (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : Efab)
    (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    pstepProg (.PHart cpu m rs none ib) d l p' d' →
    ∃ (m' : SailM Unit) (ors : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool))
      (oib : Option Ibch) (obar : Option barrier_kind) (dv : DevStates),
      pnodeStep m rs ib d.efDev l m' ors fn' dv oib obar ∧
      p' = .PHart cpu m' (ors.getD rs) fn' (oib.getD ib) := by
  intro h
  cases p' with
  | PDisk _ => exact h.elim
  | PHart c' m' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, rfl, rfl, hn, -⟩ := h
    exact ⟨m', ors, fn', oib, obar, _, hn, rfl⟩

/-! # 1. FIT-OR-STUCK at a RAM node -/

/-- A RAM read node (not a fetch): no administrative step, wires keep the node. -/
theorem kreachRdNode (pin : Wlabel → Prop) (cpu : CPU) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) (s2 : Athread) :
    devAddr req.pa = false → (classify req.access_kind).akLatest = false →
    (classify req.access_kind).akIfetch = false →
    rtc (kstep0 pin) ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ s2 →
    ∃ rs', s2 = ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs' none ib, k⟩ := by
  intro hdev hlat hnf h
  induction h with
  | refl => exact ⟨rs, rfl⟩
  | @tail s1 s3 _ hst ih =>
    obtain ⟨rs1, rfl⟩ := ih
    obtain ⟨p3, k3⟩ := s3
    rcases hst with ⟨-, d, l, d', hadm, -, hps⟩ | ⟨hk, d, d', hw⟩
    · exfalso
      obtain ⟨tvs, -, rfl, -⟩ := fetchNodePstep cpu n va req KK rs1 ib d l p3 d' hdev hlat hps
      simp [rdLabel, hnf, AxOpsem.lbAdminAx] at hadm
    · obtain ⟨-, cpu', m', rs', fn', ib', mm, b, kk, hp, -, -, hp'⟩ := pstepWireInv _ _ _ _ _ hw
      dsimp only at hp hp' hk
      cases hp
      subst hp' hk
      exact ⟨_, rfl⟩

/-- A RAM write node: no administrative step, wires keep the node. -/
theorem kreachWrNode (pin : Wlabel → Prop) (cpu : CPU) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (s2 : Athread) :
    devAddr req.pa = false → (classify req.access_kind).akLatest = false →
    rtc (kstep0 pin) ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ s2 →
    ∃ rs', s2 = ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs' none ib, k⟩ := by
  intro hdev hlat h
  induction h with
  | refl => exact ⟨rs, rfl⟩
  | @tail s1 s3 _ hst ih =>
    obtain ⟨rs1, rfl⟩ := ih
    obtain ⟨p3, k3⟩ := s3
    rcases hst with ⟨-, d, l, d', hadm, -, hps⟩ | ⟨hk, d, d', hw⟩
    · exfalso
      obtain ⟨v, -, rfl, -⟩ := storeNodePstep cpu n va req KK rs1 ib d l p3 d' hdev hlat hps
      simp [AxOpsem.lbAdminAx] at hadm
    · obtain ⟨-, cpu', m', rs', fn', ib', mm, b, kk, hp, -, -, hp'⟩ := pstepWireInv _ _ _ _ _ hw
      dsimp only at hp hp' hk
      cases hp
      subst hp' hk
      exact ⟨_, rfl⟩

/-- A barrier node: no administrative step, wires keep the node. -/
theorem kreachFenceNode (pin : Wlabel → Prop) (cpu : CPU) (bk : barrier_kind)
    (KK : Unit → SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat) (s2 : Athread) :
    rtc (kstep0 pin) ⟨.PHart cpu (.impure (.ok (.barrier bk)) KK) rs none ib, k⟩ s2 →
    ∃ rs', s2 = ⟨.PHart cpu (.impure (.ok (.barrier bk)) KK) rs' none ib, k⟩ := by
  intro h
  induction h with
  | refl => exact ⟨rs, rfl⟩
  | @tail s1 s3 _ hst ih =>
    obtain ⟨rs1, rfl⟩ := ih
    obtain ⟨p3, k3⟩ := s3
    rcases hst with ⟨-, d, l, d', hadm, -, hps⟩ | ⟨hk, d, d', hw⟩
    · exfalso
      obtain ⟨rfl, -⟩ := barrierPstep cpu bk KK rs1 ib d l p3 d' hps
      exact ebarLabelNotAdmin bk hadm
    · obtain ⟨-, cpu', m', rs', fn', ib', mm, b, kk, hp, -, -, hp'⟩ := pstepWireInv _ _ _ _ _ hw
      dsimp only at hp hp' hk
      cases hp
      subst hp' hk
      exact ⟨_, rfl⟩

section fit
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop) (i : Agent) (cpu : CPU)

/-- THE STUCK ARM at a read node. -/
theorem wpdRdStuckM (G : Gdexec → Prop)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Φ : Athread → IProp GF) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false) :
    (∀ GD, G GD → k < (AxOpsem.grow GD i).length ∧
      ∀ lb aq, (AxOpsem.grow GD i)[k]? = some lb →
        aidentRd (aident lb) ≠ some (aq, paZ req.pa, n)) →
    ⊢ wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  intro Hrej
  refine wpdMStuck M i G HG (fun _ => True) (fun _ _ _ _ => trivial) Φ _ ?_
  intro GD HGD
  obtain ⟨Hlt, Hr⟩ := Hrej GD HGD
  refine rowStuckOfFirst (fun _ => True) _ _
    (fun l => ∃ tvs : List (Nat × BitVec 8), tvs.length = n ∧
      l = LLoad (classify req.access_kind).akSync false (paZ req.pa) tvs []) ?_ ?_ Hlt
  · intro s2 Hr2 d l p' d' Hps _
    obtain ⟨rs', rfl⟩ := kreachRdNode _ cpu n va req KK rs ib k s2 Hdev Hlat Hnf Hr2
    obtain ⟨tvs, Htl, rfl, -⟩ := fetchNodePstep cpu n va req KK rs' ib d l p' d' Hdev Hlat Hps
    exact ⟨tvs, Htl, by simp [rdLabel, Hnf]⟩
  · rintro lb Hlb l ⟨tvs, Htl, rfl⟩ Hfit
    rcases Hfit with ⟨-, Hrd⟩ | ⟨Hx, -⟩ | ⟨Hx, -⟩
    · simp only [wlRd, Htl] at Hrd
      exact Hr lb _ Hlb Hrd.symm
    · simp [wlWr] at Hx
    · simp [wlFence] at Hx

/-- THE STUCK ARM at a write node. -/
theorem wpdWrStuckM (G : Gdexec → Prop)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Φ : Athread → IProp GF) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false) :
    (∀ GD, G GD → k < (AxOpsem.grow GD i).length ∧
      ∀ lb rl, (AxOpsem.grow GD i)[k]? = some lb →
        aidentWr (aident lb) ≠ some (rl, paZ req.pa, n)) →
    ⊢ wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ Φ := by
  intro Hrej
  refine wpdMStuck M i G HG (fun _ => True) (fun _ _ _ _ => trivial) Φ _ ?_
  intro GD HGD
  obtain ⟨Hlt, Hr⟩ := Hrej GD HGD
  refine rowStuckOfFirst (fun _ => True) _ _
    (fun l => ∃ (v : BitVec (8 * n)) (asrc : List Dsrc) (vsrc : List Dsrc),
      l = LStore (classify req.access_kind).akSync (paZ req.pa) (WeakInterpProj.wbytes n v)
        asrc vsrc) ?_ ?_ Hlt
  · intro s2 Hr2 d l p' d' Hps _
    obtain ⟨rs', rfl⟩ := kreachWrNode _ cpu n va req KK rs ib k s2 Hdev Hlat Hr2
    obtain ⟨v, -, rfl, -⟩ := storeNodePstep cpu n va req KK rs' ib d l p' d' Hdev Hlat Hps
    exact ⟨v, _, _, rfl⟩
  · rintro lb Hlb l ⟨v, asrc, vsrc, rfl⟩ Hfit
    rcases Hfit with ⟨Hx, -⟩ | ⟨-, Hwr⟩ | ⟨Hx, -⟩
    · simp [wlRd] at Hx
    · simp only [wlWr, wbytesLength] at Hwr
      exact Hr lb _ Hlb Hwr.symm
    · simp [wlFence] at Hx

/-- THE STUCK ARM at a barrier node. -/
theorem wpdFenceStuckM (G : Gdexec → Prop)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Φ : Athread → IProp GF) (bk : barrier_kind) (KK : Unit → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) :
    (∀ GD, G GD → k < (AxOpsem.grow GD i).length ∧
      ∀ lb, (AxOpsem.grow GD i)[k]? = some lb →
        aidentFence (aident lb) ≠ wlFence (ebarLabel bk)) →
    ⊢ wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.barrier bk)) KK) rs none ib, k⟩ Φ := by
  intro Hrej
  refine wpdMStuck M i G HG (fun _ => True) (fun _ _ _ _ => trivial) Φ _ ?_
  intro GD HGD
  obtain ⟨Hlt, Hr⟩ := Hrej GD HGD
  refine rowStuckOfFirst (fun _ => True) _ _ (fun l => l = ebarLabel bk) ?_ ?_ Hlt
  · intro s2 Hr2 d l p' d' Hps _
    obtain ⟨rs', rfl⟩ := kreachFenceNode _ cpu bk KK rs ib k s2 Hr2
    exact (barrierPstep cpu bk KK rs' ib d l p' d' Hps).1
  · rintro lb Hlb l rfl Hfit
    obtain ⟨pr, pw, sr, sw, Hlab⟩ := ebarLabelFence bk
    rcases Hfit with ⟨Hx, -⟩ | ⟨Hx, -⟩ | ⟨-, Hf⟩
    · rw [Hlab] at Hx; simp [wlRd] at Hx
    · rw [Hlab] at Hx; simp [wlWr] at Hx
    · exact Hr lb Hlb Hf.symm

/-- FIT-OR-STUCK at a read node, at a PINNED graph: the continuation learns the fit as a ROW
fact; otherwise the hart is stuck and `wpdM` holds for any `Φ`. -/
theorem wpdRdFitOrStuckM (GD0 : Gdexec)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜GD = GD0⌝)
    (Φ : Athread → IProp GF) (n va : Nat)
    (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hnf : (classify req.access_kind).akIfetch = false)
    (Hlt : k < (AxOpsem.grow GD0 i).length) :
    ⊢ (⌜∃ lb aq, (AxOpsem.grow GD0 i)[k]? = some lb ∧
          aidentRd (aident lb) = some (aq, paZ req.pa, n)⌝ -∗
        wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memRead n va req)) KK) rs none ib, k⟩ Φ := by
  iintro H
  rcases Elb : (AxOpsem.grow GD0 i)[k]? with _ | lb
  · rw [List.getElem?_eq_none_iff] at Elb
    omega
  · by_cases Hfit : ∃ aq, aidentRd (aident lb) = some (aq, paZ req.pa, n)
    · obtain ⟨aq, Ha⟩ := Hfit
      iapply H
      ipureintro
      exact ⟨lb, aq, rfl, Ha⟩
    · have Hst := wpdRdStuckM M i cpu (fun GD => GD = GD0) HG Φ n va req KK rs ib k Hdev Hlat Hnf
        (by
          rintro GD rfl
          refine ⟨Hlt, ?_⟩
          intro lb' aq' Hlb' Hrd
          rw [Elb] at Hlb'
          cases Hlb'
          exact Hfit ⟨aq', Hrd⟩)
      iclear H
      ihave Hs := Hst
      iexact Hs

/-- FIT-OR-STUCK at a write node, at a PINNED graph. -/
theorem wpdWrFitOrStuckM (GD0 : Gdexec)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜GD = GD0⌝)
    (Φ : Athread → IProp GF) (n va : Nat)
    (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (KK : Result (Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (ib : Ibch) (k : Nat)
    (Hdev : devAddr req.pa = false) (Hlat : (classify req.access_kind).akLatest = false)
    (Hlt : k < (AxOpsem.grow GD0 i).length) :
    ⊢ (⌜∃ lb rl, (AxOpsem.grow GD0 i)[k]? = some lb ∧
          aidentWr (aident lb) = some (rl, paZ req.pa, n)⌝ -∗
        wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.memWrite n va req)) KK) rs none ib, k⟩ Φ := by
  iintro H
  rcases Elb : (AxOpsem.grow GD0 i)[k]? with _ | lb
  · rw [List.getElem?_eq_none_iff] at Elb
    omega
  · by_cases Hfit : ∃ rl, aidentWr (aident lb) = some (rl, paZ req.pa, n)
    · obtain ⟨rl, Ha⟩ := Hfit
      iapply H
      ipureintro
      exact ⟨lb, rl, rfl, Ha⟩
    · have Hst := wpdWrStuckM M i cpu (fun GD => GD = GD0) HG Φ n va req KK rs ib k Hdev Hlat
        (by
          rintro GD rfl
          refine ⟨Hlt, ?_⟩
          intro lb' rl' Hlb' Hwr
          rw [Elb] at Hlb'
          cases Hlb'
          exact Hfit ⟨rl', Hwr⟩)
      iclear H
      ihave Hs := Hst
      iexact Hs

/-- FIT-OR-STUCK at a barrier node, at a PINNED graph. -/
theorem wpdFenceFitOrStuckM (GD0 : Gdexec)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜GD = GD0⌝)
    (Φ : Athread → IProp GF) (bk : barrier_kind) (KK : Unit → SailM Unit) (rs : RegFile)
    (ib : Ibch) (k : Nat) (Hlt : k < (AxOpsem.grow GD0 i).length) :
    ⊢ (⌜∃ lb, (AxOpsem.grow GD0 i)[k]? = some lb ∧
          aidentFence (aident lb) = wlFence (ebarLabel bk)⌝ -∗
        wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.barrier bk)) KK) rs none ib, k⟩ Φ) -∗
      wpdM M .MaybeStuck i ⟨.PHart cpu (.impure (.ok (.barrier bk)) KK) rs none ib, k⟩ Φ := by
  iintro H
  rcases Elb : (AxOpsem.grow GD0 i)[k]? with _ | lb
  · rw [List.getElem?_eq_none_iff] at Elb
    omega
  · by_cases Hfit : aidentFence (aident lb) = wlFence (ebarLabel bk)
    · iapply H
      ipureintro
      exact ⟨lb, rfl, Hfit⟩
    · have Hst := wpdFenceStuckM M i cpu (fun GD => GD = GD0) HG Φ bk KK rs ib k
        (by
          rintro GD rfl
          refine ⟨Hlt, ?_⟩
          intro lb' Hlb'
          rw [Elb] at Hlb'
          cases Hlb'
          exact Hfit)
      iclear H
      ihave Hs := Hst
      iexact Hs

end fit

/-! # 2. THE OFF-ROW RETURN -/

/-- Every path reaches a plain RAM read at a `P` address, or returns with `Q` (deviation 1/2:
image-answered fetches continue, image-less fetches and failure nodes have no step). -/
inductive FirstRd (img : Image) (P : Int → Nat → Prop) (Q : ExecSt → Prop) :
    SailM Unit → ExecSt → Prop where
  | frRet (t : ExecSt) : Q t → FirstRd img P Q (.pure ()) t
  | frRd (r : Register) (k : RegisterType r → SailM Unit) (t : ExecSt) :
      (AxRunClose.pinReg r → ∀ v, FirstRd img P Q (k v) t) →
      (¬ AxRunClose.pinReg r → FirstRd img P Q (k (t.regs r)) t) →
      FirstRd img P Q (.impure (.ok (.regRead r)) k) t
  | frWr (r : Register) (v : RegisterType r) (k : PUnit → SailM Unit) (t : ExecSt) :
      ¬ AxRunClose.pinReg r → FirstRd img P Q (k PUnit.unit) (t.setReg r v) →
      FirstRd img P Q (.impure (.ok (.regWrite r v)) k) t
  | frMrd (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akLatest = false →
      (classify req.access_kind).akIfetch = false → P (paZ req.pa) n →
      FirstRd img P Q (.impure (.ok (.memRead n va req)) k) t
  /-- (Lean-only, Stage C) an image-answered FETCH continues with the image bytes -/
  | frIf (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t : ExecSt)
      (vs : List (BitVec 8)) :
      devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
      imgBytes img (paZ req.pa) n = some vs →
      FirstRd img P Q (k (.Ok (wordOfBytes n vs, none))) t →
      FirstRd img P Q (.impure (.ok (.memRead n va req)) k) t
  /-- (Lean-only, Stage C) a FETCH with no image bytes: no pinned step -/
  | frNf (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
      (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM Unit) (t : ExecSt) :
      devAddr req.pa = false → (classify req.access_kind).akIfetch = true →
      imgBytes img (paZ req.pa) n = none →
      FirstRd img P Q (.impure (.ok (.memRead n va req)) k) t
  | frIa (n : Nat) (w : BitVec n) (k : Unit → SailM Unit) (t : ExecSt) :
      sfAnnB n w = false → FirstRd img P Q (k ()) t →
      FirstRd img P Q (.impure (.ok (.instrAnnounce n w)) k) t
  | frBa (n : Nat) (a : BitVec n) (k : Unit → SailM Unit) (t : ExecSt) :
      FirstRd img P Q (k ()) t → FirstRd img P Q (.impure (.ok (.branchAnnounce n a)) k) t
  | frCo (c : Arch.cache_op) (k : Unit → SailM Unit) (t : ExecSt) :
      FirstRd img P Q (k ()) t → FirstRd img P Q (.impure (.ok (.cacheOp c)) k) t
  | frTl (c : Arch.tlb_op) (k : Unit → SailM Unit) (t : ExecSt) :
      FirstRd img P Q (k ()) t → FirstRd img P Q (.impure (.ok (.tlbi c)) k) t
  | frTe (f : Arch.fault) (k : Unit → SailM Unit) (t : ExecSt) :
      FirstRd img P Q (k ()) t → FirstRd img P Q (.impure (.ok (.takeException f)) k) t
  | frRx (a : Arch.pa) (k : Unit → SailM Unit) (t : ExecSt) :
      FirstRd img P Q (k ()) t → FirstRd img P Q (.impure (.ok (.returnException a)) k) t
  | frTs (a : Arch.trans_start) (k : Unit → SailM Unit) (t : ExecSt) :
      FirstRd img P Q (k ()) t → FirstRd img P Q (.impure (.ok (.translationStart a)) k) t
  | frTx (a : Arch.trans_end) (k : Unit → SailM Unit) (t : ExecSt) :
      FirstRd img P Q (k ()) t → FirstRd img P Q (.impure (.ok (.translationEnd a)) k) t
  | frCc (k : Unit → SailM Unit) (t : ExecSt) :
      FirstRd img P Q (k ()) t → FirstRd img P Q (.impure (.ok .cycleCount) k) t
  | frMsg (a : String) (k : Unit → SailM Unit) (t : ExecSt) :
      FirstRd img P Q (k ()) t → FirstRd img P Q (.impure (.ok (.message a)) k) t
  | frGcc (k : Nat → SailM Unit) (t : ExecSt) :
      FirstRd img P Q (k (0 : Nat)) t → FirstRd img P Q (.impure (.ok .getCycleCount) k) t
  /-- (Lean-only) a failure node: no step at all -/
  | frExt (e : Sail.Error exception) (k : Empty → SailM Unit) (t : ExecSt) :
      FirstRd img P Q (.impure (.error e) k) t

section offrow
variable (img : Image) (C : RegFile → Prop)
variable (HC : ∀ rs rs', C rs → regsAgree AxRunClose.pinReg rs' rs → C rs')
variable (P : BitVec 64 → Int → Nat → Prop) (stv : BitVec 64)

def Qv (t' : ExecSt) : Prop := C t'.regs ∧ t'.regs .PC = stv

/- THE ARBITRARY-VA PREMISE (instantiated in AxSpinE5) -/
variable (HVA : ∀ rs, C rs → ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
  FirstRd img (P (rs .PC)) (fun t' => C t'.regs ∧ t'.regs .PC = stv) (riscvStep tick) t)
variable (Off : BitVec 64 → Prop) (Hstv : Off stv)
variable (cpu : CPU) (k : Nat)

/-- The states the off-row hart can be in, at position `k`. -/
def FRS (s : Athread) : Prop :=
  s.atK = k ∧
  ((∃ rs ib, s.atP = .PHart cpu (.pure ()) rs none ib ∧ C rs ∧ Off (rs .PC)) ∨
   (∃ (m : SailM Unit) (rs : RegFile) (ib : Ibch) (t : ExecSt) (v : BitVec 64),
      s.atP = .PHart cpu m rs none ib ∧ regsAgree AxRunClose.pinReg rs t.regs ∧
      Off v ∧ FirstRd img (P v) (Qv C stv) m t))

def Foff (l : Wlabel) : Prop :=
  ∃ aq pa tvs v, l = LLoad aq false pa tvs [] ∧ Off v ∧ P v pa tvs.length

include HVA in
theorem frsOfBoundary (rs : RegFile) (ib : Ibch) (tick : Bool) :
    C rs → Off (rs .PC) →
    FRS img C P stv Off cpu k ⟨.PHart cpu (riscvStep tick) rs none ib, k⟩ := by
  intro Hc Ho
  exact ⟨rfl, .inr ⟨riscvStep tick, rs, ib, ⟨rs, fun _ => none, testDevs⟩, rs .PC, rfl,
    regsAgreeRefl _ _, Ho, HVA rs Hc tick _ (regsAgreeRefl _ _)⟩⟩

include HC HVA Hstv in
theorem FirstRdStep (v : BitVec 64) (m : SailM Unit) (t : ExecSt)
    (H : FirstRd img (P v) (Qv C stv) m t) :
    Off v → ∀ rs ib, regsAgree AxRunClose.pinReg rs t.regs →
    ∀ d l p' d', pstepProg (.PHart cpu m rs none ib) d l p' d' →
      (AxOpsem.lbAdminAx true l → WeakAxRealize.fetchPin img l → FRS img C P stv Off cpu k ⟨p', k⟩) ∧
      (¬ AxOpsem.lbAdminAx true l → Foff P Off l) := by
  intro Hoff rs ib Hag d l p' d' Hps
  cases H with
  | frRet t HQ =>
    -- `.pure ()`: back to a boundary at the trap vector
    obtain ⟨rfl, tick, rfl⟩ := retPstepInv cpu rs ib d l p' d' Hps
    refine ⟨fun _ _ => ?_, fun Hn => (Hn (by simp [AxOpsem.lbAdminAx])).elim⟩
    obtain ⟨Hc, Hpc⟩ := HQ
    refine frsOfBoundary img C P stv HVA Off cpu k rs ibNone tick (HC _ _ Hc Hag) ?_
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide)), Hpc]
    exact Hstv
  | frRd r kk t H1 H2 =>
    obtain ⟨rfl, rfl⟩ := pstepRdInv cpu r kk rs ib d l p' d' Hps
    refine ⟨fun _ _ => ⟨rfl, .inr ⟨kk (rs r), rs, ibRd ib r, t, v, rfl, Hag, Hoff, ?_⟩⟩,
      fun Hn => (Hn (by simp [AxOpsem.lbAdminAx])).elim⟩
    by_cases hp : AxRunClose.pinReg r
    · exact H1 hp _
    · rw [Hag r hp]; exact H2 hp
  | frWr r v0 kk t _ Hk =>
    obtain ⟨Hadm, rfl⟩ := pstepWrInv cpu r v0 kk rs ib d l p' d' Hps
    exact ⟨fun _ _ => ⟨rfl, .inr ⟨kk PUnit.unit, rs.set r v0, ib, t.setReg r v0, v, rfl,
      regsAgreeSet _ _ _ r v0 Hag, Hoff, Hk⟩⟩, fun Hn => (Hn Hadm).elim⟩
  | frMrd n0 va req kk t Hdev Hlat Hnf HP =>
    -- THE FIRST READ
    obtain ⟨tvs, Htl, rfl, -⟩ := fetchNodePstep cpu n0 va req kk rs ib d l p' d' Hdev Hlat Hps
    simp only [rdLabel, Hnf, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun Ha => by simp [AxOpsem.lbAdminAx] at Ha, fun _ => ?_⟩
    exact ⟨_, _, tvs, v, rfl, Hoff, by rw [Htl]; exact HP⟩
  | frIf n0 va req kk t vs Hdev Hif Himg Hk =>
    obtain ⟨tvs, Htl, rfl, rfl⟩ := AxCjrWpd.fetchStepInv cpu n0 va req kk rs ib d l p' d' Hdev Hif Hps
    refine ⟨fun _ Hpin => ?_, fun Hn => (Hn (by simp [AxOpsem.lbAdminAx])).elim⟩
    obtain ⟨Hvl, Hvs⟩ := imgBytesSpec img _ _ vs Himg
    have Hsnd := AxCjrWpd.pinnedBytes img (paZ req.pa) tvs vs (by omega)
      (fun j hj => Hvs j (by omega)) Hpin
    exact ⟨rfl, .inr ⟨kk (.Ok (wordOfBytes n0 vs, none)), rs, ib, t, v, by rw [Hsnd], Hag, Hoff,
      Hk⟩⟩
  | frNf n0 va req kk t Hdev Hif Himg =>
    obtain ⟨tvs, Htl, rfl, -⟩ := AxCjrWpd.fetchStepInv cpu n0 va req kk rs ib d l p' d' Hdev Hif Hps
    exact ⟨fun _ Hpin => (AxSpinVA.noPinOfImgNone img _ _ tvs Himg Htl Hpin).elim,
      fun Hn => (Hn (by simp [AxOpsem.lbAdminAx])).elim⟩
  | frIa n0 w kk t Hs Hk =>
    obtain ⟨m', ors, fn', oib, obar, dv, hn, rfl⟩ := AxSpinE3.nodeStepInv cpu _ rs ib d l p' d' Hps
    obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := hn
    exact ⟨fun _ _ => ⟨rfl, .inr ⟨_, rs, _, t, v, rfl, Hag, Hoff, Hk⟩⟩,
      fun Hn => (Hn (AxSpinVA.annAdmin n0 w Hs)).elim⟩
  | frExt e kk t =>
    obtain ⟨m', ors, fn', oib, obar, dv, hn, -⟩ := AxSpinE3.nodeStepInv cpu _ rs ib d l p' d' Hps
    exact hn.elim
  | frBa _ _ kk t Hk | frCo _ kk t Hk | frTl _ kk t Hk | frTe _ kk t Hk | frRx _ kk t Hk
  | frTs _ kk t Hk | frTx _ kk t Hk | frCc kk t Hk | frMsg _ kk t Hk | frGcc kk t Hk =>
    obtain ⟨m', ors, fn', oib, obar, dv, hn, rfl⟩ := AxSpinE3.nodeStepInv cpu _ rs ib d l p' d' Hps
    obtain ⟨rfl, rfl, rfl, rfl, -, rfl, -⟩ := hn
    exact ⟨fun _ _ => ⟨rfl, .inr ⟨_, rs, ib, t, v, rfl, Hag, Hoff, Hk⟩⟩,
      fun Hn => (Hn (by simp [AxOpsem.lbAdminAx])).elim⟩

include HC HVA Hstv in
theorem frsClosed (s s' : Athread) :
    FRS img C P stv Off cpu k s → kstep0 (WeakAxRealize.fetchPin img) s s' →
    FRS img C P stv Off cpu k s' := by
  rintro ⟨Hk, ⟨rs, ib, Hp, Hc, Ho⟩ | ⟨m, rs, ib, t, v, Hp, Hag, Ho, Hfr⟩⟩ Hst
  · rcases Hst with ⟨Hk', d, l, d', -, -, Hps⟩ | ⟨Hk', d, d', hw⟩
    · rw [Hp] at Hps
      obtain ⟨-, tick, Hp'⟩ := retPstepInv cpu rs ib d l _ d' Hps
      obtain ⟨p1, k1⟩ := s'
      dsimp only at Hp' Hk'
      subst Hp'
      rw [Hk', Hk]
      exact frsOfBoundary img C P stv HVA Off cpu k rs ibNone tick Hc Ho
    · obtain ⟨-, cpu', m', rs', fn', ib', mm, b, kk, hp, -, -, hp'⟩ := pstepWireInv _ _ _ _ _ hw
      rw [Hp] at hp
      cases hp
      refine ⟨Hk'.trans Hk, .inl ⟨pinSet rs mm b, ib, hp', ?_, ?_⟩⟩
      · exact HC rs _ Hc (regsAgreeSym _ _ _ (AxRunClose.pinSetAgree rs mm b))
      · rw [← AxRunClose.pinSetAgree rs mm b .PC (AxSymEngine2.notPin _ (by decide) (by decide))]
        exact Ho
  · rcases Hst with ⟨Hk', d, l, d', Hadm, Hpin, Hps⟩ | ⟨Hk', d, d', hw⟩
    · rw [Hp] at Hps
      obtain ⟨-, H2⟩ := (FirstRdStep img C HC P stv HVA Off Hstv cpu k v m t Hfr Ho rs ib Hag d l
        _ d' Hps).1 Hadm Hpin
      exact ⟨Hk'.trans Hk, H2⟩
    · obtain ⟨-, cpu', m', rs', fn', ib', mm, b, kk, hp, -, -, hp'⟩ := pstepWireInv _ _ _ _ _ hw
      rw [Hp] at hp
      cases hp
      exact ⟨Hk'.trans Hk, .inr ⟨m, pinSet rs mm b, ib, t, v, hp',
        regsAgreeTrans _ _ _ _ (regsAgreeSym _ _ _ (AxRunClose.pinSetAgree rs mm b)) Hag, Ho, Hfr⟩⟩

include HC HVA Hstv in
theorem firstEvOffrow (s : Athread) :
    FRS img C P stv Off cpu k s → firstEv (WeakAxRealize.fetchPin img) (Foff P Off) s := by
  intro H0 s2 Hr
  have Hs2 : FRS img C P stv Off cpu k s2 := by
    induction Hr with
    | refl => exact H0
    | tail _ hst ih => exact frsClosed img C HC P stv HVA Off Hstv cpu k _ _ ih hst
  intro d l p' d' Hps Hna
  obtain ⟨-, ⟨rs, ib, Hp, -, -⟩ | ⟨m, rs, ib, t, v, Hp, Hag, Ho, Hfr⟩⟩ := Hs2 <;> rw [Hp] at Hps
  · obtain ⟨rfl, -⟩ := retPstepInv cpu rs ib d l p' d' Hps
    exact (Hna (by simp [AxOpsem.lbAdminAx])).elim
  · exact (FirstRdStep img C HC P stv HVA Off Hstv cpu k v m t Hfr Ho rs ib Hag d l p' d' Hps).2 Hna

include HC HVA Hstv in
/-- THE OFF-ROW HART IS ROW-STUCK (along image-pinned runs). -/
theorem offrowRowStuck (row : List Lbl)
    (Hrej : ∀ lb aq pa n v, row[k]? = some lb → Off v → P v pa n →
      aidentRd (aident lb) ≠ some (aq, pa, n))
    (Hlt : k < row.length) (rs : RegFile) (ib : Ibch) :
    C rs → Off (rs .PC) →
    rowStuckR (WeakAxRealize.fetchPin img) row ⟨.PHart cpu (.pure ()) rs none ib, k⟩ := by
  intro Hc Ho
  refine rowStuckOfFirst _ row _ (Foff P Off)
    (firstEvOffrow img C HC P stv HVA Off Hstv cpu k _ ⟨rfl, .inl ⟨rs, ib, rfl, Hc, Ho⟩⟩) ?_ Hlt
  rintro lb Hlb l ⟨aq, pa, tvs, v, rfl, Hov, HP⟩ Hfit
  rcases Hfit with ⟨-, Hrd⟩ | ⟨Hx, -⟩ | ⟨Hx, -⟩
  · exact Hrej lb aq pa tvs.length v Hlb Hov HP Hrd.symm
  · simp [wlWr] at Hx
  · simp [wlFence] at Hx

include HC HVA Hstv in
/-- ... hence `wpdM` for EVERY postcondition. -/
theorem wpdOffrowM {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
    (M : Gdexec → Prop) (i : Agent) (G : Gdexec → Prop)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (HGimg : ∀ GD, G GD → GD.gdG.gxImg = img)
    (Φ : Athread → IProp GF) (rs : RegFile) (ib : Ibch) :
    (∀ GD, G GD → k < (AxOpsem.grow GD i).length ∧
      ∀ lb aq pa n v, (AxOpsem.grow GD i)[k]? = some lb → Off v → P v pa n →
        aidentRd (aident lb) ≠ some (aq, pa, n)) →
    C rs → Off (rs .PC) →
    ⊢ wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs none ib, k⟩ Φ := by
  intro Hrow Hc Ho
  refine wpdMStuck M i G HG (WeakAxRealize.fetchPin img)
    (fun GD l HGD Hp => by rw [← HGimg GD HGD]; exact Hp) Φ _ ?_
  intro GD HGD
  obtain ⟨Hlt, Hrej⟩ := Hrow GD HGD
  exact offrowRowStuck img C HC P stv HVA Off Hstv cpu k (AxOpsem.grow GD i) Hrej Hlt rs ib Hc Ho

end offrow

/-! # 3. THE POSITIONAL X LEAF -/

section xB
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

include σi hmode hasid hppn in
theorem GoodBAgree (rs : RegFile) (pc : BitVec 64) (is_rvc : Bool) (ot : Option (BitVec 64))
    (ow : Option (BitVec 5 × BitVec 64)) (a b : RegFile) :
    GoodB T satp0 rs pc is_rvc ot ow a → regsAgree AxRunClose.pinReg b a →
    GoodB T satp0 rs pc is_rvc ot ow b := by
  rintro ⟨⟨Hc, Hpc, Hg⟩, Htl⟩ Hag
  have Hsp := SpineOkTSW σi T satp0 hmode hasid hppn
  refine ⟨⟨Hsp.sptSeip a b Hc Hag, ?_, ?_⟩, ?_⟩
  · rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact Hpc
  · intro r Hr
    rw [AxSymEngine2.uxaXgetAgree b a Hag r]
    exact Hg r Hr
  · rw [Hag .tlb (AxSymEngine2.notPin _ (by decide) (by decide))]; exact Htl

include hmode hasid hppn HG HL HGex Hmid Htext Hflow Hloc HnoRmw HnoSplit in
/-- THE POSITIONAL LEAF: exact continuation position `k + e` (deviation 1; Rocq `k + e + 1`). -/
theorem XB (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (is_rvc : Bool)
    (ins : instruction) (e : Nat) (ot : Option (BitVec 64))
    (ow : Cdata → Option (BitVec 5 × BitVec 64)) (d0 : Cdata) (r0 : Bool)
    (PX : Cdata → Bool → Prop) :
    RetX cpu rs k s → ctrlOkSW T satp0 rs → rs .PC = pc → hitW rs pc →
    textOkB σi T satp0 pc is_rvc ins → (∀ d r, PX d r → owOk (ow d)) →
    CertB σi T satp0 dok kind rs pc is_rvc ins e ot ow d0 r0 PX →
    k < L → k + e ≤ L →
    ⊢ CRes dok kind i Out d0 -∗
      (∀ d r rs' ib', ⌜PX d r⌝ -∗ ⌜GoodB T satp0 rs pc is_rvc ot (ow d) rs'⌝ -∗
          CRes dok kind i Out d -∗
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
  have H := wpdInstrOfCert (hlc := hlc) (GF := GF) (imgS σi) dok kind i Φ cpu G HG Hmid Htext Hflow
    Hloc HnoRmw HnoSplit Out
    (fun s' _ t' => ∃ d r, s' = ⟨d, .BFin (L - (k + e)), r⟩ ∧ PX d r ∧
      GoodB T satp0 rs pc is_rvc ot (ow d) t'.regs)
    ⟨d0, .BFin (e + (L - (k + e))), r0⟩ rs k s HRet Hbp Hb
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

end xB

end Weak
