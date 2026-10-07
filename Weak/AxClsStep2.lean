/-
Weak: **`AxClsStep` on message passing — the class is PROGRAM-determined, and program-level K1
REFUTES the program that `AxTokLedgerMp` "verified" per graph** (LB/AxSL), PART 1 (§1–§5.4).

Rocq: `iris/AxClsStep2.v` @ xxvzwolszwmp.  Split (Lean only, size): this file is §1–§5.4;
`Weak/AxClsStep2b.lean` is §5.5–§5.7 (the WPds, `PMpbVerified`, non-vacuity).  Downstream
ports of Rocq files importing `AxClsStep2` import BOTH (or just `Weak.AxClsStep2b`, which
imports this file).

## The Rocq header, in substance

PROGRAMS (hand `Pexv6` nodes of `AxTokLedgerMp` §2, RAM addresses):
  `PMpr` hart 0 = sd x; fence rw,w; sd y (PLAIN access kinds); hart 1 = ld.aq y; ld x.
  `PPl`  hart 0 = sd x; sd y (no fence); hart 1 as `PMpr`.
Under the language's class (`wmClassOf`) the fence rw,w ARMS `wRelp`, so `PMpr`'s plain sd y IS
a publication (`WCrel`): "sd.rl vs sd" is, in this model, "fence rw,w; sd vs sd".

RESULTS
  §2 CLASS PINNING.  `PMprPin`: every graph `PMpr` realizes with a 3-event hart-0 row has
     `WCplain` at the sd x and `WCrel` at the sd y (`h0Inv`, an invariant of the class-pinned
     runs).  Hence `PMprNotRealizesPlain : ¬ progRealizes PMpr mprPlain` while
     `PMprRealizesMpr`; the class-BLIND relation runs the same program on both
     (`h0RunBlindPlain`).  `PPlPin`: `PPl`'s hart-0 writes are `WCplain`.
  §3 THE RACE.  `mprRace` (hart 1 reads y = 0 from the image and x = 1; gmo = [W x; R y; R x;
     W y]) is cat-consistent, realized by `PMpr`, and a VIOLATION; so `PMprNotVerified :
     ¬ progLedgerVerified 2 PMpr` although `mprLedgerVerified : ledgerVerified 2 mpr` holds.
  §4 THE PLAIN PROGRAM.  `plG` is consistent, realized by `PPl`, a violation ⇒
     `PPlNotVerified`.
  §5 THE POSITIVE PROGRAM `PMpb`: hart 0 = sd x; fence rw,w; sd y; HALT; hart 1 = ld.aq y;
     if y = 1 then (ld x; HALT) else HALT.  `PMpbVerified : progLedgerVerified 2 PMpb` (file
     2b) — ONE base protocol / policy / OC (`OCX` = {x}) for the program, WPds at EVERY realized
     consistent graph; `PMpbViolFree`; non-vacuity `PMpbRealizesMpr`, `mprNoViolationProg`.
     HOW: `row0Shape`/`row1Shape` (invariants of the class-pinned runs pin every realized row,
     incl. the release CLASS of sd y); `schedG1` (fence ⇒ W x <gmo W y), `schedG2` (ld x exists
     ⇒ y = 1 came from the release ⇒ `gobCat (0,2) (1,1)`); the pure schedule `hold`/`holdStep`;
     base `baseX` = the ledger fragment of x at `hold GD |s|`; every joint obligation is
     `LJAny`; the WPds are position shells.

HONESTY (as Rocq): the WPds carry NO resources — the base protocol mirrors a PURE ledger schedule
computed from the graph, so `progLedgerVerified` reduces, for this program, to "every realized
consistent graph has a legal ledger history" plus position shells.  HALT instead of a `pure`
end: a `pure` node re-enters `riscvStep tick`, whose real Sail events the WPds would have to
cover.

## Deviations from Rocq

1. NAMES: camelCase (map below), `Z` ↦ `Int`, `bv 8` ↦ `BitVec 8`, `l !! k` ↦ `l[k]?`,
   `list_to_set` ↦ `LawfulSet.ofList`, `size` ↦ `FiniteSet.size`, `vm_compute` ↦
   `decide +kernel`.  Duplicated Rocq names are FILE-QUALIFIED: `AxClsStep2.F1`,
   `AxClsStep2.R0`, `AxClsStep2.R1`, `AxClsStep2.OCX`, `AxClsStep2.hold`.  The Rocq notations
   `B0`/`B1`/`e0..e3`/`f1`/`G` are inlined (`b0`/`b1`, literal `Geid`s, `GD.gdG`).
2. O2 STAGE C (as `AxClsStep` deviation 2): no text oracle — Rocq's `Tf`/`T` arguments of
   `cls_step`, `astep_prog`, the `aprog` record and the run lemmas are gone; `CSProg`'s middle
   premise is the image pin `WeakAxRealize.fetchPin`, `trivial` at every (non-fetch) label here;
   `h0RunBlindPlain` drops Rocq's `axirisG Σ` context (it was there only for `ax_text`).  A
   fetch is an ADMIN `astepProg` step in Lean, so `readNodeNoAstep` replaces Rocq's premise
   `wlabel_is_fetch l = false` by `(classify ak).akIfetch = false` on the node's access kind
   (as `AxTokLedgerMp.readAstepVacuous`); `readInvGen` needs no such premise (the i-cache arm
   is refuted from `areadStep`'s `wlRd`).
3. lean-sail shapes (as `AxTokLedgerMp` deviation 4): HALT `hlt` is the stuck model-error node
   `.impure (.error .Exit) (fun _ => .pure ())` (Rocq `Interface.Discard`); read answers are
   `.Ok (w, none)` (`w : BitVec (8 * 1)`), `.Err _` (Rocq `inr _`); `h1bK` and `h1bInv` use a
   decidable `if b = b1` (Rocq `bool_decide`).  `init_regstate` ↦ `zeroRegs`; the run lemmas
   `h0ClsRun`/`h1ClsRun`/`h0pClsRun` take the register file `rs` as an argument (Rocq fixes
   `init_regstate`).  Hand-node terms are `abbrev`s.
4. SECTIONS: Rocq section variables (`cpu`; `GD Hreal Hcons` of `sched`) are explicit leading
   arguments of each lemma (only those the Rocq `Proof using` names).  `gmoCases` etc. take
   `Hreal`/`Hcons` explicitly.
5. Rocq's Ltac `no_pub` is the Lean-only lemma `AxClsStep2.noPubOfB` (a kernel-decided
   boolean check over the gmo).
6. `progRealizes`'s harts-in-gmo clause is discharged through the Lean-only
   `AxClsStep2.harts01` (one kernel-decided `List.all`).

**Rocq → Lean name map.**  §1 `P_mpr` `PMpr`, `h0p_m1/m0` `h0pM1/M0`, `pl_s0` `plS0`, `P_pl`
`PPl`.  §2 `awire_rs_only2` `awireRsOnly2`, `write_inv2` `writeInv2`, `fence_inv2` `fenceInv2`,
`no_read_at_write/fence` `noReadAtWrite/Fence`, `cls_step_k_mono` `clsStepKMono`, `lcls_plain`
`lclsPlain`, `cls_at` `clsAt`, `h0_inv(_step/_nsteps)` `h0Inv(Step/Nsteps)`, `P_mpr_pin`
`PMprPin`, `P_mpr_not_realizes_plain` `PMprNotRealizesPlain`, `gx_lbl_grow` `gxLblGrow`,
`h0_cls_run` `h0ClsRun`, `h1_cls_run` `h1ClsRun`, `P_mpr_realizes_shape` `PMprRealizesShape`,
`P_mpr_realizes_mpr` `PMprRealizesMpr`, `h0_run_blind_plain` `h0RunBlindPlain`,
`h0p_inv(_step)` `h0pInv(Step)`, `P_pl_pin` `PPlPin`, `P_pl_no_release` `PPlNoRelease`.  §3
`mpr_race_row1` `mprRaceRow1`, `mpr_race` `mprRace`, `mpr_race_cat` `mprRaceCat`,
`P_mpr_realizes_race` `PMprRealizesRace`, `no_pub` (Ltac) `AxClsStep2.noPubOfB`,
`mpr_race_viol` `mprRaceViol`, `P_mpr_not_verified` `PMprNotVerified`.  §4 `pl_row0` `plRow0`,
`pl_g` `plG`, `pl_g_cat` `plGCat`, `h0p_cls_run` `h0pClsRun`, `P_pl_realizes_pl_g`
`PPlRealizesPlG`, `pl_g_viol` `plGViol`, `P_pl_not_verified` `PPlNotVerified`.  §5.1–5.4 `hlt`
`hlt`, `h0h_m2/m1/m0` `h0hM2/M1/M0`, `h1b_m1` `h1bM1`, `h1b_k` `h1bK`, `h1b_m0` `h1bM0`,
`mpb_s0` `mpbS0`, `P_mpb` `PMpb`, `hlt_no_pstep/astep/read` `hltNoPstep/Astep/Read`,
`nth_byte_bv8` `nthByteBv8`, `read_inv_gen` `readInvGen`, `wr_ok` `wrOk`, `W0` `W0`, `F1`
`AxClsStep2.F1`, `W2` `W2`, `h0h_inv(_step)` `h0hInv(Step)`, `R0` `AxClsStep2.R0`, `R1`
`AxClsStep2.R1`, `aident_read_inv` `aidentReadInv`, `read_node_no_astep` `readNodeNoAstep`,
`cls_inv_nsteps` `clsInvNsteps`, `h1b_inv(_step)` `h1bInv(Step)`, `aident_adv_cases`
`aidentAdvCases`, `row0_shape` `row0Shape`, `row1_shape` `row1Shape`, `OC_x` `AxClsStep2.OCX`,
`hold` `AxClsStep2.hold`, `wr_is_w` `wrIsW`, `lbl_in_row` `lblInRow`, `wr_ok_access`
`wrOkAccess`, `load_access` `loadAccess`, `B0_ne_B1` `B0NeB1`, `Hwf_G` `HwfG`, `gmo_cases`
`gmoCases`, `sched_G1/G2` `schedG1/G2`, `sched_rel` `schedRel`, `hold_same` `holdSame`,
`hold_step` `holdStep`, `sched_plain` `schedPlain`.  (§5.5–§5.7: `Weak/AxClsStep2b.lean`.)
Lean-only (file-qualified): `AxClsStep2.atKOfEq`, `AxClsStep2.harts01`,
`AxClsStep2.noPubOfB`, `AxClsStep2.graphValueRow`, `AxClsStep2.h1bKOk`, `AxClsStep2.wrOkLbWr`.

**Dropped:** nothing (the §6 `Print Assumptions` audit: the lint's axiom check covers it).
-/
import Weak.AxClsStep
import Weak.AxTokLedgerMp

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std Iris.Std.PartialMap MachCSL MachCSL.Stdpp
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-! # 1. THE PROGRAMS -/

def PMpr : Aprog := .AProg [0, 1] mprS0 vimg

abbrev h0pM1 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP ypaM b1))) (fun _ => .pure ())
abbrev h0pM0 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP xpaM b1))) (fun _ => h0pM1)

def plS0 (i : Agent) : Athread :=
  match i with
  | 0 => ⟨hp cpu0 h0pM0 zeroRegs, 0⟩
  | _ => ⟨hp cpu0 h1M0 zeroRegs, 0⟩

def PPl : Aprog := .AProg [0, 1] plS0 vimg

/-! # 2. CLASS PINNING -/

/-! ## 2.1 Generic step inversions at the hand nodes (any row / image) -/

section inv
variable (cpu : CPU)

theorem awireRsOnly2 (m : SailM Unit) (rs : RegFile) (k : Nat) (s' : Athread) :
    awire ⟨hp cpu m rs, k⟩ s' → ∃ rs', s' = ⟨hp cpu m rs', k⟩ :=
  awireRsOnly' cpu m rs none ibNone k s'

theorem writeInv2 (row : List Lbl) (pa : PAddr) (Hdev : devAddr pa = false) (val : BitVec 8)
    (m' : SailM Unit) (rs : RegFile) (k : Nat) (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa val))) (fun _ => m')) rs, k⟩ l s' →
    l = .LStore false (paZ pa) (WeakInterpProj.wbytes 1 val) [] [] ∧
    s' = ⟨hp cpu m' rs, k + 1⟩ ∧
    ∃ lb, row[k]? = some lb ∧ aidentWr (aident lb) = some (false, paZ pa, 1) ∧
      lblData lb = some [val] := by
  intro Hst
  generalize hs : (Athread.AThread
    (hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa val))) (fun _ => m')) rs) k) = s
    at Hst
  cases Hst with
  | AStepAdmin p k0 d l0 p' d' Hadm Hps =>
    cases hs
    obtain ⟨rfl, -, -⟩ := l3pWritePlainDet cpu pa Hdev val _ rs ibNone d _ _ _ Hps
    simp [lbAdmin] at Hadm
  | AStepWrite p k0 d l0 lb p' d' Hlk _ Heqwr Hwdat Hps =>
    cases hs
    obtain ⟨rfl, rfl, -⟩ := l3pWritePlainDet cpu pa Hdev val _ rs ibNone d _ _ _ Hps
    refine ⟨rfl, rfl, lb, Hlk, ?_, ?_⟩
    · rw [← Heqwr]
      simp [wlWr, l3pWbytes1]
    · rw [← Hwdat]
      simp [wlWdata, l3pWbytes1]
  | AStepFence p k0 d l0 lb p' d' _ Hfe _ Hps =>
    cases hs
    obtain ⟨rfl, -, -⟩ := l3pWritePlainDet cpu pa Hdev val _ rs ibNone d _ _ _ Hps
    simp [wlFence] at Hfe

theorem fenceInv2 (row : List Lbl) (m' : SailM Unit) (rs : RegFile) (k : Nat) (l : Wlabel)
    (s' : Athread) :
    AxOpsem.astepProg row
      ⟨hp cpu (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => m')) rs, k⟩ l s' →
    l = .LFence true true false true ∧ s' = ⟨hp cpu m' rs, k + 1⟩ ∧
    row[k]? = some (.LFence true true false true) := by
  intro Hst
  generalize hs : (Athread.AThread
    (hp cpu (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => m')) rs) k) = s at Hst
  cases Hst with
  | AStepAdmin p k0 d l0 p' d' Hadm Hps =>
    cases hs
    obtain ⟨rfl, -, -⟩ := l3pFenceDet cpu _ rs ibNone d _ _ _ Hps
    simp [lbAdmin] at Hadm
  | AStepWrite p k0 d l0 lb p' d' _ Hwr _ _ Hps =>
    cases hs
    obtain ⟨rfl, -, -⟩ := l3pFenceDet cpu _ rs ibNone d _ _ _ Hps
    simp [wlWr] at Hwr
  | AStepFence p k0 d l0 lb p' d' Hlk _ Heqfe Hps =>
    cases hs
    obtain ⟨rfl, rfl, -⟩ := l3pFenceDet cpu _ rs ibNone d _ _ _ Hps
    refine ⟨rfl, rfl, ?_⟩
    rw [Hlk]
    cases lb <;> simp [wlFence, aident, aidentFence] at Heqfe
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Heqfe
    rfl

/-- No read is enabled at a write / fence node. -/
theorem noReadAtWrite (row : List Lbl) (pa : PAddr) (Hdev : devAddr pa = false) (val : BitVec 8)
    (m' : SailM Unit) (rs : RegFile) (k : Nat) (id : AidentT) (K : List (BitVec 8) → Athread) :
    ¬ areadStep row
      ⟨hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa val))) (fun _ => m')) rs, k⟩
      id K := by
  rintro ⟨lb, -, -, Hsome, Hvs⟩
  obtain ⟨l, d, d', Hrd, -, Hst, -⟩ := Hvs (List.replicate (aidentN id) b0) List.length_replicate
  obtain ⟨rfl, -⟩ := l3pWritePlainDet cpu pa Hdev val _ rs ibNone d _ _ _ Hst
  rw [← Hrd] at Hsome
  simp [wlRd] at Hsome

theorem noReadAtFence (row : List Lbl) (m' : SailM Unit) (rs : RegFile) (k : Nat) (id : AidentT)
    (K : List (BitVec 8) → Athread) :
    ¬ areadStep row
      ⟨hp cpu (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => m')) rs, k⟩ id K := by
  rintro ⟨lb, -, -, Hsome, Hvs⟩
  obtain ⟨l, d, d', Hrd, -, Hst, -⟩ := Hvs (List.replicate (aidentN id) b0) List.length_replicate
  obtain ⟨rfl, -⟩ := l3pFenceDet cpu _ rs ibNone d _ _ _ Hst
  rw [← Hrd] at Hsome
  simp [wlRd] at Hsome

end inv

/-- Positions never decrease along a class-pinned step. -/
theorem clsStepKMono (GD : Gdexec) (i : Agent) (x y : Athread × Bool) :
    clsStep GD i x y → x.1.atK ≤ y.1.atK := by
  intro h
  cases h with
  | CSProg s l s' r Hst _ _ =>
    rcases astepProgK _ s l s' Hst with h | ⟨h, -⟩ <;> simp only [h] <;> omega
  | CSWire s s' r Hw =>
    simp only [Hw.1]
    omega
  | CSRead s id K v r Hrd _ Hlen =>
    rcases areadStepK _ s id K v Hrd Hlen with h | ⟨h, -⟩ <;> simp only [h] <;> omega

/-- The program's classes at the hand nodes (the language's computation). -/
theorem lclsPlain (cpu : CPU) (rs : RegFile) (pa : PAddr) (b : BitVec 8) (r : Bool)
    (K : Result (Option Bool) Arch.abort → SailM Unit) :
    lcls (hp cpu (.impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP pa b))) K) rs)
      (.LStore false (paZ pa) (WeakInterpProj.wbytes 1 b) [] []) r =
      if r then .WCrel else .WCplain := by
  cases r <;> rfl

/-! ## 2.2 `PMpr`'s hart 0: the invariant of its class-pinned runs -/

def clsAt (GD : Gdexec) (k : Nat) (c : WmClass) : Prop :=
  ∃ lb, (AxOpsem.grow GD 0)[k]? = some lb ∧ lbCls lb = c

def h0Inv (GD : Gdexec) (x : Athread × Bool) : Prop :=
  (∃ rs, x = (⟨hp cpu0 h0M0 rs, 0⟩, false)) ∨
  (∃ rs, x = (⟨hp cpu0 h0M1 rs, 1⟩, false) ∧ clsAt GD 0 .WCplain) ∨
  (∃ rs, x = (⟨hp cpu0 h0M2 rs, 2⟩, true) ∧ clsAt GD 0 .WCplain) ∨
  (3 ≤ x.1.atK ∧ clsAt GD 0 .WCplain ∧ clsAt GD 2 .WCrel)

theorem h0InvStep (GD : Gdexec) (x y : Athread × Bool) :
    h0Inv GD x → clsStep GD 0 x y → h0Inv GD y := by
  intro Hinv Hst
  rcases Hinv with ⟨rs, rfl⟩ | ⟨rs, rfl, H0⟩ | ⟨rs, rfl, H0⟩ | ⟨Hk, H0, H2⟩
  · cases Hst with
    | CSProg s l s' r Hp _ Hcls =>
      obtain ⟨rfl, rfl, lb, Hlb, -, -⟩ := writeInv2 cpu0 _ xpaM xpaMRam b1 h0M1 rs 0 l s' Hp
      exact .inr (.inl ⟨rs, rfl, lb, Hlb, by rw [Hcls lb rfl Hlb]; rfl⟩)
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 0 _ Hw
      exact .inl ⟨rs', rfl⟩
    | CSRead s id K v r Hrd _ _ =>
      exact (noReadAtWrite cpu0 _ xpaM xpaMRam b1 h0M1 rs 0 id K Hrd).elim
  · cases Hst with
    | CSProg s l s' r Hp _ _ =>
      obtain ⟨rfl, rfl, -⟩ := fenceInv2 cpu0 _ h0M2 rs 1 l s' Hp
      exact .inr (.inr (.inl ⟨rs, rfl, H0⟩))
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 1 _ Hw
      exact .inr (.inl ⟨rs', rfl, H0⟩)
    | CSRead s id K v r Hrd _ _ =>
      exact (noReadAtFence cpu0 _ h0M2 rs 1 id K Hrd).elim
  · cases Hst with
    | CSProg s l s' r Hp _ Hcls =>
      obtain ⟨rfl, rfl, lb, Hlb, -, -⟩ := writeInv2 cpu0 _ ypaM ypaMRam b1 (.pure ()) rs 2 l s' Hp
      exact .inr (.inr (.inr ⟨by simp, H0, lb, Hlb, by rw [Hcls lb rfl Hlb]; rfl⟩))
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 2 _ Hw
      exact .inr (.inr (.inl ⟨rs', rfl, H0⟩))
    | CSRead s id K v r Hrd _ _ =>
      exact (noReadAtWrite cpu0 _ ypaM ypaMRam b1 (.pure ()) rs 2 id K Hrd).elim
  · have := clsStepKMono GD 0 _ _ Hst
    exact .inr (.inr (.inr ⟨by omega, H0, H2⟩))

theorem h0InvNsteps (GD : Gdexec) (n : Nat) (x y : Athread × Bool) :
    h0Inv GD x → nsteps (clsStep GD 0) n x y → h0Inv GD y := by
  intro Hx Hrun
  induction Hrun with
  | rfl => exact Hx
  | tail w _ hs ih => exact h0InvStep GD _ _ (ih Hx) hs

/-- Lean-only: the end of a run at a stuck-shaped state names the row length. -/
theorem AxClsStep2.atKOfEq {x y : Athread × Bool} (h : x = y) : x.1.atK = y.1.atK := by
  rw [h]

/-- THE PIN: whenever `PMpr` realizes a graph whose hart-0 row has (at least) three events, the
sd x is `WCplain` and the sd y is `WCrel`. -/
theorem PMprPin (GD : Gdexec) :
    progRealizes PMpr GD → 3 ≤ (AxOpsem.grow GD 0).length →
    clsAt GD 0 .WCplain ∧ clsAt GD 2 .WCrel := by
  rintro ⟨-, -, -, -, n, sN, rN, Hr⟩ Hlen
  obtain ⟨Hrun, Hend⟩ := Hr 0 (by simp [PMpr])
  have Hinv := h0InvNsteps GD _ _ _ (.inl ⟨zeroRegs, rfl⟩) Hrun
  rcases Hinv with ⟨rs, Heq⟩ | ⟨rs, Heq, -⟩ | ⟨rs, Heq, -⟩ | ⟨-, H0, H2⟩
  · have := AxClsStep2.atKOfEq Heq
    simp only at this
    omega
  · have := AxClsStep2.atKOfEq Heq
    simp only at this
    omega
  · have := AxClsStep2.atKOfEq Heq
    simp only at this
    omega
  · exact ⟨H0, H2⟩

theorem PMprNotRealizesPlain : ¬ progRealizes PMpr mprPlain := by
  intro Hr
  obtain ⟨-, lb, Hlb, Hc⟩ := PMprPin mprPlain Hr (by decide +kernel)
  have h : some lb = some (Lbl.LStore false ya [b1] .WCplain) := Hlb.symm
  cases h
  exact absurd Hc (by decide)

/-! ## 2.3 `PMpr` DOES realize `mpr` (class-pinned runs) -/

theorem gxLblGrow (GD : Gdexec) (i k : Nat) :
    gxLbl GD.gdG (i, k) = (AxOpsem.grow GD i)[k]? := by
  unfold gxLbl AxOpsem.grow growG
  dsimp only
  cases GD.gdG.gxProg[i]? <;> rfl

section runs
variable (cpu : CPU) (rs : RegFile)

theorem h0ClsRun (GD : Gdexec) :
    AxOpsem.grow GD 0 = mprRow0 →
    nsteps (clsStep GD 0) 3 (⟨hp cpu h0M0 rs, 0⟩, false) (⟨hp cpu (.pure ()) rs, 3⟩, false) := by
  intro Hrow
  refine nsteps_l (clsStep.CSProg _ _ _ _
    (hAstepWrite cpu (AxOpsem.grow GD 0) 0 xpaM xpaMRam b1 .WCplain h0M1 rs (by rw [Hrow]; rfl))
    trivial ?_) ?_
  · intro lb _ Hlb
    rw [Hrow] at Hlb
    have h : some lb = some (Lbl.LStore false xa [b1] .WCplain) := Hlb.symm
    cases h
    rfl
  refine nsteps_l (clsStep.CSProg _ _ _ _
    (hAstepFence cpu (AxOpsem.grow GD 0) 1 h0M2 rs (by rw [Hrow]; rfl)) trivial ?_) ?_
  · intro lb Hx
    simp [wlWr] at Hx
  refine nsteps_l (clsStep.CSProg _ _ _ _
    (hAstepWrite cpu (AxOpsem.grow GD 0) 2 ypaM ypaMRam b1 .WCrel (.pure ()) rs
      (by rw [Hrow]; rfl)) trivial ?_) ?_
  · intro lb _ Hlb
    rw [Hrow] at Hlb
    have h : some lb = some (Lbl.LStore false ya [b1] .WCrel) := Hlb.symm
    cases h
    rfl
  exact nsteps_O _

/-- Hart 1 (reads only: no class condition), at any graph whose hart-1 row has `mpr`'s shape,
reading the graph's values. -/
theorem h1ClsRun (GD : Gdexec) (ts0 : List Nat) (c0 : BitVec 8) (ts1 : List Nat) (c1 : BitVec 8) :
    AxOpsem.grow GD 1 = [.LLoad true ya ts0 [c0], .LLoad false xa ts1 [c1]] →
    nsteps (clsStep GD 1) 2 (⟨hp cpu h1M0 rs, 0⟩, false) (⟨hp cpu (.pure ()) rs, 2⟩, false) := by
  intro Hrow
  have Hgv0 : graphValue GD (1, 0) = some [c0] := by
    unfold graphValue
    rw [gxLblGrow, Hrow]
    rfl
  have Hgv1 : graphValue GD (1, 1) = some [c1] := by
    unfold graphValue
    rw [gxLblGrow, Hrow]
    rfl
  refine nsteps_l (clsStep.CSRead _ (.IRead true ya 1) _ [c0] false
    (hAread cpu (AxOpsem.grow GD 1) 0 true akAq ypaM ypaMRam rfl rfl rfl ts0 c0 h1M1 rs
      (by rw [Hrow]; rfl)) Hgv0 rfl) ?_
  refine nsteps_l (clsStep.CSRead _ (.IRead false xa 1) _ [c1] false
    (hAread cpu (AxOpsem.grow GD 1) 1 false l3pAkP xpaM xpaMRam rfl rfl rfl ts1 c1 (.pure ()) rs
      (by rw [Hrow]; rfl)) Hgv1 rfl) ?_
  exact nsteps_O _

end runs

/-- Every graph with `mpr`'s hart-0 row and an `mpr`-shaped hart-1 row, image `vimg` and gmo on
harts 0/1 is realized by `PMpr`. -/
theorem PMprRealizesShape (GD : Gdexec) (ts0 : List Nat) (c0 : BitVec 8) (ts1 : List Nat)
    (c1 : BitVec 8) :
    GD.gdG.gxImg = vimg →
    (∀ e, e ∈ GD.gdG.gxGmo → e.1 ∈ ([0, 1] : List Agent)) →
    AxOpsem.grow GD 0 = mprRow0 →
    AxOpsem.grow GD 1 = [.LLoad true ya ts0 [c0], .LLoad false xa ts1 [c1]] →
    progRealizes PMpr GD := by
  intro Himg Hh Hr0 Hr1
  refine ⟨by decide, Himg, Hh, ?_, fun i => match i with | 0 => 3 | _ => 2, mprSN,
    fun _ => false, ?_⟩
  · intro i Hi
    simp only [PMpr, List.mem_cons, List.not_mem_nil, or_false] at Hi
    rcases Hi with rfl | rfl <;> rfl
  · intro i Hi
    simp only [PMpr, List.mem_cons, List.not_mem_nil, or_false] at Hi
    rcases Hi with rfl | rfl
    · exact ⟨h0ClsRun cpu0 zeroRegs GD Hr0, by rw [Hr0]; rfl⟩
    · exact ⟨h1ClsRun cpu0 zeroRegs GD ts0 c0 ts1 c1 Hr1, by rw [Hr1]; rfl⟩

/-- Lean-only: every gmo event of a concrete graph sits on hart 0 or 1. -/
theorem AxClsStep2.harts01 (G : Gexec) :
    (G.gxGmo.all fun e => decide (e.1 ∈ ([0, 1] : List Agent))) = true →
    ∀ e, e ∈ G.gxGmo → e.1 ∈ ([0, 1] : List Agent) := by
  intro h e he
  exact of_decide_eq_true (List.all_eq_true.1 h e he)

theorem PMprRealizesMpr : progRealizes PMpr AxTokLedgerMp.mpr :=
  PMprRealizesShape AxTokLedgerMp.mpr [2] b1 [1] b1 rfl
    (AxClsStep2.harts01 _ (by decide +kernel)) rfl rfl

/-- THE GAP, recorded: the class-BLIND relation runs `PMpr`'s hart 0 on the plain twin's row
too. -/
theorem h0RunBlindPlain :
    nsteps (astepAnyNfGv mprPlain 0) 3 ⟨hp cpu0 h0M0 zeroRegs, 0⟩
      ⟨hp cpu0 (.pure ()) zeroRegs, 3⟩ := by
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, hAstepWrite cpu0 (AxOpsem.grow mprPlain 0) 0 xpaM xpaMRam b1 .WCplain h0M1 zeroRegs
      rfl, trivial⟩) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, hAstepFence cpu0 (AxOpsem.grow mprPlain 0) 1 h0M2 zeroRegs rfl, trivial⟩) ?_
  refine nsteps_l (astepAnyNfGv.ANFGVProg _ _
    ⟨_, hAstepWrite cpu0 (AxOpsem.grow mprPlain 0) 2 ypaM ypaMRam b1 .WCplain (.pure ())
      zeroRegs rfl, trivial⟩) ?_
  exact nsteps_O _

/-! ## 2.4 `PPl`'s hart 0 writes are plain (the vice-versa pin) -/

def h0pInv (GD : Gdexec) (x : Athread × Bool) : Prop :=
  (∃ rs, x = (⟨hp cpu0 h0pM0 rs, 0⟩, false)) ∨
  (∃ rs, x = (⟨hp cpu0 h0pM1 rs, 1⟩, false) ∧ clsAt GD 0 .WCplain) ∨
  (2 ≤ x.1.atK ∧ clsAt GD 0 .WCplain ∧ clsAt GD 1 .WCplain)

theorem h0pInvStep (GD : Gdexec) (x y : Athread × Bool) :
    h0pInv GD x → clsStep GD 0 x y → h0pInv GD y := by
  intro Hinv Hst
  rcases Hinv with ⟨rs, rfl⟩ | ⟨rs, rfl, H0⟩ | ⟨Hk, H0, H1⟩
  · cases Hst with
    | CSProg s l s' r Hp _ Hcls =>
      obtain ⟨rfl, rfl, lb, Hlb, -, -⟩ := writeInv2 cpu0 _ xpaM xpaMRam b1 h0pM1 rs 0 l s' Hp
      exact .inr (.inl ⟨rs, rfl, lb, Hlb, by rw [Hcls lb rfl Hlb]; rfl⟩)
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 0 _ Hw
      exact .inl ⟨rs', rfl⟩
    | CSRead s id K v r Hrd _ _ =>
      exact (noReadAtWrite cpu0 _ xpaM xpaMRam b1 h0pM1 rs 0 id K Hrd).elim
  · cases Hst with
    | CSProg s l s' r Hp _ Hcls =>
      obtain ⟨rfl, rfl, lb, Hlb, -, -⟩ := writeInv2 cpu0 _ ypaM ypaMRam b1 (.pure ()) rs 1 l s' Hp
      exact .inr (.inr ⟨by simp, H0, lb, Hlb, by rw [Hcls lb rfl Hlb]; rfl⟩)
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 1 _ Hw
      exact .inr (.inl ⟨rs', rfl, H0⟩)
    | CSRead s id K v r Hrd _ _ =>
      exact (noReadAtWrite cpu0 _ ypaM ypaMRam b1 (.pure ()) rs 1 id K Hrd).elim
  · have := clsStepKMono GD 0 _ _ Hst
    exact .inr (.inr ⟨by omega, H0, H1⟩)

theorem PPlPin (GD : Gdexec) :
    progRealizes PPl GD → 2 ≤ (AxOpsem.grow GD 0).length →
    clsAt GD 0 .WCplain ∧ clsAt GD 1 .WCplain := by
  rintro ⟨-, -, -, -, n, sN, rN, Hr⟩ Hlen
  obtain ⟨Hrun, Hend⟩ := Hr 0 (by simp [PPl])
  have Hinv : h0pInv GD (sN 0, rN 0) := by
    have key : ∀ m y, nsteps (clsStep GD 0) m (PPl.apS0 0, false) y → h0pInv GD y := by
      intro m y h
      have Hx0 : h0pInv GD (PPl.apS0 0, false) := .inl ⟨zeroRegs, rfl⟩
      generalize (PPl.apS0 0, false) = x at h Hx0
      induction h with
      | rfl => exact Hx0
      | tail w _ hs ih => exact h0pInvStep GD _ _ (ih Hx0) hs
    exact key _ _ Hrun
  rcases Hinv with ⟨rs, Heq⟩ | ⟨rs, Heq, -⟩ | ⟨-, H0, H1⟩
  · have := AxClsStep2.atKOfEq Heq
    simp only at this
    omega
  · have := AxClsStep2.atKOfEq Heq
    simp only at this
    omega
  · exact ⟨H0, H1⟩

/-- Hence `PPl` never realizes a graph whose hart-0 sd y is a publication. -/
theorem PPlNoRelease (GD : Gdexec) :
    progRealizes PPl GD → 2 ≤ (AxOpsem.grow GD 0).length → ¬ clsAt GD 1 .WCrel := by
  rintro Hr Hl ⟨lb, Hlb, Hc⟩
  obtain ⟨-, lb', Hlb', Hc'⟩ := PPlPin GD Hr Hl
  rw [Hlb] at Hlb'
  cases Hlb'
  rw [Hc] at Hc'
  cases Hc'

/-! # 3. THE RACE: `PMpr` realizes a violating graph -/

def mprRaceRow1 : List Lbl :=
  [.LLoad true ya [0] [b0],
   .LLoad false xa [1] [b1]]

/-- W x (e0); R y = 0 (init) (e2); R x = 1 (e3); W y (e1). -/
def mprRace : Gdexec :=
  ⟨⟨vimg, [mprRow0, mprRaceRow1], [(0, 0), (1, 0), (1, 1), (0, 2)]⟩, []⟩

theorem mprRaceCat : rvwmoCatConsistent mprRace :=
  catConsistentBSound _ (by decide +kernel)

theorem PMprRealizesRace : progRealizes PMpr mprRace :=
  PMprRealizesShape mprRace [0] b0 [1] b1 rfl (AxClsStep2.harts01 _ (by decide +kernel)) rfl rfl

/-- Lean-only (Rocq's Ltac `no_pub`): no publication of `w` gmo-before `e`, decided on the
concrete graph. -/
theorem AxClsStep2.noPubOfB (G : Gexec) (w e : Geid) :
    (G.gxGmo.all fun h => !((gxLbl G h).any lbRelw && decide (gpos G h < gpos G e))) = true →
    ¬ gpubBefore G w e := by
  rintro hb ⟨h, -, ⟨l, hl, hr⟩, -, hin, -, hlt⟩
  have := List.all_eq_true.1 hb h hin
  rw [hl] at this
  simp [hr, hlt] at this

theorem mprRaceViol : gdviolationHart 2 mprRace := by
  refine ⟨(0, 0), (1, 1), xa, b1, by decide +kernel,
    (gwbBSpec _ _ _ _).1 (by decide +kernel), ⟨_, rfl, by decide +kernel⟩, trivial,
    ⟨0, rfl, by omega⟩, ⟨1, rfl, by omega⟩, by decide, ?_⟩
  refine .inr ⟨1, b1, (grbBSpec _ _ _ _ _).1 (by decide +kernel),
    by decide +kernel, AxClsStep2.noPubOfB _ _ _ (by decide +kernel), ?_⟩
  intro ws Hws
  have h : gwriteAt mprRace.gdG 1 = some (0, 0) := by decide +kernel
  rw [h] at Hws
  cases Hws
  exact AxClsStep2.noPubOfB _ _ _ (by decide +kernel)

/-- PROGRAM-LEVEL K1 REFUTES the program `AxTokLedgerMp` verified per graph
(`mprLedgerVerified : ledgerVerified 2 mpr`). -/
theorem PMprNotVerified : ¬ progLedgerVerified 2 PMpr :=
  progNotVerifiedOfViol 2 PMpr mprRace PMprRealizesRace mprRaceCat mprRaceViol

/-! # 4. THE PLAIN PROGRAM: realized violating graph -/

def plRow0 : List Lbl :=
  [.LStore false xa [b1] .WCplain,
   .LStore false ya [b1] .WCplain]

/-- W x (e0); W y (f1); R y = 1 (e2); R x = 1 (e3). -/
def plG : Gdexec :=
  ⟨⟨vimg, [plRow0, mprRow1], [(0, 0), (0, 1), (1, 0), (1, 1)]⟩, []⟩

theorem plGCat : rvwmoCatConsistent plG :=
  catConsistentBSound _ (by decide +kernel)

theorem h0pClsRun (rs : RegFile) (GD : Gdexec) :
    AxOpsem.grow GD 0 = plRow0 →
    nsteps (clsStep GD 0) 2 (⟨hp cpu0 h0pM0 rs, 0⟩, false) (⟨hp cpu0 (.pure ()) rs, 2⟩, false) := by
  intro Hrow
  refine nsteps_l (clsStep.CSProg _ _ _ _
    (hAstepWrite cpu0 (AxOpsem.grow GD 0) 0 xpaM xpaMRam b1 .WCplain h0pM1 rs (by rw [Hrow]; rfl))
    trivial ?_) ?_
  · intro lb _ Hlb
    rw [Hrow] at Hlb
    have h : some lb = some (Lbl.LStore false xa [b1] .WCplain) := Hlb.symm
    cases h
    rfl
  refine nsteps_l (clsStep.CSProg _ _ _ _
    (hAstepWrite cpu0 (AxOpsem.grow GD 0) 1 ypaM ypaMRam b1 .WCplain (.pure ()) rs
      (by rw [Hrow]; rfl)) trivial ?_) ?_
  · intro lb _ Hlb
    rw [Hrow] at Hlb
    have h : some lb = some (Lbl.LStore false ya [b1] .WCplain) := Hlb.symm
    cases h
    rfl
  exact nsteps_O _

theorem PPlRealizesPlG : progRealizes PPl plG := by
  refine ⟨by decide, rfl, AxClsStep2.harts01 _ (by decide +kernel), ?_, fun _ => 2,
    fun _ => ⟨hp cpu0 (.pure ()) zeroRegs, 2⟩, fun _ => false, ?_⟩
  · intro i Hi
    simp only [PPl, List.mem_cons, List.not_mem_nil, or_false] at Hi
    rcases Hi with rfl | rfl <;> rfl
  · intro i Hi
    simp only [PPl, List.mem_cons, List.not_mem_nil, or_false] at Hi
    rcases Hi with rfl | rfl
    · exact ⟨h0pClsRun zeroRegs plG rfl, rfl⟩
    · exact ⟨h1ClsRun cpu0 zeroRegs plG [2] b1 [1] b1 rfl, rfl⟩

theorem plGViol : gdviolationHart 2 plG := by
  refine ⟨(0, 0), (1, 1), xa, b1, by decide +kernel,
    (gwbBSpec _ _ _ _).1 (by decide +kernel), ⟨_, rfl, by decide +kernel⟩, trivial,
    ⟨0, rfl, by omega⟩, ⟨1, rfl, by omega⟩, by decide, ?_⟩
  refine .inr ⟨1, b1, (grbBSpec _ _ _ _ _).1 (by decide +kernel),
    by decide +kernel, AxClsStep2.noPubOfB _ _ _ (by decide +kernel), ?_⟩
  intro ws Hws
  have h : gwriteAt plG.gdG 1 = some (0, 0) := by decide +kernel
  rw [h] at Hws
  cases Hws
  exact AxClsStep2.noPubOfB _ _ _ (by decide +kernel)

theorem PPlNotVerified : ¬ progLedgerVerified 2 PPl :=
  progNotVerifiedOfViol 2 PPl plG PPlRealizesPlG plGCat plGViol

/-! # 5. THE POSITIVE PROGRAM: branchy reader, halting harts -/

/-! ## 5.1 The program.  hart 0 = sd x; fence rw,w; sd y; HALT.  hart 1 = ld.aq y; if y = 1 then
(ld x; HALT) else HALT.  HALT is a STUCK node (`WeakEvInst.pnodeStep`'s model-error arm; Rocq
`Discard`). -/

abbrev hlt : SailM Unit := .impure (.error .Exit) (fun _ => .pure ())

abbrev h0hM2 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP ypaM b1))) (fun _ => hlt)
abbrev h0hM1 : SailM Unit :=
  .impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => h0hM2)
abbrev h0hM0 : SailM Unit :=
  .impure (.ok (.memWrite 1 64 (l3pWreq l3pAkP xpaM b1))) (fun _ => h0hM1)

abbrev h1bM1 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq l3pAkP xpaM))) (fun _ => hlt)
def h1bK (res : Result (BitVec (8 * 1) × Option Bool) Arch.abort) : SailM Unit :=
  match res with
  | .Ok (w, _) => if w = b1 then h1bM1 else hlt
  | .Err _ => hlt
abbrev h1bM0 : SailM Unit :=
  .impure (.ok (.memRead 1 64 (l3pRreq akAq ypaM))) h1bK

def mpbS0 (i : Agent) : Athread :=
  match i with
  | 0 => ⟨hp cpu0 h0hM0 zeroRegs, 0⟩
  | _ => ⟨hp cpu0 h1bM0 zeroRegs, 0⟩

def PMpb : Aprog := .AProg [0, 1] mpbS0 vimg

/-! ## 5.2 Node facts -/

theorem hltNoPstep (cpu : CPU) (rs : RegFile) (d : Efab) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
    ¬ pstepProg (hp cpu hlt rs) d l p' d' := by
  intro h
  cases p' with
  | PDisk _ => exact h.elim
  | PHart cpu' m' rs' fn' ib' =>
    obtain ⟨-, ors, oib, obar, -, -, hn, -⟩ := h
    simp [pstepNode, pnodeStep] at hn

theorem hltNoAstep (cpu : CPU) (row : List Lbl) (rs : RegFile) (k : Nat) (l : Wlabel)
    (s' : Athread) : ¬ AxOpsem.astepProg row ⟨hp cpu hlt rs, k⟩ l s' := by
  intro h
  obtain ⟨d, d', hs⟩ := astepProgPstep _ _ _ _ h
  exact hltNoPstep cpu rs d l _ d' hs

theorem hltNoRead (cpu : CPU) (row : List Lbl) (rs : RegFile) (k : Nat) (id : AidentT)
    (K : List (BitVec 8) → Athread) : ¬ areadStep row ⟨hp cpu hlt rs, k⟩ id K := by
  rintro ⟨lb, -, -, -, Hvs⟩
  obtain ⟨l, d, d', -, -, Hst, -⟩ := Hvs (List.replicate (aidentN id) b0) List.length_replicate
  exact hltNoPstep cpu rs d l _ d' Hst

theorem nthByteBv8 (w : BitVec (8 * 1)) : nthByte w 0 = w := by
  unfold nthByte
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.mul_zero, Nat.shiftRight_zero]
  exact Nat.mod_eq_of_lt w.isLt

/-- THE READ INVERSION at a 1-byte RAM `memRead` node with ANY continuation. -/
theorem readInvGen (cpu : CPU) (row : List Lbl) (ak : AK) (pa : PAddr) (Hdev : devAddr pa = false)
    (Hlat : (classify ak).akLatest = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat)
    (id : AidentT) (K : List (BitVec 8) → Athread) (v : List (BitVec 8)) :
    areadStep row ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ id K →
    v.length = aidentN id →
    ∃ lb b, row[k]? = some lb ∧ aident lb = id ∧
      aidentRd id = some ((classify ak).akSync, paZ pa, 1) ∧ v = [b] ∧
      K v = ⟨hp cpu (KK (.Ok (b, none))) rs, k + aidentAdvRd id⟩ := by
  rintro ⟨lb, Hlk, Hid, Hsome, Hvs⟩ Hlen
  obtain ⟨l, d, d', Hrd, Hrv, Hst, Hk⟩ := Hvs v Hlen
  rcases HKv : K v with ⟨p', k'⟩
  rw [HKv] at Hst Hk
  simp only at Hst Hk
  cases p' with
  | PDisk _ => exact Hst.elim
  | PHart cpu' m'' rs' fn' ib' =>
    obtain ⟨rfl, ors, oib, obar, Hrs, Hib, Hn, -⟩ := Hst
    have hpa : devAddr (l3pRreq ak pa).pa = false := Hdev
    simp only [pstepNode, pnodeStep, hpa, Bool.false_eq_true, ↓reduceIte] at Hn
    rcases Hn with ⟨-, w, tvs, -, -, rfl, -⟩ |
      ⟨-, ⟨-, w, tvs, hlen, hby, rfl, rfl, rfl, rfl, -, rfl, -⟩ | ⟨hlat', -⟩⟩
    · rw [← Hrd] at Hsome
      simp [wlRd] at Hsome
    · simp only [Option.getD_none] at Hrs Hib
      subst Hrs Hib Hk
      rcases tvs with _ | ⟨⟨t0, c⟩, _ | _⟩ <;> simp at hlen
      have hc : c = w := by
        have h0 := hby 0 (by omega)
        simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at h0
        rw [h0, nthByteBv8]
      subst hc
      exact ⟨lb, c, Hlk, Hid, Hrd.symm, Hrv.symm, rfl⟩
    · have Hlat2 : (classify (l3pRreq ak pa).access_kind).akLatest = false := Hlat
      rw [Hlat2] at hlat'
      cases hlat'

def wrOk (lb : Lbl) (base : Int) (c : WmClass) : Prop :=
  aidentWr (aident lb) = some (false, base, 1) ∧ lblData lb = some [b1] ∧ lbCls lb = c

def W0 (GD : Gdexec) : Prop := ∃ lb, (AxOpsem.grow GD 0)[0]? = some lb ∧ wrOk lb xa .WCplain
def AxClsStep2.F1 (GD : Gdexec) : Prop :=
  (AxOpsem.grow GD 0)[1]? = some (.LFence true true false true)
def W2 (GD : Gdexec) : Prop := ∃ lb, (AxOpsem.grow GD 0)[2]? = some lb ∧ wrOk lb ya .WCrel

def h0hInv (GD : Gdexec) (x : Athread × Bool) : Prop :=
  (∃ rs, x = (⟨hp cpu0 h0hM0 rs, 0⟩, false)) ∨
  (∃ rs, x = (⟨hp cpu0 h0hM1 rs, 1⟩, false) ∧ W0 GD) ∨
  (∃ rs, x = (⟨hp cpu0 h0hM2 rs, 2⟩, true) ∧ W0 GD ∧ AxClsStep2.F1 GD) ∨
  (∃ rs, x = (⟨hp cpu0 hlt rs, 3⟩, false) ∧ W0 GD ∧ AxClsStep2.F1 GD ∧ W2 GD)

theorem h0hInvStep (GD : Gdexec) (x y : Athread × Bool) :
    h0hInv GD x → clsStep GD 0 x y → h0hInv GD y := by
  intro Hinv Hst
  rcases Hinv with ⟨rs, rfl⟩ | ⟨rs, rfl, H0⟩ | ⟨rs, rfl, H0, H1⟩ | ⟨rs, rfl, H0, H1, H2⟩
  · cases Hst with
    | CSProg s l s' r Hp _ Hcls =>
      obtain ⟨rfl, rfl, lb, Hlb, Hwr, Hd⟩ := writeInv2 cpu0 _ xpaM xpaMRam b1 h0hM1 rs 0 l s' Hp
      exact .inr (.inl ⟨rs, rfl, lb, Hlb, Hwr, Hd, by rw [Hcls lb rfl Hlb]; rfl⟩)
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 0 _ Hw
      exact .inl ⟨rs', rfl⟩
    | CSRead s id K v r Hrd _ _ =>
      exact (noReadAtWrite cpu0 _ xpaM xpaMRam b1 h0hM1 rs 0 id K Hrd).elim
  · cases Hst with
    | CSProg s l s' r Hp _ _ =>
      obtain ⟨rfl, rfl, Hf⟩ := fenceInv2 cpu0 _ h0hM2 rs 1 l s' Hp
      exact .inr (.inr (.inl ⟨rs, rfl, H0, Hf⟩))
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 1 _ Hw
      exact .inr (.inl ⟨rs', rfl, H0⟩)
    | CSRead s id K v r Hrd _ _ =>
      exact (noReadAtFence cpu0 _ h0hM2 rs 1 id K Hrd).elim
  · cases Hst with
    | CSProg s l s' r Hp _ Hcls =>
      obtain ⟨rfl, rfl, lb, Hlb, Hwr, Hd⟩ := writeInv2 cpu0 _ ypaM ypaMRam b1 hlt rs 2 l s' Hp
      exact .inr (.inr (.inr ⟨rs, rfl, H0, H1, lb, Hlb, Hwr, Hd,
        by rw [Hcls lb rfl Hlb]; rfl⟩))
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 2 _ Hw
      exact .inr (.inr (.inl ⟨rs', rfl, H0, H1⟩))
    | CSRead s id K v r Hrd _ _ =>
      exact (noReadAtWrite cpu0 _ ypaM ypaMRam b1 hlt rs 2 id K Hrd).elim
  · cases Hst with
    | CSProg s l s' r Hp _ _ =>
      exact (hltNoAstep cpu0 _ rs 3 l s' Hp).elim
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 3 _ Hw
      exact .inr (.inr (.inr ⟨rs', rfl, H0, H1, H2⟩))
    | CSRead s id K v r Hrd _ _ =>
      exact (hltNoRead cpu0 _ rs 3 id K Hrd).elim

def AxClsStep2.R0 (GD : Gdexec) (b : BitVec 8) : Prop :=
  ∃ ts, (AxOpsem.grow GD 1)[0]? = some (.LLoad true ya ts [b])
def AxClsStep2.R1 (GD : Gdexec) : Prop :=
  ∃ ts b, (AxOpsem.grow GD 1)[1]? = some (.LLoad false xa ts [b])

/-- A 1-byte load row item under an `IRead` identity. -/
theorem aidentReadInv (lb : Lbl) (aq : Bool) (base : Int) :
    aident lb = .IRead aq base 1 → ∃ ts b, lb = .LLoad aq base ts [b] := by
  intro H
  cases lb with
  | LLoad aq' base' ts vs =>
    simp only [aident, AidentT.IRead.injEq] at H
    obtain ⟨rfl, rfl, hl⟩ := H
    rcases vs with _ | ⟨b, _ | _⟩ <;> simp at hl
    exact ⟨ts, b, rfl⟩
  | _ => simp [aident] at H

/-- No program step at a RAM read node (Stage C: the node's access kind is not an i-fetch). -/
theorem readNodeNoAstep (cpu : CPU) (row : List Lbl) (ak : AK) (pa : PAddr)
    (Hdev : devAddr pa = false) (Hfe : (classify ak).akIfetch = false)
    (KK : Result (BitVec (8 * 1) × Option Bool) Arch.abort → SailM Unit) (rs : RegFile) (k : Nat)
    (l : Wlabel) (s' : Athread) :
    AxOpsem.astepProg row ⟨hp cpu (.impure (.ok (.memRead 1 64 (l3pRreq ak pa))) KK) rs, k⟩ l s' →
    False := by
  intro Hst
  obtain ⟨d, d', hps⟩ := astepProgPstep _ _ l s' Hst
  obtain ⟨hrd, _⟩ := pstepProgMemreadLbl cpu 1 64 (l3pRreq ak pa) KK rs ibNone d l s'.atP d' Hdev
    Hfe hps
  rcases l3pAstepProgShape _ _ l s' Hst with hadm | hwr | hfn
  · exact l3pRdExclAdmin l hrd hadm
  · exact l3pRdExclWr l hrd hwr
  · exact l3pRdExclFence l hrd hfn

theorem clsInvNsteps (I : Athread × Bool → Prop) (GD : Gdexec) (i : Agent) (n : Nat)
    (x y : Athread × Bool) :
    (∀ x y, I x → clsStep GD i x y → I y) → I x → nsteps (clsStep GD i) n x y → I y := by
  intro Hs Hx Hr
  induction Hr with
  | rfl => exact Hx
  | tail w _ h ih => exact Hs _ _ (ih Hx) h

def h1bInv (GD : Gdexec) (x : Athread × Bool) : Prop :=
  (∃ rs, x = (⟨hp cpu0 h1bM0 rs, 0⟩, false)) ∨
  (∃ rs b, x = (⟨hp cpu0 (if b = b1 then h1bM1 else hlt) rs, 1⟩, false) ∧ AxClsStep2.R0 GD b) ∨
  (∃ rs, x = (⟨hp cpu0 hlt rs, 2⟩, false) ∧ AxClsStep2.R0 GD b1 ∧ AxClsStep2.R1 GD) ∨
  -- dead states: a fused-RMW row item (its read half keeps the position)
  (∃ rs m, x.1 = ⟨hp cpu0 m rs, 0⟩ ∧ (m = h1bM1 ∨ m = hlt) ∧
    ∃ lb, (AxOpsem.grow GD 1)[0]? = some lb ∧ aidentRd (aident lb) = some (true, ya, 1)) ∨
  (∃ rs, x.1 = ⟨hp cpu0 hlt rs, 1⟩ ∧ ((AxOpsem.grow GD 1)[1]?).isSome = true)

theorem aidentAdvCases (lb : Lbl) (aq : Bool) (base : Int) :
    aidentRd (aident lb) = some (aq, base, 1) →
    (aidentAdvRd (aident lb) = 1 ∧ ∃ ts b, lb = .LLoad aq base ts [b]) ∨
    aidentAdvRd (aident lb) = 0 := by
  intro H
  cases lb with
  | LLoad aq' base' ts vs =>
    left
    simp only [aident, aidentRd, Option.some.injEq, Prod.mk.injEq] at H
    obtain ⟨rfl, rfl, hl⟩ := H
    rcases vs with _ | ⟨b, _ | _⟩ <;> simp at hl
    exact ⟨rfl, ts, b, rfl⟩
  | LRmw => exact .inr rfl
  | _ => simp [aident, aidentRd] at H

/-- Lean-only: a graph value read off the row. -/
theorem AxClsStep2.graphValueRow (GD : Gdexec) (i k : Nat) (lb : Lbl) :
    (AxOpsem.grow GD i)[k]? = some lb → graphValue GD (i, k) = lblValue lb := by
  intro h
  unfold graphValue
  rw [gxLblGrow, h]
  rfl

/-- Lean-only: `h1bK` at a returned byte. -/
theorem AxClsStep2.h1bKOk (b : BitVec 8) :
    h1bK (.Ok (b, none)) = if b = b1 then h1bM1 else hlt := rfl

theorem h1bInvStep (GD : Gdexec) (x y : Athread × Bool) :
    h1bInv GD x → clsStep GD 1 x y → h1bInv GD y := by
  intro Hinv Hst
  rcases Hinv with ⟨rs, rfl⟩ | ⟨rs, b, rfl, HR0⟩ | ⟨rs, rfl, HR0, HR1⟩ |
    ⟨rs, m, Hx, Hm, lb0, Hlb0, Hrd0⟩ | ⟨rs, Hx, Hs1⟩
  · cases Hst with
    | CSProg s l s' r Hp _ _ =>
      exact (readNodeNoAstep cpu0 _ akAq ypaM ypaMRam rfl h1bK rs 0 l s' Hp).elim
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 0 _ Hw
      exact .inl ⟨rs', rfl⟩
    | CSRead s id K v r Hrd Hgv Hlen =>
      obtain ⟨lb, b, Hlb, rfl, Hrdid, rfl, HK⟩ :=
        readInvGen cpu0 _ akAq ypaM ypaMRam rfl h1bK rs 0 id K v Hrd Hlen
      rcases aidentAdvCases lb true ya Hrdid with ⟨Hadv, ts, b', rfl⟩ | Hadv
      · refine .inr (.inl ⟨rs, b, ?_, ts, ?_⟩)
        · rw [HK, Hadv]
          rfl
        · have Hgv' : graphValue GD (1, 0) = some [b] := Hgv
          rw [AxClsStep2.graphValueRow GD 1 0 _ Hlb] at Hgv'
          simp only [lblValue, Option.some.injEq, List.cons.injEq, and_true] at Hgv'
          subst Hgv'
          exact Hlb
      · refine .inr (.inr (.inr (.inl ⟨rs, h1bK (.Ok (b, none)), by rw [HK, Hadv], ?_, lb,
          Hlb, Hrdid⟩)))
        rw [AxClsStep2.h1bKOk]
        split
        · exact .inl rfl
        · exact .inr rfl
  · by_cases hb : b = b1
    · subst hb
      have he : (if b1 = b1 then h1bM1 else hlt) = h1bM1 := if_pos rfl
      rw [he] at Hst
      cases Hst with
      | CSProg s l s' r Hp _ _ =>
        exact (readNodeNoAstep cpu0 _ l3pAkP xpaM xpaMRam rfl (fun _ => hlt) rs 1 l s' Hp).elim
      | CSWire s s' r Hw =>
        obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 1 _ Hw
        exact .inr (.inl ⟨rs', b1, by rw [he], HR0⟩)
      | CSRead s id K v r Hrd Hgv Hlen =>
        obtain ⟨lb, b', Hlb, rfl, Hrdid, rfl, HK⟩ :=
          readInvGen cpu0 _ l3pAkP xpaM xpaMRam rfl (fun _ => hlt) rs 1 id K v Hrd Hlen
        rcases aidentAdvCases lb false xa Hrdid with ⟨Hadv, ts, b'', rfl⟩ | Hadv
        · exact .inr (.inr (.inl ⟨rs, by rw [HK, Hadv], HR0, ts, b'', Hlb⟩))
        · exact .inr (.inr (.inr (.inr ⟨rs, by rw [HK, Hadv], by rw [Hlb]; rfl⟩)))
    · have he : (if b = b1 then h1bM1 else hlt) = hlt := if_neg hb
      rw [he] at Hst
      cases Hst with
      | CSProg s l s' r Hp _ _ =>
        exact (hltNoAstep cpu0 _ rs 1 l s' Hp).elim
      | CSWire s s' r Hw =>
        obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 1 _ Hw
        exact .inr (.inl ⟨rs', b, by rw [he], HR0⟩)
      | CSRead s id K v r Hrd _ _ =>
        exact (hltNoRead cpu0 _ rs 1 id K Hrd).elim
  · cases Hst with
    | CSProg s l s' r Hp _ _ =>
      exact (hltNoAstep cpu0 _ rs 2 l s' Hp).elim
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 2 _ Hw
      exact .inr (.inr (.inl ⟨rs', rfl, HR0, HR1⟩))
    | CSRead s id K v r Hrd _ _ =>
      exact (hltNoRead cpu0 _ rs 2 id K Hrd).elim
  · obtain ⟨s0, r0⟩ := x
    simp only at Hx
    subst Hx
    rcases Hm with rfl | rfl
    · cases Hst with
      | CSProg s l s' r Hp _ _ =>
        exact (readNodeNoAstep cpu0 _ l3pAkP xpaM xpaMRam rfl (fun _ => hlt) rs 0 l s' Hp).elim
      | CSWire s s' r Hw =>
        obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 0 _ Hw
        exact .inr (.inr (.inr (.inl ⟨rs', h1bM1, rfl, .inl rfl, lb0, Hlb0, Hrd0⟩)))
      | CSRead s id K v r Hrd _ Hlen =>
        obtain ⟨lb, b, Hlb, rfl, Hrdid, -, -⟩ :=
          readInvGen cpu0 _ l3pAkP xpaM xpaMRam rfl (fun _ => hlt) rs 0 id K v Hrd Hlen
        rw [Hlb0] at Hlb
        cases Hlb
        rw [Hrd0] at Hrdid
        exact absurd (congrArg (fun o => o.map Prod.fst) Hrdid) (by decide)
    · cases Hst with
      | CSProg s l s' r Hp _ _ =>
        exact (hltNoAstep cpu0 _ rs 0 l s' Hp).elim
      | CSWire s s' r Hw =>
        obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 0 _ Hw
        exact .inr (.inr (.inr (.inl ⟨rs', hlt, rfl, .inr rfl, lb0, Hlb0, Hrd0⟩)))
      | CSRead s id K v r Hrd _ _ =>
        exact (hltNoRead cpu0 _ rs 0 id K Hrd).elim
  · obtain ⟨s0, r0⟩ := x
    simp only at Hx
    subst Hx
    cases Hst with
    | CSProg s l s' r Hp _ _ =>
      exact (hltNoAstep cpu0 _ rs 1 l s' Hp).elim
    | CSWire s s' r Hw =>
      obtain ⟨rs', rfl⟩ := awireRsOnly2 cpu0 _ rs 1 _ Hw
      exact .inr (.inr (.inr (.inr ⟨rs', rfl, Hs1⟩)))
    | CSRead s id K v r Hrd _ _ =>
      exact (hltNoRead cpu0 _ rs 1 id K Hrd).elim

/-- THE ROW SHAPES of a realized graph. -/
theorem row0Shape (GD : Gdexec) : progRealizes PMpb GD →
    ∀ k lb, (AxOpsem.grow GD 0)[k]? = some lb →
      (k = 0 ∧ wrOk lb xa .WCplain) ∨
      (k = 1 ∧ lb = .LFence true true false true) ∨
      (k = 2 ∧ wrOk lb ya .WCrel) := by
  rintro ⟨-, -, -, -, n, sN, rN, Hr⟩ k lb Hk
  obtain ⟨Hrun, Hend⟩ := Hr 0 (by simp [PMpb])
  have Hinv := clsInvNsteps (h0hInv GD) GD 0 _ _ _ (h0hInvStep GD) (.inl ⟨zeroRegs, rfl⟩) Hrun
  have Hlt : k < (AxOpsem.grow GD 0).length := lookup_lt_Some Hk
  rcases Hinv with ⟨rs, Heq⟩ | ⟨rs, Heq, H0⟩ | ⟨rs, Heq, H0, H1⟩ | ⟨rs, Heq, H0, H1, H2⟩ <;>
    have Hk' := AxClsStep2.atKOfEq Heq <;> simp only at Hk' <;> rw [← Hend, Hk'] at Hlt <;>
    rcases k with _ | _ | _ | k
  all_goals first
    | omega
    | (obtain ⟨lb0, Hlb0, Hok0⟩ := H0; rw [Hk] at Hlb0; cases Hlb0; exact .inl ⟨rfl, Hok0⟩)
    | (unfold AxClsStep2.F1 at H1; rw [Hk] at H1; cases H1; exact .inr (.inl ⟨rfl, rfl⟩))
    | (obtain ⟨lb2, Hlb2, Hok2⟩ := H2; rw [Hk] at Hlb2; cases Hlb2; exact .inr (.inr ⟨rfl, Hok2⟩))

theorem row1Shape (GD : Gdexec) : progRealizes PMpb GD →
    ∀ k lb, (AxOpsem.grow GD 1)[k]? = some lb →
      (k = 0 ∧ ∃ ts b, lb = .LLoad true ya ts [b]) ∨
      (k = 1 ∧ (∃ ts b, lb = .LLoad false xa ts [b]) ∧ AxClsStep2.R0 GD b1) := by
  rintro ⟨-, -, -, -, n, sN, rN, Hr⟩ k lb Hk
  obtain ⟨Hrun, Hend⟩ := Hr 1 (by simp [PMpb])
  have Hinv := clsInvNsteps (h1bInv GD) GD 1 _ _ _ (h1bInvStep GD) (.inl ⟨zeroRegs, rfl⟩) Hrun
  have Hlt : k < (AxOpsem.grow GD 1).length := lookup_lt_Some Hk
  rcases Hinv with ⟨rs, Heq⟩ | ⟨rs, b, Heq, HR0⟩ | ⟨rs, Heq, HR0, HR1⟩ |
    ⟨rs, m, Hx, -, lb0, Hlb0, -⟩ | ⟨rs, Hx, Hs1⟩
  · have Hk' := AxClsStep2.atKOfEq Heq
    simp only at Hk'
    omega
  · have Hk' := AxClsStep2.atKOfEq Heq
    simp only at Hk'
    rw [← Hend, Hk'] at Hlt
    rcases k with _ | k
    · obtain ⟨ts, Hts⟩ := HR0
      rw [Hk] at Hts
      cases Hts
      exact .inl ⟨rfl, ts, b, rfl⟩
    · omega
  · have Hk' := AxClsStep2.atKOfEq Heq
    simp only at Hk'
    rw [← Hend, Hk'] at Hlt
    rcases k with _ | _ | k
    · obtain ⟨ts, Hts⟩ := HR0
      rw [Hk] at Hts
      cases Hts
      exact .inl ⟨rfl, ts, b1, rfl⟩
    · obtain ⟨ts, b, Hts⟩ := HR1
      rw [Hk] at Hts
      cases Hts
      exact .inr ⟨rfl, ⟨ts, b, rfl⟩, HR0⟩
    · omega
  · have Hk' : (sN 1).atK = 0 := by rw [show sN 1 = (sN 1, rN 1).1 from rfl, Hx]
    have := lookup_lt_Some Hlb0
    omega
  · have Hk' : (sN 1).atK = 1 := by rw [show sN 1 = (sN 1, rN 1).1 from rfl, Hx]
    have := lookup_lt_is_Some.1 Hs1
    omega

/-! ## 5.4 THE LEDGER SCHEDULE, for every realized consistent graph (pure)

Byte x is the only Own-class byte (`OCX`: the one plain hart write).  `hold GD k` = x's holder
before gmo position `k`: hart 0 until the release `(0, 2)` (sd y) is validated; then PENDING at
`(0, 2)` until the ld x `(1, 1)` is validated; then hart 1. -/

def AxClsStep2.OCX (a : Int) : Prop := a = xa

def AxClsStep2.hold (GD : Gdexec) (k : Nat) : Holder :=
  if ((0, 2) : Geid) ∈ GD.gdG.gxGmo ∧ gpos GD.gdG (0, 2) < k then
    (if ((1, 1) : Geid) ∈ GD.gdG.gxGmo ∧ gpos GD.gdG (1, 1) < k then .held 1
     else .pending (0, 2))
  else .held 0

theorem wrIsW (lb : Lbl) (base : Int) (c : WmClass) : wrOk lb base c → lbIsW lb = true := by
  rintro ⟨h, -⟩
  cases lb <;> simp [aident, aidentWr] at h <;> rfl

/-- Lean-only: `wrOk` pins the write footprint. -/
theorem AxClsStep2.wrOkLbWr (lb : Lbl) (base : Int) (c : WmClass) :
    wrOk lb base c → lbWr lb = some (base, [b1]) := by
  rintro ⟨h1, h2, -⟩
  cases lb <;> simp_all [aident, aidentWr, lblData, lbWr]

theorem lblInRow (G : Gexec) (e : Geid) (lb : Lbl) :
    gxLbl G e = some lb → ∃ p, G.gxProg[e.1]? = some p ∧ p[e.2]? = some lb := by
  unfold gxLbl
  intro H
  cases hp : G.gxProg[e.1]? with
  | none => rw [hp] at H; cases H
  | some p => rw [hp] at H; exact ⟨p, rfl, H⟩

theorem wrOkAccess (G : Gexec) (e : Geid) (lb : Lbl) (base : Int) (c : WmClass) (a : Int) :
    gwf G → gxLbl G e = some lb → wrOk lb base c → gaccesses G e a → a = base := by
  rintro ⟨-, -, Hsh⟩ Hl Hok Hacc
  have HW := AxClsStep2.wrOkLbWr lb base c Hok
  obtain ⟨p, Hp, Hpk⟩ := lblInRow G e lb Hl
  have Hs := Hsh _ _ _ _ Hp Hpk
  rcases Hacc with ⟨v, l, base', vs, j, Hl', Hwr', Hj, Ha⟩ |
    ⟨t, v, l, base', ts, vs, j, Hl', Hrd, Htj, Hj, Ha⟩ <;> rw [Hl] at Hl' <;> cases Hl'
  · rw [HW] at Hwr'
    cases Hwr'
    have hj : j = 0 := by
      have := (List.getElem?_eq_some_iff.1 Hj).1
      simp at this
      omega
    subst hj
    unfold accAddr at Ha
    omega
  · cases lb with
    | LRmw aq rl b' ts' rvs wvs cl =>
      simp only [lbWr, lbRd, Option.some.injEq, Prod.mk.injEq] at HW Hrd
      obtain ⟨rfl, rfl⟩ := HW
      obtain ⟨rfl, rfl, rfl⟩ := Hrd
      obtain ⟨-, h1, h2⟩ := Hs
      have hj : j = 0 := by
        have := (List.getElem?_eq_some_iff.1 Hj).1
        simp at h1
        omega
      subst hj
      unfold accAddr at Ha
      omega
    | _ => first | (simp [lbWr] at HW; done) | (simp [lbRd] at Hrd; done)

theorem loadAccess (G : Gexec) (e : Geid) (aq : Bool) (base : Int) (ts : List Nat) (b : BitVec 8)
    (a : Int) :
    gwf G → gxLbl G e = some (.LLoad aq base ts [b]) → gaccesses G e a → a = base := by
  intro _ Hl Hacc
  rcases Hacc with ⟨v, l, base', vs, j, Hl', Hwr', Hj, Ha⟩ |
    ⟨t, v, l, base', ts', vs, j, Hl', Hrd, Htj, Hj, Ha⟩ <;> rw [Hl] at Hl' <;> cases Hl'
  · simp [lbWr] at Hwr'
  · simp only [lbRd, Option.some.injEq, Prod.mk.injEq] at Hrd
    obtain ⟨rfl, rfl, rfl⟩ := Hrd
    have hj : j = 0 := by
      have := (List.getElem?_eq_some_iff.1 Hj).1
      simp at this
      omega
    subst hj
    unfold accAddr at Ha
    omega

theorem B0NeB1 : b0 ≠ b1 := by decide

theorem HwfG (GD : Gdexec) (Hcons : rvwmoCatConsistent GD) : gwf GD.gdG := Hcons.1

/-- The gmo events are exactly (a subset of) the four accesses. -/
theorem gmoCases (GD : Gdexec) (Hreal : progRealizes PMpb GD) (Hcons : rvwmoCatConsistent GD)
    (e : Geid) : e ∈ GD.gdG.gxGmo →
    (e = (0, 0) ∧ ∃ lb, gxLbl GD.gdG (0, 0) = some lb ∧ wrOk lb xa .WCplain) ∨
    (e = (0, 2) ∧ ∃ lb, gxLbl GD.gdG (0, 2) = some lb ∧ wrOk lb ya .WCrel) ∨
    (e = (1, 0) ∧ ∃ ts b, gxLbl GD.gdG (1, 0) = some (.LLoad true ya ts [b])) ∨
    (e = (1, 1) ∧ (∃ ts b, gxLbl GD.gdG (1, 1) = some (.LLoad false xa ts [b])) ∧
      AxClsStep2.R0 GD b1) := by
  intro He
  have Hh := Hreal.2.2.1 e He
  obtain ⟨l, Hl, Hm⟩ := ((HwfG GD Hcons).2.1 e).1 He
  obtain ⟨i, k⟩ := e
  rw [gxLblGrow] at Hl
  simp only [PMpb, List.mem_cons, List.not_mem_nil, or_false] at Hh
  rcases Hh with rfl | rfl
  · rcases row0Shape GD Hreal k l Hl with ⟨rfl, Hok⟩ | ⟨rfl, rfl⟩ | ⟨rfl, Hok⟩
    · exact .inl ⟨rfl, l, by rw [gxLblGrow]; exact Hl, Hok⟩
    · simp [lbIsMem, lbIsR, lbIsW] at Hm
    · exact .inr (.inl ⟨rfl, l, by rw [gxLblGrow]; exact Hl, Hok⟩)
  · rcases row1Shape GD Hreal k l Hl with ⟨rfl, ts, b, rfl⟩ | ⟨rfl, ⟨ts, b, rfl⟩, HR0⟩
    · exact .inr (.inr (.inl ⟨rfl, ts, b, by rw [gxLblGrow]; exact Hl⟩))
    · exact .inr (.inr (.inr ⟨rfl, ⟨ts, b, by rw [gxLblGrow]; exact Hl⟩, HR0⟩))

/-- G1: the fence orders sd x before sd y. -/
theorem schedG1 (GD : Gdexec) (Hreal : progRealizes PMpb GD) (Hcons : rvwmoCatConsistent GD) :
    ((0, 0) : Geid) ∈ GD.gdG.gxGmo → ((0, 2) : Geid) ∈ GD.gdG.gxGmo →
    gmoLt GD.gdG (0, 0) (0, 2) := by
  intro H0 H1
  rcases gmoCases GD Hreal Hcons _ H0 with ⟨-, lb0, Hl0, Hok0⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
    try exact absurd h (by decide)
  rcases gmoCases GD Hreal Hcons _ H1 with ⟨h, -⟩ | ⟨-, lb1, Hl1, Hok1⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
    try exact absurd h (by decide)
  have Hf : gxLbl GD.gdG (0, 1) = some (.LFence true true false true) := by
    rw [gxLblGrow] at Hl1 ⊢
    have Hlt : 1 < (AxOpsem.grow GD 0).length := by
      have := lookup_lt_Some Hl1
      omega
    obtain ⟨lbf, Hlbf⟩ := Option.isSome_iff_exists.1 (lookup_lt_is_Some_2 Hlt)
    rcases row0Shape GD Hreal 1 lbf Hlbf with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩
    · omega
    · exact Hlbf
    · omega
  exact Hcons.2.1 _ _ (.inl (.inr (.inr (.inr (.inl ⟨true, true, false, true,
    ⟨rfl, by decide, 1, by decide, by decide, Hf⟩,
    .inr ⟨⟨lb0, Hl0, wrIsW _ _ _ Hok0⟩, rfl⟩, .inr ⟨⟨lb1, Hl1, wrIsW _ _ _ Hok1⟩, rfl⟩⟩)))))

/-- G2: the ld x exists only after an rf from the release, and the release is ob-before it. -/
theorem schedG2 (GD : Gdexec) (Hreal : progRealizes PMpb GD) (Hcons : rvwmoCatConsistent GD) :
    ((1, 1) : Geid) ∈ GD.gdG.gxGmo →
    ((0, 2) : Geid) ∈ GD.gdG.gxGmo ∧ gobCat GD (0, 2) (1, 1) := by
  intro H3
  rcases gmoCases GD Hreal Hcons _ H3 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
    ⟨-, ⟨ts3, b3, Hl3⟩, ts0, Hts0⟩ <;> try exact absurd h (by decide)
  have Hl2 : gxLbl GD.gdG (1, 0) = some (.LLoad true ya ts0 [b1]) := by
    rw [gxLblGrow]
    exact Hts0
  obtain ⟨-, -, Hsh⟩ := HwfG GD Hcons
  obtain ⟨p, Hp, Hpk⟩ := lblInRow GD.gdG (1, 0) _ Hl2
  have Hs := Hsh _ _ _ _ Hp Hpk
  simp only at Hs
  rcases ts0 with _ | ⟨t, _ | _⟩ <;> simp at Hs
  have Hrd : greadsByte GD.gdG (1, 0) ya t b1 :=
    ⟨_, ya, [t], [b1], 0, Hl2, rfl, rfl, rfl, by simp [accAddr]⟩
  have Hlv := (Hcons.2.2.1 _ _ _ _ Hrd).1
  rcases t with _ | t
  · simp only at Hlv
    rw [Hreal.2.1] at Hlv
    exact absurd (Option.some.inj Hlv) B0NeB1
  obtain ⟨w, Hw, Hwb, -⟩ := Hlv
  have Hwin : w ∈ GD.gdG.gxGmo := gwritesByteGmo _ _ _ _ (HwfG GD Hcons) Hwb
  have Hacc : gaccesses GD.gdG w ya := .inl ⟨b1, Hwb⟩
  rcases gmoCases GD Hreal Hcons w Hwin with ⟨rfl, lb0, Hl0, Hok0⟩ | ⟨rfl, lb1, Hl1, Hok1⟩ |
    ⟨rfl, ts, b, Hl⟩ | ⟨rfl, ⟨ts, b, Hl⟩, -⟩
  · exact absurd (wrOkAccess _ _ lb0 xa .WCplain ya (HwfG GD Hcons) Hl0 Hok0 Hacc).symm xaNeYa
  · refine ⟨Hwin, gobCatTrans GD (0, 2) (1, 0) (1, 1) (gobCatStep _ _ _ ?_)
      (gobCatStep _ _ _ ?_)⟩
    · exact .inr (.inr (.inl ⟨grfAtGrf _ ya _ _ ⟨t + 1, b1, Hrd, Hw⟩, by decide⟩))
    · refine .inl (.inl (.inr (.inr (.inr (.inr (.inl
        ⟨⟨rfl, by decide, by rw [Hl2]; rfl, by rw [Hl3]; rfl⟩, ⟨_, Hl2, rfl⟩, ⟨_, Hl2, rfl⟩,
          ⟨_, Hl3, rfl⟩⟩))))))
  · obtain ⟨l, base, vs, j, Hl', Hwr, -⟩ := Hwb
    rw [Hl] at Hl'
    cases Hl'
    simp [lbWr] at Hwr
  · obtain ⟨l, base, vs, j, Hl', Hwr, -⟩ := Hwb
    rw [Hl] at Hl'
    cases Hl'
    simp [lbWr] at Hwr

theorem schedRel (GD : Gdexec) :
    ∀ lb, gxLbl GD.gdG (0, 2) = some lb → wrOk lb ya .WCrel → glblIs GD.gdG (0, 2) lbRelw := by
  intro lb Hl Hok
  refine ⟨lb, Hl, ?_⟩
  simp [lbRelw, wrIsW _ _ _ Hok, Hok.2.2]

theorem holdSame (GD : Gdexec) (n : Nat) (e : Geid) :
    GD.gdG.gxGmo[n]? = some e → e ≠ (0, 2) → e ≠ (1, 1) →
    AxClsStep2.hold GD n = AxClsStep2.hold GD (n + 1) := by
  intro Hn H1 H3
  have Hne : ∀ w, w ∈ GD.gdG.gxGmo → w ≠ e → gpos GD.gdG w ≠ n := by
    intro w Hw Hwe Hp
    apply Hwe
    have := gposElemLookup GD.gdG w Hw
    rw [Hp, Hn] at this
    exact (Option.some.inj this).symm
  unfold AxClsStep2.hold
  by_cases Hi1 : ((0, 2) : Geid) ∈ GD.gdG.gxGmo
  · have Hp1 := Hne _ Hi1 (Ne.symm H1)
    have E1 : gpos GD.gdG (0, 2) < n + 1 ↔ gpos GD.gdG (0, 2) < n := by omega
    by_cases Hi3 : ((1, 1) : Geid) ∈ GD.gdG.gxGmo
    · have Hp3 := Hne _ Hi3 (Ne.symm H3)
      have E3 : gpos GD.gdG (1, 1) < n + 1 ↔ gpos GD.gdG (1, 1) < n := by omega
      simp only [E1, E3]
    · simp only [E1, Hi3, false_and]
  · simp only [Hi1, false_and, ↓reduceIte]

/-- THE PER-EVENT LEDGER FACT. -/
theorem holdStep (GD : Gdexec) (Hreal : progRealizes PMpb GD) (Hcons : rvwmoCatConsistent GD)
    (n : Nat) (e : Geid) : GD.gdG.gxGmo[n]? = some e →
    ledgerMove GD e (some (AxClsStep2.hold GD n)) (some (AxClsStep2.hold GD (n + 1))) ∧
    (gaccesses GD.gdG e xa →
      ledgerAccessOk e (some (AxClsStep2.hold GD n)) (some (AxClsStep2.hold GD (n + 1)))) := by
  intro Hn
  have He : e ∈ GD.gdG.gxGmo := elem_of_list_lookup_2 Hn
  have Hpe : gpos GD.gdG e = n := gposOfLookup GD.gdG n e (HwfG GD Hcons).1 Hn
  rcases gmoCases GD Hreal Hcons e He with ⟨rfl, lb0, Hl0, Hok0⟩ | ⟨rfl, lb1, Hl1, Hok1⟩ |
    ⟨rfl, ts, b, Hl⟩ | ⟨rfl, ⟨ts, b, Hl⟩, -⟩
  · have Hh : ∀ m, m ≤ n + 1 → AxClsStep2.hold GD m = .held 0 := by
      intro m Hm
      unfold AxClsStep2.hold
      rw [if_neg]
      rintro ⟨Hi1, Hlt⟩
      have := (schedG1 GD Hreal Hcons He Hi1).2.2
      omega
    rw [Hh n (by omega), Hh (n + 1) (Nat.le_refl _)]
    exact ⟨.lmSame _, fun _ => .inl rfl⟩
  · have Hh0 : AxClsStep2.hold GD n = .held 0 := by
      unfold AxClsStep2.hold
      rw [if_neg]
      rintro ⟨-, Hlt⟩
      omega
    have Hh1 : AxClsStep2.hold GD (n + 1) = .pending (0, 2) := by
      unfold AxClsStep2.hold
      rw [if_pos ⟨He, by omega⟩, if_neg]
      rintro ⟨Hi3, Hlt⟩
      obtain ⟨-, Hob⟩ := schedG2 GD Hreal Hcons Hi3
      have := (obCatSubGmo GD _ _ Hcons Hob).2.2
      omega
    rw [Hh0, Hh1]
    exact ⟨.lmRelease (schedRel GD lb1 Hl1 Hok1), fun Hacc =>
      (xaNeYa (wrOkAccess _ _ lb1 ya .WCrel xa (HwfG GD Hcons) Hl1 Hok1 Hacc)).elim⟩
  · rw [holdSame GD n (1, 0) Hn (by decide) (by decide)]
    exact ⟨.lmSame _, fun Hacc => (xaNeYa (loadAccess _ _ true ya ts b xa (HwfG GD Hcons) Hl
      Hacc)).elim⟩
  · obtain ⟨Hi1, Hob⟩ := schedG2 GD Hreal Hcons He
    have Hlt := (obCatSubGmo GD _ _ Hcons Hob).2.2
    have Hh0 : AxClsStep2.hold GD n = .pending (0, 2) := by
      unfold AxClsStep2.hold
      rw [if_pos ⟨Hi1, by omega⟩, if_neg]
      rintro ⟨-, h⟩
      omega
    have Hh1 : AxClsStep2.hold GD (n + 1) = .held 1 := by
      unfold AxClsStep2.hold
      rw [if_pos ⟨Hi1, by omega⟩, if_pos ⟨He, by omega⟩]
    rw [Hh0, Hh1]
    exact ⟨.lmAcquire (0, 2) (.inr (.inl Hob)), fun _ => .inr ⟨(0, 2), rfl, rfl⟩⟩

/-- Plain hart writes touch only x. -/
theorem schedPlain (GD : Gdexec) (Hreal : progRealizes PMpb GD) (Hcons : rvwmoCatConsistent GD)
    (w : Geid) (a : Int) (v : BitVec 8) :
    w ∈ GD.gdG.gxGmo → glblIs GD.gdG w lbPlain → gwritesByte GD.gdG w a v → AxClsStep2.OCX a := by
  rintro Hw ⟨l, Hl, Hpl⟩ Hwb
  have Hacc : gaccesses GD.gdG w a := .inl ⟨v, Hwb⟩
  rcases gmoCases GD Hreal Hcons w Hw with ⟨rfl, lb0, Hl0, Hok0⟩ | ⟨rfl, lb1, Hl1, Hok1⟩ |
    ⟨rfl, ts, b, Hl'⟩ | ⟨rfl, ⟨ts, b, Hl'⟩, -⟩
  · exact wrOkAccess _ _ lb0 xa .WCplain a (HwfG GD Hcons) Hl0 Hok0 Hacc
  · rw [Hl1] at Hl
    cases Hl
    simp [lbPlain, Hok1.2.2] at Hpl
  · rw [Hl'] at Hl
    cases Hl
    simp [lbPlain, lbIsW] at Hpl
  · rw [Hl'] at Hl
    cases Hl
    simp [lbPlain, lbIsW] at Hpl

end Weak
