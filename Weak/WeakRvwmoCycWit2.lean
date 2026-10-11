/-
Weak: **THE RE-CONVERGENCE WITNESS** (route B).

Rocq: `iris/WeakRvwmoCycWit2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

THE AUDIT'S RULE: every new hypothesis needs a NON-COINCIDENTAL satisfiability witness.
`WeakRvwmoCert3` §5b introduced three — `tailSilent` (the instruction tail is administrative),
`csync`'s DIVERGED arm, and the segment iteration `certSegment''` that consumes them.  This leaf
inhabits them at a witness read whose VALUE IS USED before the boundary and whose two runs carry
DIFFERENT values — what `WeakRvwmoCycWit.cyNodeVindep` (the value-INDEPENDENT node) could not
test.

REAL: the load REQUEST `ldReql` (`WeakRvwmoConfWit2`: hart 1's spin load `lw a5,0(a4)` at
`main+0x16`; width 4, address `&started` = `evFlag`, plain, RAM) and the DESTINATION `a5` =
`x15`, whose dependency carrier is 15.  HAND-BUILT: the instruction TAIL — the real one is nine
nodes (the `x15` write, then `hart_state`, `nextPC`, `PC`, `minstret_increment`, `minstret`), and
`WeakEvProv.taintClosure` cannot absorb its `PC`/`minstret` writes (not carriers), so the tail
modelled here is the real one's FIRST node, the destination write, then the boundary.

  §1  the node `w2M` (the real request; a tail that WRITES the loaded value).
  §2  the tail is silent, and termination is a theorem (`w2ReachesBoundary`).
  §3  the re-convergence at two genuinely different nodes (`w2NodesDiffer`, `w2Reconverge`).
  §3b the node is pinned (no admin step moves it) and the block is re-answered (`w2BlkSubst`).
  §3c the DIVERGED arm, fired by the generic segment engine
      `WeakRvwmoCert4.segStepOfSegment` on a one-event row at the real load, with a NON-EMPTY
      taint set and `Nd := ndreach` (`w2SegStepDiverged`).
  §3d the POISONED block — the per-hart-taint migration's own witness: a block that READS the
      tainted carrier `x15` to compute its address (`cyA` vs `cyB`), so no mirror exists; the
      labels are `lblPoisoned`-related and by neither `lblReidx` nor `lblReidxSub`; the exit is
      `csync`'s DIVERGED arm at the GROWN taint `[15, 14]` and not lockstep (`w3Pair`).
  §4  (Rocq comment) what is left open: (a) the real nine-node tail needs a PAIRED taint law
      (`WeakEvProv2.laTailPar`); (b) the segment cannot be run across the boundary here (the
      node after `.pure ()` is the real `riscvStep`); (c) the policy interface carries `Nd`
      (done; §3b/§3c are its payoff); (d) §3c PRODUCES the diverged arm but does not CONSUME it
      (that needs a second block after the boundary, i.e. (a)).

## Deviations from Rocq

1. NAMES / VOCABULARY as `WeakRvwmoCycWit` deviation 1 (`regstate` ↦ `RegFile`, `oib32` ↦
   `Ibch`, `dev_state` ↦ `Efab` (`DevStates` at the `pnodeStep` tier), `wreg` ↦ `Nat`,
   `M unit` ↦ `SailM Unit`, `R_bitvector_64 x15` ↦ `.x15`, `type_of_register r` ↦
   `RegisterType r`, `register_lookup r rs` ↦ `rs r`, `register_set r v rs` ↦ `rs.set r v`,
   `Interface.Next (RegWrite r None v) k` ↦ `.impure (.ok (.regWrite r v)) k`,
   `Interface.MemRead 4 req` ↦ `.memRead 4 64 req`, `Interface.Ret tt` ↦ `.pure ()`, the read
   answer `inl (w, _)`/`inr _` ↦ `.Ok (w, _)`/`.Err _`, `Z_to_bv 64 (bv_unsigned w)` ↦
   `BitVec.ofNat 64 w.toNat`, `bool_decide (bv_unsigned v = 0)` ↦ `v.toNat = 0`,
   `tvs.*1/.*2` ↦ `tvs.map Prod.fst/snd`, `CSt` ↦ the `CycState` literal, `SegOut` ↦ the
   `Segout` literal).  Rocq's `Section w2seg` context (`cpu d0 t w ib rs rs2`) is explicit
   parameters; each def/theorem takes only the ones it uses.
2. THE NODE STEP's Lean shape (`WeakEvInst`): `pnodeStep`/`pstepHw` carry the barrier output
   `obar`, so `w2MStepInv` also concludes `obar = none`, `w2MStepRds`/`w2MAdmStep` quantify it,
   and `phrunOne` returns it existentially.  `pnodeStep` is over `DevStates`.
3. O2 / STAGE C — THE PINNED POLICY (`WeakRvwmoCert4` deviation 4): `segStepOfSegment`'s
   `Hpol''` takes and returns `WeakRvwmoCert2.cblkPin c0.cdImg` blocks, so `w2Hpol` is stated
   on pinned blocks (Rocq: plain `cblk`) and the engine's new premise
   `WeakRvwmoCert2.esPin St.cstC.cdImg es` is the Lean-only `WeakRvwmoCycWit2.w2EsPin`.
   `w2BlkSubst` keeps Rocq's plain `cblk`; it is the `lbAdmin true` instance of the Lean-only
   generic `WeakRvwmoCycWit2.w2BlkSubstG` (any admin sub-alphabet), whose other instance
   `WeakRvwmoCycWit2.w2BlkSubstPin` is the pinned block (as `WeakRvwmoCycWit.cyBlkSubstPin`).
   `w2Hpol` takes its read set from `w2BlkSubstPin` (`rds = []`) and mirrors with
   `WeakRvwmoCert2.certBlockMirrorG` at `lbPin`; `w2Hrds` keeps Rocq's plain statement.
4. `w2ReachesBoundary` projects away `tailSilentRun`'s Lean-only last conjunct (the fetch pins).
5. `vm_compute` facts (`w2RdNum`, `w3DstNum`, `w3Rds`, `w2ValuesDiffer`, `w3Addr0/1`,
   `w3ZAZB`) are `rfl`/`decide`/`decide +kernel`; `w3NodesDiffer` is proved through the same
   `esilNodeAny` read-back as `w2NodesDiffer` (Rocq inlines it).
6. KERNEL DRIFT: `cyA`/`cyB` are the Lean image's (`started` = `0x8000a400`,
   `WeakRvwmoCycWit` deviation 2).
7. §5's `Print Assumptions` are dropped (the lint's axiom/sorry ban is the audit).

**Rocq → Lean name map.**  `w2_rd` `w2Rd`, `w2_T` `w2T`, `w2_rd_num` `w2RdNum`, `w2_k1` `w2K1`,
`w2_val` `w2Val`, `w2_m` `w2M`, `w2_p0` `w2P0`, `w2_p1` `w2P1`, `w2_pstep` `w2Pstep`,
`w2_realizes` `w2Realizes`, `w2_tail_silent` `w2TailSilent`, `w2_reaches_boundary`
`w2ReachesBoundary`, `w2_step_any` `w2StepAny`, `w2_wrval` `w2Wrval`, `w2_wrval_k1`
`w2WrvalK1`, `w2_nodes_differ` `w2NodesDiffer`, `w2_values_differ` `w2ValuesDiffer`,
`w2_csync` `w2Csync`, `w2_reconverge` `w2Reconverge`, `w2_m_step_inv` `w2MStepInv`,
`phrun_one` `phrunOne`, `w2_m_step_rds` `w2MStepRds`, `w2_m_adm_step` `w2MAdmStep`,
`w2_m_adm_fix` `w2MAdmFix`, `w2_pstep_any` `w2PstepAny`, `w2_blk_subst` `w2BlkSubst`, `w2_lb`
`w2Lb`, `w2_Q` `w2Q`, `w2_Ctx` `w2Ctx`, `w2_Nd` `w2Nd`, `w2_pst` `w2Pst`, `w2_St` `w2St`,
`w2_nd_pin` `w2NdPin`, `w2_hemit` `w2Hemit`, `w2_devfree` `w2Devfree`, `w2_cst_ok` `w2CstOk`,
`w2_HQ` `w2HQ`, `w2_Q_rmwfree` `w2QRmwfree`, `w2_Hpres` `w2Hpres`, `w2_Hrds` `w2Hrds`,
`w2_Hrdsp` `w2Hrdsp`, `w2_Hpol` `w2Hpol`, `w2_seg_step_diverged` `w2SegStepDiverged`,
`w3_src` `w3Src`, `w3_dst` `w3Dst`, `w3_T0` `w3T0`, `w3_T1` `w3T1`, `w3_dst_num` `w3DstNum`,
`w3_taint_grows` `w3TaintGrows`, `w3_val` `w3Val`, `w3_k1` `w3K1`, `w3_ld` `w3Ld`, `w3_addr`
`w3Addr`, `w3_m` `w3M`, `w3_rds` `w3Rds`, `w3_not_rds_ok` `w3NotRdsOk`, `w3_addr_ram`
`w3AddrRam`, `w3_regread` `w3Regread`, `w3_ld_step` `w3LdStep`, `w3_realizes` `w3Realizes`,
`w3_blk` `w3Blk`, `w3_rs2` `w3Rs2`, `w3_agree` `w3Agree`, `w3_lookup2` `w3Lookup2`,
`w3_addr0` `w3Addr0`, `w3_addr1` `w3Addr1`, `w3_zA_zB` `w3ZAZB`, `w3_poisoned` `w3Poisoned`,
`w3_not_reidx` `w3NotReidx`, `w3_tail_silent` `w3TailSilent`, `w3_tail_writes_dst`
`w3TailWritesDst`, `w3_csync_grown` `w3CsyncGrown`, `w3_nodes_differ` `w3NodesDiffer`,
`w3_not_clockstep` `w3NotClockstep`, `w3_pair` `w3Pair`.

**File-qualified names:** none of this file's Rocq names is in `notes/weak-port-dupnames.json`;
Lean-only: `WeakRvwmoCycWit2.w2BlkSubstG`, `WeakRvwmoCycWit2.w2BlkSubstPin`,
`WeakRvwmoCycWit2.w2EsPin` (deviation 3).

**Dropped:** nothing (Rocq 75 declarations; Lean 75 + 3 Lean-only).
-/
import Weak.WeakRvwmoCycWit

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D

/-- The parked-fence field, abbreviated (as in `WeakRvwmoCert2`). -/
local notation "Ofence" => Option (Bool × Bool × Bool × Bool)

/-! # 1. THE NODE: the real load, and a tail that USES the value -/

/-- `a5`, the real destination of `lw a5,0(a4)`; its dependency carrier. -/
abbrev w2Rd : Register := .x15
def w2T : List Nat := [15]

theorem w2RdNum : eregNum w2Rd = some 15 := rfl

/-- The tail: WRITE THE LOADED VALUE into `a5`, then the boundary. -/
def w2K1 (v : RegisterType w2Rd) : SailM Unit :=
  .impure (.ok (.regWrite w2Rd v)) (fun _ => .pure ())

def w2Val (ans : Result (BitVec (8 * 4) × Option Bool) Arch.abort) : RegisterType w2Rd :=
  match ans with
  | .Ok (w, _) => (BitVec.ofNat 64 w.toNat : BitVec 64)
  | .Err _ => (BitVec.ofNat 64 0 : BitVec 64)

/-- THE NODE: the REAL request of `lw a5,0(a4)`, and the tail above. -/
noncomputable def w2M : SailM Unit :=
  .impure (.ok (.memRead 4 64 ldReql)) (fun ans => w2K1 (w2Val ans))

noncomputable def w2P0 (cpu : CPU) (rs : RegFile) (ib : Ibch) : Pexv6 :=
  .PHart cpu w2M rs none ib
def w2P1 (w : BitVec 32) (cpu : CPU) (rs : RegFile) (ib : Ibch) : Pexv6 :=
  .PHart cpu (w2K1 (w2Val (.Ok (w, none)))) rs none ib

/-- THE STEP, at EVERY answer: the successor node CARRIES THE VALUE. -/
theorem w2Pstep (cpu : CPU) (rs : RegFile) (ib : Ibch) (d : Efab) (t : Nat) (w : BitVec 32) :
    pstepEv (w2P0 cpu rs ib) d (.LLoad false false (paZ evFlag) (ldTvs t w) [])
      (w2P1 w cpu rs ib) d := by
  refine ⟨rfl, none, none, none, rfl, rfl, Or.inl ⟨?_, rfl⟩⟩
  simp only [pstepNode, pnodeStep, w2M, ldLoadRam, Bool.false_eq_true, if_false]
  refine Or.inr ⟨by rw [ldLoadPlain], Or.inl ⟨by rw [ldLoadPlain], w, ldTvs t w, rfl, ?_, ?_,
    by trivial, by trivial, by trivial, by trivial, by trivial, by trivial⟩⟩
  · intro j hj
    rcases j with _ | _ | _ | _ | j
    · rfl
    · rfl
    · rfl
    · rfl
    · omega
  · rw [ldLoadPlain, ldLoadPa]

theorem w2Realizes (cpu : CPU) (rs : RegFile) (ib : Ibch) (ws : Wstate) (t : Nat)
    (w : BitVec 32) :
    hlblRealizes (w2P0 cpu rs ib) ws
      (.LLoad false (paZ evFlag) (ldTs t) (WeakRvwmoConfWit2.ldVs w))
      (.LLoad false false (paZ evFlag) (ldTvs t w) []) :=
  ⟨trivial, rfl, rfl, rfl⟩

/-! # 2. THE TAIL IS SILENT, AND TERMINATION IS A THEOREM -/

theorem w2TailSilent (v : RegisterType w2Rd) : tailSilent w2T (w2K1 v) := by
  refine .tsNext _ _ trivial ?_ (fun _ => .tsRet _)
  intro r hr
  simp only [pnodeWrs, List.mem_singleton] at hr
  subst hr
  exact ⟨15, w2RdNum, List.mem_singleton_self _⟩

/-- `tailSilentRun` at the witness node: the hart REACHES the boundary. -/
theorem w2ReachesBoundary (cpu : CPU) (d0 : Efab) (v : RegisterType w2Rd) (rs : RegFile)
    (ib : Ibch) :
    ∃ (ls : List Wlabel) (rds : List Nat) (wrs : List Register) (ann : Bool) (rs' : RegFile)
      (ib' : Ibch),
      (∀ l0, l0 ∈ ls → lbAdmin true l0) ∧ Wlabel.LInstr ∉ ls ∧
      phrun cpu ls rds wrs ann (w2K1 v) rs none ib d0 (.pure ()) rs' none ib' d0 ∧
      (∀ r, r ∈ wrs → ∃ n, eregNum r = some n ∧ n ∈ w2T) := by
  obtain ⟨ls, rds, wrs, ann, rs', ib', h1, h2, h3, h4, -⟩ :=
    tailSilentRun w2T cpu d0 _ (w2TailSilent v) rs ib
  exact ⟨ls, rds, wrs, ann, rs', ib', h1, h2, h3, h4⟩

/-! # 3. THE RE-CONVERGENCE, AT TWO GENUINELY DIFFERENT NODES -/

theorem w2StepAny (v : RegisterType w2Rd) (rs : RegFile) :
    esilNodeAny rs (w2K1 v) = some (rs.set w2Rd v, .pure ()) := rfl

def w2Wrval (rs : RegFile) (m : SailM Unit) : RegisterType w2Rd :=
  match esilNodeAny rs m with
  | some (rs', _) => rs' w2Rd
  | none => (BitVec.ofNat 64 0 : BitVec 64)

theorem w2WrvalK1 (v : RegisterType w2Rd) (rs : RegFile) : w2Wrval rs (w2K1 v) = v := by
  unfold w2Wrval
  rw [w2StepAny]
  exact RegFile.set_same rs w2Rd v

theorem w2NodesDiffer (v1 v2 : RegisterType w2Rd) : v1 ≠ v2 → w2K1 v1 ≠ w2K1 v2 := by
  intro hne heq
  apply hne
  rw [← w2WrvalK1 v1 ldRs0, ← w2WrvalK1 v2 ldRs0, heq]

theorem w2ValuesDiffer :
    w2Val (.Ok (BitVec.ofNat 32 0, none)) ≠ w2Val (.Ok (BitVec.ofNat 32 1, none)) := by
  show (BitVec.ofNat 64 0 : BitVec 64) ≠ BitVec.ofNat 64 1
  decide

/-- `csync`'s DIVERGED arm, inhabited. -/
theorem w2Csync (v1 v2 : RegisterType w2Rd) (rs1 rs2 : RegFile) (ib : Ibch) :
    dregAgree (fun n => n ∉ w2T) rs1 rs2 →
    csync w2T (w2K1 v1) rs1 none ib (w2K1 v2) rs2 none ib :=
  fun hag => .inr ⟨rfl, rfl, w2TailSilent v1, w2TailSilent v2, hag⟩

/-- … AND THE RE-CONVERGENCE ITSELF: the same boundary node, register files agreeing off the
taint set. -/
theorem w2Reconverge (cpu : CPU) (d0 : Efab) (v1 v2 : RegisterType w2Rd) (rs1 rs2 : RegFile)
    (ib1 ib2 : Ibch) :
    dregAgree (fun n => n ∉ w2T) rs1 rs2 →
    ∃ (ls1 ls2 : List Wlabel) (rds1 rds2 : List Nat) (wrs1 wrs2 : List Register)
      (ann1 ann2 : Bool) (rs1' rs2' : RegFile) (ib1' ib2' : Ibch),
      phrun cpu ls1 rds1 wrs1 ann1 (w2K1 v1) rs1 none ib1 d0 (.pure ()) rs1' none ib1' d0 ∧
      phrun cpu ls2 rds2 wrs2 ann2 (w2K1 v2) rs2 none ib2 d0 (.pure ()) rs2' none ib2' d0 ∧
      WeakRvwmoCert3.atBoundary (.pure ()) ∧
      dregAgree (fun n => n ∉ w2T) rs1' rs2' := by
  intro hag
  obtain ⟨ls1, rds1, wrs1, ann1, rs1', ib1', -, -, hr1, hw1⟩ :=
    w2ReachesBoundary cpu d0 v1 rs1 ib1
  obtain ⟨ls2, rds2, wrs2, ann2, rs2', ib2', -, -, hr2, hw2⟩ :=
    w2ReachesBoundary cpu d0 v2 rs2 ib2
  refine ⟨ls1, ls2, rds1, rds2, wrs1, wrs2, ann1, ann2, rs1', rs2', ib1', ib2', hr1, hr2,
    atBoundaryRet, ?_⟩
  refine taintClosure (fun n => n ∉ w2T) cpu ls1 rds1 wrs1 ann1 (w2K1 v1) rs1 none ib1 d0
    (.pure ()) rs1' none ib1' d0 cpu ls2 rds2 wrs2 ann2 (w2K1 v2) rs2 none ib2 d0 (.pure ()) rs2'
    none ib2' d0 hag hr1 hr2 ?_
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · obtain ⟨n, hn, hin⟩ := hw1 r hr
    exact ⟨n, hn, fun hno => hno hin⟩
  · obtain ⟨n, hn, hin⟩ := hw2 r hr
    exact ⟨n, hn, fun hno => hno hin⟩

/-! # 3b. THE NODE IS PINNED, AND THE BLOCK RE-ANSWERED -/

theorem w2MStepInv (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel) (m' : SailM Unit)
    (ors : Option RegFile) (fn' : Ofence) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pnodeStep w2M rs ib d l m' ors fn' d' oib obar →
    ∃ tvs : List (Nat × BitVec 8),
      tvs.length = 4 ∧
      l = .LLoad false false (paZ evFlag) tvs [] ∧
      (∃ v : RegisterType w2Rd, m' = w2K1 v) ∧
      ors = none ∧ fn' = none ∧ d' = d ∧ oib = none ∧ obar = none := by
  intro hst
  simp only [pnodeStep, w2M, ldLoadRam, Bool.false_eq_true, if_false, ldLoadPlain] at hst
  rcases hst with ⟨hc, _⟩ | ⟨_, ⟨_, w, tvs, hlen, _, hl, hm, ho, hf, hd, hoib, hobar⟩ | ⟨hc, _⟩⟩
  · exact absurd hc (by decide)
  · refine ⟨tvs, hlen, ?_, ⟨_, hm⟩, ho, hf, hd, hoib, hobar⟩
    rw [hl, ldLoadPa]
  · exact absurd hc (by decide)

/-- ONE labelled step, as a `pstepHw` — the annotated run's own inversion. -/
theorem phrunOne (cpu : CPU) (l : Wlabel) (rds : List Nat) (wrs : List Register) (ann : Bool)
    (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch) (d : Efab) (m' : SailM Unit)
    (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (d' : Efab) :
    phrun cpu [l] rds wrs ann m rs fn ib d m' rs' fn' ib' d' →
    ∃ (ors : Option RegFile) (oib : Option Ibch) (wrs0 : List Register) (ann0 : Bool)
      (obar : Option barrier_kind),
      pstepHw cpu m rs fn ib d l rds wrs0 ann0 m' ors fn' d' oib obar := by
  intro h
  cases h with
  | more hs hr =>
    cases hr
    rw [List.append_nil]
    exact ⟨_, _, _, _, _, hs⟩

/-- `w2M` READS NO REGISTER. -/
theorem w2MStepRds (cpu : CPU) (rs : RegFile) (fn : Ofence) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (wrs : List Register) (ann : Bool) (m1 : SailM Unit) (ors : Option RegFile)
    (fn1 : Ofence) (d1 : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepHw cpu w2M rs fn ib d l rds wrs ann m1 ors fn1 d1 oib obar → rds = [] := by
  rintro (⟨_, _, rfl, _⟩ | ⟨_, _, _, _, _, _, rfl, _⟩ | ⟨_, rfl, _⟩) <;> rfl

theorem w2MAdmStep (cpu : CPU) (rs : RegFile) (fn : Ofence) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (wrs : List Register) (ann : Bool) (m1 : SailM Unit) (ors : Option RegFile)
    (fn1 : Ofence) (d1 : Efab) (oib : Option Ibch) (obar : Option barrier_kind) :
    lbAdmin true l →
    pstepHw cpu w2M rs fn ib d l rds wrs ann m1 ors fn1 d1 oib obar →
    m1 = w2M ∧ rds = [] := by
  intro hadm hst
  have hr : rds = [] := w2MStepRds cpu rs fn ib d l rds wrs ann m1 ors fn1 d1 oib obar hst
  refine ⟨?_, hr⟩
  rcases hst with ⟨rfl, ⟨hn, _⟩, _⟩ | ⟨pr, pw, sr, sw, rfl, ⟨hn, _⟩, _⟩ | ⟨hp, _⟩
  · obtain ⟨tvs, _, rfl, _⟩ := w2MStepInv rs ib d.efDev l m1 ors fn1 d1.efDev oib obar hn
    exact absurd hadm id
  · obtain ⟨rfl, _⟩ := hn
    exact absurd hadm id
  · obtain ⟨_, _, _, _, _, rfl, _⟩ := hp
    rfl

theorem w2MAdmFix (cpu : CPU) (ls : List Wlabel) (rds : List Nat) (wrs : List Register)
    (ann : Bool) (m : SailM Unit) (rs : RegFile) (fn : Ofence) (ib : Ibch) (d : Efab)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch) (d' : Efab) :
    phrun cpu ls rds wrs ann m rs fn ib d m' rs' fn' ib' d' →
    (∀ l0, l0 ∈ ls → lbAdmin true l0) →
    m = w2M → m' = w2M ∧ rds = [] := by
  intro hrun
  induction hrun with
  | nil => intro _ hm; exact ⟨hm, rfl⟩
  | more hstep _ ih =>
    intro hadm hm
    subst hm
    obtain ⟨hm1, rfl⟩ := w2MAdmStep cpu _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (hadm _ (List.mem_cons.2 (Or.inl rfl))) hstep
    obtain ⟨hm2, rfl⟩ := ih (fun l0 hl0 => hadm l0 (List.mem_cons_of_mem _ hl0)) hm1
    exact ⟨hm2, rfl⟩

/-- THE STEP AT ANY ANSWER LIST of the read's own width. -/
theorem w2PstepAny (cpu : CPU) (rs : RegFile) (ib : Ibch) (d : Efab)
    (tvs : List (Nat × BitVec 8)) :
    tvs.length = 4 →
    ∃ v : RegisterType w2Rd,
      pstepEv (.PHart cpu w2M rs none ib) d (.LLoad false false (paZ evFlag) tvs [])
        (.PHart cpu (w2K1 v) rs none ib) d := by
  intro hlen
  obtain ⟨w, hw⟩ := bvOfBytes 4 (tvs.map Prod.snd) (by rw [List.length_map, hlen])
  refine ⟨w2Val (.Ok (w, none)), rfl, none, none, none, rfl, rfl, Or.inl ⟨?_, rfl⟩⟩
  simp only [pstepNode, pnodeStep, w2M, ldLoadRam, Bool.false_eq_true, if_false]
  refine Or.inr ⟨by rw [ldLoadPlain], Or.inl ⟨by rw [ldLoadPlain], w, tvs, hlen, hw, ?_,
    by trivial, by trivial, by trivial, by trivial, by trivial, by trivial⟩⟩
  rw [ldLoadPlain, ldLoadPa]

/-- (Lean-only, deviation 3) THE BLOCK, RE-ANSWERED, over any admin sub-alphabet `A`. -/
theorem WeakRvwmoCycWit2.w2BlkSubstG (A : Wlabel → Prop) (hA : ∀ l, A l → lbAdmin true l)
    (cpu : CPU) (d0 : Efab) (ws : Wstate) (aq : Bool) (base : Int) (ts : List Nat)
    (vs : List (BitVec 8)) (l : Wlabel) (rds : List Nat) (wrs : List Register) (rs : RegFile)
    (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch)
    (tvs2 : List (Nat × BitVec 8)) :
    tvs2.length = 4 →
    WeakRvwmoCert2.cblkG A cpu d0 ws (.LLoad aq base ts vs) l rds wrs w2M rs fn ib m' rs' fn'
      ib' →
    rds = [] ∧ fn' = none ∧ (∃ v1 : RegisterType w2Rd, m' = w2K1 v1) ∧
    ∃ (l2 : Wlabel) (rds2 : List Nat) (wrs2 : List Register) (v2 : RegisterType w2Rd),
      WeakRvwmoCert2.cblkG A cpu d0 ws
        (.LLoad false (paZ evFlag) (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        l2 rds2 wrs2 w2M rs fn ib (w2K1 v2) rs' fn' ib' := by
  intro hlen2 hblk
  obtain ⟨ls, ma, rsa, fna, iba, da, rdsA, wrsA, annA, rdsB, wrsB, annB, hadm, hA', hre, hB,
    rfl, rfl⟩ := hblk
  obtain ⟨hma, rfl⟩ :=
    w2MAdmFix cpu ls rdsA wrsA annA _ rs fn ib d0 ma rsa fna iba da hA'
      (fun l0 h => hA l0 (hadm l0 h)) rfl
  subst hma
  obtain ⟨ors2, oib2, wrs02, ann02, obar2, hhw⟩ :=
    phrunOne cpu l rdsB wrsB annB _ rsa fna iba da m' rs' fn' ib' d0 hB
  have hrdsB : rdsB = [] :=
    w2MStepRds cpu rsa fna iba da l rdsB wrs02 ann02 m' ors2 fn' d0 oib2 obar2 hhw
  subst hrdsB
  have hst := pevrunSingleInv l _ _ _ _
    (phrunPevrun cpu [l] [] wrsB annB _ rsa fna iba da m' rs' fn' ib' d0 hB)
  obtain ⟨tvs, -, -, hshape⟩ := hlblRealizesLoadShape _ ws aq base ts vs l hre
  obtain ⟨-, ors, oib, obar, hrs, hib, hhart⟩ := hst
  have hnotd : ∀ kd ba bs, l ≠ .LDev kd ba bs := by
    rintro kd ba bs rfl
    rcases hshape with h | ⟨_, h⟩ <;> cases h
  rcases hhart with ⟨hnode, hd⟩ | hplic
  · cases fna with
    | some f =>
      obtain ⟨pr, pw, sr, sw⟩ := f
      obtain ⟨rfl, _⟩ := hnode
      rcases hshape with h | ⟨_, h⟩ <;> cases h
    | none =>
      obtain ⟨tvs0, -, -, hv1, hors, hfn', hd', hoib, -⟩ :=
        w2MStepInv rsa iba da.efDev l m' ors fn' d0.efDev oib obar hnode
      subst hors hfn' hoib
      have hdd : d0 = da := by rw [hd, hd']
      subst hdd
      have hrs' : rs' = rsa := hrs
      have hib' : ib' = iba := hib
      subst hrs' hib'
      refine ⟨rfl, rfl, hv1, ?_⟩
      obtain ⟨v2, hst2⟩ := w2PstepAny cpu rs' ib' d0 tvs2 hlen2
      obtain ⟨rdsB2, wrsB2, annB2, hB2⟩ :=
        pevrunPhrun [.LLoad false false (paZ evFlag) tvs2 []] _ d0 _ d0
          (pevrun.more hst2 (pevrun.nil _ _))
          cpu w2M rs' none ib' (w2K1 v2) rs' none ib' rfl rfl
      exact ⟨.LLoad false false (paZ evFlag) tvs2 [], [] ++ rdsB2, wrsA ++ wrsB2, v2, ls, w2M,
        rs', none, ib', d0, [], wrsA, annA, rdsB2, wrsB2, annB2, hadm, hA',
        hlblRealizesLoad _ ws false (paZ evFlag) tvs2, hB2, rfl, rfl⟩
  · obtain ⟨_, _, _, _, hl, _⟩ := hplic
    exact absurd hl (hnotd _ _ _)

/-- THE BLOCK, RE-ANSWERED (Rocq's statement, at plain `cblk`). -/
theorem w2BlkSubst (cpu : CPU) (d0 : Efab) (ws : Wstate) (aq : Bool) (base : Int)
    (ts : List Nat) (vs : List (BitVec 8)) (l : Wlabel) (rds : List Nat) (wrs : List Register)
    (rs : RegFile) (fn : Ofence) (ib : Ibch) (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence)
    (ib' : Ibch) (tvs2 : List (Nat × BitVec 8)) :
    tvs2.length = 4 →
    cblk cpu d0 ws (.LLoad aq base ts vs) l rds wrs w2M rs fn ib m' rs' fn' ib' →
    rds = [] ∧ fn' = none ∧ (∃ v1 : RegisterType w2Rd, m' = w2K1 v1) ∧
    ∃ (l2 : Wlabel) (rds2 : List Nat) (wrs2 : List Register) (v2 : RegisterType w2Rd),
      cblk cpu d0 ws (.LLoad false (paZ evFlag) (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        l2 rds2 wrs2 w2M rs fn ib (w2K1 v2) rs' fn' ib' :=
  WeakRvwmoCycWit2.w2BlkSubstG (lbAdmin true) (fun _ h => h) cpu d0 ws aq base ts vs l rds wrs
    rs fn ib m' rs' fn' ib' tvs2

/-- (Lean-only, deviation 3) … and the PINNED block's, at any image. -/
theorem WeakRvwmoCycWit2.w2BlkSubstPin (im : Image) (cpu : CPU) (d0 : Efab) (ws : Wstate)
    (aq : Bool) (base : Int) (ts : List Nat) (vs : List (BitVec 8)) (l : Wlabel)
    (rds : List Nat) (wrs : List Register) (rs : RegFile) (fn : Ofence) (ib : Ibch)
    (m' : SailM Unit) (rs' : RegFile) (fn' : Ofence) (ib' : Ibch)
    (tvs2 : List (Nat × BitVec 8)) :
    tvs2.length = 4 →
    WeakRvwmoCert2.cblkPin im cpu d0 ws (.LLoad aq base ts vs) l rds wrs w2M rs fn ib m' rs' fn'
      ib' →
    rds = [] ∧ fn' = none ∧ (∃ v1 : RegisterType w2Rd, m' = w2K1 v1) ∧
    ∃ (l2 : Wlabel) (rds2 : List Nat) (wrs2 : List Register) (v2 : RegisterType w2Rd),
      WeakRvwmoCert2.cblkPin im cpu d0 ws
        (.LLoad false (paZ evFlag) (tvs2.map Prod.fst) (tvs2.map Prod.snd))
        l2 rds2 wrs2 w2M rs fn ib (w2K1 v2) rs' fn' ib' :=
  WeakRvwmoCycWit2.w2BlkSubstG (WeakRvwmoCert2.lbPin im) (fun _ h => h.1) cpu d0 ws aq base ts
    vs l rds wrs rs fn ib m' rs' fn' ib' tvs2

/-! # 3c. THE DIVERGED ARM, FIRED BY THE GENERIC SEGMENT ENGINE

Rocq's `Section w2seg` context (`cpu d0 t w ib rs rs2`) is explicit (deviation 1). -/

def w2Lb (t : Nat) (w : BitVec 32) : Lbl :=
  .LLoad false (paZ evFlag) (ldTs t) (WeakRvwmoConfWit2.ldVs w)
def w2Q (t : Nat) (w : BitVec 32) : Nat → Lbl → Prop :=
  fun k lb => k = 0 ∧ lb = w2Lb t w
def w2Ctx : Nat → Cand → Prop :=
  fun _ c => latestBytesOk c (paZ evFlag) 4
def w2Nd (cpu : CPU) (d0 : Efab) (t : Nat) (w : BitVec 32) : Nat → SailM Unit → Prop :=
  ndreach cpu d0 (w2Q t w) 0 w2M
noncomputable def w2Pst (cpu : CPU) (rs2 : RegFile) (ib : Ibch) : Nat → List Pexv6 :=
  fun _ => [.PHart cpu w2M rs2 none ib]
noncomputable def w2St (cpu : CPU) (d0 : Efab) (rs2 : RegFile) (ib : Ibch) : CycState :=
  ⟨cwC0, w2Pst cpu rs2 ib, fun _ => d0⟩

/-- THE NODE IS PINNED at row position 0. -/
theorem w2NdPin (cpu : CPU) (d0 : Efab) (t : Nat) (w : BitVec 32) (k : Nat) (m : SailM Unit) :
    w2Nd cpu d0 t w k m → k = 0 → m = w2M := by
  intro hnd hk
  refine ndreachFix cpu d0 (w2Q t w) (fun mm => mm = w2M) w2M rfl ?_ k m hnd hk
  intro m1 m2 rs1' rs2' fn1 fn2 ib1 ib2 ls rds wrs ann hm1 hadm hrun
  exact (w2MAdmFix cpu ls rds wrs ann m1 rs1' fn1 ib1 d0 m2 rs2' fn2 ib2 d0 hrun hadm hm1).1

/-- THE EMISSION: one block, no administrative stretch, at the REAL load request. -/
theorem w2Hemit (cpu : CPU) (d0 : Efab) (t : Nat) (w : BitVec 32) (ib : Ibch) (rs : RegFile) :
    hemit (fun _ => d0) 0 ((candLastSt cwC0).msWs 0) [w2Lb t w] (w2P0 cpu rs ib)
      [(.LLoad false false (paZ evFlag) (ldTvs t w) [], some 0)] (w2P1 w cpu rs ib) :=
  hemit.HEone (dv := fun _ => d0) 0 ((candLastSt cwC0).msWs 0) (w2Lb t w) [] (w2P0 cpu rs ib) []
    (w2P0 cpu rs ib) d0 (.LLoad false false (paZ evFlag) (ldTvs t w) []) (w2P1 w cpu rs ib) []
    (w2P1 w cpu rs ib) (.ARnil _ _) (w2Realizes cpu rs ib _ t w) (w2Pstep cpu rs ib d0 t w)
    (.HEnil _ _ _)

theorem w2Devfree (t : Nat) (w : BitVec 32) (kd : IoKind) (ba : Int) (bs : List (BitVec 8)) :
    Wlabel.LDev kd ba bs ∉
      ([(.LLoad false false (paZ evFlag) (ldTvs t w) [], some 0)] : List Eitem).map Prod.fst := by
  simp

/-- (Lean-only, deviation 3) the emission's labels are pinned (it has no fetch item). -/
theorem WeakRvwmoCycWit2.w2EsPin (im : Image) (t : Nat) (w : BitVec 32) :
    WeakRvwmoCert2.esPin im [(.LLoad false false (paZ evFlag) (ldTvs t w) [], some 0)] := by
  intro l hl
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hl
  subst hl
  trivial

theorem w2CstOk (cpu : CPU) (d0 : Efab) (rs2 : RegFile) (ib : Ibch) :
    cstOk d0 (w2St cpu d0 rs2 ib) := by
  refine ⟨cwC0Cons, ?_, rfl⟩
  intro k s hs
  exact absurd hs (by simp [candExec, w2St, cwC0])

theorem w2HQ (t : Nat) (w : BitVec 32) (i : Nat) (lb : Lbl) :
    [w2Lb t w][i]? = some lb → w2Q t w (0 + i) lb := by
  intro h
  cases i with
  | zero => exact ⟨rfl, (Option.some.inj h).symm⟩
  | succ i => simp at h

theorem w2QRmwfree (t : Nat) (w : BitVec 32) (k : Nat) (lb : Lbl) :
    w2Q t w k lb → lbRmwfree lb := by
  rintro ⟨-, rfl⟩
  trivial

theorem w2Hpres (t : Nat) (w : BitVec 32) (k : Nat) (c0 : Cand) (lb lb' : Lbl) :
    w2Ctx k c0 → srvwmoConsistent c0 → w2Q t w k lb →
    lblReidxW lb lb' → mstepOk (candLastSt c0) 0 lb' → True →
    w2Ctx (k + 1) (candSnoc c0 ⟨0, lb'⟩) := by
  rintro hctx - ⟨-, rfl⟩ hri - -
  have hw' : lbIsW lb' = false := lblReidxWNotw (w2Lb t w) lb' hri rfl
  unfold w2Ctx latestBytesOk
  rw [candSnocImg, cdLogEndSnoc, esMsgNotw ⟨0, lb'⟩ hw', List.append_nil]
  exact hctx

theorem w2Hrds (cpu : CPU) (d0 : Efab) (t : Nat) (w : BitVec 32) (k : Nat) (lb : Lbl)
    (ws : Wstate) (l : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit)
    (rs1 : RegFile) (fn : Ofence) (ib1 : Ibch) (m' : SailM Unit) (rs1' : RegFile)
    (fn' : Ofence) (ib1' : Ibch) :
    w2Q t w k lb → w2Nd cpu d0 t w k m →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib1 m' rs1' fn' ib1' →
    rdsOk (fun n => n ∉ w2T) rds := by
  rintro ⟨hk, rfl⟩ hnd hblk
  rw [w2NdPin cpu d0 t w k m hnd hk] at hblk
  obtain ⟨rfl, -⟩ := w2BlkSubst cpu d0 ws false (paZ evFlag) (ldTs t)
    (WeakRvwmoConfWit2.ldVs w) l rds wrs rs1 fn ib1 m' rs1' fn' ib1'
    (ldTvs 0 (BitVec.ofNat 32 0)) rfl hblk
  intro n hn
  exact absurd hn List.not_mem_nil

theorem w2Hrdsp (cpu : CPU) (d0 : Efab) (t : Nat) (w : BitVec 32) (k : Nat) (lb : Lbl)
    (ws : Wstate) (l1 l2 : Wlabel) (rds : List Nat) (wrs : List Register) (m : SailM Unit)
    (rs1 : RegFile) (fn : Ofence) (ib1 : Ibch) (m' : SailM Unit) (rs1' : RegFile)
    (fn' : Ofence) (ib1' : Ibch) :
    w2Q t w k lb → w2Nd cpu d0 t w k m →
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib1 m' rs1' fn' ib1' →
    rdsOk (fun n => n ∉ w2T) rds := by
  rintro ⟨-, rfl⟩ - hblk
  exact (cblkpRmw cpu d0 ws _ l1 l2 rds wrs m rs1 fn ib1 m' rs1' fn' ib1' hblk trivial).elim

/-- THE POLICY (deviation 3: on pinned blocks).  The certified run reads the CANDIDATE's latest
bytes; the emission read `w`; the two runs leave the memory node at DIFFERENT successors, and
`csync`'s DIVERGED arm admits it. -/
theorem w2Hpol (cpu : CPU) (d0 : Efab) (t : Nat) (w : BitVec 32) (k : Nat) (c0 : Cand)
    (ws : Wstate) (lb : Lbl) (l : Wlabel) (rds : List Nat) (wrs : List Register)
    (m : SailM Unit) (rs1 rs1b : RegFile) (fn : Ofence) (ib1 : Ibch) (m' : SailM Unit)
    (rs1' : RegFile) (fn' : Ofence) (ib1' : Ibch) :
    srvwmoConsistent c0 → w2Ctx k c0 → w2Q t w k lb →
    ((candLastSt c0).msWs 0).wRelp = ws.wRelp →
    dregAgree (fun n => n ∉ w2T) rs1 rs1b →
    w2Nd cpu d0 t w k m →
    WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb l rds wrs m rs1 fn ib1 m' rs1' fn' ib1' →
    ∃ (lb' : Lbl) (l' : Wlabel) (rds' : List Nat) (wrs' : List Register) (rs2' : RegFile)
      (m2' : SailM Unit) (fn2' : Ofence) (ib2' : Ibch),
      WeakRvwmoCert2.cblkPin c0.cdImg cpu d0 ws lb' l' rds' wrs' m rs1b fn ib1 m2' rs2' fn2'
        ib2' ∧
      mstepOk (candLastSt c0) 0 lb' ∧
      lblReidxW lb lb' ∧
      True ∧
      csync w2T m' rs1' fn' ib1' m2' rs2' fn2' ib2' ∧
      (lbIsW lb = true → clockstep w2T m' rs1' fn' ib1' m2' rs2' fn2' ib2') := by
  rintro hc hctx ⟨hk, rfl⟩ - hag hnd hblk
  have hm := w2NdPin cpu d0 t w k m hnd hk
  subst hm
  obtain ⟨hrn, hfn', ⟨v1, hm'⟩, -⟩ :=
    WeakRvwmoCycWit2.w2BlkSubstPin c0.cdImg cpu d0 ws false (paZ evFlag) (ldTs t)
      (WeakRvwmoConfWit2.ldVs w) l rds wrs rs1 fn ib1 m' rs1' fn' ib1'
      (ldTvs 0 (BitVec.ofNat 32 0)) rfl hblk
  obtain ⟨rs2b, hblk2, hag2⟩ :=
    WeakRvwmoCert2.certBlockMirrorG (WeakRvwmoCert2.lbPin c0.cdImg) (fun n => n ∉ w2T) cpu d0
      ws (w2Lb t w) l rds wrs w2M rs1 fn ib1 m' rs1' fn' ib1' rs1b hblk
      (by rw [hrn]; intro n hn; exact absurd hn List.not_mem_nil) hag
  obtain ⟨-, -, -, l2, rds2, wrs2, v2, hblk3⟩ :=
    WeakRvwmoCycWit2.w2BlkSubstPin c0.cdImg cpu d0 ws false (paZ evFlag) (ldTs t)
      (WeakRvwmoConfWit2.ldVs w) l rds wrs rs1b fn ib1 m' rs2b fn' ib1'
      (witTvs c0 (paZ evFlag) 4) (witTvsLength c0 (paZ evFlag) 4) hblk2
  rw [witTvsLbl c0 false (paZ evFlag) 4] at hblk3
  subst hm'
  refine ⟨latestReadLbl c0 false (paZ evFlag) 4, l2, rds2, wrs2, rs2b, w2K1 v2, fn', ib1', hblk3,
    certReadWitness c0 0 false (paZ evFlag) 4 hc hctx, ?_, trivial,
    .inr ⟨hfn', hfn', w2TailSilent v1, w2TailSilent v2, hag2⟩, fun h => by simp [w2Lb, lbIsW] at h⟩
  exact Or.inr (Or.inl ⟨rfl, rfl, rfl, by simp [lrdTs, ldTs], by simp [lrdTs, lrdVs]⟩)

/-- THE INSTANCE.  One `segStep` of the generic engine, at the real load, with the diverged arm
at its exit. -/
theorem w2SegStepDiverged (cpu : CPU) (d0 : Efab) (t : Nat) (w : BitVec 32) (ib : Ibch)
    (rs rs2 : RegFile) :
    dregAgree (fun n => n ∉ w2T) rs rs2 →
    ∃ (St' : CycState) (tradd : List Estep) (m21 : SailM Unit) (rs21 : RegFile)
      (fn21 : Ofence) (ib21 : Ibch),
      segStep d0 ⟨0, [w2Lb t w], 0, tradd⟩ (w2St cpu d0 rs2 ib) St' ∧
      (St'.cstPst (cdEnd St'.cstC))[0]? = some (.PHart cpu m21 rs21 fn21 ib21) ∧
      -- the two runs are `csync` at the exit …
      csync w2T (w2K1 (w2Val (.Ok (w, none)))) rs none ib m21 rs21 fn21 ib21 ∧
      -- … and BOTH are inside the instruction's silent tail: the DIVERGED arm
      tailSilent w2T (w2K1 (w2Val (.Ok (w, none)))) ∧
      tailSilent w2T m21 := by
  intro hag
  obtain ⟨St', tradd, hstep, -, -, -, -,
      ⟨m1, rs11, fn1, ib1, m21, rs21, fn21, ib21, hpfin, hpx, hsync, -, -⟩, -⟩ :=
    segStepOfSegment 0 cpu d0 (fun _ => w2T) (w2Q t w) w2Ctx (fun _ _ => True)
      (w2Nd cpu d0 t w) (fun _ _ h => h) (w2Hpres t w) (w2Hrdsp cpu d0 t w)
      (fun k m m' rs' rs'' fn fn' ib' ib'' ls rds wrs ann hnd ha hr =>
        ndreach.ndAdm k m m' rs' rs'' fn fn' ib' ib'' ls rds wrs ann hnd ha hr)
      (fun k m m' ws lb l rds wrs rs' rs'' fn fn' ib' ib'' hnd hq hb =>
        ndreach.ndBlk k m m' ws lb l rds wrs rs' rs'' fn fn' ib' ib'' hnd hq hb)
      (fun k m m' ws lb l1 l2 rds wrs rs' rs'' fn fn' ib' ib'' hnd hq hb =>
        ndreach.ndBlkp k m m' ws lb l1 l2 rds wrs rs' rs'' fn fn' ib' ib'' hnd hq hb)
      (w2Hpol cpu d0 t w)
      (cpolprOfCpolp 0 cpu d0 w2T (w2Nd cpu d0 t w) w2Ctx (fun _ _ => True) (w2Q t w)
        (cpolpOfRmwfree 0 cpu d0 w2T w2Ctx (fun _ _ => True) (w2Q t w) (w2QRmwfree t w)))
      0 ((candLastSt cwC0).msWs 0) [w2Lb t w] _ _ w2M rs none ib (w2St cpu d0 rs2 ib) w2M rs2
      none ib (w2Hemit cpu d0 t w ib rs) (w2Devfree t w) (WeakRvwmoCycWit2.w2EsPin _ t w)
      (w2HQ t w) (w2CstOk cpu d0 rs2 ib) cwBytes0 rfl .ndStart (.inl ⟨rfl, rfl, rfl, hag⟩) rfl
  simp only [w2P1, Pexv6.PHart.injEq] at hpfin
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hpfin
  have hts1 : tailSilent w2T (w2K1 (w2Val (.Ok (w, none)))) := w2TailSilent _
  refine ⟨St', tradd, m21, rs21, fn21, ib21, hstep, hpx, hsync, hts1, ?_⟩
  rcases hsync with ⟨rfl, -⟩ | ⟨-, -, -, hts2, -⟩
  · exact hts1
  · exact hts2

/-! # 3d. THE POISONED BLOCK — the per-hart-taint migration's own witness -/

abbrev w3Src : Register := .x15
abbrev w3Dst : Register := .x14

/-- THE TAINT, BEFORE AND AFTER. -/
def w3T0 : List Nat := [15]
def w3T1 : List Nat := [15, 14]

theorem w3DstNum : eregNum w3Dst = some 14 := rfl

theorem w3TaintGrows : w3T0 ⊆ w3T1 ∧ 14 ∈ w3T1 ∧ 14 ∉ w3T0 := by
  refine ⟨?_, by simp [w3T1], by simp [w3T0]⟩
  intro n hn
  simp only [w3T0, List.mem_singleton] at hn
  subst hn
  simp [w3T1]

def w3Val (ans : Result (BitVec (8 * 4) × Option Bool) Arch.abort) : RegisterType w3Dst :=
  match ans with
  | .Ok (w, _) => (BitVec.ofNat 64 w.toNat : BitVec 64)
  | .Err _ => (BitVec.ofNat 64 0 : BitVec 64)

def w3K1 (v : RegisterType w3Dst) : SailM Unit :=
  .impure (.ok (.regWrite w3Dst v)) (fun _ => .pure ())

noncomputable def w3Ld (a : PAddr) : SailM Unit :=
  .impure (.ok (.memRead 4 64 (cyRreq a))) (fun ans => w3K1 (w3Val ans))

/-- THE ADDRESS DEPENDS ON THE TAINTED CARRIER — this is what a poisoned block IS. -/
def w3Addr (v : RegisterType w3Src) : PAddr :=
  if (v : BitVec 64).toNat = 0 then cyA else cyB

noncomputable def w3M : SailM Unit :=
  .impure (.ok (.regRead w3Src)) (fun v => w3Ld (w3Addr v))

theorem w3Rds : pnodeRds w3M = [15] := rfl

/-- … so the block's read set MEETS the taint. -/
theorem w3NotRdsOk : ¬ rdsOk (fun n => n ∉ w3T0) (pnodeRds w3M) := by
  intro h
  exact h 15 (by rw [w3Rds]; exact List.mem_singleton_self _) (List.mem_singleton_self _)

theorem w3AddrRam (v : RegisterType w3Src) : devAddr (w3Addr v) = false := by
  unfold w3Addr
  split
  · exact cyARam
  · exact cyBRam

/-- ONE ADMINISTRATIVE STEP: the register read. -/
theorem w3Regread (cpu : CPU) (rs : RegFile) (ib : Ibch) (d : Efab) :
    phrun cpu [.LSilent] ([15] ++ []) ([] ++ []) (false || false) w3M rs none ib d
      (w3Ld (w3Addr (rs w3Src))) rs none (ibRd ib w3Src) d :=
  phrun.more (Or.inl ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, w3Rds.symm, rfl, rfl⟩)
    (phrun.nil _ _ _ _ _)

/-- THE LOAD NODE STEPS AT EVERY ANSWER of its own width. -/
theorem w3LdStep (cpu : CPU) (rs : RegFile) (ib : Ibch) (d : Efab) (a : PAddr)
    (tvs : List (Nat × BitVec 8)) :
    devAddr a = false → tvs.length = 4 →
    ∃ v : RegisterType w3Dst,
      pstepEv (.PHart cpu (w3Ld a) rs none ib) d (.LLoad false false (paZ a) tvs [])
        (.PHart cpu (w3K1 v) rs none ib) d := by
  intro hram hlen
  obtain ⟨w, hw⟩ := bvOfBytes 4 (tvs.map Prod.snd) (by rw [List.length_map, hlen])
  refine ⟨w3Val (.Ok (w, none)), rfl, none, none, none, rfl, rfl, Or.inl ⟨?_, rfl⟩⟩
  simp only [pstepNode, pnodeStep, w3Ld, WeakRvwmoCycWit.cyRreqPa, hram, Bool.false_eq_true,
    if_false]
  refine Or.inr ⟨by rw [cyRreqPlain], Or.inl ⟨by rw [cyRreqPlain], w, tvs, hlen, hw, ?_,
    by trivial, by trivial, by trivial, by trivial, by trivial, by trivial⟩⟩
  rw [cyRreqPlain]

theorem w3Realizes (cpu : CPU) (rs : RegFile) (ib : Ibch) (ws : Wstate) (a : PAddr)
    (tvs : List (Nat × BitVec 8)) :
    hlblRealizes (.PHart cpu (w3Ld a) rs none ib) ws
      (.LLoad false (paZ a) (tvs.map Prod.fst) (tvs.map Prod.snd))
      (.LLoad false false (paZ a) tvs []) :=
  ⟨trivial, rfl, rfl, rfl⟩

/-- THE BLOCK, at whatever the tainted carrier holds. -/
theorem w3Blk (cpu : CPU) (d0 : Efab) (ws : Wstate) (rs : RegFile) (ib : Ibch)
    (tvs : List (Nat × BitVec 8)) :
    tvs.length = 4 →
    ∃ (v : RegisterType w3Dst) (rds : List Nat) (wrs : List Register),
      cblk cpu d0 ws
        (.LLoad false (paZ (w3Addr (rs w3Src))) (tvs.map Prod.fst) (tvs.map Prod.snd))
        (.LLoad false false (paZ (w3Addr (rs w3Src))) tvs [])
        rds wrs w3M rs none ib (w3K1 v) rs none (ibRd ib w3Src) ∧
      -- … and the block's READ SET holds the tainted carrier
      15 ∈ rds := by
  intro hlen
  obtain ⟨v, hst⟩ := w3LdStep cpu rs (ibRd ib w3Src) d0 (w3Addr (rs w3Src)) tvs
    (w3AddrRam _) hlen
  obtain ⟨rdsB, wrsB, annB, hB⟩ :=
    pevrunPhrun [.LLoad false false (paZ (w3Addr (rs w3Src))) tvs []] _ d0 _ d0
      (pevrun.more hst (pevrun.nil _ _))
      cpu (w3Ld (w3Addr (rs w3Src))) rs none (ibRd ib w3Src) (w3K1 v) rs none (ibRd ib w3Src)
      rfl rfl
  refine ⟨v, ([15] ++ []) ++ rdsB, ([] ++ []) ++ wrsB,
    ⟨[.LSilent], w3Ld (w3Addr (rs w3Src)), rs, none, ibRd ib w3Src, d0, [15] ++ [], [] ++ [],
      false || false, rdsB, wrsB, annB, ?_, w3Regread cpu rs ib d0,
      w3Realizes cpu rs (ibRd ib w3Src) ws _ tvs, hB, rfl, rfl⟩, ?_⟩
  · intro l0 hl0
    rw [List.mem_singleton] at hl0
    subst hl0
    trivial
  · simp

/-! ## 3d.1 THE TWO RUNS, AND THE THREE FACTS THE ARM RESTS ON -/

def w3Rs2 (rs : RegFile) : RegFile := rs.set w3Src (BitVec.ofNat 64 1 : BitVec 64)

theorem w3Agree (rs : RegFile) : dregAgree (fun n => n ∉ w3T0) rs (w3Rs2 rs) := by
  intro r hr
  unfold w3Rs2
  by_cases h : r = w3Src
  · subst h
    exact absurd (List.mem_singleton_self 15) (hr 15 w2RdNum)
  · exact (RegFile.set_other rs w3Src r _ h).symm

theorem w3Lookup2 (rs : RegFile) : w3Rs2 rs w3Src = (BitVec.ofNat 64 1 : BitVec 64) :=
  RegFile.set_same rs w3Src _

/-- THE TWO ADDRESSES REALLY DIFFER when the carrier does. -/
theorem w3Addr0 : w3Addr (BitVec.ofNat 64 0 : BitVec 64) = cyA := rfl
theorem w3Addr1 : w3Addr (BitVec.ofNat 64 1 : BitVec 64) = cyB := rfl
theorem w3ZAZB : paZ cyA ≠ paZ cyB := by
  show zA ≠ zB
  rw [zAVal, zBVal]
  decide

/-- (i) THE THIRD ARM IS INHABITED. -/
theorem w3Poisoned (ts1 ts2 : List Nat) (vs1 vs2 : List (BitVec 8)) :
    vs2.length = ts2.length →
    lblPoisoned (.LLoad false (paZ cyA) ts1 vs1) (.LLoad false (paZ cyB) ts2 vs2) :=
  fun h => ⟨rfl, h⟩

/-- … and it is the ONLY one that relates the two labels: their ADDRESSES differ. -/
theorem w3NotReidx (ts1 ts2 : List Nat) (vs1 vs2 : List (BitVec 8)) :
    ¬ lblReidx (.LLoad false (paZ cyA) ts1 vs1) (.LLoad false (paZ cyB) ts2 vs2) ∧
    ¬ lblReidxSub (.LLoad false (paZ cyA) ts1 vs1) (.LLoad false (paZ cyB) ts2 vs2) :=
  ⟨fun ⟨_, hb, _⟩ => w3ZAZB hb.symm, fun ⟨_, _, hb, _⟩ => w3ZAZB hb.symm⟩

/-- (ii) THE TAIL IS SILENT AT THE GROWN TAINT. -/
theorem w3TailSilent (v : RegisterType w3Dst) : tailSilent w3T1 (w3K1 v) := by
  refine .tsNext _ _ trivial ?_ (fun _ => .tsRet _)
  intro r hr
  simp only [pnodeWrs, List.mem_singleton] at hr
  subst hr
  exact ⟨14, w3DstNum, by simp [w3T1]⟩

/-- … and `w3T0` does NOT admit it. -/
theorem w3TailWritesDst (v : RegisterType w3Dst) :
    pnodeWrs (w3K1 v) = [w3Dst] ∧ eregNum w3Dst = some 14 ∧ 14 ∉ w3T0 :=
  ⟨rfl, w3DstNum, by simp [w3T0]⟩

/-- (iii) THE TWO RUNS ARE IN `csync`'s DIVERGED ARM at the GROWN taint … -/
theorem w3CsyncGrown (v1 v2 : RegisterType w3Dst) (rs1' rs2' : RegFile) (ib' : Ibch) :
    dregAgree (fun n => n ∉ w3T1) rs1' rs2' →
    csync w3T1 (w3K1 v1) rs1' none ib' (w3K1 v2) rs2' none ib' :=
  fun hag => .inr ⟨rfl, rfl, w3TailSilent v1, w3TailSilent v2, hag⟩

theorem w3NodesDiffer (v1 v2 : RegisterType w3Dst) : v1 ≠ v2 → w3K1 v1 ≠ w3K1 v2 := by
  intro hne heq
  apply hne
  have hf : ∀ v : RegisterType w3Dst,
      (match esilNodeAny ldRs0 (w3K1 v) with
        | some (rs', _) => rs' w3Dst
        | none => (BitVec.ofNat 64 0 : BitVec 64)) = v :=
    fun v => RegFile.set_same ldRs0 w3Dst v
  rw [← hf v1, ← hf v2, heq]

/-- … and NOT in lockstep. -/
theorem w3NotClockstep (v1 v2 : RegisterType w3Dst) (rs1' rs2' : RegFile) (ib' : Ibch) :
    v1 ≠ v2 → ¬ clockstep w3T1 (w3K1 v1) rs1' none ib' (w3K1 v2) rs2' none ib' :=
  fun hne ⟨heq, _⟩ => w3NodesDiffer v2 v1 (fun h => hne h.symm) heq

/-! ## 3d.2 THE WITNESS, ASSEMBLED -/

theorem w3Pair (cpu : CPU) (d0 : Efab) (ws : Wstate) (rs : RegFile) (ib : Ibch)
    (tvs1 tvs2 : List (Nat × BitVec 8)) :
    rs w3Src = (BitVec.ofNat 64 0 : BitVec 64) →
    tvs1.length = 4 → tvs2.length = 4 →
    ∃ (v1 v2 : RegisterType w3Dst) (rds1 rds2 : List Nat) (wrs1 wrs2 : List Register)
      (l1 l2 : Wlabel),
      -- the emission's block: address `cyA`
      cblk cpu d0 ws (.LLoad false (paZ cyA) (tvs1.map Prod.fst) (tvs1.map Prod.snd)) l1 rds1
        wrs1 w3M rs none ib (w3K1 v1) rs none (ibRd ib w3Src) ∧
      -- the certified run's block, from the SAME node: address `cyB`
      cblk cpu d0 ws (.LLoad false (paZ cyB) (tvs2.map Prod.fst) (tvs2.map Prod.snd)) l2 rds2
        wrs2 w3M (w3Rs2 rs) none ib (w3K1 v2) (w3Rs2 rs) none (ibRd ib w3Src) ∧
      -- the register files agree off the taint …
      dregAgree (fun n => n ∉ w3T0) rs (w3Rs2 rs) ∧
      -- … the block's read set MEETS it, so no mirror exists …
      15 ∈ rds1 ∧ ¬ rdsOk (fun n => n ∉ w3T0) rds1 ∧
      -- … the two labels are related by the POISONED arm and by nothing weaker …
      lblPoisoned (.LLoad false (paZ cyA) (tvs1.map Prod.fst) (tvs1.map Prod.snd))
        (.LLoad false (paZ cyB) (tvs2.map Prod.fst) (tvs2.map Prod.snd)) ∧
      ¬ lblReidx (.LLoad false (paZ cyA) (tvs1.map Prod.fst) (tvs1.map Prod.snd))
        (.LLoad false (paZ cyB) (tvs2.map Prod.fst) (tvs2.map Prod.snd)) ∧
      ¬ lblReidxSub (.LLoad false (paZ cyA) (tvs1.map Prod.fst) (tvs1.map Prod.snd))
        (.LLoad false (paZ cyB) (tvs2.map Prod.fst) (tvs2.map Prod.snd)) ∧
      -- … and the exit is `csync`'s DIVERGED arm at the GROWN taint.
      csync w3T1 (w3K1 v1) rs none (ibRd ib w3Src) (w3K1 v2) (w3Rs2 rs) none (ibRd ib w3Src) := by
  intro hv hl1 hl2
  have hA : w3Addr (rs w3Src) = cyA := by rw [hv]; exact w3Addr0
  have hB : w3Addr (w3Rs2 rs w3Src) = cyB := by rw [w3Lookup2]; exact w3Addr1
  obtain ⟨v1, rds1, wrs1, hb1, hin1⟩ := w3Blk cpu d0 ws rs ib tvs1 hl1
  obtain ⟨v2, rds2, wrs2, hb2, -⟩ := w3Blk cpu d0 ws (w3Rs2 rs) ib tvs2 hl2
  rw [hA] at hb1
  rw [hB] at hb2
  refine ⟨v1, v2, rds1, rds2, wrs1, wrs2, .LLoad false false (paZ cyA) tvs1 [],
    .LLoad false false (paZ cyB) tvs2 [], hb1, hb2, w3Agree rs, hin1,
    fun h => h 15 hin1 (List.mem_singleton_self _), ?_, (w3NotReidx _ _ _ _).1,
    (w3NotReidx _ _ _ _).2, ?_⟩
  · exact w3Poisoned _ _ _ _ (by rw [List.length_map, List.length_map])
  · exact w3CsyncGrown v1 v2 rs (w3Rs2 rs) (ibRd ib w3Src)
      (dregAgreeTaintMono w3T0 w3T1 rs (w3Rs2 rs) w3TaintGrows.1 (w3Agree rs))

end Weak
