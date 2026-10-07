/-
Weak: **THE PAIRED TAINT LAW** (route B, the audit's `tail_par`).

Rocq: `iris/WeakEvProv2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

`WeakEvProv.taintClosure` is the UNPAIRED frame law: two runs that have parted company after a
witness read agree off `T` plus whatever either remainder wrote, PROVIDED every register either
remainder writes is a dependency carrier the taint set holds.  That hypothesis is FALSE at the
real tail of `lw a5,0(a4)` at `main+0x16`: nine nodes -- the `x15` write (the loaded value), reads
of `hart_state`, `nextPC`, a write of `PC`, …, a WRITE of `minstret`, then the boundary.  `PC` and
`minstret` are not carriers (§5 `laTailTaintClosureFails`, machine-checked).

THE LAW.  Both runs write those two nodes WITH THE SAME VALUE, and a `regWrite`'s value is part of
the node term, so the law is a SIMULATION on node PAIRS:

  §2 `tpar T m1 m2` -- four arms: `tpConv` (the same node), `tpGen` (the same non-writing outcome,
     successors related pointwise: the `regRead` arm, the silent nodes, memory nodes, the retry
     self-loop), `tpWrEq` (a register write of the SAME value from two different continuations,
     NO carrier condition: the `PC`/`minstret` arm), `tpWr` (DIFFERENT values into a carrier the
     taint set holds: the witness load's destination).
  §3 `tparRun` / `tparInstr`: two runs from `tpar`-related nodes stay in step (same labels, same
     annotations, nodes still related, register files agreeing off `T`); existential in the
     second run.  `tparBoundary` / `tparReconverge`: the re-convergence as a corollary.
  §4 `tparOfWitness` / `tparRunLoad`; §4.1 the law's own non-vacuity (`twTpar`, `tgTpar`,
     `tgRun`, `tgNonvacuous`).
  §5 THE REAL TAIL `laTailPar`: the two nine-node tails of the real load at two arbitrary loaded
     words, read off the machine with `WeakRvwmoAdm`'s reflective cursor.

## Deviations from Rocq

1. NAMES / VOCABULARY: camelCase (map below); `WeakEvProv`'s vocabulary (`M unit` ↦
   `SailM Unit`, `regstate` ↦ `RegFile`, `register_set r v rs` ↦ `rs.set r v`, `register_lookup r
   rs` ↦ `rs r`, `oib32` ↦ `Ibch`, `wreg` ↦ `Nat`, `dev_state` ↦ `Efab` / `DevStates`, `ib_rds` ↦
   `Ibch.ibRds`, `bv 32` ↦ `BitVec 32`, `bv_unsigned w` ↦ `w.toNat`, `ib_none` ↦ `ibNone`).
2. lean-sail's `regWrite r v` carries NO access kind (Rocq `RegWrite r ak v`): `tpWrEq` drops `ak`,
   `tpWr` drops `ak1 ak2`, `tparOfWitness` drops `ak1 ak2`.  `tpGen` ranges over the `.ok o`
   outcomes (`k1 k2 : Outcome.ret o → SailM Unit`); a Lean `.error` node is stuck and needs no arm.
3. `obar` (`WeakEvInst` deviation 4): `pnodeStepPair` / `tparStep` carry the executed barrier
   `obar`, the same in both runs.  `pnodeStepPair` is stated at the `pnodeStep` tier (`DevStates`);
   `tparStep` at `pstepHw`'s (`Efab`), whose node arms also carry `d' = { d with efDev := … }`.
4. THE PLIC WIRE (`WeakEvProv` deviation 4): Lean's wire sets either pin (`pinSet`), so the wire arm
   of `tparStep` is closed by case analysis on the pin (as `WeakEvProv.pstepPlicDagree`).
5. THE COMPUTATIONS (§5): Rocq's `vm_cast_no_check` and `exact_no_check eq_refl` facts are closed by
   `WeakRvwmoAdm`'s `weak_adm_krfl` (kernel `Eq.refl` over the local context); the closed `Option`
   / `Bool` facts (`eregNum …`, `laX2NoRd`) by `decide +kernel`.  Rocq's `bool_decide (15 ∈ …)` ↦
   `decide (15 ∈ …)`.  The tail is the Lean cursor's (`laX2`, `ahRead w.toNat laX2`); its
   measurements match Rocq (nine nodes, `PC` written at node 4, `minstret` at node 8).
   `laHeadSucc` (an equation between two MONAD terms at two free words) is NOT closable by
   `weak_adm_krfl`: the kernel's lazy conversion of `mrwSucc (laTl w1) ≡ mrwSucc (laTl w2)` hits a
   deterministic timeout (and "deep recursion" at 20× the heartbeats) -- the continuation of the
   `x15` write still mentions the loaded word (`wX`'s `xreg_write_callback … in_v`), and the
   kernel's compare-the-arguments-first strategy then descends into the symbolic `BitVec`
   arithmetic.  It is closed by the Lean-only tactic `weak_ev_prov2_kwhnf`: `Kernel.whnf` of both
   sides (the next node, `regRead hart_state`, whose continuation no longer mentions the word),
   checked SYNTACTICALLY equal, then two kernel-checked auxiliary theorems `lhs = W`, `rhs = W`.
6. Lean-only helpers (file-qualified): `WeakEvProv2.pnodeRdsCongr`, `WeakEvProv2.pnodeWrsCongr`,
   `WeakEvProv2.ibnAnnCongr` (the three annotations are functions of the OUTCOME, not of the
   continuation -- Rocq gets them by `simpl`), `WeakEvProv2.mrwRegInv` (the inversion `tpar_of_rw`
   does by `destruct`).
7. `Example tg_nonvacuous` ↦ `theorem`; §6's `Print Assumptions` are dropped (the lint's
   axiom/sorry ban is the audit).

**File-qualified names:** none of this file's Rocq names is in `notes/weak-port-dupnames.json`;
the Lean-only helpers of deviation 6 are file-qualified.

Q7 (owner ruling, `notes/weak-port-q7-sfence.md` route (a), Lean-only): `tparInstr` takes `LFence false false false false ∉ ls` (`WeakEvProv.phrunNoInstr`); Lean-only `WeakEvProv2.laLsNoMark` supplies it for the real tail.

**Rocq → Lean name map.**  `dreg_agree_excl2` `dregAgreeExcl2`, `mrw_reg` `mrwReg`, `mrw_succ`
`mrwSucc`, `mrw_set` `mrwSet`, `tpar` `tpar` (`tp_conv/gen/wr_eq/wr` `tpConv/tpGen/tpWrEq/tpWr`),
`tpar_boundary` `tparBoundary`, `tpar_boundary_r` `tparBoundaryR`, `pnode_step_pair`
`pnodeStepPair`, `tpar_step` `tparStep`, `tpar_run` `tparRun`, `tpar_instr` `tparInstr`,
`tpar_reconverge` `tparReconverge`, `tpar_of_witness` `tparOfWitness`, `tpar_run_load`
`tparRunLoad`, `tw_m` `twM`, `tw_pc_not_carrier` `twPcNotCarrier`, `tw_x14_carrier`
`twX14Carrier`, `tw_tpar` `twTpar`, `tw_nodes_differ` `twNodesDiffer`, `tg_m` `tgM`, `tg_tpar`
`tgTpar`, `tg_run` `tgRun`, `tg_nonvacuous` `tgNonvacuous`, `la_st` `laSt`, `la_tl` `laTl`,
`la_end` `laEnd`, `la_head_reg` `laHeadReg`, `la_rd_carrier` `laRdCarrier`, `la_head_succ`
`laHeadSucc`, `tpar_of_rw` `tparOfRw`, `la_tpar` `laTpar`, `la_end_ret` `laEndRet`, `la_ls_len`
`laLsLen`, `la_ls_val` `laLsVal`, `la_ls_no_instr` `laLsNoInstr`, `la_end_ibrds` `laEndIbrds`,
`la_x2_no_rd` `laX2NoRd`, `la_end_untainted` `laEndUntainted`, `la_tail_writes_pc`
`laTailWritesPc`, `la_tail_writes_minstret` `laTailWritesMinstret`, `la_pc_not_carrier`
`laPcNotCarrier`, `la_minstret_not_carrier` `laMinstretNotCarrier`,
`la_tail_taint_closure_fails` `laTailTaintClosureFails`, `la_phrun` `laPhrun`, `la_tail_par`
`laTailPar`.

**Dropped:** nothing (Rocq 45 declarations; Lean 45 + 4 Lean-only + the tactic
`weak_ev_prov2_kwhnf`).
-/
import Weak.WeakRvwmoAdm

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D
open Wlabel

/-! ## 1. THE ONE MISSING AGREEMENT LEMMA -/

theorem dregAgreeExcl2 (P : Nat → Prop) (rs1 rs2 : RegFile) (r : Register)
    (v1 v2 : RegisterType r) :
    (∃ n, eregNum r = some n ∧ ¬ P n) →
    dregAgree P rs1 rs2 →
    dregAgree P (rs1.set r v1) (rs2.set r v2) := by
  rintro ⟨n, hn, hP⟩ hag r' hr'
  by_cases he : r' = r
  · subst he; exact absurd (hr' n hn) hP
  · rw [RegFile.set_other _ _ _ _ he, RegFile.set_other _ _ _ _ he]; exact hag r' hr'

/-- The register a register-write node writes. -/
def mrwReg (m : SailM Unit) : Option Register :=
  match m with
  | .impure (.ok (.regWrite r _)) _ => some r
  | _ => none

/-- The successor of a register-write node. -/
def mrwSucc (m : SailM Unit) : SailM Unit :=
  match m with
  | .impure (.ok (.regWrite _ _)) k => k PUnit.unit
  | _ => .pure ()

/-- A register-write node's effect on a register file. -/
def mrwSet (m : SailM Unit) (rs : RegFile) : RegFile :=
  match m with
  | .impure (.ok (.regWrite r v)) _ => rs.set r v
  | _ => rs

/-! ## 2. THE RELATION -/

inductive tpar (T : List Nat) : SailM Unit → SailM Unit → Prop where
  /-- RE-CONVERGED: the two runs are at the same node. -/
  | tpConv (m : SailM Unit) : tpar T m m
  /-- THE SAME NON-WRITING OUTCOME, successors related pointwise. -/
  | tpGen (o : Outcome Register RegisterType) (k1 k2 : Outcome.ret o → SailM Unit) :
      pnodeWrs (.impure (.ok o) k1) = [] →
      (∀ v, tpar T (k1 v) (k2 v)) →
      tpar T (.impure (.ok o) k1) (.impure (.ok o) k2)
  /-- A REGISTER WRITE OF THE SAME VALUE, from two continuations; no carrier condition. -/
  | tpWrEq (r : Register) (v : RegisterType r) (k1 k2 : PUnit → SailM Unit) :
      tpar T (k1 PUnit.unit) (k2 PUnit.unit) →
      tpar T (.impure (.ok (.regWrite r v)) k1) (.impure (.ok (.regWrite r v)) k2)
  /-- A REGISTER WRITE OF DIFFERENT VALUES INTO A TAINTED CARRIER. -/
  | tpWr (r : Register) (n : Nat) (v1 v2 : RegisterType r) (k1 k2 : PUnit → SailM Unit) :
      eregNum r = some n → n ∈ T →
      tpar T (k1 PUnit.unit) (k2 PUnit.unit) →
      tpar T (.impure (.ok (.regWrite r v1)) k1) (.impure (.ok (.regWrite r v2)) k2)

/-- THE BOUNDARY IS SHARED. -/
theorem tparBoundary (T : List Nat) (y : Unit) (m : SailM Unit) :
    tpar T (.pure y) m → m = .pure y := by
  intro h
  cases h
  rfl

/-- … and the mirror. -/
theorem tparBoundaryR (T : List Nat) (y : Unit) (m : SailM Unit) :
    tpar T m (.pure y) → m = .pure y := by
  intro h
  cases h
  rfl

/-! ## 3. THE SIMULATION -/

theorem WeakEvProv2.pnodeRdsCongr (o : Outcome Register RegisterType)
    (k1 k2 : Outcome.ret o → SailM Unit) :
    pnodeRds (.impure (.ok o) k1) = pnodeRds (.impure (.ok o) k2) := by
  cases o <;> rfl

theorem WeakEvProv2.pnodeWrsCongr (o : Outcome Register RegisterType)
    (k1 k2 : Outcome.ret o → SailM Unit) :
    pnodeWrs (.impure (.ok o) k1) = pnodeWrs (.impure (.ok o) k2) := by
  cases o <;> rfl

theorem WeakEvProv2.ibnAnnCongr (o : Outcome Register RegisterType)
    (k1 k2 : Outcome.ret o → SailM Unit) :
    ibnAnn (.impure (.ok o) k1) = ibnAnn (.impure (.ok o) k2) := by
  cases o <;> rfl

/-- ONE NON-WRITING NODE, paired: the second run's step is CONSTRUCTED from the first one's. -/
theorem pnodeStepPair (T : List Nat) (o : Outcome Register RegisterType)
    (k1 k2 : Outcome.ret o → SailM Unit) (rs1 rs2 : RegFile) (ib : Ibch) (d : DevStates)
    (l : Wlabel) (m1' : SailM Unit) (ors1 : Option RegFile)
    (fn' : Option (Bool × Bool × Bool × Bool)) (d' : DevStates) (oib : Option Ibch)
    (obar : Option barrier_kind) :
    pnodeWrs (.impure (.ok o) k1) = [] →
    rdsOk (fun n => n ∉ T) (pnodeRds (.impure (.ok o) k1)) →
    (∀ v, tpar T (k1 v) (k2 v)) →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    pnodeStep (.impure (.ok o) k1) rs1 ib d l m1' ors1 fn' d' oib obar →
    ors1 = none ∧
    ∃ m2' : SailM Unit,
      pnodeStep (.impure (.ok o) k2) rs2 ib d l m2' none fn' d' oib obar ∧ tpar T m1' m2' := by
  intro hw hrds hk hag h
  cases o with
  | regRead r =>
    -- THE ONE PLACE THE REGISTER FILE IS CONSULTED
    have hlk : rs1 r = rs2 r := hag r (fun n hn => pnodeRdsRead r k1 _ n hrds hn)
    obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := h
    exact ⟨rfl, _, ⟨h1, rfl, rfl, h4, h5, h6, h7⟩, by rw [hlk]; exact hk _⟩
  | regWrite r v => simp [pnodeWrs] at hw
  | memRead n va req =>
    cases hdev : devAddr req.pa
    · simp only [pnodeStep, hdev, Bool.false_eq_true, if_false] at h ⊢
      rcases h with ⟨hif, w, tvs, hlen, hb, h1, rfl, rfl, h4, h5, h6, h7⟩ |
        ⟨hif, ⟨hlat, w, tvs, hlen, hb, h1, rfl, rfl, h4, h5, h6, h7⟩ |
          ⟨hlat, w, tvs, hlen, hb, h1, rfl, rfl, h4, h5, h6, h7⟩⟩
      · exact ⟨rfl, _, Or.inl ⟨hif, w, tvs, hlen, hb, h1, rfl, trivial, h4, h5, h6, h7⟩, hk _⟩
      · exact ⟨rfl, _, Or.inr ⟨hif, Or.inl ⟨hlat, w, tvs, hlen, hb, h1, rfl, trivial, h4, h5, h6,
          h7⟩⟩, hk _⟩
      · exact ⟨rfl, _, Or.inr ⟨hif, Or.inr ⟨hlat, w, tvs, hlen, hb, h1, rfl, trivial, h4, h5, h6,
          h7⟩⟩, hk _⟩
    · simp only [pnodeStep, hdev, if_true] at h ⊢
      obtain ⟨w, h1, h2, rfl, rfl, h5, h6, h7⟩ := h
      exact ⟨rfl, _, ⟨w, h1, h2, rfl, trivial, h5, h6, h7⟩, hk _⟩
  | memWrite n va req =>
    cases hdev : devAddr req.pa <;> cases hv : req.value <;>
      simp only [pnodeStep, hdev, hv, Bool.false_eq_true, if_false, if_true] at h ⊢
    · rcases h with ⟨hn0, ⟨hlat, h1, rfl, rfl, h4, h5, h6, h7⟩ |
        ⟨hlat, ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ | ⟨h1, rfl, rfl, h4, h5, h6, h7⟩⟩⟩
      · exact ⟨rfl, _, ⟨hn0, Or.inl ⟨hlat, h1, rfl, trivial, h4, h5, h6, h7⟩⟩, hk _⟩
      · exact ⟨rfl, _, ⟨hn0, Or.inr ⟨hlat, Or.inl ⟨h1, rfl, trivial, h4, h5, h6, h7⟩⟩⟩, hk _⟩
      · -- THE RETRY SELF-LOOP: the successor is the node itself
        exact ⟨rfl, _, ⟨hn0, Or.inr ⟨hlat, Or.inr ⟨h1, rfl, trivial, h4, h5, h6, h7⟩⟩⟩,
          tpar.tpGen _ k1 k2 rfl hk⟩
    · obtain ⟨h1, h2, rfl, rfl, h5, h6, h7⟩ := h
      exact ⟨rfl, _, ⟨h1, h2, rfl, trivial, h5, h6, h7⟩, hk _⟩
  | readRam => exact h.elim
  | writeRam => exact h.elim
  | choose p =>
    obtain ⟨ch, h1, rfl, rfl, h4, h5, h6, h7⟩ := h
    exact ⟨rfl, _, ⟨ch, h1, rfl, rfl, h4, h5, h6, h7⟩, hk _⟩
  | _ =>
    obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := h
    exact ⟨rfl, _, ⟨h1, rfl, rfl, h4, h5, h6, h7⟩, hk _⟩

/-- ONE HART STEP, paired: the annotations are carried UNCHANGED to the second run. -/
theorem tparStep (T : List Nat) (cpu : CPU) (m1 m2 : SailM Unit) (rs1 rs2 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (l : Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m1' : SailM Unit)
    (ors1 : Option RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (d' : Efab)
    (oib : Option Ibch) (obar : Option barrier_kind) :
    pstepHw cpu m1 rs1 fn ib d l rds ws ann m1' ors1 fn' d' oib obar →
    tpar T m1 m2 →
    rdsOk (fun n => n ∉ T) rds →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    ∃ (m2' : SailM Unit) (ors2 : Option RegFile),
      pstepHw cpu m2 rs2 fn ib d l rds ws ann m2' ors2 fn' d' oib obar ∧
      tpar T m1' m2' ∧
      dregAgree (fun n => n ∉ T) (ors1.getD rs1) (ors2.getD rs2) := by
  intro hhw htp hrds hag
  rcases hhw with ⟨rfl, ⟨hst, hd⟩, rfl, rfl, rfl⟩ |
    ⟨pr, pw, sr, sw, rfl, ⟨hst, hd⟩, rfl, rfl, rfl⟩ | ⟨hp, rfl, rfl, rfl⟩
  · -- THE MONAD NODE
    cases htp with
    | tpConv =>
      -- RE-CONVERGED: `WeakEvProv`'s own lockstep step serves
      obtain ⟨ors2, hst2, hag2⟩ := pnodeStepDagree _ _ rs1 rs2 ib d.efDev l m1' ors1 fn'
        d'.efDev oib obar hrds hag hst
      exact ⟨m1', ors2, Or.inl ⟨rfl, ⟨hst2, hd⟩, rfl, rfl, rfl⟩, .tpConv _, hag2⟩
    | tpGen o k1 k2 hnw hk =>
      -- THE SAME NON-WRITING OUTCOME
      obtain ⟨rfl, m2', hst2, htp2⟩ := pnodeStepPair T o k1 k2 rs1 rs2 ib d.efDev l m1' ors1 fn'
        d'.efDev oib obar hnw hrds hk hag hst
      exact ⟨m2', none, Or.inl ⟨rfl, ⟨hst2, hd⟩, WeakEvProv2.pnodeRdsCongr o k1 k2,
        WeakEvProv2.pnodeWrsCongr o k1 k2, WeakEvProv2.ibnAnnCongr o k1 k2⟩, htp2, hag⟩
    | tpWrEq r v k1 k2 hk =>
      -- THE SAME VALUE WRITTEN — the `PC`/`minstret` arm
      obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := hst
      exact ⟨k2 PUnit.unit, some (rs2.set r v),
        Or.inl ⟨rfl, ⟨⟨h1, rfl, rfl, h4, h5, h6, h7⟩, hd⟩, rfl, rfl, rfl⟩, hk,
        dregAgreeSet _ rs1 rs2 r v hag⟩
    | tpWr r n v1 v2 k1 k2 hn hnT hk =>
      -- DIFFERENT VALUES INTO A TAINTED CARRIER
      obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := hst
      exact ⟨k2 PUnit.unit, some (rs2.set r v2),
        Or.inl ⟨rfl, ⟨⟨h1, rfl, rfl, h4, h5, h6, h7⟩, hd⟩, rfl, rfl, rfl⟩, hk,
        dregAgreeExcl2 _ rs1 rs2 r v1 v2 ⟨n, hn, fun hno => hno hnT⟩ hag⟩
  · -- THE PARKED FENCE: the node does not move
    obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := hst
    exact ⟨m2, none, Or.inr (Or.inl ⟨pr, pw, sr, sw, rfl, ⟨⟨h1, rfl, rfl, h4, h5, h6, h7⟩, hd⟩,
      rfl, rfl, rfl⟩), htp, hag⟩
  · -- THE PLIC WIRE: the node does not move, and both runs write the same pin
    obtain ⟨mm, b, k, hk, h1, rfl, h3, h4, h5, h6, rfl⟩ := hp
    refine ⟨m2, some (pinSet rs2 mm b),
      Or.inr (Or.inr ⟨⟨mm, b, k, hk, h1, rfl, h3, h4, h5, h6, rfl⟩, rfl, rfl, rfl⟩), htp, ?_⟩
    cases mm
    · exact dregAgreeSet _ rs1 rs2 _ _ hag
    · exact dregAgreeSet _ rs1 rs2 _ _ hag

/-- THE LAW.  Two runs from `tpar`-related nodes stay in step to whatever the first one reaches. -/
theorem tparRun (T : List Nat) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m1 : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m1' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab)
    (m2 : SailM Unit) (rs2 : RegFile) :
    phrun cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' →
    tpar T m1 m2 →
    rdsOk (fun n => n ∉ T) rds →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    ∃ (m2' : SailM Unit) (rs2' : RegFile),
      phrun cpu ls rds ws ann m2 rs2 fn ib d m2' rs2' fn' ib' d' ∧
      tpar T m1' m2' ∧ dregAgree (fun n => n ∉ T) rs1' rs2' := by
  intro hrun
  induction hrun generalizing m2 rs2 with
  | nil m rs fn ib d =>
    intro htp _ hag
    exact ⟨m2, rs2, phrun.nil _ _ _ _ _, htp, hag⟩
  | @more l ls rds rds' ws ws' ann ann' m rs fn ib d ma ors fn1 oib obar d1 mb rsb fn2 ib2 d2
      hstep _ ih =>
    intro htp hrds hag
    obtain ⟨hrds1, hrds2⟩ := rdsOkApp _ rds rds' hrds
    obtain ⟨mc, orsc, hstepc, htp1, hagc⟩ :=
      tparStep T cpu m m2 rs rs2 fn ib d l rds ws ann ma ors fn1 d1 oib obar hstep htp hrds1 hag
    obtain ⟨mc', rsc', hrunc, htp', hag'⟩ := ih mc (orsc.getD rs2) htp1 hrds2 hagc
    exact ⟨mc', rsc', phrun.more hstepc hrunc, htp', hag'⟩

/-- … at `WeakEvProv.instrDagree`'s hypothesis shape. -/
theorem tparInstr (T : List Nat) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m1 : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m1' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab)
    (m2 : SailM Unit) (rs2 : RegFile) :
    phrun cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' →
    tpar T m1 m2 →
    LInstr ∉ ls → LFence false false false false ∉ ls →
    (∀ n, n ∈ ib'.ibRds → n ∉ T) →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    ∃ (m2' : SailM Unit) (rs2' : RegFile),
      phrun cpu ls rds ws ann m2 rs2 fn ib d m2' rs2' fn' ib' d' ∧
      tpar T m1' m2' ∧ dregAgree (fun n => n ∉ T) rs1' rs2' := by
  intro hrun htp hni hnf hib hag
  have hann := phrunNoInstr cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' hrun hni hnf
  have hcov := phrunIbRds cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' hrun hann
  refine tparRun T cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' m2 rs2 hrun htp ?_ hag
  intro n hn
  apply hib
  rw [hcov]
  exact List.mem_append_right _ hn

/-- THE RE-CONVERGENCE, as a corollary: if the first run stops at the boundary, so does the
second. -/
theorem tparReconverge (T : List Nat) (cpu : CPU) (ls : List Wlabel) (rds : List Nat)
    (ws : List Register) (ann : Bool) (m1 : SailM Unit) (rs1 : RegFile) (ib : Ibch) (d : Efab)
    (rs1' : RegFile) (ib' : Ibch) (m2 : SailM Unit) (rs2 : RegFile) :
    phrun cpu ls rds ws ann m1 rs1 none ib d (.pure ()) rs1' none ib' d →
    tpar T m1 m2 →
    rdsOk (fun n => n ∉ T) rds →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    ∃ rs2' : RegFile,
      phrun cpu ls rds ws ann m2 rs2 none ib d (.pure ()) rs2' none ib' d ∧
      dregAgree (fun n => n ∉ T) rs1' rs2' := by
  intro hrun htp hrds hag
  obtain ⟨m2', rs2', hrunb, htp', hag'⟩ :=
    tparRun T cpu ls rds ws ann m1 rs1 none ib d (.pure ()) rs1' none ib' d m2 rs2 hrun htp hrds hag
  rw [tparBoundary T () m2' htp'] at hrunb
  exact ⟨rs2', hrunb, hag'⟩

/-! ## 4. THE WITNESS STEP, AND THE TAINT SET'S ONE GROWTH -/

theorem tparOfWitness (T : List Nat) (r : Register) (n : Nat) (v1 v2 : RegisterType r)
    (k : PUnit → SailM Unit) :
    eregNum r = some n → n ∈ T →
    tpar T (.impure (.ok (.regWrite r v1)) k) (.impure (.ok (.regWrite r v2)) k) :=
  fun hn hnT => .tpWr r n v1 v2 k k hn hnT (.tpConv _)

/-- … and the taint set's one growth, in `WeakEvProv.taintClosureLoad`'s form. -/
theorem tparRunLoad (T : List Nat) (rd : Nat) (cpu : CPU) (ls : List Wlabel)
    (rds : List Nat) (ws : List Register) (ann : Bool) (m1 : SailM Unit) (rs1 : RegFile)
    (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (d : Efab) (m1' : SailM Unit)
    (rs1' : RegFile) (fn' : Option (Bool × Bool × Bool × Bool)) (ib' : Ibch) (d' : Efab)
    (m2 : SailM Unit) (rs2 : RegFile) :
    phrun cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' →
    tpar (rd :: T) m1 m2 →
    rdsOk (fun n => n ∉ rd :: T) rds →
    dregAgree (fun n => n ∉ T) rs1 rs2 →
    ∃ (m2' : SailM Unit) (rs2' : RegFile),
      phrun cpu ls rds ws ann m2 rs2 fn ib d m2' rs2' fn' ib' d' ∧
      tpar (rd :: T) m1' m2' ∧ dregAgree (fun n => n ∉ rd :: T) rs1' rs2' := by
  intro hrun htp hrds hag
  refine tparRun _ cpu ls rds ws ann m1 rs1 fn ib d m1' rs1' fn' ib' d' m2 rs2 hrun htp hrds ?_
  exact dregAgreeMono _ _ rs1 rs2 (fun n hn hin => hn (List.mem_cons_of_mem _ hin)) hag

/-! ### 4.1 NON-VACUITY OF THE LAW ITSELF -/

/-- A write of the SAME value into the NON-carrier `PC`, then of `v` into the carrier `x14`. -/
def twM (v : RegisterType .x14) : SailM Unit :=
  .impure (.ok (.regWrite .PC (BitVec.ofNat 64 4)))
    (fun _ => .impure (.ok (.regWrite .x14 v)) (fun _ => .pure ()))

theorem twPcNotCarrier : eregNum .PC = none := by decide +kernel

theorem twX14Carrier : eregNum .x14 = some 14 := by decide +kernel

theorem twTpar (v1 v2 : RegisterType .x14) : tpar [14] (twM v1) (twM v2) :=
  .tpWrEq _ _ _ _ (.tpWr _ 14 v1 v2 _ _ twX14Carrier (List.mem_singleton_self _) (.tpConv _))

/-- The two nodes are NOT equal when the values differ, so `tpConv` alone could not serve. -/
theorem twNodesDiffer (rs : RegFile) (v1 v2 : RegisterType .x14) : twM v1 = twM v2 → v1 = v2 := by
  intro heq
  have hpr : ∀ v : RegisterType .x14, (mrwSet (mrwSucc (twM v)) rs) .x14 = v := by
    intro v
    simp only [twM, mrwSucc, mrwSet, RegFile.set_same]
  rw [← hpr v1, ← hpr v2, heq]

/-- `tpGen` inhabited too, at a genuine `regRead` whose two continuations are different terms. -/
def tgM (g : RegisterType .x13 → RegisterType .x14) : SailM Unit :=
  .impure (.ok (.regRead .x13)) (fun u => twM (g u))

theorem tgTpar (g1 g2 : RegisterType .x13 → RegisterType .x14) : tpar [14] (tgM g1) (tgM g2) :=
  .tpGen _ _ _ rfl (fun u => twTpar (g1 u) (g2 u))

/-- … and a RUN of it: reading the carrier `x13`, writing the NON-carrier `PC` and the carrier
`x14`, then the boundary. -/
theorem tgRun (cpu : CPU) (rs : RegFile) (d : Efab) (g : RegisterType .x13 → RegisterType .x14) :
    ∃ (ls : List Wlabel) (rds : List Nat) (ws : List Register) (ann : Bool) (rs' : RegFile)
      (ib' : Ibch),
      phrun cpu ls rds ws ann (tgM g) rs none ibNone d (.pure ()) rs' none ib' d ∧
      rds = [13] ∧ ws = [(.PC : Register), (.x14 : Register)] ∧ LInstr ∉ ls := by
  refine ⟨_, _, _, _, _, _,
    phrun.more (Or.inl ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl⟩)
      (phrun.more (Or.inl ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl⟩)
        (phrun.more (Or.inl ⟨rfl, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, rfl, rfl, rfl⟩)
          (phrun.nil _ _ _ _ _))), rfl, rfl, ?_⟩
  intro hin
  rcases List.mem_cons.1 hin with h | h
  · cases h
  · rcases List.mem_cons.1 h with h | h
    · exact erwLabelNeInstr _ h.symm
    · rcases List.mem_cons.1 h with h | h
      · exact erwLabelNeInstr _ h.symm
      · cases h

/-- THE LAW AT THAT PAIR, end to end. -/
theorem tgNonvacuous (cpu : CPU) (rs1 rs2 : RegFile) (d : Efab)
    (g1 g2 : RegisterType .x13 → RegisterType .x14) :
    dregAgree (fun n => n ∉ [14]) rs1 rs2 →
    ∃ (ls : List Wlabel) (ann : Bool) (rs1' rs2' : RegFile) (ib' : Ibch),
      LInstr ∉ ls ∧
      phrun cpu ls [13] [(.PC : Register), (.x14 : Register)] ann (tgM g1) rs1 none ibNone d
        (.pure ()) rs1' none ib' d ∧
      phrun cpu ls [13] [(.PC : Register), (.x14 : Register)] ann (tgM g2) rs2 none ibNone d
        (.pure ()) rs2' none ib' d ∧
      dregAgree (fun n => n ∉ [14]) rs1' rs2' := by
  intro hag
  obtain ⟨ls, rds, ws, ann, rs1', ib', hrun1, rfl, rfl, hni⟩ := tgRun cpu rs1 d g1
  obtain ⟨rs2', hrun2, hag2⟩ :=
    tparReconverge [14] cpu ls [13] [.PC, .x14] ann (tgM g1) rs1 ibNone d rs1' ib' (tgM g2) rs2
      hrun1 (tgTpar g1 g2) (by intro n hn; simp at hn; subst hn; decide) hag
  exact ⟨ls, ann, rs1', rs2', ib', hni, hrun1, hrun2, hag2⟩

/-! ## 5. THE REAL TAIL -/

noncomputable def laSt (w : BitVec 32) : aht := ahRead w.toNat laX2
noncomputable def laTl (w : BitVec 32) : SailM Unit := ahM (laSt w)
noncomputable def laEnd (w : BitVec 32) : aht := admIter false 9 (laSt w)

/-- (i) THE TAIL'S FIRST NODE IS THE DESTINATION WRITE, at every answer. -/
theorem laHeadReg (w : BitVec 32) : mrwReg (laTl w) = some .x15 := by
  weak_adm_krfl

theorem laRdCarrier : eregNum .x15 = some 15 := by decide +kernel

open Lean Elab Tactic Meta in
/-- (Lean-only, deviation 5) Close `lhs = rhs` when the KERNEL's weak head normal forms of the two
sides are the SAME term `W`: two auxiliary theorems `lhs = W`, `rhs = W` (each a kernel `Eq.refl`
over the local context), composed. -/
elab "weak_ev_prov2_kwhnf" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := tgt.eq? | throwError "weak_ev_prov2_kwhnf: the goal is not an equation"
    let env ← getEnv
    let lctx ← getLCtx
    let wl ← ofExceptKernelException (Kernel.whnf env lctx lhs)
    let wr ← ofExceptKernelException (Kernel.whnf env lctx rhs)
    unless wl == wr do
      throwError "weak_ev_prov2_kwhnf: the kernel whnfs differ"
    let e1 ← mkAuxTheorem (← mkEq lhs wl) (← mkEqRefl lhs)
    let e2 ← mkAuxTheorem (← mkEq rhs wl) (← mkEqRefl rhs)
    g.assign (← mkEqTrans e1 (← mkEqSymm e2))
    replaceMainGoal []

/-- (ii) THE ANSWER REACHES THE TAIL ONLY THROUGH THAT WRITE'S VALUE: the continuation is the
SAME TERM at two arbitrary answers (both sides' kernel whnf is one term). -/
theorem laHeadSucc (w1 w2 : BitVec 32) : mrwSucc (laTl w1) = mrwSucc (laTl w2) := by
  weak_ev_prov2_kwhnf

/-- (Lean-only) the inversion of a register-write node. -/
theorem WeakEvProv2.mrwRegInv (m : SailM Unit) (r : Register) :
    mrwReg m = some r →
    ∃ (v : RegisterType r) (k : PUnit → SailM Unit),
      m = .impure (.ok (.regWrite r v)) k ∧ mrwSucc m = k PUnit.unit := by
  intro h
  rcases m with _ | ⟨_ | o, k⟩
  · simp [mrwReg] at h
  · simp [mrwReg] at h
  · cases o with
    | regWrite r' v =>
      simp only [mrwReg, Option.some.injEq] at h
      subst h
      exact ⟨v, k, rfl, rfl⟩
    | _ => simp [mrwReg] at h

/-- THE RECONSTRUCTION: `tparOfWitness` at the two computed projections. -/
theorem tparOfRw (T : List Nat) (m1 m2 : SailM Unit) (r : Register) (n : Nat) :
    mrwReg m1 = some r → mrwReg m2 = some r →
    eregNum r = some n → n ∈ T →
    mrwSucc m1 = mrwSucc m2 →
    tpar T m1 m2 := by
  intro h1 h2 hn hnT hs
  obtain ⟨v1, k1, rfl, hs1⟩ := WeakEvProv2.mrwRegInv m1 r h1
  obtain ⟨v2, k2, rfl, hs2⟩ := WeakEvProv2.mrwRegInv m2 r h2
  refine .tpWr r n v1 v2 k1 k2 hn hnT ?_
  rw [← hs1, ← hs2, hs]
  exact .tpConv _

/-- … AND THE PAIRING ITSELF, at the real node. -/
theorem laTpar (w1 w2 : BitVec 32) : tpar [15] (laTl w1) (laTl w2) :=
  tparOfRw _ _ _ _ _ (laHeadReg w1) (laHeadReg w2) laRdCarrier (List.mem_singleton_self _)
    (laHeadSucc w1 w2)

/-- (iii) THE TAIL'S SHAPE, computed. -/
theorem laEndRet (w : BitVec 32) : ahM (laEnd w) = .pure () := by
  weak_adm_krfl

theorem laLsLen (w : BitVec 32) : (admLbls false 9 (laSt w)).length = 9 := by
  weak_adm_krfl

theorem laLsVal (w : BitVec 32) :
    admLbls false 9 (laSt w) =
      [LRegW 15 [.DLdRes, .DReg 14, .DReg 39, .DReg 45, .DReg 44],
       LSilent, LSilent, LSilent, LSilent, LSilent, LSilent, LSilent, LSilent] := by
  weak_adm_krfl

theorem laLsNoInstr (w : BitVec 32) : LInstr ∉ admLbls false 9 (laSt w) := by
  rw [laLsVal]
  simp

/-- Q7 (Lean-only): nor the sfence.vma marker. -/
theorem WeakEvProv2.laLsNoMark (w : BitVec 32) :
    LFence false false false false ∉ admLbls false 9 (laSt w) := by
  rw [laLsVal]
  simp

theorem laEndIbrds (w : BitVec 32) : (ahIb (laEnd w)).ibRds = (ahIb laX2).ibRds := by
  weak_adm_krfl

theorem laX2NoRd : decide (15 ∈ (ahIb laX2).ibRds) = false := by decide +kernel

theorem laEndUntainted (w : BitVec 32) : ∀ n, n ∈ (ahIb (laEnd w)).ibRds → n ∉ [15] := by
  intro n hn hin
  rw [List.mem_singleton] at hin
  subst hin
  have h15 : 15 ∉ (ahIb laX2).ibRds := by
    intro h
    have h' := laX2NoRd
    rw [decide_eq_true h] at h'
    cases h'
  rw [laEndIbrds w] at hn
  exact h15 hn

/-- (iv) WHY THE UNPAIRED LAW CANNOT DO IT. -/
theorem laTailWritesPc (w : BitVec 32) :
    pnodeWrs (ahM (admIter false 4 (laSt w))) = [(.PC : Register)] := by
  weak_adm_krfl

theorem laTailWritesMinstret (w : BitVec 32) :
    pnodeWrs (ahM (admIter false 8 (laSt w))) = [(.minstret : Register)] := by
  weak_adm_krfl

theorem laPcNotCarrier : eregNum .PC = none := by decide +kernel

theorem laMinstretNotCarrier : eregNum .minstret = none := by decide +kernel

theorem laTailTaintClosureFails (T : List Nat) (w : BitVec 32) :
    ¬ (∀ r, r ∈ pnodeWrs (ahM (admIter false 4 (laSt w))) →
        ∃ n, eregNum r = some n ∧ n ∈ T) ∧
    ¬ (∀ r, r ∈ pnodeWrs (ahM (admIter false 8 (laSt w))) →
        ∃ n, eregNum r = some n ∧ n ∈ T) := by
  constructor
  · intro hall
    obtain ⟨n, hn, _⟩ := hall .PC (by rw [laTailWritesPc]; exact List.mem_singleton_self _)
    rw [laPcNotCarrier] at hn
    cases hn
  · intro hall
    obtain ⟨n, hn, _⟩ :=
      hall .minstret (by rw [laTailWritesMinstret]; exact List.mem_singleton_self _)
    rw [laMinstretNotCarrier] at hn
    cases hn

/-- (v) THE RUN, from `WeakRvwmoAdm`'s once-proven bridge. -/
theorem laPhrun (cpu : CPU) (d : Efab) (w : BitVec 32) :
    ∃ (rds : List Nat) (ws : List Register) (ann : Bool),
      phrun cpu (admLbls false 9 (laSt w)) rds ws ann (laTl w) (ahRs laX2) none (ahIb laX2) d
        (.pure ()) (ahRs (laEnd w)) none (ahIb (laEnd w)) d := by
  obtain ⟨rds, ws, ann, hrun⟩ :=
    pevrunPhrun (admLbls false 9 (laSt w)) (ahP cpu (laSt w)) d (ahP cpu (laEnd w)) d
      (pevrunOfIter false 9 cpu d (laSt w)) cpu (laTl w) (ahRs laX2) none (ahIb laX2)
      (ahM (laEnd w)) (ahRs (laEnd w)) none (ahIb (laEnd w)) rfl rfl
  rw [laEndRet w] at hrun
  exact ⟨rds, ws, ann, hrun⟩

/-- THE INSTANCE.  Two runs of the REAL nine-node tail of `lw a5,0(a4)` at two ARBITRARY loaded
words: the same labels and annotations, both reaching the boundary, register files agreeing off
`[15]` -- the `PC` and `minstret` writes admitted because EQUAL. -/
theorem laTailPar (cpu : CPU) (d : Efab) (w1 w2 : BitVec 32) :
    ∃ (ls : List Wlabel) (rds : List Nat) (ws : List Register) (ann : Bool) (rs2' : RegFile),
      ls.length = 9 ∧ LInstr ∉ ls ∧
      phrun cpu ls rds ws ann (laTl w1) (ahRs laX2) none (ahIb laX2) d
        (.pure ()) (ahRs (laEnd w1)) none (ahIb (laEnd w1)) d ∧
      phrun cpu ls rds ws ann (laTl w2) (ahRs laX2) none (ahIb laX2) d
        (.pure ()) rs2' none (ahIb (laEnd w1)) d ∧
      dregAgree (fun n => n ∉ [15]) (ahRs (laEnd w1)) rs2' := by
  obtain ⟨rds, ws, ann, hrun1⟩ := laPhrun cpu d w1
  obtain ⟨m2', rs2', hrun2, htp2, hag2⟩ :=
    tparInstr [15] cpu (admLbls false 9 (laSt w1)) rds ws ann (laTl w1) (ahRs laX2) none
      (ahIb laX2) d (.pure ()) (ahRs (laEnd w1)) none (ahIb (laEnd w1)) d (laTl w2) (ahRs laX2)
      hrun1 (laTpar w1 w2) (laLsNoInstr w1) (WeakEvProv2.laLsNoMark w1) (laEndUntainted w1)
      (dregAgreeRefl _ _)
  rw [tparBoundary [15] () m2' htp2] at hrun2
  exact ⟨admLbls false 9 (laSt w1), rds, ws, ann, rs2', laLsLen w1, laLsNoInstr w1, hrun1, hrun2,
    hag2⟩

end Weak
