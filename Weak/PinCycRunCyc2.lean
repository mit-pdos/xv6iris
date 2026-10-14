/-
Weak: **W9a (B) B5 cycRun — the Sail cycle walk, part 2: the step's arms, the epilogue, the clock
tick** ([OWN.85] Q-B5-CYCLE = C1; report `PROGRESS-cycRun.md`).  Lean-only.

`ucFinish st = ucArm st >>= fun _ => ucEpilogue (ucRetired st)` (`MachCSL/UCycleDefs.lean`),
then `if tick then tick_clock () else pure ()` (`MachCSL/Lang.lean:242`):
* a RETIRED instruction (`Retire_Success`): the `hart_state` assertion, `tick_pc` (`PC :=
  nextPC`, `PcAccess.lean:218`), the `minstret` bump, the clock tick — the mirror's `PC` becomes its
  `nextPC`, the protected rest kept, B1's slots kept (`PC`/`minstret`/`mcycle` have no dependency
  number; `mtime`/`mip` are no destination of a walk role, `dfNwRole`);
* an execute TRAP (`Trap`), a fetch failure (`Step_Fetch_Failure`) and an interrupt
  (`Step_Pending_Interrupt`): the trap handler's first cause write (`cyTrapHandler`), with the
  trap's interrupt bit.

Every helper is `Weak.PinCycRun.*`.
-/
import Weak.PinCycRunCyc

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open KernelPinsDef

namespace PinCycRun
open SailCycleOrderK PinDataflow
open PinCycRunFp (pfB pfT pfProt pfRegOk pfW)

/-! ## 1. Footprints of the tail pieces -/

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfTickClock : pfT (tick_clock ()) := by
  pf_walk

set_option maxHeartbeats 40000000 in
theorem PinCycRun.nwTickClock : nwT (tick_clock ()) := by
  nw_walk

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfExceptionDelegatee (e : ExceptionType) (p : Privilege) :
    pfT (exception_delegatee e p) := by
  pf_walk

/-! ## 2. The dataflow of an unnumbered write -/

/-- A write to a register with no dependency number moves no slot. -/
theorem PinCycRun.dfWrUnnum (d : DfSt) (r : Register) (h : eregNum r = none) (hn : r ≠ .nextPC) :
    (dfWr d r).n = d.n ∧ (dfWr d r).ok = d.ok ∧ (dfWr d r).ro = d.ro := by
  have hl : ∀ rd srcs, erwLabel (erwOf d.ro d.rds r) ≠ Wlabel.LRegW rd srcs := by
    intro rd srcs e
    unfold erwOf at e
    rw [if_neg hn] at e
    have hd : ∀ o, erwDest d.rds r o = .ERWnone := by
      intro o
      cases o with
      | none => rfl
      | some p => obtain ⟨rd', srcs'⟩ := p; simp only [erwDest, h]
    rw [hd, hd] at e
    cases e
  have := dfLabNeutral d.ro d.n d.ok _ hl
  simp only [dfWr, this, and_self]

section tail
variable (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
  (T : CySt → (r : Register) → RegisterType r → Prop)

/-- The tail's state relation: `PC` from `nextPC`, the protected rest kept, the log, the flag, the
role, the slots kept. -/
def tailRel (st st' : CySt) : Prop :=
  st'.rv .PC = st.rv .nextPC ∧ (∀ r, pfProt r = true → r ≠ .PC → st'.rv r = st.rv r) ∧
  st'.fe = st.fe ∧ st'.an = st.an ∧ st'.d.ro = st.d.ro ∧ st'.d.n = st.d.n ∧ st'.d.ok = st.d.ok ∧
  RbootAll st'.rv

/-- **The clock tick** (header): frame, B1's slots kept at a `dfNwRole` role. -/
theorem cyTick (Q : Unit → CySt → Prop) (tick : Bool) (st : CySt)
    (hrb : RbootAll st.rv) (hnw : dfNwRole st.d.ro)
    (hk : ∀ st', cyFrame st st' → st'.d.ro = st.d.ro → st'.d.n = st.d.n → st'.d.ok = st.d.ok →
      Q () st') :
    cyB A Aa cyS T Q (if tick then tick_clock () else pure ()) st := by
  cases tick
  · exact hk st (cyFrameRefl st hrb) rfl rfl rfl
  · simp only [if_true]
    refine cyOfPfDf A Aa cyS T ?_ (fun _ => True) (fun _ d' => True ∧ dfExt st.d d') _ _ st
      pfTickClock (dfOfNw false _ _ st.d hnw PinCycRun.nwTickClock) hrb ?_
    · intro r hr
      simp only [cyS, Bool.or_eq_true, decide_eq_true_eq] at hr
      rcases hr with rfl | rfl <;> rfl
    · intro u st' _ hf hd
      cases u
      obtain ⟨-, e1, e2, e3, -⟩ := hd
      exact hk st' hf e1 e2 e3

/-- The tail's PRE-WRITE relation: the protected mirror, the log, the flag, the role, the slots
kept. -/
def pwRel (st st' : CySt) : Prop :=
  (∀ r, pfProt r = true → st'.rv r = st.rv r) ∧ st'.fe = st.fe ∧ st'.an = st.an ∧
  st'.d.ro = st.d.ro ∧ st'.d.n = st.d.n ∧ st'.d.ok = st.d.ok ∧ RbootAll st'.rv

theorem PinCycRun.pwRefl (st : CySt) (h : RbootAll st.rv) : pwRel st st :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, h⟩

theorem PinCycRun.pwRd (st X : CySt) (r : Register) (h : pwRel st X) : pwRel st (cyRd X r) := h

theorem PinCycRun.pwToTail (st X : CySt) (h : pwRel st X) :
    tailRel st (cyWr X .PC (st.rv .nextPC)) := by
  have hW := PinCycRun.dfWrUnnum X.d .PC rfl (by decide)
  refine ⟨RegFile.set_same X.rv .PC _, fun r hr hne => ?_, h.2.1, h.2.2.1, hW.2.2.trans h.2.2.2.1,
    hW.1.trans h.2.2.2.2.1, hW.2.1.trans h.2.2.2.2.2.1, rbootAllSet _ _ _ h.2.2.2.2.2.2 trivial⟩
  show (X.rv.set .PC _) r = _
  rw [RegFile.set_other _ _ _ _ hne]; exact h.1 r hr

theorem PinCycRun.tailRd (st X : CySt) (r : Register) (h : tailRel st X) :
    tailRel st (cyRd X r) := h

theorem PinCycRun.tailWr (st X : CySt) (r : Register) (v : RegisterType r) (h : tailRel st X)
    (hn : eregNum r = none) (hnp : r ≠ .nextPC) (hp : pfProt r = false) (hv : Rboot r v) :
    tailRel st (cyWr X r v) := by
  have hW := PinCycRun.dfWrUnnum X.d r hn hnp
  have hne : ∀ r', pfProt r' = true → r' ≠ r := by rintro r' h' rfl; rw [hp] at h'; cases h'
  refine ⟨?_, fun r' hr hne' => ?_, h.2.2.1, h.2.2.2.1, hW.2.2.trans h.2.2.2.2.1,
    hW.1.trans h.2.2.2.2.2.1, hW.2.1.trans h.2.2.2.2.2.2.1,
    rbootAllSet _ _ _ h.2.2.2.2.2.2.2 hv⟩
  · show (X.rv.set r v) .PC = _
    rw [RegFile.set_other _ _ _ _ (hne .PC (by decide))]; exact h.1
  · show (X.rv.set r v) r' = _
    rw [RegFile.set_other _ _ _ _ (hne r' hr)]; exact h.2.1 r' hr hne'

theorem PinCycRun.tailFrame (st X Y : CySt) (h : tailRel st X) (hf : cyFrame X Y)
    (h1 : Y.d.ro = X.d.ro) (h2 : Y.d.n = X.d.n) (h3 : Y.d.ok = X.d.ok) : tailRel st Y := by
  refine ⟨?_, fun r hr hne => ?_, hf.2.2.1.trans h.2.2.1, hf.2.2.2.trans h.2.2.2.1,
    h1.trans h.2.2.2.2.1, h2.trans h.2.2.2.2.2.1, h3.trans h.2.2.2.2.2.2.1, hf.2.1⟩
  · rw [hf.1 .PC (by decide)]; exact h.1
  · rw [hf.1 r hr]; exact h.2.1 r hr hne

/-- **A RETIRED instruction's tail** (header): `ucFinish (Step_Execute (Retire_Success, ib))`,
then the optional clock tick. -/
theorem cyFinishRetire (Q : Unit → CySt → Prop) (ib : BitVec 32) (tick : Bool) (st : CySt)
    (hhs : st.rv .hart_state = .HART_ACTIVE ()) (hrb : RbootAll st.rv) (hnw : dfNwRole st.d.ro)
    (hQ : ∀ st', tailRel st st' → Q () st') :
    cyB A Aa cyS T Q (ucFinish (.Step_Execute (RETIRE_SUCCESS, ib)) >>=
      fun _ => if tick then tick_clock () else pure ()) st := by
  simp only [ucFinish, ucArm, ucRetired, ucEpilogue, RETIRE_SUCCESS, bind_assoc, tick_pc,
    get_config_rvfi, Bool.false_eq_true, ↓reduceIte, pure_bind]
  have hp0 := PinCycRun.pwRefl st hrb
  refine cyReadBind _ _ _ _ (fun v1 hv1 => ?_)
  have e1 : v1 = .HART_ACTIVE () := by rw [PinCycRun.rdMirror _ _ _ (by decide) hv1, hhs]
  subst e1
  refine cyAssertBind A Aa T _ _ _ _ _ (fun _ => ?_)
  have hp1 := PinCycRun.pwRd st _ .hart_state hp0
  refine cyReadBind _ _ _ _ (fun v2 hv2 => ?_)
  have e2 : v2 = .HART_ACTIVE () := by
    rw [PinCycRun.rdMirror _ _ _ (by decide) hv2, hp1.1 .hart_state (by decide)]; exact hhs
  subst e2
  have hp2 := PinCycRun.pwRd st _ .hart_state hp1
  try simp only [bind_assoc]
  refine cyReadBind _ _ _ _ (fun npc hnpc => ?_)
  have e3 : npc = st.rv .nextPC := by
    rw [PinCycRun.rdMirror _ _ _ (by decide) hnpc]; exact hp2.1 .nextPC (by decide)
  subst e3
  have hp3 := PinCycRun.pwRd st _ .nextPC hp2
  refine cyWriteBind _ _ _ _ _ (by decide) trivial ?_
  have ht4 := PinCycRun.pwToTail st _ hp3
  refine cyReadBind _ _ _ _ (fun v4 _ => ?_)
  have ht5 := PinCycRun.tailRd st _ .PC ht4
  try simp only [pure_bind]
  refine cyReadBind _ _ _ _ (fun mi _ => ?_)
  have ht6 := PinCycRun.tailRd st _ .minstret_increment ht5
  have hnw6 : ∀ X, tailRel st X → dfNwRole X.d.ro := fun X h => by rw [h.2.2.2.2.1]; exact hnw
  cases mi
  · try simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
    exact cyTick A Aa T Q tick _ ht6.2.2.2.2.2.2.2 (hnw6 _ ht6)
      (fun st' hf h1 h2 h3 => hQ st' (PinCycRun.tailFrame st _ st' ht6 hf h1 h2 h3))
  · try simp only [if_true, bind_assoc]
    refine cyReadBind _ _ _ _ (fun m5 _ => ?_)
    have ht7 := PinCycRun.tailRd st _ .minstret ht6
    refine cyWriteBind _ _ _ _ _ (by decide) trivial ?_
    have ht8 := PinCycRun.tailWr st _ .minstret (BitVec.addInt m5 1) ht7 rfl (by decide) (by decide)
      trivial
    try simp only [pure_bind]
    exact cyTick A Aa T Q tick _ ht8.2.2.2.2.2.2.2 (hnw6 _ ht8)
      (fun st' hf h1 h2 h3 => hQ st' (PinCycRun.tailFrame st _ st' ht8 hf h1 h2 h3))

/-- **The exception handler** (header): the delegation, then the trap handler — the obligation
ends at its first cause write, an EXCEPTION's (bit 63 clear). -/
theorem cyExcHandler {Y : Type} (Q : Y → CySt → Prop) (priv : Privilege) (exc : sync_exception)
    (pc : BitVec 64) (f : BitVec 64 → SailM Y) (st : CySt) (hrb : RbootAll st.rv)
    (hT : ∀ st' (r : Register) (v : RegisterType r), st'.fe = st.fe → st'.an = st.an →
      cyS r = true → causeBit r v = false → T st' r v) :
    cyB A Aa cyS T Q (exception_handler priv exc pc >>= f) st := by
  unfold exception_handler
  simp only [get_config_print_exception, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  refine cyBBind (fun _ st' => cyFrame st st') _ _ _ st ?_ (fun del st1 hf => ?_)
  · refine cyOfPf A Aa cyS T ?_ _ _ _ _ (pfExceptionDelegatee _ _) hrb (fun _ st' _ h => h)
    intro r hr
    simp only [cyS, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with rfl | rfl <;> rfl
  · refine cyTrapHandler A Aa T _ _ _ _ _ _ _ st1 hf.2.1 (fun st' r v h1 h2 h3 h4 => ?_)
    exact hT st' r v (h1.trans hf.2.2.1) (h2.trans hf.2.2.2) h3 h4

/-- **An execute trap's tail** (header). -/
theorem cyFinishTrap (Q : Unit → CySt → Prop) (x : Privilege × sync_exception × BitVec 64)
    (ib : BitVec 32) (tick : Bool) (st : CySt) (hrb : RbootAll st.rv)
    (hT : ∀ st' (r : Register) (v : RegisterType r), st'.fe = st.fe → st'.an = st.an →
      cyS r = true → causeBit r v = false → T st' r v) :
    cyB A Aa cyS T Q (ucFinish (.Step_Execute (.Trap x, ib)) >>=
      fun _ => if tick then tick_clock () else pure ()) st := by
  obtain ⟨priv, exc, pc⟩ := x
  simp only [ucFinish, ucArm, bind_assoc]
  exact cyExcHandler A Aa T _ _ _ _ _ st hrb hT

/-- **A fetch failure's tail** (header). -/
theorem cyFinishFetchFail (Q : Unit → CySt → Prop) (p : virtaddr × ExceptionType) (tick : Bool)
    (st : CySt) (hrb : RbootAll st.rv)
    (hT : ∀ st' (r : Register) (v : RegisterType r), st'.fe = st.fe → st'.an = st.an →
      cyS r = true → causeBit r v = false → T st' r v) :
    cyB A Aa cyS T Q (ucFinish (.Step_Fetch_Failure p) >>=
      fun _ => if tick then tick_clock () else pure ()) st := by
  obtain ⟨va, e⟩ := p
  simp only [ucFinish, ucArm, handle_exception, bind_assoc]
  refine cyReadBind _ _ _ _ (fun v1 _ => ?_)
  refine cyReadBind _ _ _ _ (fun v2 _ => ?_)
  exact cyExcHandler A Aa T _ _ _ _ _ _ hrb (fun st' r v h1 h2 h3 h4 => hT st' r v h1 h2 h3 h4)

/-- **An interrupt's tail** (header): the trap handler's first cause write, an INTERRUPT's. -/
theorem cyFinishIntr (Q : Unit → CySt → Prop) (ip : InterruptType × Privilege) (tick : Bool)
    (st : CySt) (hrb : RbootAll st.rv)
    (hT : ∀ st' (r : Register) (v : RegisterType r), st'.fe = st.fe → st'.an = st.an →
      cyS r = true → causeBit r v = true → T st' r v) :
    cyB A Aa cyS T Q (ucFinish (.Step_Pending_Interrupt ip) >>=
      fun _ => if tick then tick_clock () else pure ()) st := by
  obtain ⟨intr, priv⟩ := ip
  simp only [ucFinish, ucArm, handle_interrupt, get_config_print_instr, Bool.false_eq_true,
    ↓reduceIte, bind_assoc]
  refine cyReadBind _ _ _ _ (fun v1 _ => ?_)
  exact cyTrapHandler A Aa T _ _ _ _ _ _ _ _ hrb (fun st' r v h1 h2 h3 h4 => hT st' r v h1 h2 h3 h4)

end tail

end PinCycRun
end Weak
