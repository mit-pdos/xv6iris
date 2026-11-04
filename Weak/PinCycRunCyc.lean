/-
Weak: **W9a (B) B5 cycRun — the Sail cycle walk, part 1: the instruction-independent stretches**
([OWN.85] Q-B5-CYCLE = C1; report `PROGRESS-cycRun.md`).  Lean-only.

The cycle `riscvStep tick` (`MachCSL/Lang.lean:242`) cut as `MachCSL/UCycleDefs.lean` cuts it:
`ucPrelude` (the `minstret_increment` write, the `hart_state` read), `ucBody` (`run_hart_active`
= `ucDispatch`, then the fetch and `ucAfterFetch`), `ucFinish` (the step's arm and the
`tick_pc` epilogue), the optional `tick_clock`.  Each stretch is walked under the cycle predicate
`PinCycRun.cyB` (`Weak/PinCycRun.lean`) with the kernel instance (`Weak/PinCycRunAsm.lean`):
footprints by the `pfB` lift (`Weak/PinCycRunLift.lean`), the protected registers' reads by the
mirror, the trap handler up to its first cause write by hand.

Every helper is `Weak.PinCycRun.*`.
-/
import Weak.PinCycRunAsm
import Weak.PinCycRunLift
import Weak.PinCycRunMem

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open KernelPinsDef

namespace PinCycRun
open SailCycleOrderK PinDataflow
open PinCycRunFp (pfB pfT pfProt pfRegOk pfW)

/-! ## 1. Node lemmas -/

section nodes
variable {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop} {S : Register → Bool}
  {T : CySt → (r : Register) → RegisterType r → Prop}

theorem cyReadBind {Y : Type} (Q : Y → CySt → Prop) (r : Register) (f : RegisterType r → SailM Y)
    (st : CySt) (h : ∀ v, rdOk st r v → cyB A Aa S T Q (f v) (cyRd st r)) :
    cyB A Aa S T Q (readReg r >>= f) st := h

theorem cyRead (r : Register) (Q : RegisterType r → CySt → Prop) (st : CySt)
    (h : ∀ v, rdOk st r v → Q v (cyRd st r)) : cyB A Aa S T Q (readReg r) st := h

theorem cyWriteBind {Y : Type} (Q : Y → CySt → Prop) (r : Register) (v : RegisterType r)
    (f : PUnit → SailM Y) (st : CySt) (hs : S r = false) (hb : Rboot r v)
    (h : cyB A Aa S T Q (f ()) (cyWr st r v)) : cyB A Aa S T Q (writeReg r v >>= f) st :=
  ⟨fun h' => absurd (hs.symm.trans h') (by decide), fun _ => ⟨hb, fun u => by cases u; exact h⟩⟩

theorem cyWrite (Q : PUnit → CySt → Prop) (r : Register) (v : RegisterType r) (st : CySt)
    (hs : S r = false) (hb : Rboot r v) (h : Q () (cyWr st r v)) :
    cyB A Aa S T Q (writeReg r v) st :=
  ⟨fun h' => absurd (hs.symm.trans h') (by decide), fun _ => ⟨hb, fun u => by cases u; exact h⟩⟩

theorem cyPureBind {X Y : Type} (Q : Y → CySt → Prop) (x : X) (f : X → SailM Y) (st : CySt)
    (h : cyB A Aa S T Q (f x) st) : cyB A Aa S T Q ((pure x : SailM X) >>= f) st := h

/-- A non-wire read is answered by the mirror. -/
theorem PinCycRun.rdMirror (st : CySt) (r : Register) (v : RegisterType r) (hw : wireReg r = false)
    (h : rdOk st r v) : v = st.rv r := h hw

end nodes

/-! ## 2. The pre-announce dataflow: no destination, nothing moves -/

/-- At a role with no destination, a register write moves no slot. -/
theorem PinCycRun.dfWrNoDest (d : DfSt) (r : Register) (h1 : depsRd d.ro = none)
    (h2 : depsRd2 d.ro = none) : (dfWr d r).n = d.n ∧ (dfWr d r).ok = d.ok := by
  have hl : ∀ rd srcs, erwLabel (erwOf d.ro d.rds r) ≠ Wlabel.LRegW rd srcs := by
    intro rd srcs e
    unfold erwOf at e
    split at e
    · cases e
    · rw [h1] at e
      simp only [erwDest, h2] at e
      cases e
  have := dfLabNeutral d.ro d.n d.ok _ hl
  simp only [dfWr, this, and_self]

/-- **The dataflow of a footprint at a role with no destination**: role, slots, flag kept. -/
theorem PinCycRun.dfKeepNoDest {X : Type} (P : X → Prop) :
    ∀ (m : SailM X) (d : DfSt), depsRd d.ro = none → depsRd2 d.ro = none → pfB false P m →
      dfB (fun _ d' => d'.ro = d.ro ∧ d'.n = d.n ∧ d'.ok = d.ok) m d := by
  intro m
  induction m with
  | pure x =>
    intro d _ _ _
    exact (⟨rfl, rfl, rfl⟩ : d.ro = d.ro ∧ d.n = d.n ∧ d.ok = d.ok)
  | impure call k ih =>
    intro d h1 h2 hp
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        intro v hv
        exact dfBMono _ _ (fun _ _ h => h) _ _ (ih v (dfRd d r) h1 h2 (hp v hv))
      case regWrite r v =>
        refine ⟨hp.1.1, fun u => ?_⟩
        obtain ⟨e1, e2⟩ := PinCycRun.dfWrNoDest d r h1 h2
        refine dfBMono _ _ (fun _ d' h => ?_) _ _ (ih u (dfWr d r) h1 h2 (hp.2 u))
        exact ⟨h.1, h.2.1.trans e1, h.2.2.trans e2⟩
      case memRead => exact fun v => ih v d h1 h2 (hp.2 v)
      case instrAnnounce => exact hp.elim
      case barrier => exact fun v => ih v d h1 h2 hp.2
      all_goals exact fun v => ih v d h1 h2 (hp v)

/-- The pre-announce lift: a `pfB` stretch at a destination-free role keeps the frame and the
dataflow state's role, slots and flag. -/
theorem cyLiftPre {X Y : Type} (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (T : CySt → (r : Register) → RegisterType r → Prop) (P : X → Prop) (Q : Y → CySt → Prop)
    (m : SailM X) (f : X → SailM Y) (st : CySt) (hp : pfB false P m) (hrb : RbootAll st.rv)
    (h1 : depsRd st.d.ro = none) (h2 : depsRd2 st.d.ro = none)
    (hk : ∀ x st', P x → cyFrame st st' → st'.d.ro = st.d.ro → st'.d.n = st.d.n →
      st'.d.ok = st.d.ok → cyB A Aa cyS T Q (f x) st') :
    cyB A Aa cyS T Q (m >>= f) st := by
  refine cyBBind (fun x st' => P x ∧ cyFrame st st' ∧ st'.d.ro = st.d.ro ∧ st'.d.n = st.d.n ∧
    st'.d.ok = st.d.ok) Q m f st ?_ (fun x st' h => hk x st' h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  refine cyOfPfDf A Aa cyS T ?_ P _ _ m st hp (PinCycRun.dfKeepNoDest P m st.d h1 h2 hp) hrb
    (fun x st' h1' h2' h3' => ⟨h1', h2', h3'⟩)
  intro r hr
  simp only [cyS, Bool.or_eq_true, decide_eq_true_eq] at hr
  rcases hr with rfl | rfl <;> rfl

/-! ## 3. The prelude -/

set_option maxHeartbeats 4000000 in
@[pf_reg] theorem pfShouldIncMinstret (p : Privilege) : pfT (should_inc_minstret p) := by
  pf_walk

/-- The cycle's PRE-ANNOUNCE invariant relative to the cycle's start `st0`: the protected mirror
kept, `Rboot`, the log and the flag kept, the reset channel. -/
def preInv (st0 st : CySt) : Prop :=
  cyFrame st0 st ∧ st.d.ro = OpRoles.ORnone ∧ st.d.n = 0 ∧ st.d.ok = true

theorem PinCycRun.preInvFrame (st0 st st' : CySt) (h : preInv st0 st) (hf : cyFrame st st')
    (hro : st'.d.ro = st.d.ro) (hn : st'.d.n = st.d.n) (hok : st'.d.ok = st.d.ok) :
    preInv st0 st' :=
  ⟨cyFrameTrans _ _ _ h.1 hf, hro.trans h.2.1, hn.trans h.2.2.1, hok.trans h.2.2.2⟩

theorem PinCycRun.preInvRd (st0 st : CySt) (r : Register) (h : preInv st0 st) :
    preInv st0 (cyRd st r) :=
  PinCycRun.preInvFrame st0 st _ h (cyFrameRefl _ h.1.2.1) rfl rfl rfl

theorem PinCycRun.preInvWr (st0 st : CySt) (r : Register) (v : RegisterType r) (h : preInv st0 st)
    (hp : pfProt r = false) (hv : Rboot r v) : preInv st0 (cyWr st r v) := by
  have hd := PinCycRun.dfWrNoDest st.d r (by rw [h.2.1]; rfl) (by rw [h.2.1]; rfl)
  exact PinCycRun.preInvFrame st0 st _ h (PinCycRun.frameWr st r v h.1.2.1 hp hv) rfl hd.1 hd.2

section pre
variable (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
  (T : CySt → (r : Register) → RegisterType r → Prop)

/-- **The prelude** (header): the `hart_state` it returns is the mirror's. -/
theorem cyPrelude {Y : Type} (Q : Y → CySt → Prop) (f : HartState → SailM Y) (st0 st : CySt)
    (h : preInv st0 st)
    (hk : ∀ st', preInv st0 st' → cyB A Aa cyS T Q (f (st0.rv .hart_state)) st') :
    cyB A Aa cyS T Q (ucPrelude >>= f) st := by
  unfold ucPrelude
  simp only [bind_assoc]
  refine cyReadBind _ _ _ _ (fun v _ => ?_)
  have h1 := PinCycRun.preInvRd st0 st .cur_privilege h
  refine cyLiftPre A Aa T _ _ _ _ _ (pfShouldIncMinstret v) h1.1.2.1
    (by rw [h1.2.1]; rfl) (by rw [h1.2.1]; rfl) (fun b st1 _ hf hro hn hok => ?_)
  have h2 := PinCycRun.preInvFrame st0 _ st1 h1 hf hro hn hok
  refine cyWriteBind _ _ _ _ _ (by decide) trivial ?_
  have h3 := PinCycRun.preInvWr st0 st1 .minstret_increment b h2 (by decide) trivial
  refine cyReadBind _ _ _ _ (fun hs hhs => ?_)
  have e : hs = st0.rv .hart_state := by
    rw [PinCycRun.rdMirror _ _ _ (by decide) hhs]
    exact h3.1.1 .hart_state (by decide)
  rw [e]
  exact hk _ (PinCycRun.preInvRd st0 _ _ h3)

end pre

/-! ## 4. The dispatch; the trap handler up to its first cause write -/

set_option maxHeartbeats 40000000 in
@[pf_reg] theorem pfDispatchInterrupt (p : Privilege) : pfT (dispatchInterrupt p) := by
  pf_walk

set_option maxHeartbeats 4000000 in
@[pf_reg] theorem pfCurrentlyEnabled (e : extension) : pfT (currentlyEnabled e) := by
  cases e <;> pf_walk

section trap
variable (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
  (T : CySt → (r : Register) → RegisterType r → Prop)

/-- **The dispatch** (header): any answer, the pre-announce invariant kept. -/
theorem cyDispatch {Y : Type} (Q : Y → CySt → Prop) (f : Option (InterruptType × Privilege) → SailM Y)
    (st0 st : CySt) (h : preInv st0 st)
    (hk : ∀ o st', preInv st0 st' → cyB A Aa cyS T Q (f o) st') :
    cyB A Aa cyS T Q (ucDispatch >>= f) st := by
  unfold ucDispatch
  simp only [bind_assoc]
  refine cyReadBind _ _ _ _ (fun v _ => ?_)
  have h1 := PinCycRun.preInvRd st0 st .cur_privilege h
  exact cyLiftPre A Aa T _ _ _ _ _ (pfDispatchInterrupt v) h1.1.2.1
    (by rw [h1.2.1]; rfl) (by rw [h1.2.1]; rfl)
    (fun o st1 _ hf hro hn hok => hk o st1 (PinCycRun.preInvFrame st0 _ st1 h1 hf hro hn hok))

/-- A write of a stop register ends the obligation with the stop post. -/
theorem cyStopBind {Y : Type} (Q : Y → CySt → Prop) (r : Register) (v : RegisterType r)
    (f : PUnit → SailM Y) (st : CySt) (hs : cyS r = true) (hT : T st r v) :
    cyB A Aa cyS T Q (writeReg r v >>= f) st :=
  ⟨fun _ => hT, fun h' => absurd (hs.symm.trans h') (by decide)⟩

theorem PinCycRun.causeBitUpd (b : Bool) (v : BitVec 64) :
    (Sail.BitVec.updateSubrange v 63 63 (bool_to_bit b)).getLsbD 63 = b := by
  cases b <;>
    simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', bool_to_bit,
      bool_bit_forwards]

/-- An `assert` whose condition is a footprint's answer: on the failing arm the tree fails. -/
theorem cyAssertBind {Y : Type} (Q : Y → CySt → Prop) (b : Bool) (msg : String)
    (f : Unit → SailM Y) (st : CySt) (h : b = true → cyB A Aa cyS T Q (f ()) st) :
    cyB A Aa cyS T Q (assert b msg >>= f) st := by
  cases b
  · simp only [assert]
    exact trivial
  · simp only [assert]
    exact h rfl

/-- **The trap handler** (header): every path writes the cause register (`mcause` for a
machine-mode trap, `scause` for a supervisor one) with the trap's interrupt bit, or fails, before
it returns — so the obligation ends at that write with the stop post. -/
theorem cyTrapHandler {Y : Type} (Q : Y → CySt → Prop) (del : Privilege) (c : TrapCause)
    (pc : BitVec 64) (info : Option (BitVec 64)) (ext : Option Unit) (f : BitVec 64 → SailM Y)
    (st : CySt) (hrb : RbootAll st.rv)
    (hT : ∀ st' (r : Register) (v : RegisterType r), st'.fe = st.fe → st'.an = st.an →
      cyS r = true → causeBit r v = trapCause_is_interrupt c → T st' r v) :
    cyB A Aa cyS T Q (trap_handler del c pc info ext >>= f) st := by
  unfold trap_handler
  simp only [get_config_print_exception, get_config_print_interrupt, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  -- since 2026-11-04 no Zicfilp: the trap neither banks nor resets `elp`
  have hz : hartSupports extension.Ext_Zicfilp = false := by
    simp [hartSupports]
  rw [if_neg (by simp [hz])]
  try simp only [pure_bind]
  cases del with
  | Machine =>
    simp only [bind_assoc]
    refine cyReadBind _ _ _ _ (fun v3 _ => ?_)
    refine cyStopBind A Aa T _ _ _ _ _ (by decide) ?_
    refine hT _ _ _ rfl rfl (by decide) ?_
    exact PinCycRun.causeBitUpd _ _
  | Supervisor =>
    simp only [bind_assoc]
    refine cyBBind (fun b st' => st'.fe = st.fe ∧ st'.an = st.an) _ _ _ _ ?_
      (fun b st1 hfe => ?_)
    · refine cyOfPf A Aa cyS T ?_ _ _ _ _ (pfCurrentlyEnabled _) ?_
        (fun _ st' _ hf => ⟨hf.2.2.1, hf.2.2.2⟩)
      · intro r hr
        simp only [cyS, Bool.or_eq_true, decide_eq_true_eq] at hr
        rcases hr with rfl | rfl <;> rfl
      · exact hrb
    · refine cyAssertBind A Aa T _ _ _ _ _ (fun _ => ?_)
      refine cyReadBind _ _ _ _ (fun v3 _ => ?_)
      refine cyStopBind A Aa T _ _ _ _ _ (by decide) ?_
      refine hT _ _ _ hfe.1 hfe.2 (by decide) ?_
      exact PinCycRun.causeBitUpd _ _
  | User => exact trivial
  | VirtualUser => exact trivial
  | VirtualSupervisor => exact trivial

end trap

/-! ## 5. The decoder: `runRead`'s value, transported to the mirror -/

theorem PinCycRun.mapSome {α β : Type} (o : Option α) (f : α → β) (y : β) (h : o.map f = some y) :
    ∃ x, o = some x ∧ f x = y := by
  cases o with
  | none => cases h
  | some x => exact ⟨x, rfl, Option.some.inj h⟩

/-- **The decoder's walk** (header): a tree whose `runRead` walk at a reference map `dref`
returns `x`, and which is a footprint (so has no announce), satisfies `cyB` with post `x` at any
state whose mirror agrees with `dref` (off the wires). -/
theorem cyOfRunRead {X : Type} (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)
    (S : Register → Bool) (T : CySt → (r : Register) → RegisterType r → Prop)
    (dref : (r : Register) → Option (RegisterType r)) (P' : X → Prop) (Q : X → CySt → Prop) :
    ∀ (m : SailM X) (st : CySt) (x : X) (b : Bool), runRead dref m = some (x, b) →
      SailCycleOrderFp.fp P' m →
      (∀ r v, dref r = some v → wireReg r = false ∧ st.rv r = v) → RbootAll st.rv →
      (∀ st', st'.rv = st.rv → st'.fe = st.fe → st'.an = st.an → st'.d.ro = st.d.ro →
        st'.d.n = st.d.n → st'.d.ok = st.d.ok → Q x st') →
      cyB A Aa S T Q m st := by
  intro m
  induction m with
  | pure y =>
    intro st x b h _ _ _ hq
    simp only [runRead, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hq st rfl rfl rfl rfl rfl rfl
  | impure call k ih =>
    intro st x b h hfp hd hrb hq
    cases call with
    | error e => trivial
    | ok o =>
      have hq' : ∀ st', st'.rv = st.rv → st'.fe = st.fe → st'.an = st.an →
          st'.d.ro = st.d.ro → st'.d.n = st.d.n → st'.d.ok = st.d.ok → Q x st' := hq
      cases o
      case regRead r =>
        simp only [runRead] at h
        split at h
        · rename_i v hv
          obtain ⟨⟨x', b'⟩, h1, h2⟩ := PinCycRun.mapSome _ _ _ h
          simp only [Prod.mk.injEq] at h2
          obtain ⟨rfl, -⟩ := h2
          intro v' hv'
          obtain ⟨hw, he⟩ := hd r v hv
          have e : v' = v := by rw [hv' hw, he]
          subst e
          exact ih _ (cyRd st r) _ _ h1 (hfp _ (by rw [← he]; exact hrb r)) hd hrb
            (fun st' h1 h2 h3 h4 h5 h6 => hq' st' h1 h2 h3 h4 h5 h6)
        · cases h
      case instrAnnounce => exact hfp.elim
      case getCycleCount =>
        simp only [runRead] at h
        obtain ⟨⟨x', b'⟩, h1, h2⟩ := PinCycRun.mapSome _ _ _ h
        simp only [Prod.mk.injEq] at h2
        obtain ⟨rfl, -⟩ := h2
        exact ih _ st _ _ h1 (hfp _) hd hrb hq'
      all_goals first
        | (simp only [runRead] at h
           obtain ⟨⟨x', b'⟩, h1, h2⟩ := PinCycRun.mapSome _ _ _ h
           simp only [Prod.mk.injEq] at h2
           obtain ⟨rfl, -⟩ := h2
           intro v
           cases v
           first
             | exact ih _ st _ _ h1 (hfp _) hd hrb hq'
             | exact ih _ st _ _ h1 hfp.2 hd hrb hq')
        | (simp only [runRead] at h; cases h)

end PinCycRun
end Weak
