/-
Weak: **W11-C2′ (a3) relArmed — the cycle under `amB`: node lemmas, the trap tails, the decoder**
(`PROGRESS-relArmed.md`).  Lean-only.

The `amB` twins of w1's `PinCycRunCyc*` node lemmas: a register read/write bind, the stop at a
cause write, `assert`; the trap handler (every path writes a cause register first among the
pinned/cause registers, so the obligation ends there), the exception / interrupt / fetch-failure
tails; the decoder's `runRead drefS` walk (its reads are pinned, so answered by the pins); the
retire tail and the prelude pieces as `zfB` footprints.

Every helper is `Weak.PinRelArm.*`.
-/
import Weak.PinRelArmRun

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel

namespace PinRelArmFp
open SailCycleOrderK

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfTickClock : zfT (tick_clock ()) := by zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfExceptionDelegatee (e : ExceptionType) (p : Privilege) :
    zfT (exception_delegatee e p) := by zf_walk

set_option maxHeartbeats 4000000 in
@[zf_reg] theorem zfShouldIncMinstret (p : Privilege) : zfT (should_inc_minstret p) := by zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfDispatchInterrupt (p : Privilege) : zfT (dispatchInterrupt p) := by zf_walk

set_option maxHeartbeats 40000000 in
/-- The retire tail (`ucFinish` of a retired step, then the optional tick): no pinned or cause
register write, no plain store. -/
theorem zfFinishRetire (ib : BitVec 32) (tick : Bool) :
    zfT (ucFinish (.Step_Execute (RETIRE_SUCCESS, ib)) >>=
      fun _ => if tick then tick_clock () else pure ()) := by
  simp only [ucFinish, ucArm, ucRetired, ucEpilogue, RETIRE_SUCCESS, bind_assoc, tick_pc,
    get_config_rvfi, Bool.false_eq_true, ↓reduceIte, pure_bind]
  cases tick <;> zf_walk

end PinRelArmFp

namespace PinRelArm
open SailCycleOrderK PinCycRun PinRelArmFp PinDataflow

section nodes
variable {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop}

theorem amReadBind {Y : Type} (Q : Y → AmSt → Prop) (r : Register) (f : RegisterType r → SailM Y)
    (st : AmSt) (h : ∀ v, Rboot r v → gOk r v → amB A Aa Q (f v) st) :
    amB A Aa Q (readReg r >>= f) st := h

theorem amWriteBind {Y : Type} (Q : Y → AmSt → Prop) (r : Register) (v : RegisterType r)
    (f : PUnit → SailM Y) (st : AmSt) (hb : Rboot r v) (hd : drefH r = none)
    (h : amB A Aa Q (f ()) st) : amB A Aa Q (writeReg r v >>= f) st :=
  fun _ => ⟨hb, hd, fun u => by cases u; exact h⟩

theorem amStopBind {Y : Type} (Q : Y → AmSt → Prop) (r : Register) (v : RegisterType r)
    (f : PUnit → SailM Y) (st : AmSt) (hs : cyS r = true) : amB A Aa Q (writeReg r v >>= f) st :=
  fun h' => absurd (hs.symm.trans h') (by decide)

theorem amPureBind {X Y : Type} (Q : Y → AmSt → Prop) (x : X) (f : X → SailM Y) (st : AmSt)
    (h : amB A Aa Q (f x) st) : amB A Aa Q ((pure x : SailM X) >>= f) st := h

theorem amAssertBind {Y : Type} (Q : Y → AmSt → Prop) (b : Bool) (msg : String)
    (f : Unit → SailM Y) (st : AmSt) (h : b = true → amB A Aa Q (f ()) st) :
    amB A Aa Q (assert b msg >>= f) st := by
  cases b
  · simp only [assert]; exact trivial
  · simp only [assert]; exact h rfl

end nodes

section trap
variable (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)

/-- **The trap handler** (header): its first pinned/cause write is a cause register's — the
obligation ends there. -/
theorem amTrapHandler {Y : Type} (Q : Y → AmSt → Prop) (del : Privilege) (c : TrapCause)
    (pc : BitVec 64) (info : Option (BitVec 64)) (ext : Option Unit) (f : BitVec 64 → SailM Y)
    (st : AmSt) (ha : st.amo = false) :
    amB A Aa Q (trap_handler del c pc info ext >>= f) st := by
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
    refine amReadBind _ _ _ _ (fun v3 _ _ => ?_)
    exact amStopBind _ _ _ _ _ (by decide)
  | Supervisor =>
    simp only [bind_assoc]
    refine amBind (fun _ st' => st'.amo = false) _ _ _ _ ?_ (fun b st1 h1 => ?_)
    · exact amOfZf _ _ _ _ (zfCurrentlyEnabled _) ha (fun _ _ _ _ h _ => h)
    · refine amAssertBind _ _ _ _ _ (fun _ => ?_)
      refine amReadBind _ _ _ _ (fun v3 _ _ => ?_)
      exact amStopBind _ _ _ _ _ (by decide)
  | User => exact trivial
  | VirtualUser => exact trivial
  | VirtualSupervisor => exact trivial

theorem amExcHandler {Y : Type} (Q : Y → AmSt → Prop) (priv : Privilege) (exc : sync_exception)
    (pc : BitVec 64) (f : BitVec 64 → SailM Y) (st : AmSt) (ha : st.amo = false) :
    amB A Aa Q (exception_handler priv exc pc >>= f) st := by
  unfold exception_handler
  simp only [get_config_print_exception, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  refine amBind (fun _ st' => st'.amo = false) _ _ _ st ?_ (fun del st1 h1 => ?_)
  · exact amOfZf _ _ _ _ (zfExceptionDelegatee _ _) ha (fun _ _ _ _ h _ => h)
  · exact amTrapHandler A Aa _ _ _ _ _ _ _ st1 h1

theorem amFinishTrap (Q : Unit → AmSt → Prop) (x : Privilege × sync_exception × BitVec 64)
    (ib : BitVec 32) (tick : Bool) (st : AmSt) (ha : st.amo = false) :
    amB A Aa Q (ucFinish (.Step_Execute (.Trap x, ib)) >>=
      fun _ => if tick then tick_clock () else pure ()) st := by
  obtain ⟨priv, exc, pc⟩ := x
  simp only [ucFinish, ucArm, bind_assoc]
  exact amExcHandler A Aa _ _ _ _ _ st ha

theorem amFinishFetchFail (Q : Unit → AmSt → Prop) (p : virtaddr × ExceptionType) (tick : Bool)
    (st : AmSt) (ha : st.amo = false) :
    amB A Aa Q (ucFinish (.Step_Fetch_Failure p) >>=
      fun _ => if tick then tick_clock () else pure ()) st := by
  obtain ⟨va, e⟩ := p
  simp only [ucFinish, ucArm, handle_exception, bind_assoc]
  refine amReadBind _ _ _ _ (fun v1 _ _ => ?_)
  refine amReadBind _ _ _ _ (fun v2 _ _ => ?_)
  exact amExcHandler A Aa _ _ _ _ _ _ ha

theorem amFinishIntr (Q : Unit → AmSt → Prop) (ip : InterruptType × Privilege) (tick : Bool)
    (st : AmSt) (ha : st.amo = false) :
    amB A Aa Q (ucFinish (.Step_Pending_Interrupt ip) >>=
      fun _ => if tick then tick_clock () else pure ()) st := by
  obtain ⟨intr, priv⟩ := ip
  simp only [ucFinish, ucArm, handle_interrupt, get_config_print_instr, Bool.false_eq_true,
    ↓reduceIte, bind_assoc]
  refine amReadBind _ _ _ _ (fun v1 _ _ => ?_)
  exact amTrapHandler A Aa _ _ _ _ _ _ _ _ ha

end trap

/-! ## The decoder -/

theorem drefHS (r : Register) (v : RegisterType r) (h : drefS r = some v) : drefH r = some v := by
  unfold drefH
  split
  · simp [drefS] at h
  · exact h

section dec
variable (A : Int → BitVec 8 → Prop) (Aa : Nat → Int → Prop)

/-- **The decoder's walk** (header): a footprint whose `runRead drefS` walk returns `x` satisfies
`amB` with post `x` (its reads are pinned registers, answered by the pins). -/
theorem amOfRunRead {X : Type} (P' : X → Prop) (Q : X → AmSt → Prop) :
    ∀ (m : SailM X) (st : AmSt) (x : X) (b : Bool), runRead drefS m = some (x, b) →
      SailCycleOrderFp.fp P' m →
      (∀ st', st'.fe = st.fe → st'.amo = st.amo → (st.armed = true → st'.armed = true) →
        Q x st') →
      amB A Aa Q m st := by
  intro m
  induction m with
  | pure y =>
    intro st x b h _ hq
    simp only [runRead, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hq st rfl rfl id
  | impure call k ih =>
    intro st x b h hfp hq
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r =>
        simp only [runRead] at h
        split at h
        · rename_i v hv
          obtain ⟨⟨x', b'⟩, h1, h2⟩ := PinCycRun.mapSome _ _ _ h
          simp only [Prod.mk.injEq] at h2
          obtain ⟨rfl, -⟩ := h2
          intro v' hb hg
          have e : v' = v := hg v (drefHS r v hv)
          subst e
          exact ih _ st _ _ h1 (hfp _ hb) hq
        · cases h
      case instrAnnounce => exact hfp.elim
      case barrier bk =>
        simp only [runRead] at h
        obtain ⟨⟨x', b'⟩, h1, h2⟩ := PinCycRun.mapSome _ _ _ h
        simp only [Prod.mk.injEq] at h2
        obtain ⟨rfl, -⟩ := h2
        exact ih _ _ _ _ h1 hfp.2 (fun st' e1 e2 e3 => hq st' e1 e2 (fun ha => e3 (armBarMono bk _ ha)))
      case getCycleCount =>
        simp only [runRead] at h
        obtain ⟨⟨x', b'⟩, h1, h2⟩ := PinCycRun.mapSome _ _ _ h
        simp only [Prod.mk.injEq] at h2
        obtain ⟨rfl, -⟩ := h2
        exact ih _ st _ _ h1 (hfp _) hq
      all_goals first
        | (simp only [runRead] at h
           obtain ⟨⟨x', b'⟩, h1, h2⟩ := PinCycRun.mapSome _ _ _ h
           simp only [Prod.mk.injEq] at h2
           obtain ⟨rfl, -⟩ := h2
           intro v
           cases v
           exact ih _ st _ _ h1 (hfp _) hq)
        | (simp only [runRead] at h; cases h)

end dec

end PinRelArm
end Weak
