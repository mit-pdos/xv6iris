/-
Weak: **`dataOkR` (4c) — an INTERRUPT's tail under `cyDB`**: the trap handler's two cause writes
of an interrupt carry the interrupt bit (the second reads the first back through the mirror), so
`cyDB` does not stop at them; everything after writes no cause register (`yfB`, walked by
`yf_walk`) — the whole tail satisfies `cyDB` with the trivial post (`PROGRESS-dataOk.md`).
Lean-only.  Every helper is `Weak.PinDataOk.*`.
-/
import Weak.PinDataOkRun
import Weak.PinDataOkFp
import Weak.PinCycRunCyc2

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)

namespace PinDataOk
open SailCycleOrderK PinCycRun

section intr
variable {G : (r : Register) → RegisterType r → Prop} {D : BitVec 64 → (n : Nat) → BitVec (8 * n) → Prop}
  {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop} {T : CySt → (r : Register) → RegisterType r → Prop}

/-- **The lift from the cause-free footprint**: a `yfB` tree satisfies `cyDB` with its post (read
filters boot-admitted). -/
theorem cyDOfYf {X : Type} (S : X → Prop) (hG : ∀ r v, G r v → Rboot r v) :
    ∀ (m : SailM X) st, PinDataOkFp.yf S m → cyDB G D A Aa T (fun x _ => S x) m st := by
  intro m
  induction m with
  | pure y => exact fun st h => h
  | impure call k ih =>
    intro st hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r => exact fun v _ hg => ih v _ (hm v (hG r v hg))
      case regWrite r v =>
        have hs : cyS r = false := by
          have h2 := hm.1.2
          simp only [PinDataOkFp.yfRegOk, PinDataOkFp.yfProt, Bool.not_eq_true'] at h2
          simpa [cyS] using h2
        refine ⟨fun h => absurd (hs.symm.trans h) (by decide), fun _ => ⟨hm.1.1, fun u => ih u _ (hm.2 u)⟩⟩
      case memRead n va req =>
        refine ⟨fun _ h2 => ?_, fun _ w _ => ih _ _ (hm.2 _)⟩
        have h1 : (classify req.access_kind).akIfetch = false := hm.1
        rw [h1] at h2; cases h2
      case instrAnnounce => exact hm.elim
      case barrier => exact fun v => ih v _ hm.2
      case memWrite => exact ih _ _ (hm _)
      case getCycleCount => exact ih _ _ (hm _)
      all_goals exact fun v => ih v _ (hm v)

theorem PinDataOk.updLowKeep63 (v : BitVec 64) (x : BitVec 63) :
    (Sail.BitVec.updateSubrange v (64 - 2) 0 x).getLsbD 63 = v.getLsbD 63 := by
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  generalize v = y
  bv_decide

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **An interrupt's trap handler** under `cyDB`: no stop; the continuation a cause-free footprint. -/
theorem cyDTrapIntr {Y : Type} (hG : ∀ r v, G r v → Rboot r v) (del : Privilege) (i : InterruptType)
    (pc : BitVec 64) (f : BitVec 64 → SailM Y) (st : CySt)
    (hf : ∀ x, PinDataOkFp.yf (fun _ => True) (f x)) :
    cyDB G D A Aa T (fun _ _ => True) (trap_handler del (.Interrupt i) pc none none >>= f) st := by
  unfold trap_handler
  simp only [get_config_print_exception, get_config_print_interrupt, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  have hz : hartSupports extension.Ext_Zicfilp = true := by
    simp [hartSupports]
  rw [if_pos hz]
  unfold zicfilp_preserve_elp_on_trap
  have hint : trapCause_is_interrupt (TrapCause.Interrupt i) = true := rfl
  cases del with
  | Machine =>
    simp only [bind_assoc]
    refine cyDReadBind _ _ _ _ (fun v1 _ _ => ?_)
    refine cyDReadBind _ _ _ _ (fun v2 _ _ => ?_)
    refine cyDWriteBind _ _ _ _ _ (Or.inl (by decide)) trivial ?_
    unfold reset_elp
    try simp only [bind_assoc]
    refine cyDWriteBind _ _ _ _ _ (Or.inl (by decide)) trivial ?_
    refine cyDReadBind _ _ _ _ (fun v3 _ _ => ?_)
    have hc1 := PinCycRun.causeBitUpd (trapCause_is_interrupt (TrapCause.Interrupt i)) v3
    rw [hint] at hc1
    refine cyDWriteBind _ _ _ _ _ (Or.inr hc1) trivial ?_
    refine cyDReadBind _ _ _ _ (fun v4 hv4 _ => ?_)
    have hv4' := hv4 (by decide)
    simp only [cyRd, cyWr, RegFile.set_same] at hv4'
    subst hv4'
    refine cyDWriteBind _ _ _ _ _ (Or.inr ?_) trivial ?_
    · show (BitVec.updateSubrange _ _ _ _).getLsbD 63 = true
      reduce_closed_widths
      simp only [hint, BitVec.updateSubrange, BitVec.updateSubrange', bool_to_bit, bool_bit_forwards,
        zero_extend, Sail.BitVec.zeroExtend]
      clear hc1 hz hint
      generalize v3 = y
      generalize trapCause_bits_forwards (TrapCause.Interrupt i) = z
      bv_decide
    exact cyDOfYf _ hG _ _ (by yf_walk)
  | Supervisor =>
    simp only [bind_assoc]
    refine cyDReadBind _ _ _ _ (fun v1 _ _ => ?_)
    refine cyDReadBind _ _ _ _ (fun v2 _ _ => ?_)
    refine cyDWriteBind _ _ _ _ _ (Or.inl (by decide)) trivial ?_
    unfold reset_elp
    try simp only [bind_assoc]
    refine cyDWriteBind _ _ _ _ _ (Or.inl (by decide)) trivial ?_
    refine cyDBind (fun _ _ => True) _ _ _ _ (cyDOfYf _ hG _ _ (by yf_walk)) (fun b _ _ => ?_)
    cases b
    · simp only [assert]; exact trivial
    · simp only [assert, pure_bind]
      refine cyDReadBind _ _ _ _ (fun v3 _ _ => ?_)
      have hc1 := PinCycRun.causeBitUpd (trapCause_is_interrupt (TrapCause.Interrupt i)) v3
      rw [hint] at hc1
      refine cyDWriteBind _ _ _ _ _ (Or.inr hc1) trivial ?_
      refine cyDReadBind _ _ _ _ (fun v4 hv4 _ => ?_)
      have hv4' := hv4 (by decide)
      simp only [cyRd, cyWr, RegFile.set_same] at hv4'
      subst hv4'
      refine cyDWriteBind _ _ _ _ _ (Or.inr ?_) trivial ?_
      · show (BitVec.updateSubrange _ _ _ _).getLsbD 63 = true
        reduce_closed_widths
        simp only [hint, BitVec.updateSubrange, BitVec.updateSubrange', bool_to_bit, bool_bit_forwards,
          zero_extend, Sail.BitVec.zeroExtend]
        clear hc1 hz hint
        generalize v3 = y
        generalize trapCause_bits_forwards (TrapCause.Interrupt i) = z
        bv_decide
      exact cyDOfYf _ hG _ _ (by yf_walk)
  | User => exact trivial
  | VirtualUser => exact trivial
  | VirtualSupervisor => exact trivial

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 100000 in
/-- **An interrupt's tail** under `cyDB`: no stop. -/
theorem cyDFinishIntr (hG : ∀ r v, G r v → Rboot r v) (ip : InterruptType × Privilege) (tick : Bool)
    (st : CySt) :
    cyDB G D A Aa T (fun _ _ => True) (ucFinish (.Step_Pending_Interrupt ip) >>=
      fun _ => if tick then tick_clock () else pure ()) st := by
  obtain ⟨intr, priv⟩ := ip
  simp only [ucFinish, ucArm, handle_interrupt, get_config_print_instr, Bool.false_eq_true,
    ↓reduceIte, bind_assoc]
  refine cyDReadBind _ _ _ _ (fun v1 _ _ => ?_)
  exact cyDTrapIntr hG priv intr v1 _ st (fun x => by yf_walk)

end intr

end PinDataOk
end Weak
