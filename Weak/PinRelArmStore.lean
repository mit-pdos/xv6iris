/-
Weak: **W11-C2′ (a3) relArmed — a STORE's execute under `amB`** (`PROGRESS-relArmed.md`).
Lean-only.

A plain 4-byte `memWrite` happens only UNSPLIT, as the instruction's first and only one: the page
split (`split_on_page_boundary`, `SplitAccessUtils.lean:277`) and the misaligned split
(`split_misaligned`, `:256`) cut the access into pieces of fewer bytes.

Every helper is `Weak.PinRelArm.*`.
-/
import Weak.PinRelArmTab

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
open Wlabel KernelPinsDef

namespace PinRelArm
open SailCycleOrderK PinCycRun PinRelArmFp PinDataflow

end PinRelArm

namespace PinRelArmFp
open SailCycleOrderK

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfCheckPmaPmp (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type)
    (priv : Privilege) (pa : physaddr) (w : Nat) (b : Bool) :
    zfT (check_pma_with_pmp_priority acc pbmt priv pa w b) := by zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfWithinMmioWritable (pa : physaddr) (w : Nat) :
    zfT (within_mmio_writable pa w) := by zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfMmioWrite (pa : physaddr) (w : Nat) (v : BitVec (8 * w)) :
    zfT (mmio_write pa w v) := by zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfMemoryException (va : virtaddr) (e : ExceptionType) :
    zf (fun r => PinCycRunFp.isTrapR r = true) (memory_exception va e) := by zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfMemWriteEa (pa : physaddr) (w : Nat) (acc : MemoryAccessType mem_payload)
    (pbmt : page_based_mem_type) (aq rl con : Bool) :
    zfT (mem_write_ea pa w acc pbmt aq rl con) := by
  unfold mem_write_ea; zf_walk

/-- A data-address check that succeeded. -/
def addrOk {X : Type} (r : Ext_DataAddr_Check X) : Bool :=
  match r with
  | .Ext_DataAddr_OK _ => true
  | _ => false

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfGetTransformedDataAddr (rs : regidx) (off : BitVec 64)
    (acc : MemoryAccessType mem_payload) (w : Nat) :
    zf (fun r => addrOk r = true) (get_transformed_data_addr rs off acc w) := by
  unfold get_transformed_data_addr ext_data_get_addr; zf_walk

set_option maxHeartbeats 40000000 in
@[zf_reg] theorem zfTranslationMode (p : Privilege) : zfT (translationMode p) := by zf_walk

end PinRelArmFp

namespace PinRelArm
open SailCycleOrderK PinCycRun PinRelArmFp PinDataflow

section st
variable {A : Int → BitVec 8 → Prop} {Aa : Nat → Int → Prop}

set_option maxHeartbeats 4000000 in
/-- A plain RAM write of `n` bytes: it owes the flag iff `n = 4`; the AMO bit kept. -/
theorem amWriteRamPlain (pa : physaddr) (n : Nat) (data : BitVec (8 * n)) (m : Unit) (st : AmSt)
    (hn : n = 4 → st.armed = true) :
    amB A Aa (fun _ st' => st'.amo = st.amo) (write_ram .Write_plain pa n data m) st := by
  unfold write_ram
  simp only [pure_bind]
  exact ⟨fun _ => rfl, fun _ _ => ⟨hn, rfl⟩, fun _ hx => absurd hx (by simp [akExcl])⟩

theorem splitAux (w : Nat) (b : Int) (hb : 0 < b) (hc : (w == ((↑w : Int).tdiv b * b).toNat) = true) :
    (↑w : Int).tdiv b * b = ↑w := by
  have hq : 0 ≤ (↑w : Int).tdiv b := Int.tdiv_nonneg (by omega) (by omega)
  have e : w = ((↑w : Int).tdiv b * b).toNat := by simpa using hc
  have h2 : 0 ≤ (↑w : Int).tdiv b * b := Int.mul_nonneg hq (by omega)
  omega

set_option maxHeartbeats 4000000 in
/-- The misaligned split's value: `N` pieces of `sw > 0` bytes, `N * sw = w`. -/
theorem amSplitMis (pa : physaddr) (w : Nat) (e : Nat) (sp : Splittability) (st : AmSt)
    (hw : 0 < w) :
    amB A Aa (fun p st' => st' = st ∧ p.1 * p.2 = (w : Int) ∧ 0 < p.2)
      (split_misaligned pa w e sp) st := by
  unfold split_misaligned
  simp only [sys_misaligned_byte_by_byte, Bool.false_eq_true, ↓reduceIte]
  split
  · exact ⟨rfl, by simp, by omega⟩
  · unfold split_access
    refine amAssertBind _ _ _ _ _ (fun hc => ⟨rfl, splitAux w _ (Int.pow_pos (by decide)) hc,
      Int.pow_pos (by decide)⟩)

/-- **The loop** (`untilFuelM.go` under `ExceptT.run`): an invariant indexed by the fuel left. -/
theorem amRGo {α R : Type} (cnd : α → Bool) (body : α → SailME R α) (Inv : Nat → AmSt → Prop)
    (Post : AmSt → Prop) (hInv : ∀ n st, Inv n st → Post st)
    (hb : ∀ n x st, Inv (n + 1) st →
      amB A Aa (fun r st' => (∀ y, r = .ok y → Inv n st') ∧ (∀ e, r = .error e → Post st'))
        (ExceptT.run (body x)) st) :
    ∀ n x st, Inv n st →
      amB A Aa (fun _ st' => Post st') (ExceptT.run (untilFuelM.go (fun x => pure (cnd x)) body x n)) st := by
  intro n
  induction n with
  | zero => intro x st h; exact hInv 0 st h
  | succ n ih =>
    intro x st h
    simp only [untilFuelM.go]
    rw [ExceptT.run_bind]
    refine amBind _ _ _ _ st (hb n x st h) (fun r st' hr => ?_)
    cases r with
    | error e => exact hr.2 e rfl
    | ok y =>
      simp only [ExceptT.run_bind, ExceptT.run_pure, pure_bind]
      split
      · exact hInv n st' (hr.1 y rfl)
      · exact ih y st' (hr.1 y rfl)

set_option maxHeartbeats 4000000 in
theorem amCheckedMemWritePlain (pa : physaddr) (w : Nat) (data : BitVec (8 * w))
    (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (priv : Privilege) (m : Unit)
    (st : AmSt) (ha : st.amo = false) (hw0 : 0 < w) (hw : w ≤ 4) (harm : w = 4 → st.armed = true) :
    amB A Aa (fun _ st' => st'.amo = false)
      (checked_mem_write pa w data acc pbmt priv m false false false) st := by
  unfold checked_mem_write
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
  refine amBind (fun _ st' => st'.amo = false ∧ (st.armed = true → st'.armed = true)) _ _ _ st
    (amOfZf _ _ _ _ (zfCheckPmaPmp _ _ _ _ _ _) ha (fun _ st' _ _ e2 e3 => ⟨e2, e3⟩))
    (fun r st1 h1 => ?_)
  cases r with
  | Err e =>
    simp only [run_SailME_throw, pure_bind]
    exact h1.1
  | Ok ai =>
    simp only [ExceptT.run_pure, pure_bind]
    refine amBindF (fun _ st' => st'.amo = false) _ _ _ st1 ?_ (fun r st' h => ?_)
    rotate_left
    · rcases r with (e | e) | e
      · exact trivial
      · exact h
      · exact h
    refine amBindF _ _ _ _ st1 (amSplitMis pa w _ _ st1 hw0) (fun p st2 h2 => ?_)
    obtain ⟨rfl, hNs, hs0⟩ := h2
    obtain ⟨N, sw⟩ := p
    simp only [write_kind_of_flags, pure_bind, untilFuelM] at hNs hs0 ⊢
    -- the invariant: the AMO bit clear; a 4-byte piece is the only one, and finds the flag armed
    let Inv : Nat → AmSt → Prop := fun n st' =>
      st'.amo = false ∧ (sw.toNat = 4 → n ≤ 1 ∧ (n = 1 → st'.armed = true))
    have hI0 : Inv N.toNat st2 := by
      refine ⟨h1.1, fun h4 => ?_⟩
      have hsw : sw = 4 := by omega
      subst hsw
      have hN : N = 1 := by omega
      subst hN
      exact ⟨by decide, fun _ => h1.2 (harm (by omega))⟩
    refine amBindF (fun _ st' => st'.amo = false) _ _ _ st2
      (amRGo _ _ Inv (fun st' => st'.amo = false) (fun _ _ h => h.1) ?_ N.toNat _ st2 hI0)
      (fun r st' h => ?_)
    rotate_left
    · rcases r with e | ⟨fin, i, ws⟩
      · exact h
      · exact h
    intro n x st' hI
    obtain ⟨hIa, hI4⟩ := hI
    have hn0 : sw.toNat = 4 → n = 0 := fun h => by have := (hI4 h).1; omega
    simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, assert, ExceptT.run_pure,
      PreSail.assert, ↓reduceIte]
    refine amBindF (fun _ s => s.amo = false ∧ (st'.armed = true → s.armed = true)) _ _ _ st'
      (amOfZf _ _ _ _ (zfPmpCheck _ _ _ _) hIa (fun _ s _ _ e2 e3 => ⟨e2, e3⟩)) (fun o s1 hs1 => ?_)
    cases o with
    | some e =>
      dsimp only
      simp only [ExceptT.run_bind, run_SailME_throw, pure_bind]
      exact ⟨fun y hy => (by cases hy), fun _ _ => hs1.1⟩
    | none =>
      simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure]
      refine amBindF (fun _ s => s.amo = false ∧ (st'.armed = true → s.armed = true)) _ _ _ s1
        (amOfZf _ _ _ _ (zfWithinMmioWritable _ _) hs1.1
          (fun _ s _ _ e2 e3 => ⟨e2, fun h => e3 (hs1.2 h)⟩)) (fun b s2 hs2 => ?_)
      refine amBindF (fun r s => (∀ y, r = .ok y → s.amo = false) ∧
        (∀ e, r = .error e → s.amo = false)) _ _ _ s2 ?_ (fun r s3 hs3 => ?_)
      · cases b with
        | true =>
          simp only [↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
          refine amBindF (fun _ s => s.amo = false) _ _ _ s2
            (amOfZf _ _ _ _ (zfMmioWrite _ _ _) hs2.1 (fun _ s _ _ e2 _ => e2)) (fun r s4 hs4 => ?_)
          cases r with
          | Ok v => exact ⟨fun _ _ => hs4, fun _ h => by cases h⟩
          | Err e =>
            simp only [run_SailME_throw]
            exact ⟨fun _ h => (by cases h), fun _ _ => hs4⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
          refine amBindF (fun _ s => s.amo = s2.amo) _ _ _ s2
            (amWriteRamPlain _ _ _ _ s2 (fun h4 => hs2.2 ((hI4 h4).2 (by have := hn0 h4; omega))))
            (fun r s4 hs4 => ?_)
          exact ⟨fun _ _ => hs4.trans hs2.1, fun _ h => by cases h⟩
      · cases r with
        | ok y =>
          refine ⟨fun _ _ => ⟨hs3.1 y rfl, fun h4 => ⟨by have := hn0 h4; omega, fun h => ?_⟩⟩,
            fun _ h => by cases h⟩
          have := hn0 h4; omega
        | error e => exact ⟨fun _ h => (by cases h), fun _ _ => hs3.2 e rfl⟩

set_option maxHeartbeats 4000000 in
/-- A plain `mem_write_value` of `0 < w ≤ 4` bytes: the AMO bit kept, a 4-byte piece armed. -/
theorem amMemWriteValue (pa : physaddr) (w : Nat) (v : BitVec (8 * w))
    (acc : MemoryAccessType mem_payload) (pbmt : page_based_mem_type) (st : AmSt)
    (ha : st.amo = false) (hw0 : 0 < w) (hw : w ≤ 4) (harm : w = 4 → st.armed = true) :
    amB A Aa (fun _ st' => st'.amo = false) (mem_write_value pa w v acc pbmt false false false) st := by
  unfold mem_write_value mem_write_value_meta mem_write_value_priv_meta
  simp only [bind_assoc]
  refine amReadBind _ _ _ _ (fun ms _ _ => ?_)
  refine amReadBind _ _ _ _ (fun cp _ _ => ?_)
  refine amBind (fun _ s => s.amo = false ∧ (st.armed = true → s.armed = true)) _ _ _ st
    (amOfZf _ _ _ _ (zfEffectivePrivilege _ _ _) ha (fun _ s _ _ e2 e3 => ⟨e2, e3⟩))
    (fun p s1 hs1 => ?_)
  refine amBind (fun _ s => s.amo = false) _ _ _ s1
    (amCheckedMemWritePlain _ _ _ _ _ _ _ s1 hs1.1 hw0 hw (fun h => hs1.2 (harm h)))
    (fun r s2 hs2 => hs2)

/-- A data access's result: a value, or a trap. -/
def resT {X : Type} (r : Result X ExecutionResult) : Prop :=
  match r with
  | .Err e => PinCycRunFp.isTrapR e = true
  | .Ok _ => True

set_option maxHeartbeats 4000000 in
/-- A plain `translate_and_write_value` of `0 < w ≤ 4` bytes: a value or a trap. -/
theorem amTranslateWrite (va : virtaddr) (w : Nat) (v : BitVec (8 * w))
    (acc : MemoryAccessType mem_payload) (st : AmSt) (ha : st.amo = false) (hw0 : 0 < w)
    (hw : w ≤ 4) (harm : w = 4 → st.armed = true) :
    amB A Aa (fun r st' => st'.amo = false ∧ resT r)
      (translate_and_write_value va w v acc false false false) st := by
  unfold translate_and_write_value
  simp only [bind_assoc]
  refine amBind (fun _ s => s.amo = false ∧ (st.armed = true → s.armed = true)) _ _ _ st
    (amOfZf _ _ _ _ (zfTranslateAddr _ _) ha (fun _ s _ _ e2 e3 => ⟨e2, e3⟩)) (fun r s1 hs1 => ?_)
  have hexc : ∀ (X : Type) (va' : virtaddr) (e : ExceptionType) (s : AmSt), s.amo = false →
      amB A Aa (fun (r : Result X ExecutionResult) st' => st'.amo = false ∧ resT r)
        (memory_exception va' e >>= fun x => (pure (Err x) : SailM (Result X ExecutionResult))) s :=
    fun X va' e s hs =>
    amBind _ _ _ _ s (amOfZf _ _ _ _ (zfMemoryException _ _) hs
      (fun x s' hx _ e2 _ => (⟨e2, hx⟩ : s'.amo = false ∧ PinCycRunFp.isTrapR x = true)))
      (fun x s' h => ⟨h.1, h.2⟩)
  cases r with
  | Err q =>
    obtain ⟨e, _⟩ := q
    exact hexc _ _ _ s1 hs1.1
  | Ok q =>
    obtain ⟨pa, pbmt, _⟩ := q
    simp only [bind_assoc]
    refine amBind (fun _ s => s.amo = false ∧ (st.armed = true → s.armed = true)) _ _ _ s1
      (amOfZf _ _ _ _ (zfMemWriteEa _ _ _ _ _ _ _) hs1.1
        (fun _ s _ _ e2 e3 => ⟨e2, fun h => e3 (hs1.2 h)⟩)) (fun r s2 hs2 => ?_)
    cases r with
    | Err q => obtain ⟨ea, e⟩ := q; exact hexc _ _ _ s2 hs2.1
    | Ok u =>
      simp only [bind_assoc]
      refine amBind (fun _ s => s.amo = false) _ _ _ s2
        (amMemWriteValue _ _ _ _ _ s2 hs2.1 hw0 hw (fun h => hs2.2 (harm h))) (fun r s3 hs3 => ?_)
      cases r with
      | Err q => obtain ⟨ea, e⟩ := q; exact hexc _ _ _ s3 hs3
      | Ok b => exact ⟨hs3, trivial⟩

set_option maxHeartbeats 4000000 in
/-- The page split's value: the whole access, or two pieces each of fewer bytes. -/
theorem amSplitPage {k : Nat} (addr : BitVec k) (w : Nat) (st : AmSt) :
    amB A Aa (fun p s => s = st ∧ ((p.1 = (w : Int) ∧ p.2 = 0) ∨
        (0 < p.1 ∧ p.1 < (w : Int) ∧ 0 < p.2 ∧ p.2 < (w : Int))))
      (split_on_page_boundary addr w) st := by
  unfold split_on_page_boundary
  simp only
  split
  · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · refine amAssertBind _ _ _ _ _ (fun hc => ⟨rfl, Or.inr ?_⟩)
    generalize Sail.BitVec.extractLsb addr (3 - 1).toNat 0 = x at hc ⊢
    have hlt := x.isLt
    simp only [BitVec.toNatInt] at hc ⊢
    simp at hc hlt ⊢
    omega

/-- **The 4-byte data write** (`vmem_write_addr`, `VmemUtils.lean:345`) under `amB`: a value or a
trap; a 4-byte plain piece only unsplit, finding the flag armed. -/
theorem amVmemWriteAddr (va : virtaddr) (v : BitVec (8 * 4)) (st : AmSt) (ha : st.amo = false)
    (harm : st.armed = true) :
    amB A Aa (fun r st' => st'.amo = false ∧ resT r)
      (vmem_write_addr va 4 v (.Store .Data) false false false) st := by
  unfold vmem_write_addr
  simp only [SailME.run, PreSail.PreSailME.run, bind_assoc, pure_bind,
    sys_misaligned_order_decreasing, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    plat_misaligned_exception, is_amo_access, is_vector_access, plat_misaligned_access]
  refine amBindF (fun r s => s.amo = false ∧ (∀ e, r = .ok e → resT e) ∧
    (∀ e, r = .error (.inr e) → resT e)) _ _ _ st ?_ (fun r s h => ?_)
  rotate_left
  · rcases r with (e | e) | e
    · exact trivial
    · exact ⟨h.1, h.2.2 e rfl⟩
    · exact ⟨h.1, h.2.1 e rfl⟩
  rw [PinFetchVal.runIte]
  split
  all_goals
    simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, ExceptT.run_pure]
  all_goals
    refine amBindF _ _ _ _ st (amSplitPage _ 4 st) (fun p s1 h1 => ?_)
    obtain ⟨rfl, hp⟩ := h1
    obtain ⟨inb, nxb⟩ := p
    simp only at hp
    refine amReadBind _ _ _ _ (fun ms _ _ => ?_)
    refine amReadBind _ _ _ _ (fun cp _ _ => ?_)
    refine amBindF (fun _ s => s.amo = false ∧ s.armed = true) _ _ _ s1
      (amOfZf _ _ _ _ (zfEffectivePrivilege _ _ _) ha (fun _ s _ _ e2 e3 => ⟨e2, e3 harm⟩))
      (fun ep s2 h2 => ?_)
    refine amBindF (fun _ s => s.amo = false ∧ s.armed = true) _ _ _ s2
      (amOfZf _ _ _ _ (zfTranslationMode _) h2.1 (fun _ s _ _ e2 e3 => ⟨e2, e3 h2.2⟩))
      (fun md s3 h3 => ?_)
    refine amBindF (fun _ s => s.amo = false ∧ s.armed = true) _ _ _ s3
      (amOfZf _ _ _ _ (zfTranslateAddr _ _) h3.1 (fun _ s _ _ e2 e3 => ⟨e2, e3 h3.2⟩))
      (fun tr s4 h4 => ?_)
    simp only at *
    have hthr : ∀ (va' : virtaddr) (e : ExceptionType) (s : AmSt), s.amo = false →
        amB A Aa (fun (r : Except (Sail.Error exception ⊕ Result Bool ExecutionResult) Bool) s' =>
            s'.amo = false ∧ ∀ e', r = .error (.inr e') → resT e')
          (memory_exception va' e >>= fun d => pure (Except.error (Sum.inr (Err d)))) s :=
      fun va' e s hs => amBind _ _ _ _ _ (amOfZf _ _ _ _ (zfMemoryException _ _) hs
        (fun x s' hx _ e2 _ => (⟨e2, hx⟩ : s'.amo = false ∧ PinCycRunFp.isTrapR x = true)))
        (fun x s' h => ⟨h.1, fun e' he => by
          simp only [Except.error.injEq, Sum.inr.injEq] at he; subst he; exact h.2⟩)
    have hW : ∀ c : Bool, 0 < (if c = true then inb else ((4 : Nat) : Int)).toNat ∧
        (if c = true then inb else ((4 : Nat) : Int)).toNat ≤ 4 := by
      intro c; cases c <;> simp <;> omega
    refine amBindF (fun r s => s.amo = false ∧ (∀ e, r = .error (.inr e) → resT e)) _ _ _ s4 ?_
      (fun r s5 h5 => ?_)
    · cases tr with
      | Err q =>
        obtain ⟨e, _⟩ := q
        simp only [ExceptT.run_bind, run_liftM, bind_assoc, run_SailME_throw, pure_bind]
        exact hthr _ _ _ h4.1
      | Ok q =>
        obtain ⟨paddr, pbmt, _⟩ := q
        simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, is_store_conditional,
          PreSail.assert, beq_self_eq_true, ↓reduceIte]
        refine amBindF (fun _ s => s.amo = false ∧ s.armed = true) _ _ _ s4
          (amOfZf _ _ _ _ (zfMemWriteEa _ _ _ _ _ _ _) h4.1 (fun _ s _ _ e2 e3 => ⟨e2, e3 h4.2⟩))
          (fun r s6 h6 => ?_)
        cases r with
        | Err q =>
          obtain ⟨ea, e⟩ := q
          simp only [ExceptT.run_bind, run_liftM, bind_assoc, run_SailME_throw, pure_bind]
          exact hthr _ _ _ h6.1
        | Ok u =>
          simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
          refine amBindF (fun _ s => s.amo = false) _ _ _ s6
            (amMemWriteValue _ _ _ _ _ s6 h6.1 (hW _).1 (hW _).2 (fun _ => h6.2)) (fun r s7 h7 => ?_)
          cases r with
          | Err q =>
            obtain ⟨ea, e⟩ := q
            simp only [ExceptT.run_bind, run_liftM, bind_assoc, run_SailME_throw, pure_bind]
            exact hthr _ _ _ h7
          | Ok b => exact ⟨h7, fun e he => by cases he⟩
    cases r with
    | error e => exact ⟨h5.1, fun e' he => (by cases he), fun e' he => h5.2 e' (by simp only [Except.error.injEq] at he ⊢; exact he)⟩
    | ok x7 =>
      dsimp only
      refine amBindF (fun r s => s.amo = false ∧ (∀ e, r = .error (.inr e) → resT e)) _ _ _ s5 ?_
        (fun r s8 h8 => ?_)
      · rw [PinFetchVal.runIte]
        split
        · rename_i hc
          have hn : 0 < nxb ∧ nxb < 4 := by
            simp at hc
            rcases hp with ⟨_, h0⟩ | ⟨_, _, h1, h2⟩ <;> omega
          simp only [ExceptT.run_bind, run_liftM, bind_assoc, pure_bind, is_store_conditional,
            PreSail.assert, Functions.not, ↓reduceIte, Bool.not_false]
          refine amBindF (fun r s => s.amo = false ∧ resT r) _ _ _ s5
            (amTranslateWrite _ _ _ _ s5 h5.1 (by omega) (by omega) (fun h => by omega))
            (fun r s9 h9 => ?_)
          cases r with
          | Err e =>
            simp only [run_SailME_throw]
            exact ⟨h9.1, fun e' he => by
              simp only [Except.error.injEq, Sum.inr.injEq] at he; subst he; exact h9.2⟩
          | Ok b => exact ⟨h9.1, fun e he => by cases he⟩
        · exact ⟨h5.1, fun e he => by cases he⟩
      · cases r with
        | ok x => exact ⟨h8.1, fun e he => by
            simp only [Except.ok.injEq] at he; subst he; trivial, fun e he => by cases he⟩
        | error e => exact ⟨h8.1, fun e' he => (by cases he), fun e' he => h8.2 e' (by simp only [Except.error.injEq] at he ⊢; exact he)⟩

set_option maxHeartbeats 4000000 in
theorem amVmemWrite (rs : regidx) (off : BitVec 64) (v : BitVec (8 * 4)) (st : AmSt)
    (ha : st.amo = false) (harm : st.armed = true) :
    amB A Aa (fun r st' => st'.amo = false ∧ resT r)
      (vmem_write rs off 4 v (.Store .Data) false false false) st := by
  unfold vmem_write
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run_bind, run_liftM, bind_assoc, pure_bind]
  refine amBindF (fun r s => addrOk r = true ∧ s.amo = false ∧ s.armed = true) _ _ _ st
    (amOfZf _ _ _ _ (zfGetTransformedDataAddr _ _ _ _) ha (fun x s hx _ e2 e3 => ⟨hx, e2, e3 harm⟩))
    (fun r s1 h1 => ?_)
  cases r with
  | Ext_DataAddr_Error e => simp [addrOk] at h1
  | Ext_DataAddr_OK va =>
    simp only [ExceptT.run_pure, pure_bind]
    refine amBindF (fun r s => s.amo = false ∧ ∃ a, r = .ok a ∧ resT a) _ _ _ s1 ?_
      (fun r s2 h2 => ?_)
    · exact amBind _ _ _ _ s1 (amVmemWriteAddr va v s1 h1.2.1 h1.2.2)
        (fun a s h => ⟨h.1, a, rfl, h.2⟩)
    · obtain ⟨h2a, a, rfl, h2b⟩ := h2
      exact ⟨h2a, h2b⟩

set_option maxHeartbeats 4000000 in
/-- **A `sw`'s `execute`**: it retires or traps, the AMO bit clear. -/
theorem amExecuteStore (imm : BitVec 12) (rs2 rs1 : regidx) (st : AmSt) (ha : st.amo = false)
    (harm : st.armed = true) :
    amB A Aa (execPostAm false) (execute (.STORE (imm, rs2, rs1, 4))) st := by
  simp only [execute, execute_STORE, bind_assoc, show Int.toNat 4 = 4 from rfl]
  refine amAssertBind _ _ _ _ _ (fun _ => ?_)
  refine amBindF (fun _ s => s.amo = false ∧ s.armed = true) _ _ _ st
    (amOfZf _ _ _ _ (zfRXBits _) ha (fun _ s _ _ e2 e3 => ⟨e2, e3 harm⟩)) (fun x s1 h1 => ?_)
  simp only [pure_bind]
  refine amBindF (fun r s => s.amo = false ∧ resT r) _ _ _ s1
    (amVmemWrite _ _ _ s1 h1.1 h1.2) (fun r s2 h2 => ?_)
  cases r with
  | Ok x => exact Or.inl ⟨rfl, h2.1, fun h => by cases h⟩
  | Err e =>
    have he := h2.2
    simp only [resT] at he
    cases e <;> simp [PinCycRunFp.isTrapR] at he
    exact Or.inr ⟨⟨_, rfl⟩, h2.1⟩

theorem execPostNotAs (r : ExecutionResult) (st : AmSt) (h : execPostAm false r st) :
    ∀ i, r ≠ .ExecuteAs i := by
  rintro i rfl
  rcases h with ⟨h, -⟩ | ⟨⟨x, h⟩, -⟩ <;> cases h

/-- **A `sw` under `uxaExecAs`** (header). -/
theorem amExecStore (imm : BitVec 12) (rs2 rs1 : regidx) (st : AmSt) (ha : st.amo = false)
    (harm : st.armed = true) :
    amB A Aa (execPostAm false) (uxaExecAs (.STORE (imm, rs2, rs1, 4))) st := by
  unfold uxaExecAs
  refine amBind _ _ _ _ st (amExecuteStore imm rs2 rs1 st ha harm) (fun r s h => ?_)
  cases r
  case ExecuteAs i => exact absurd rfl (execPostNotAs _ s h i)
  all_goals exact h

/-- **A `c.sw` under `uxaExecAs`** (header): it redirects to the 4-byte `sw`. -/
theorem amExecCSw (uimm : BitVec 5) (rsc1 rsc2 : cregidx) (st : AmSt) (ha : st.amo = false)
    (harm : st.armed = true) :
    amB A Aa (execPostAm false) (uxaExecAs (.C_SW (uimm, rsc1, rsc2))) st := by
  unfold uxaExecAs
  simp only [execute, execute_C_SW, pure_bind]
  exact amExecuteStore _ _ _ st ha harm
end st

/-! ## The release stores, decided -/

def isSw4 : Option instruction → Bool
  | some (.STORE (_, _, _, w)) => w == 4
  | _ => false

theorem isSw4Of (o : Option instruction) (h : isSw4 o = true) :
    ∃ imm rs2 rs1, o = some (.STORE (imm, rs2, rs1, 4)) := by
  match o, h with
  | some (.STORE (imm, rs2, rs1, w)), h =>
    simp only [isSw4, beq_iff_eq] at h
    subst h
    exact ⟨imm, rs2, rs1, rfl⟩

def isCSw : Option instruction → Bool
  | some (.C_SW _) => true
  | _ => false

theorem isCSwOf (o : Option instruction) (h : isCSw o = true) :
    ∃ uimm rsc1 rsc2, o = some (.C_SW (uimm, rsc1, rsc2)) := by
  match o, h with
  | some (.C_SW (uimm, rsc1, rsc2)), _ => exact ⟨uimm, rsc1, rsc2, rfl⟩

theorem relSwText : textLo ≤ (KernelSyms.«release» : Int) + 0x1a ∧
    (KernelSyms.«release» : Int) + 0x1a + 3 < textHi := by decide +kernel
theorem relSwDec : isSw4 (PinWalkTab.decS ((KernelSyms.«release» : Int) + 0x1a)) = true := by
  decide +kernel
theorem relSwRvc : wIsRvc (kw ((KernelSyms.«release» : Int) + 0x1a)) = false := by decide +kernel
theorem relSwAmo :
    WbPrimed.ibAmo (ibAnn (ibOfBvn (kword ((KernelSyms.«release» : Int) + 0x1a)))) = false := by
  decide +kernel

theorem mainSwText : textLo ≤ (KernelSyms.«main» : Int) + 0xb0 ∧
    (KernelSyms.«main» : Int) + 0xb0 + 3 < textHi := by decide +kernel
theorem mainSwDec : isCSw (PinWalkTab.decS ((KernelSyms.«main» : Int) + 0xb0)) = true := by
  decide +kernel
theorem mainSwRvc : wIsRvc (kw ((KernelSyms.«main» : Int) + 0xb0)) = true := by decide +kernel
theorem mainSwAmo : WbPrimed.ibAmo (ibAnn (ibOfBvn
    (BitVec.ofNat 16 (kw ((KernelSyms.«main» : Int) + 0xb0))))) = false := by decide +kernel

/-- **THE STORE CYCLE** (header): at a release pc, every cycle started with an empty log, no AMO
bit and the flag ARMED satisfies `amB` — its 4-byte plain store finds the flag armed. -/
theorem swCycle (pc : Int) (hpc : pc ∈ releasePcs) (tick : Bool) (st : AmSt) (hfe : st.fe = [])
    (ha : st.amo = false) (harm : st.armed = true) :
    amB kA (kAa pc) (fun _ st' => false = true → st'.armed = true) (riscvStep tick) st := by
  simp only [releasePcs, List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl
  · obtain ⟨imm, rs2, rs1, hd⟩ := isSw4Of _ relSwDec
    exact amSailOf _ relSwText _ hd relSwRvc relSwAmo true false
      (fun st' ha' h0 => amExecStore imm rs2 rs1 st' ha' (h0 rfl)) tick st hfe ha (fun _ => harm)
  · obtain ⟨u, r1, r2, hd⟩ := isCSwOf _ mainSwDec
    exact amSailOfC _ mainSwText _ hd mainSwRvc mainSwAmo true false
      (fun st' ha' h0 => amExecCSw u r1 r2 st' ha' (h0 rfl)) tick st hfe ha (fun _ => harm)

end PinRelArm
end Weak
