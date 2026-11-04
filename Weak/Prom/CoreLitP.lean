/-
Weak/Prom: **row 38, MP-ptr no-fault, proved IN THE LOGIC through guarded Ψ on its doomed branch** (stage S2; plan
rev 7 §5 row 38, §2 "Ψ … in guarded form ⟦V⟧⌜Ψ h τ′⌝ … After a racy read of a not-yet-valid value, the hart keeps
executing on a branch that no valid run takes, for example dereferencing junk.  An unguarded 'no fault' may be false
there.  The guarded form is proved there from ⟦s⟧False", §8 S2 "row 38 proved through guarded Ψ on its doomed
branch").

## The fault event (the minimal extension of the label-level front end)

`litStep` (MachCert.lean) has no fault: a load at any aligned address simply reads.  Row 38 is about ACCESS FAULTS
(the privileged spec's physical-memory attributes: an access to a region the PMAs do not allow "raises an
access-fault exception" instead of performing the access), so the front end needs one event for it.  The minimal
faithful extension, `litStepF acc` (this file; MachCert.lean and Machine.lean are unchanged):
* `acc : Nat → Bool` is the PMA's accessible set (here: the three 8-byte locations the test uses);
* a hart whose next instruction is a load at an address outside `acc` emits the label `LSilent` (machine v2's
  answer-free, view-free label: the faulting load performs no memory access) and traps; the trap handler is not
  modelled, so the hart stops (`pc := |prog|`);
* every other step is `litStep`'s.  `litStep` itself never emits `LSilent`, so in a `litStepF` trace an `LSilent`
  entry IS a load-access fault.
What is NOT modelled (and must wait for the Sail-level front end, `Weak/Prom/Emit.lean`): the trap's architectural
effects (CSR writes, the handler's own memory accesses), misaligned-access faults (`litStep` gets stuck instead),
and store/fetch faults.  For row 38 none matters: the claim is that no valid run reaches a faulting access.

## The proof

π = `πPtr`, the protocol "p holds &x or &z" byte-wise (`ptrByte`).  Ψ: H0's memory entries are two loads, the second
at an accessible address; H1's is one store.  H1 discharges its store's protocol obligation outright (it stores &z).
H0's first load reads the 8 bytes of p from sources `t_j`; under `Valid(|M|)` each byte meets `ptrByte` (the image's
by PO-img, a message's by its own protocol), so the pointer is &x or &z — accessible.  On the DOOMED branch (the
pointer is not accessible, possible only for a junk value no valid run reads) the fault step's obligation is
`⟦|M|⟧⌜Ψ⌝`, proved from `⟦|M|⟧False`; on the live branch the second load is an ordinary `wpK_ld`.  A0's export (iv)
gives `Valid(|M|)` in every valid run, (ii) removes the guard: no trace of any valid run contains a fault.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.CoreLitM

namespace Weak.Prom.PF

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64 aluOp brEval amoOp sext byteList bytesVal FenceSet AmoOp)
open Weak.Prom.Ref.Lit (X Y Z A)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The faulting front end -/

/-- The access-fault condition at `s`: the next instruction is a load whose address the PMA does not allow. -/
def faultsAt (acc : Nat → Bool) (s : LP) : Bool :=
  match s.q, s.prog[s.pc]? with
  | [], some (.load _ _ _ rs1 off) => !acc ((s.rd rs1 + off) % two64)
  | _, _ => false

/-- One label of a litmus hart with load-access faults: a faulting load emits `LSilent` and the hart stops. -/
def litNextF (acc : Nat → Bool) (s : LP) (l : PLabel) : Option LP :=
  if faultsAt acc s = true then (if l = LSilent then some { s with pc := s.prog.length, q := [] } else none)
  else litNext s l

/-- THE PROGRAM HALF WITH FAULTS. -/
def litStepF (acc : Nat → Bool) (s : LP) (_ : Unit) (l : PLabel) (s' : LP) (_ : Unit) : Prop :=
  litNextF acc s l = some s'

theorem faultsAt_q {acc : Nat → Bool} {s : LP} (h : s.q ≠ []) : faultsAt acc s = false := by
  unfold faultsAt; split
  · next hq _ => exact absurd hq h
  · rfl

theorem faultsAt_end {acc : Nat → Bool} {s : LP} (h : s.prog.length ≤ s.pc) : faultsAt acc s = false := by
  unfold faultsAt; rw [List.getElem?_eq_none h]; split <;> simp_all

theorem faultsAt_nonload {acc : Nat → Bool} {s : LP} {ins : Instr} (hp : s.prog[s.pc]? = some ins)
    (hn : ∀ sz sg rd rs1 off, ins ≠ .load sz sg rd rs1 off) : faultsAt acc s = false := by
  unfold faultsAt; rw [hp]; split
  · next _ heq => cases heq; exact absurd rfl (hn _ _ _ _ _)
  · rfl

theorem litAgF {V : Type} {acc : Nat → Bool} (pdone : LP → Option V) (img : Image) (M : List PMsg) (h : Nat)
    {s : LP} (hf : faultsAt acc s = false) : LitAg (⟨litStepF acc, pdone, img, M, h⟩ : HW LP Unit V) s := by
  intro l s'
  constructor
  · rintro ⟨_, _, hs⟩
    simp only [litStepF, litNextF, hf, Bool.false_eq_true, if_false] at hs
    exact hs
  · intro hs
    refine ⟨(), (), ?_⟩
    simp only [litStepF, litNextF, hf, Bool.false_eq_true, if_false]
    exact hs

theorem litWF (acc : Nat → Bool) (img : Image) (M : List PMsg) (h : Nat) :
    LitW (⟨litStepF acc, litDone, img, M, h⟩ : HW LP Unit Unit) := by
  refine ⟨fun s hs => litAgF _ _ _ _ (faultsAt_q hs), fun s hs => ?_⟩
  rcases hs with hs | hs
  · exact litDone_q hs
  · exact litDone_pc hs

theorem devFree_litF (acc : Nat → Bool) (ps : List LP) : devFreeProg (litStepF acc) ps := by
  intro _ _ _ _ _ d l p' d' hs
  cases d; cases d'
  exact ⟨rfl, fun d0 => by cases d0; exact hs⟩

section rule

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **THE FAULT STEP** (the lifting lemma at a faulting state): the hart emits `LSilent` and stops; the client proves
the guarded trace invariant of the new trace — on a doomed branch, from `⟦V⟧False`. -/
theorem wpK_fault {img : Image} {M : List PMsg} {h : Nat} {acc : Nat → Bool} {γ : GName} {π : Proto}
    {Q : Trace → Prop} {Φ : Unit → IProp GF} {s : LP} {ws : PState} {pr : GSet Nat} {ev : Trace}
    (hf : faultsAt acc s = true) (hd : litDone s = none) :
    lh γ π ⟨litStepF acc, litDone, img, M, h⟩ Q ws pr ev ∗
    ▷ (⌜∃ V, grd π img M V (Q (ev ++ [(LSilent, none)]))⌝ ∗
       (lh γ π ⟨litStepF acc, litDone, img, M, h⟩ Q ws pr (ev ++ [(LSilent, none)]) -∗
         wpK γ π ⟨litStepF acc, litDone, img, M, h⟩ Q { s with pc := s.prog.length, q := [] } Φ))
    ⊢ wpK γ π ⟨litStepF acc, litDone, img, M, h⟩ Q s Φ := by
  iintro ⟨⟨%τ, Hst, %hinv⟩, Hk⟩
  obtain ⟨he, hw, _⟩ := hinv
  iapply (wpH_any (Ψ := ΨK M Q) (w := ⟨litStepF acc, litDone, img, M, h⟩) hd)
  iframe Hst
  inext
  icases Hk with ⟨%hQ, Hk⟩
  iintro %l %ots %s' %ws' %pr' %hp %hm Hc
  obtain ⟨_, _, hp⟩ := hp
  simp only [litStepF, litNextF, hf, if_true] at hp
  split at hp
  · next hl =>
    subst hl
    cases hp
    cases hm
    obtain ⟨V', hg⟩ := hQ
    imodintro
    isplitr
    · ipureintro
      exact ⟨⟨V', fun hv => ⟨by rw [memEv_snoc _ _ rfl, he]; exact hg hv, wrOk_snoc_none hw⟩⟩, fun t ht => by cases ht⟩
    · iintro Hst
      iapply Hk
      iexists τ ++ [(LSilent, none)]
      iframe Hst
      ipureintro
      exact ⟨by rw [memEv_snoc _ _ rfl, he], wrOk_snoc_none hw, V', hg⟩
  · cases hp

end rule

/-! ## 2. The test, the protocol -/

/-- Row 38: `p = 0x4000` holds &x initially; H0 `ld a0,(p); ld a1,0(a0)` ‖ H1 `li t,&z; sd t,(p)`. -/
def mpPtr : Test :=
  Weak.Prom.Ref.Lit.mk [[.load 8 true 10 8 0, .load 8 true 11 10 0], [.alui .add 5 0 Z, .store 8 5 8 0]]
    [[(8, A)], [(8, A)]] (Weak.Prom.Ref.Lit.ini A X) .tt

/-- The PMA's accessible set: the test's three locations. -/
def accPtr (a : Nat) : Bool := a == X || a == Z || a == A

/-- Byte `j` of &x or &z (they differ only in byte 1: 0x10 / 0x30). -/
def ptrByte (j : Nat) (b : BitVec 8) : Prop := if j = 1 then (b = 0x10 ∨ b = 0x30) else b = 0

/-- THE PROTOCOL of row 38: every byte written at `p + j` (and the image's) is byte `j` of &x or &z. -/
def πPtr : Proto :=
  ⟨fun m => ∀ j : Nat, j < 8 → ∀ b, m.byteAt ((A : Int) + (j : Int)) = some b → ptrByte j b,
   fun img => ∀ j : Nat, j < 8 → ∀ b, img ((A : Int) + (j : Int)) = some b → ptrByte j b⟩

theorem ptr_img : ∀ j : Nat, j < 8 → testImg mpPtr ((A : Int) + (j : Int)) = some (if j = 1 then 0x10 else 0) := by
  intro j hj
  match j, hj with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide

theorem ptr_st (t : Option Nat) (c : PClass) : ∀ j : Nat, j < 8 →
    (⟨(A : Int), toBytes Z 8, t, c⟩ : PMsg).byteAt ((A : Int) + (j : Int)) = some (if j = 1 then 0x30 else 0) := by
  intro j hj
  match j, hj with
  | 0, _ => show (⟨(A : Int), toBytes Z 8, none, .plain⟩ : PMsg).byteAt _ = _; decide
  | 1, _ => show (⟨(A : Int), toBytes Z 8, none, .plain⟩ : PMsg).byteAt _ = _; decide
  | 2, _ => show (⟨(A : Int), toBytes Z 8, none, .plain⟩ : PMsg).byteAt _ = _; decide
  | 3, _ => show (⟨(A : Int), toBytes Z 8, none, .plain⟩ : PMsg).byteAt _ = _; decide
  | 4, _ => show (⟨(A : Int), toBytes Z 8, none, .plain⟩ : PMsg).byteAt _ = _; decide
  | 5, _ => show (⟨(A : Int), toBytes Z 8, none, .plain⟩ : PMsg).byteAt _ = _; decide
  | 6, _ => show (⟨(A : Int), toBytes Z 8, none, .plain⟩ : PMsg).byteAt _ = _; decide
  | 7, _ => show (⟨(A : Int), toBytes Z 8, none, .plain⟩ : PMsg).byteAt _ = _; decide

theorem po_img_ptr : PO_img πPtr (testImg mpPtr) := by
  intro j hj b hb
  rw [ptr_img j hj] at hb
  cases hb
  unfold ptrByte; split <;> simp_all

theorem ptr_okSt (t : Option Nat) (c : PClass) : πPtr.okMsg ⟨(A : Int), toBytes Z 8, t, c⟩ := by
  intro j hj b hb
  rw [ptr_st t c j hj] at hb
  cases hb
  unfold ptrByte; split <;> simp_all

/-- Under `Valid(|M|)`, a byte the memory holds at `p + j` meets `ptrByte j`. -/
theorem valid_ptr {img : Image} {M : List PMsg} (hv : Valid πPtr img M M.length) {t j : Nat} {v : BitVec 8}
    (hj : j < 8) (hb : memByte img M t ((A : Int) + (j : Int)) = some v) : ptrByte j v := by
  cases t with
  | zero => exact hv.1 j hj v hb
  | succ k =>
    obtain ⟨m, hm, hmb⟩ := memByte_succ hb
    have hk : k < M.length := (List.getElem?_eq_some_iff.1 hm).1
    exact hv.2 (k + 1) (by omega) (by omega) m (by simpa [msgAt] using hm) j hj v hmb

/-- The pointer value of eight bytes meeting `ptrByte` is &x or &z. -/
theorem ptr_val {v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 8} (h0 : ptrByte 0 v0) (h1 : ptrByte 1 v1) (h2 : ptrByte 2 v2)
    (h3 : ptrByte 3 v3) (h4 : ptrByte 4 v4) (h5 : ptrByte 5 v5) (h6 : ptrByte 6 v6) (h7 : ptrByte 7 v7) :
    accPtr (ofBytes [v0, v1, v2, v3, v4, v5, v6, v7] % two64) = true := by
  simp only [ptrByte, if_true, if_neg (by decide : (0 : Nat) ≠ 1), if_neg (by decide : (2 : Nat) ≠ 1),
    if_neg (by decide : (3 : Nat) ≠ 1), if_neg (by decide : (4 : Nat) ≠ 1), if_neg (by decide : (5 : Nat) ≠ 1),
    if_neg (by decide : (6 : Nat) ≠ 1), if_neg (by decide : (7 : Nat) ≠ 1)] at h0 h1 h2 h3 h4 h5 h6 h7
  subst h0 h2 h3 h4 h5 h6 h7
  rcases h1 with rfl | rfl <;> decide

/-! ## 3. The harts -/

/-- H0's Ψ: two loads, the second at an accessible address. -/
def qPtr0 : Trace → Prop :=
  q2 (isLd (A : Int) 8 [.DReg 8]) (fun _ e1 => ∃ b : Nat, accPtr b = true ∧ isLd (b : Int) 8 [.DReg 10] e1)

/-- H1's Ψ: one store of &z at p. -/
def qPtr1 : Trace → Prop := qS (A : Int) (toBytes Z 8) [.DReg 8] [.DReg 5]

section harts

variable {hlc : HasLC} {GF : BundledGFunctors} [GhostVarG GF HSt] [InvGS_gen hlc GF]

/-- **H0 in the logic, with its doomed branch**. -/
theorem ptr0_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP)
    (hprog : s0.prog = [.load 8 true 10 8 0, .load 8 true 11 10 0]) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hlen : s0.regs.length = 32) (ha : s0.rd 8 = A)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a := by assumption) :   -- MachFix-R-b5
    ⊢@{IProp GF} wpPF πPtr ⟨litStepF accPtr, litDone, img, M, h⟩ (ΨK M qPtr0) s0
      (fun _ => iprop(⌜∃ V, grd πPtr img M V True⌝)) := by
  have hw := litWF accPtr img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  have hp0 : s0.prog[s0.pc]? = some (.load 8 true 10 8 0) := by rw [hprog, hpc]; rfl
  have hf0 : faultsAt accPtr s0 = false := by unfold faultsAt; rw [hq, hp0]; simp only [ha]; decide
  iapply (wpK_ld (sz := 8) (sgn := true) (rd := 10) (rs1 := 8) (off := 0) (base := (A : Int)) hw
    (litAgF _ _ _ _ hf0) hq hp0 (alg_of ha (by decide) (by decide)) (base_of ha (by decide)))
  iframe Hl
  inext
  iintro %tvs %hl %hlo
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨tvs, rfl, hl⟩⟩
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hp1 : s1.prog[s1.pc]? = some (.load 8 true 11 10 0) := by rw [hP1, hc1]; rfl
  have hr10 : s1.rd 10 = ldVal true 8 tvs % two64 := LPstep_rd_eq hs1 (by decide) (by rw [hlen]; decide)
  -- under `Valid(|M|)` the pointer is accessible: the bytes of p meet the protocol
  have hacc : Valid πPtr img M M.length → accPtr ((s1.rd 10 + 0) % two64) = true := by
    intro hv
    have hmem := bytesAll_mono (fun a t v h => h.1) _ _ hlo
    rw [hr10, Nat.add_zero, Nat.mod_mod]
    clear hlo hr10
    match tvs, hl, hmem with
    | [(t0, v0), (t1, v1), (t2, v2), (t3, v3), (t4, v4), (t5, v5), (t6, v6), (t7, v7)], _,
        ⟨b0, b1, b2, b3, b4, b5, b6, b7, _⟩ =>
      have := ptr_val (valid_ptr hv (j := 0) (by decide) (by simpa using b0))
        (valid_ptr hv (j := 1) (by decide) (by simpa using b1))
        (valid_ptr hv (j := 2) (by decide) (by rw [show (A : Int) + ((2 : Nat) : Int) = (A : Int) + 1 + 1 by omega]; exact b2))
        (valid_ptr hv (j := 3) (by decide) (by rw [show (A : Int) + ((3 : Nat) : Int) = (A : Int) + 1 + 1 + 1 by omega]; exact b3))
        (valid_ptr hv (j := 4) (by decide) (by rw [show (A : Int) + ((4 : Nat) : Int) = (A : Int) + 1 + 1 + 1 + 1 by omega]; exact b4))
        (valid_ptr hv (j := 5) (by decide)
          (by rw [show (A : Int) + ((5 : Nat) : Int) = (A : Int) + 1 + 1 + 1 + 1 + 1 by omega]; exact b5))
        (valid_ptr hv (j := 6) (by decide)
          (by rw [show (A : Int) + ((6 : Nat) : Int) = (A : Int) + 1 + 1 + 1 + 1 + 1 + 1 by omega]; exact b6))
        (valid_ptr hv (j := 7) (by decide)
          (by rw [show (A : Int) + ((7 : Nat) : Int) = (A : Int) + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]; exact b7))
      have hl8 : ldVal true 8 [(t0, v0), (t1, v1), (t2, v2), (t3, v3), (t4, v4), (t5, v5), (t6, v6), (t7, v7)] =
          ofBytes [v0, v1, v2, v3, v4, v5, v6, v7] := by
        simp only [ldVal, if_true, sext, List.map]; rw [if_neg (by omega)]
      rw [hl8]; exact this
  by_cases hf1 : faultsAt accPtr s1 = true
  · -- THE DOOMED BRANCH: the pointer is not accessible, so `Valid(|M|)` is false: `⟦|M|⟧False`
    have hnot : accPtr ((s1.rd 10 + 0) % two64) = false := by
      unfold faultsAt at hf1; rw [hq1, hp1] at hf1; simpa using hf1
    iapply (wpK_fault hf1 (litDone_pc (by rw [hP1, hc1]; decide)))
    iframe Hl
    inext
    isplitr
    · ipureintro
      exact ⟨M.length, fun hv => absurd (hacc hv) (by rw [hnot]; decide)⟩
    · iintro Hl
      iapply (wpK_end (v := ()) (s := { s1 with pc := s1.prog.length, q := [] })
        (litAgF _ _ _ _ (faultsAt_end (by simp))) rfl (by simp)
        (by show litDone { s1 with pc := s1.prog.length, q := [] } = some (); unfold litDone; simp))
      iframe Hl
      imodintro
      ipureintro
      exact ⟨0, grd_intro trivial⟩
  · -- THE LIVE BRANCH: an ordinary load at an accessible address
    have hf1' : faultsAt accPtr s1 = false := by simpa using hf1
    have hacc1 : accPtr ((s1.rd 10 + 0) % two64) = true := by
      unfold faultsAt at hf1'; rw [hq1, hp1] at hf1'; simpa using hf1'
    have halg : aligned ((s1.rd 10 + 0) % two64) 8 = true := by
      revert hacc1; generalize (s1.rd 10 + 0) % two64 = b; intro hacc1
      simp only [accPtr, Bool.or_eq_true, beq_iff_eq] at hacc1
      rcases hacc1 with (rfl | rfl) | rfl <;> decide
    iapply (wpK_ld (sz := 8) (sgn := true) (rd := 11) (rs1 := 10) (off := 0)
      (base := (((s1.rd 10 + 0) % two64 : Nat) : Int)) hw (litAgF _ _ _ _ hf1') hq1 hp1 halg rfl)
    iframe Hl
    inext
    iintro %tvs1 %hl1 %_
    imodintro
    isplitr
    · ipureintro; exact ⟨0, grd_intro ⟨⟨tvs, rfl, hl⟩, _, hacc1, tvs1, rfl, hl1⟩⟩
    iintro %s2 %hs2 Hl
    obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
    have hend : s2.prog.length ≤ s2.pc := by rw [hP2, hc2]; simp
    iapply (wpK_end (v := ()) (litAgF _ _ _ _ (faultsAt_end hend)) hq2 hend
      (by show litDone s2 = some (); unfold litDone; rw [if_pos ⟨hq2, hend⟩]))
    iframe Hl
    imodintro
    ipureintro
    exact ⟨0, grd_intro trivial⟩

/-- **H1 in the logic**: `li t,&z; sd t,(p)` stores &z, which meets the protocol outright. -/
theorem ptr1_hart (img : Image) (M : List PMsg) (h : Nat) (s0 : LP)
    (hprog : s0.prog = [.alui .add 5 0 Z, .store 8 5 8 0]) (hpc : s0.pc = 0) (hq : s0.q = [])
    (hlen : s0.regs.length = 32) (ha : s0.rd 8 = A) :
    ⊢@{IProp GF} wpPF πPtr ⟨litStepF accPtr, litDone, img, M, h⟩ (ΨK M qPtr1) s0
      (fun _ => iprop(⌜∃ V, grd πPtr img M V True⌝)) := by
  have hw := litWF accPtr img M h
  iapply (wpK_start (by trivial))
  iintro %γ %P0 Hl
  have hp0 : s0.prog[s0.pc]? = some (.alui .add 5 0 Z) := by rw [hprog, hpc]; rfl
  iapply (wpK_alui hw (litAgF _ _ _ _ (faultsAt_nonload hp0 (fun _ _ _ _ _ h => by cases h))) hq hp0 (by decide))
  iframe Hl
  inext
  iintro %s1 %hs1 Hl
  obtain ⟨hP1, hc1, hq1⟩ := LPstep_at hs1 hprog (by rw [hpc])
  have hp1 : s1.prog[s1.pc]? = some (.store 8 5 8 0) := by rw [hP1, hc1]; rfl
  have e1 : s1.rd 8 = A := by rw [LPstep_rd hs1 8 (.inl (by decide)), ha]
  have e5 : s1.rd 5 = Z := li_val hs1 (by decide) (by rw [hlen]; decide) (by decide)
  iapply (wpK_sw (sz := 8) (rs2 := 5) (rs1 := 8) (off := 0) (base := (A : Int)) hw
    (litAgF _ _ _ _ (faultsAt_nonload hp1 (fun _ _ _ _ _ h => by cases h))) hq1 hp1
    (alg_of e1 (by decide) (by decide)) (base_of e1 (by decide)))
  iframe Hl
  inext
  iintro %t %_ %_ %_ %hx
  imodintro
  isplitr
  · ipureintro; exact ⟨0, grd_intro ⟨t, by omega, by simp only [e5, srcR_pos (by decide : (8 : Nat) ≠ 0),
      srcR_pos (by decide : (5 : Nat) ≠ 0)]⟩⟩
  isplitr
  · ipureintro; exact grd_intro (by rw [e5]; exact ptr_okSt _ _)
  iintro %s2 %hs2 Hl
  obtain ⟨hP2, hc2, hq2⟩ := LPstep_at hs2 hP1 (by rw [hc1])
  have hend : s2.prog.length ≤ s2.pc := by rw [hP2, hc2]; simp
  iapply (wpK_end (v := ()) (litAgF _ _ _ _ (faultsAt_end hend)) hq2 hend
    (by show litDone s2 = some (); unfold litDone; rw [if_pos ⟨hq2, hend⟩]))
  iframe Hl
  imodintro
  ipureintro
  exact ⟨0, grd_intro trivial⟩

end harts

/-! ## 4. The verdict -/

def QsPtr : Nat → Trace → Prop
  | 0 => qPtr0
  | 1 => qPtr1
  | _ => q0

/-- MachFix-R-b5: the faulting front end issues no cache-block operation either (LitNoCmo.lean). -/
theorem litF_noInvalT {acc : Nat → Bool} {T : Test} {img : Image} {M : List PMsg} {run : PFRun LP Unit}
    (hv : validRun (litStepF acc) img () (progs T) M run) : ∀ t a, ¬ cmoAt M isInvalK t a := by
  rw [← hv.2]
  refine Own.noInval_of_noCmoLab (fun s => qOk s.q) (fun p hp => by rw [Own.progs_q T p hp]; exact qOk_nil)
    (fun s l s' hq hs => ?_) hv.1
  unfold litStepF litNextF at hs
  split at hs
  · split at hs
    · rename_i hl
      cases hs; subst hl
      exact ⟨qOk_nil, fun _ _ _ _ h => by cases h⟩
    · cases hs
  · exact ⟨Mach.litNext_q hq hs, (Own.litNext_nf hq hs).2⟩

/-- **ROW 38, MP-ptr no-fault: proved IN THE LOGIC** (plan §5 row 38, §2 guarded Ψ, A0 (ii), (iv)): in every valid
run of the faulting front end, no hart's trace contains a load-access fault. -/
theorem lit_mpPtr : ∀ (M : List PMsg) (run : PFRun LP Unit),
    validRun (litStepF accPtr) (testImg mpPtr) () (progs mpPtr) M run →
    ∀ h, ∀ e ∈ run.trace h, e.1 ≠ LSilent := by
  intro M run hrun
  have hnoinv := litF_noInvalT hrun   -- MachFix-R-b5
  obtain ⟨_, hii, _, _, _, _, _⟩ := adequacy (hlc := HasLC.hasLC) (GF := pfGF) (pdone := litDone)
    πPtr (fun _ _ => True) (fun h => ΨK M (QsPtr h)) po_img_ptr (PO_ad_all _ _ _)
    (fun h => match h with | 0 => ⟨trivial, wrOk_nil M⟩ | 1 => ⟨trivial, wrOk_nil M⟩ | _ + 2 => ⟨rfl, wrOk_nil M⟩)
    (devFree_litF accPtr _)
    (fun h p hp _ => by
      obtain ⟨hpr, hpc, hq, hlen, hrd⟩ := progs_get hp
      match h with
      | 0 => exact ptr0_hart _ M 0 p (by rw [hpr]; rfl) hpc hq hlen (by rw [hrd 8 (by decide) (by decide)]; rfl)
      | 1 => exact ptr1_hart _ M 1 p (by rw [hpr]; rfl) hpc hq hlen (by rw [hrd 8 (by decide) (by decide)]; rfl)
      | n + 2 =>
        have hl : (progs mpPtr).length = 2 := rfl
        rw [List.getElem?_eq_none (by omega)] at hp; cases hp) hrun
  intro h e he hs
  have hfin := (hii h (run.trace h).length)
  rw [List.take_length] at hfin
  have hm : e ∈ memEv (run.trace h) := by
    unfold memEv; rw [List.mem_filter]; exact ⟨he, by simp [keepE, hs, quietL]⟩
  have hQ := hfin.1
  match h, hQ with
  | 0, hQ =>
    rcases q2_cases hQ with hev | ⟨e0, hev, ⟨_, rfl, _⟩⟩ | ⟨e0, e1, hev, ⟨_, rfl, _⟩, ⟨_, _, _, rfl, _⟩⟩ <;>
      rw [hev] at hm <;> simp at hm <;> (try rcases hm with rfl | rfl) <;> (try subst hm) <;> cases hs
  | 1, hQ =>
    rcases q1_cases hQ with hev | ⟨e0, hev, ⟨_, _, rfl⟩⟩ <;> rw [hev] at hm <;> simp at hm <;>
      (try subst hm) <;> cases hs
  | n + 2, hQ =>
    have h0 : memEv (run.trace (n + 2)) = [] := hQ
    rw [h0] at hm; cases hm

end Weak.Prom.PF

#print axioms Weak.Prom.PF.lit_mpPtr
