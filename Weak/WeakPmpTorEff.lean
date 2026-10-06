/-
Weak: **the `execEff` twin of the PMP TOR-entry-0 grant**.

Rocq: `iris/WeakPmpTorEff.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakPmpEff` mirrors the all-OFF / unlocked arms
of the PMP cone at `execEff`; once `start()` has written pmpaddr0/pmpcfg0 (a TOR
entry covering all of RAM) every later data access is granted by the entry-0
full-match arm instead, i.e. by `ExecSC3.execPmpCheckMachineTor0`.  This file is
that arm's `execEff` twin, and nothing else.  The method is the name swap
(`execBind` ↦ `execEffBindNil`, `execRBind` ↦ `execREffBindEq`, `execRLiftR` ↦
`execREffLiftRSeq`, `execCatchEarlyReturn` ↦ `execEffCatchEarlyReturn`, the loop's
first iteration as in SC); the pure pieces `pmpRangeMatch_full` and
`pmpTor0Grants` are REUSED from `Weak/ExecSC3.lean`.  Every trace here is
literally `[]`: the PMP cone is register-only.

**Deviations from Rocq.**
1. Vocabulary as `Weak/ExecSC3.lean` (conventions and deviation 1): `uint x` ↦
   `x.toNat`, `Z` widths/indices ↦ `Nat`, `vec_access_dec v i` ↦ `v[i]!`,
   `register_lookup r s.(sregs)` ↦ `s.regs r`, `zeros' 64` ↦ `zeros (n := 64)`,
   `returnM` / `Defs.returnm` ↦ `pure`, `Defs.monadR R exception X` ↦ `SailME R X`.
2. `exec_eff_pmpReadAddrReg`: the Lean grain is `0`, so the read is the stored
   value with no case split on the match type (as `ExecSC3.execPmpReadAddrReg`).
3. `exec_eff_pmpCheck_machine_tor0`: the Rocq `foreach_ZM_up` unrolling is
   lean-sail's `IntRange` `forIn`; its first-iteration early exit is the Lean-only
   `execREffForInFirstEarly` (the `execEff` twin of `ExecSC2.execRForInFirstEarly`).
4. Rocq `Local Lemma`s are ordinary theorems here (unique names).
5. Rocq §4's `Print Assumptions` is not a declaration (no Lean twin).

**Rocq → Lean name map.**  `wpte_exec_eff_returnM` ↦ `wpteExecEffReturnM`,
`wpte_execR_eff_returnm_fwd` ↦ `wpteExecREffReturnmFwd`,
`exec_eff_pmpReadAddrReg` ↦ `execEffPmpReadAddrReg`,
`exec_eff_pmpMatchAddr_tor0_match` ↦ `execEffPmpMatchAddrTor0Match`,
`exec_eff_pmpCheck_machine_tor0` ↦ `execEffPmpCheckMachineTor0`.
Lean-only: `execREffForInFirstEarly`.

**Dropped:** nothing (Rocq 5 lemmas; Lean 5 + 1 Lean-only).
-/
import Weak.WeakEffSkel
import Weak.ExecSC3

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 0. The two trivial twins -/

theorem wpteExecEffReturnM {X : Type} (x : X) (s : ExecSt) :
    execEff (pure x : SailM X) s = some (x, s, []) := rfl

theorem wpteExecREffReturnmFwd {R X : Type} (x : X) (s : ExecSt) :
    execREff (pure x : SailME R X) s = some (.inr x, s, []) := rfl

/-! ## 1. `pmpReadAddrReg`, at its exact value -/

theorem execEffPmpReadAddrReg (n : Nat) (s : ExecSt) :
    execEff (pmpReadAddrReg n) s = some ((s.regs .pmpaddr_n)[n]!, s, []) := by
  unfold pmpReadAddrReg
  rw [execEffBindNil _ _ _ _ _ (execEffReadReg .pmpcfg_n s)]
  rw [execEffBindNil _ _ _ _ _ (wpteExecEffReturnM _ s)]
  rw [execEffBindNil _ _ _ _ _ (execEffReadReg .pmpaddr_n s)]
  rw [execEffBindNil _ _ _ _ _ (wpteExecEffReturnM _ s)]
  split <;> rfl

/-! ## 2. The entry-0 TOR full match -/

theorem execEffPmpMatchAddrTor0Match (a wbv : BitVec 64) (ent : BitVec 8) (paddr : BitVec 64)
    (s : ExecSt) (hA : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A ent) = .TOR)
    (hw : 0 < wbv.toNat) (hin : a.toNat + wbv.toNat ≤ paddr.toNat * 4) :
    execEff (pmpMatchAddr (.Physaddr a) wbv ent paddr (zeros (n := 64))) s =
      some (.PMP_Match, s, []) := by
  have hz : (zeros (n := 64)).toNat = 0 := rfl
  have hlt : zopz0zKzJ_u (zeros (n := 64)) paddr = false := by
    unfold zopz0zKzJ_u
    simp only [decide_eq_false_iff_not, BitVec.toNatInt, Int.ofNat_eq_natCast, hz]
    omega
  have hr : pmpRangeMatch ((zeros (n := 64)).toNat * 4) (paddr.toNat * 4) a.toNat wbv.toNat =
      .PMP_Match :=
    pmpRangeMatch_full _ _ _ _ (by rw [hz]; exact Nat.zero_le _) hw hin
  unfold pmpMatchAddr
  simp only [hA, hlt, Bool.false_eq_true, ↓reduceIte, toNatInt_mul4_toNat, toNatInt_toNat, hr]
  rfl

/-! ## 3. The reduction -/

/-- The first iteration of an `IntRange` loop early-returns (Lean-only; the
`execEff` twin of `ExecSC2.execRForInFirstEarly`). -/
theorem execREffForInFirstEarly {R : Type} (range : IntRange)
    (f : Int → Unit → SailME R (ForInStep Unit)) (s s' : ExecSt) (r : R) (es : List Weff)
    (h0 : range.start ∈ range) (hf : execREff (f range.start ()) s = some (.inl r, s', es)) :
    execREff (forIn range () f) s = some (.inl r, s', es) := by
  show execREff (IntRange.forIn'.loop range (fun a _ b => f a b) () range.start (by simp)) s = _
  rw [IntRange.loop_unfold]
  simp only [dif_pos h0]
  rw [execREffBindEq, hf]

theorem execEffPmpCheckMachineTor0 (addr : BitVec 64) (width : Nat)
    (access : MemoryAccessType mem_payload) (s : ExecSt)
    (hg : pmpTor0Grants (s.regs .pmpcfg_n) (s.regs .pmpaddr_n) addr width)
    (hrwx : ∀ ent, ∃ b, execEff (pmpCheckRWX ent access) s = some (b, s, []))
    (hwidth : (to_bits (l := 64) width).toNat = width) :
    execEff (pmpCheck (.Physaddr addr) width access .Machine) s = some (none, s, []) := by
  obtain ⟨hA, hL, hw, hin⟩ := hg
  have hA' : pmpAddrMatchType_encdec_backwards (_get_Pmpcfg_ent_A (s.regs .pmpcfg_n)[(0 : Int)]!) =
      .TOR := hA
  have hL' : pmpLocked (s.regs .pmpcfg_n)[(0 : Int)]! = false := hL
  obtain ⟨b, hb⟩ := hrwx (s.regs .pmpcfg_n)[(0 : Int)]!
  have hm := execEffPmpMatchAddrTor0Match addr (to_bits (l := 64) width) _ (s.regs .pmpaddr_n)[0]! s
    hA' (by rw [hwidth]; exact hw) (by rw [hwidth]; exact hin)
  have hrd : execEff (pmpReadAddrReg (0 : Int).toNat) s = some ((s.regs .pmpaddr_n)[0]!, s, []) :=
    execEffPmpReadAddrReg 0 s
  unfold pmpCheck
  rw [execEffCatchEarlyReturn]
  have hc : (sys_pmp_count == 0) = false := by decide
  simp only [hc, Bool.false_eq_true, ↓reduceIte]
  rw [execREffBindEq, execREffForInFirstEarly _ _ s s none [] (by decide)]
  dsimp only
  rw [if_neg (by decide)]
  rw [execREffBindNil _ _ _ _ _ (wpteExecREffReturnmFwd _ s),
    execREffLiftRSeq _ _ _ _ _ (execEffReadReg .pmpcfg_n s),
    execREffBindNil _ _ _ _ _ (wpteExecREffReturnmFwd _ s),
    execREffLiftRSeq _ _ _ _ _ hrd, execREffLiftRSeq _ _ _ _ _ hm]
  dsimp only
  rw [execREffLiftRSeq _ _ _ _ _ hb]
  cases b
  · simp only [hL', Bool.false_or, Functions.not]
    rfl
  · rfl

end Weak
