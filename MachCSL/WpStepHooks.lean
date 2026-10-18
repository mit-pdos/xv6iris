/-
MachCSL: the per-step hooks sail-riscv 0.16 runs around every instruction,
proved once.

* `swp_read_mip_any`: the effective pending word the interrupt check reads
  (`read_mip .IncludePlatformInterrupts`), `mip` ORed with the interrupt PINS
  (read off-frame) and the H-extension wires (`hgeie`, off the frozen bundle):
  an ARBITRARY word.  (Moved here from `MachCSL.WpTrap` so that `WpSmode`, which
  does not import the trap, can use it too.)
* `swp_update_mip` (and the script `cycle_prologue`): the per-cycle prologue of
  `try_step` -- 0.16 pulls the timer and software interrupts into `mip` at the
  start of EVERY cycle rather than at the tick: `mip := mipUpd ...`, from the
  CLINT's `msip`, `mtime`, `mtimecmp`, and `stimecmp` under `menvcfg.STCE`.
* `swp_prevent_reentrance`: the Sdtrig breakpoint-reentrancy check every
  active step makes before its fetch (`Use_interrupt_enables`: `mstatus.MIE`
  in M-mode, `medeleg`'s breakpoint bit and `mstatus.SIE` in S-mode); its
  answer only feeds the (disabled) icount triggers, so it is left arbitrary.
-/
import MachCSL.ModelFacts
import MachCSL.PlatformFacts
import MachCSL.MConf
import MachCSL.Tactics
import MachCSL.BvEnums -- `bv_decide`'s enum encodings, declared once

noncomputable section

namespace MachCSL

open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Std
open Sail Sail.ArchSem
open LeanRV64D LeanRV64D.Functions

variable {GF : BundledGFunctors.{0}} [MachGS GF]

set_option maxHeartbeats 4000000 in
/-- The effective pending word the interrupt check reads (`read_mip`): `mip`
ORed with the interrupt PINS (`sig_meip`/`sig_seip`, read off-frame) and with
the H-extension wires (`hgeie`, off the frozen bundle; H is disabled, so they
contribute nothing).  The answer is an ARBITRARY word: the pins are not in the
hart's frame.  `mip` itself is owned and unmoved. -/
theorem swp_read_mip_any (cpu : CPU) (ip : BitVec 64) (Φ : BitVec 64 → IProp GF) :
    hwConfig cpu ∗ Register.mip ↦ᵣ[cpu] ip ∗ ▷ (∀ ip', Register.mip ↦ᵣ[cpu] ip -∗ Φ ip')
    ⊢ swp cpu (read_mip .IncludePlatformInterrupts) Φ := by
  iintro ⟨#Hhw, Hmip, HΦ⟩
  unfold read_mip
  swp_run 60
  iapply HΦ $$ Hmip

/-- A cell's value rewritten by an equation. -/
theorem regPointsTo_of_eq (cpu : CPU) (r : Register) (a b : RegisterType r) (h : a = b) :
    (r ↦ᵣ[cpu] a : IProp GF) ⊢ r ↦ᵣ[cpu] b := h ▸ .rfl

/-- `mip` after the per-cycle refresh `update_mip` (sail-riscv 0.16): `MSIP := msip[0]` (the
CLINT's software-interrupt register), `MTIP := mtimecmp ≤ mtime`, and, when `menvcfg.STCE` is set
(Sstc), `STIP := stimecmp ≤ mtime` (unsigned compares); every other bit kept.  (The model masks
the word to the supported interrupts, which on this platform are all of them; the H wires are
off.) -/
def mipUpd (ip : BitVec 64) (ms : BitVec 32) (mt tcmp scmp envcfg : BitVec 64) : BitVec 64 :=
  let m := Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange ip 3 3 (BitVec.access ms 0)) 7 7
    (bool_to_bit (zopz0zIzJ_u tcmp mt))
  if BitVec.extractLsb' 63 1 envcfg = 1#1 then
    Sail.BitVec.updateSubrange m 5 5 (bool_to_bit (zopz0zIzJ_u scmp mt))
  else m

set_option maxHeartbeats 4000000 in
/-- **The per-cycle prologue** `update_mip` (sail-riscv 0.16 `try_step`): `mip` is refreshed from
the CLINT (`msip`, `mtime`, `mtimecmp`) and the Sstc compare (`stimecmp`, under `menvcfg.STCE`) to
`mipUpd ...`; when it changed, the model reads the effective word (pins and all) for its write
callback, which does nothing. -/
theorem swp_update_mip (cpu : CPU) (dq : DFrac) (ip : BitVec 64) (ms : BitVec 32)
    (mt tcmp scmp envcfg : BitVec 64) (Φ : Unit → IProp GF) :
    hwConfig cpu ∗ Register.mip ↦ᵣ[cpu] ip ∗ Register.msip ↦ᵣ[cpu] ms ∗ Register.mtime ↦ᵣ[cpu] mt ∗
    Register.mtimecmp ↦ᵣ[cpu]{dq} tcmp ∗ Register.stimecmp ↦ᵣ[cpu]{dq} scmp ∗
    Register.menvcfg ↦ᵣ[cpu]{dq} envcfg ∗
    ▷ (Register.mip ↦ᵣ[cpu] mipUpd ip ms mt tcmp scmp envcfg -∗ Register.msip ↦ᵣ[cpu] ms -∗
      Register.mtime ↦ᵣ[cpu] mt -∗ Register.mtimecmp ↦ᵣ[cpu]{dq} tcmp -∗
      Register.stimecmp ↦ᵣ[cpu]{dq} scmp -∗ Register.menvcfg ↦ᵣ[cpu]{dq} envcfg -∗ Φ ())
    ⊢ swp cpu (update_mip ()) Φ := by
  iintro ⟨#Hhw, Hmip, Hmsip, Hmtime, Hmtimecmp, Hstimecmp, Hmenvcfg, HΦ⟩
  unfold update_mip
  swp_run 80
  cases hst : (BitVec.extractLsb' 63 1 envcfg == 1#1)
  · swp_run 80
    ihave Hmip := regPointsTo_of_eq cpu Register.mip _ (mipUpd ip ms mt tcmp scmp envcfg) ?h $$ Hmip
    case h =>
      have : BitVec.extractLsb' 63 1 envcfg ≠ 1#1 := by simpa using hst
      simp only [mipUpd, this, ite_false, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
        BitVec.access, bool_to_bit, bool_bit_forwards, zopz0zIzJ_u]
      by_cases hle : tcmp.toNat ≤ mt.toNat <;> simp [BitVec.toNatInt, hle] <;> bv_decide
    split
    · swp_run 40
      iapply HΦ $$ Hmip Hmsip Hmtime Hmtimecmp Hstimecmp Hmenvcfg
    · swp_run 40
      iapply HΦ $$ Hmip Hmsip Hmtime Hmtimecmp Hstimecmp Hmenvcfg
  · swp_run 80
    ihave Hmip := regPointsTo_of_eq cpu Register.mip _ (mipUpd ip ms mt tcmp scmp envcfg) ?h $$ Hmip
    case h =>
      have : BitVec.extractLsb' 63 1 envcfg = 1#1 := by simpa using hst
      simp only [mipUpd, this, ite_true, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
        BitVec.access, bool_to_bit, bool_bit_forwards, zopz0zIzJ_u]
      by_cases hle : tcmp.toNat ≤ mt.toNat <;> by_cases hle' : scmp.toNat ≤ mt.toNat <;>
        simp [BitVec.toNatInt, hle, hle'] <;> bv_decide
    split
    · swp_run 40
      iapply HΦ $$ Hmip Hmsip Hmtime Hmtimecmp Hstimecmp Hmenvcfg
    · swp_run 40
      iapply HΦ $$ Hmip Hmsip Hmtime Hmtimecmp Hstimecmp Hmenvcfg

/-- **The Sdtrig breakpoint-reentrancy check** (`prevent_reentrance TA_Breakpoint p`, run by
every active step before its fetch since 0.16) in machine or supervisor mode: it reads `mstatus`
(M) or `medeleg` and maybe `mstatus` (S), and its answer is left arbitrary (it only feeds the
disabled icount triggers). -/
theorem swp_prevent_reentrance (cpu : CPU) (dq : DFrac) (p : Privilege)
    (hp : p = Privilege.Machine ∨ p = Privilege.Supervisor)
    (ms md : BitVec 64) (Φ : Bool → IProp GF) :
    Register.mstatus ↦ᵣ[cpu]{dq} ms ∗ Register.medeleg ↦ᵣ[cpu]{dq} md ∗
    ▷ (∀ b, Register.mstatus ↦ᵣ[cpu]{dq} ms -∗ Register.medeleg ↦ᵣ[cpu]{dq} md -∗ Φ b)
    ⊢ swp cpu (prevent_reentrance Trig_Action.TA_Breakpoint p) Φ := by
  iintro ⟨Hmstatus, Hmedeleg, HΦ⟩
  unfold prevent_reentrance
  rcases hp with rfl | rfl
  · swp_run 20
    iapply HΦ $$ Hmstatus Hmedeleg
  · swp_run 20
    split
    · swp_run 20
      iapply HΦ $$ Hmstatus Hmedeleg
    · swp_run 20
      iapply HΦ $$ Hmstatus Hmedeleg

set_option hygiene false in
/-- The 0.16 prologue of a cycle, `try_step`'s `update_mip ()` (`swp_update_mip`), over the cells
named `Hhw`, `Hmip`, `Hmsip`, `Hmtime`, `Hmtimecmp`, `Hstimecmp`, `Hmenvcfg`. -/
macro "cycle_prologue" : tactic =>
  `(tactic| (generalize hU : update_mip () = U
             swp_run 5
             subst hU
             iapply swp_bind
             iapply swp_update_mip
             iframe Hhw Hmip Hmsip Hmtime Hmtimecmp Hstimecmp Hmenvcfg
             inext
             iintro Hmip Hmsip Hmtime Hmtimecmp Hstimecmp Hmenvcfg))

end MachCSL
