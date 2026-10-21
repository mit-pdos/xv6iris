/-
MachCSL: **the clock tick over the user frames**, as a walk (lane U1-C;
Rocq `HartStepFull.swp_exec_step_waiting`'s tick and HartMCycle's
`tk_clock3`).

`riscvStep tick ew` is `try_step 0 ew` followed, on the nondeterministic
tick, by `tick_clock ()`: since sail-riscv 0.16 just `mcycle` (if counting)
and `mtime` -- the timer interrupt is pulled into `mip` by the NEXT cycle's
prologue (`UCycle.uc_updateMip`), not by the tick.  Over the user frames it is
one walk that moves only clock cells (Rocq `tk_clock3`): `uc_tickClock` --
the landing agrees with the start off `mcycle`/`mtime`/`mip`
(`ucClockAgree`; `mip` no longer moves here, the agreement keeps its old
shape), bytes and reservation bit untouched.  The branch on symbolic data
(the `mcycle` enable) is split in the proof.
-/
import MachCSL.UCycle

noncomputable section

namespace MachCSL

open Sail Sail.ArchSem
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions
open Register

/-- What the tick reads and writes: the counter enables and the clock cells.  (The other
fields -- `mip`, the timer compares, `menvcfg`, the PLIC wires -- are what the 0.15 tick also
read; sail-riscv 0.16 moved that to the cycle's prologue, `UcFoot`.  They are kept so that the
footprint's statement does not move.) -/
structure UcTickFoot (D : UFoot) : Prop where
  rd_priv : D.Dr .cur_privilege = true
  rd_mcountinhibit : D.Dr .mcountinhibit = true
  rd_mcyclecfg : D.Dr .mcyclecfg = true
  rd_mcycle : D.Dr .mcycle = true
  wr_mcycle : D.Dw .mcycle = true
  rd_mtime : D.Dr .mtime = true
  wr_mtime : D.Dw .mtime = true
  rd_mip : D.Dr .mip = true
  wr_mip : D.Dw .mip = true
  rd_mtimecmp : D.Dr .mtimecmp = true
  rd_stimecmp : D.Dr .stimecmp = true
  rd_menvcfg : D.Dr .menvcfg = true
  meip_nr : D.Dr .sig_meip = false
  meip_any : D.Dany .sig_meip = true
  seip_nr : D.Dr .sig_seip = false
  seip_any : D.Dany .sig_seip = true

/-- Two walker states agree off the three clock cells (Rocq
`reg_agree_on (D ∖ tk_clock3)`), with the same bytes and reservation bit. -/
def ucClockAgree (s s' : UWSt) : Prop :=
  s'.mm = s.mm ∧ s'.rv = s.rv ∧
    ∀ r, r ≠ .mcycle → r ≠ .mtime → r ≠ .mip → s'.file r = s.file r

theorem ucClockAgree_refl (s : UWSt) : ucClockAgree s s := ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

theorem ucClockAgree_setR (s : UWSt) (r : Register) (v : RegisterType r)
    (h : r = .mcycle ∨ r = .mtime ∨ r = .mip) : ucClockAgree s (s.setR r v) := by
  refine ⟨rfl, rfl, fun x h1 h2 h3 => UWSt.setR_file_other _ _ _ _ ?_⟩
  rcases h with rfl | rfl | rfl <;> assumption

theorem ucClockAgree_trans {s s' s'' : UWSt} (h1 : ucClockAgree s s') (h2 : ucClockAgree s' s'') :
    ucClockAgree s s'' :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r a b c => (h2.2.2 r a b c).trans (h1.2.2 r a b c)⟩

variable {D : UFoot}

/-- **The clock tick** (over any user frame): one walk, moving only
`mcycle`/`mtime` (Rocq `tk_clock3`). -/
theorem uc_tickClock (hT : UcTickFoot D) (orc : UOrc) (s : UWSt) (_hm : UcMisa D s) :
    ∃ s' orc', runRW D orc s (tick_clock ()) = some ((), s', orc') ∧ ucClockAgree s s' := by
  simp only [tick_clock, clint_tick_clock, should_inc_mcycle, bind_assoc,
    MachCSL.uxa_readReg_bind D _ _ _ _ hT.rd_priv, MachCSL.uxa_readReg_bind D _ _ _ _ hT.rd_mcountinhibit]
  have rest : ∀ (t : UWSt), ucClockAgree s t →
      ∃ s' orc', runRW D orc t (do
        writeReg mtime (BitVec.addInt (← readReg mtime) 1)) = some ((), s', orc') ∧ ucClockAgree s s' := by
    intro t ht
    rw [MachCSL.uxa_readReg_bind D _ _ _ _ hT.rd_mtime]
    exact ⟨_, orc, ucRW_writeReg_pure D orc t _ _ hT.wr_mtime,
      ucClockAgree_trans ht (ucClockAgree_setR _ _ _ (Or.inr (Or.inl rfl)))⟩
  -- `mcyclecfg` is read only under `mcountinhibit.CY = 0`
  split
  · simp only [bind_assoc, pure_bind, MachCSL.uxa_readReg_bind D _ _ _ _ hT.rd_mcyclecfg]
    split
    · simp only [MachCSL.uxa_readReg_bind D _ _ _ _ hT.rd_mcycle, ucRW_writeReg D _ _ _ _ _ hT.wr_mcycle]
      exact rest _ (ucClockAgree_setR _ _ _ (Or.inl rfl))
    · try simp only [pure_bind]
      exact rest s (ucClockAgree_refl s)
  · simp only [pure_bind, Bool.false_eq_true, ↓reduceIte]
    exact rest s (ucClockAgree_refl s)

end MachCSL
