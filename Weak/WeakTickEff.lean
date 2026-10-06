/-
Weak: `MinstretInv`'s **clock-tick cone, at `execEff`** (M4): the `execEff`
twin of `ExecSC7.execTickClock`, i.e. the cone

  `should_inc_mcycle` → `csr_name_write_callback "mip"` →
  `external_interrupts_pending` → `read_mip IncludePlatformInterrupts` →
  `clint_dispatch false` → `tick_clock`

replayed with the trace threaded.

Rocq: `iris/WeakTickEff.v` @ xxvzwolszwmp.

The Rocq header, in substance.  `WeakEffSkel` §6b named two facts between the
weak step assembly and `WeakCert.wPEff`; `WeakFetchEff` supplies the first
(the fetch), THIS FILE the second.  EVERY trace in the cone is `[]`: the tick
is register-only from top to bottom (counter-inhibit / cycle-config / misa /
mip / mtime / mtimecmp / stimecmp / menvcfg / privilege reads; mcycle / mtime /
mip writes), and a register access is not a memory outcome.  It must be `[]`
and not merely `WeakEff.quietTrace`: `WeakCert.wstepConfEff` fixes ONE trace
`es` and quantifies over `tick`, so the tick branch must contribute nothing;
`WeakEff.execEffQuietOfEmpty` can only conclude `quietTrace`, so the cone is
peeled bind by bind.

Sections: §0 the trivial twins (`pure`, the boolean connectives, the
three-tuple `if_some_bool`); §1 the extension-enable probes (`Ext_S`,
`Ext_Sstc`); §2 the cone, ending in `execEffTickClock`.

**Deviations from Rocq.**
1. NAMES and vocabulary: the tree's camelCase (map below); as
   `Weak/WeakEff.lean` deviation 1 and the `Weak/ExecSC*.lean` conventions
   (`register_lookup r s.(sregs)` ↦ `s.regs r`, `eq_vec x 'b"1"` ↦
   `x == 1#1`, `mword 64` ↦ `BitVec 64`, `tt` ↦ `()`,
   `set_reg s r v` ↦ `s.setReg r v`).
2. `Defs.and_boolM` / `Defs.or_boolM` do not exist in the Lean model (its Sail
   backend inlines `&&` / `||` as `do`-`if`s).  `wteExecEffAndBoolMNil` /
   `wteExecEffOrBoolMNil` are stated on the monadic shape those combinators
   unfold to in Rocq (`l >>= fun b => if b then r else pure false`, resp.
   `… then pure true else r`); the cone's proofs below do not need them.
3. `hartSupports` is pure in Lean (`ExecSC*` convention): Rocq
   `exec_eff (hartSupports X) s = Some (true, s, [])` ↦ `hartSupports .X = true`.
   Rocq's fuelled `_rec_currentlyEnabled Ext_Zicsr 0 acc` fact is stated on
   `currentlyEnabled .Ext_Zicsr` (no fuel in Lean).
4. `exec_eff_currentlyEnabled_S`'s value is `_get_Misa_S (s.regs .misa) == 1#1`
   (as `ExecSC2.execCurrentlyEnabledS`).
5. The cone is proved by a `simp` peel over `WeakEff.execEffBindEq` (the
   local tactic `wte_run`) rather than one `erewrite` per bind; the pure
   register-file helpers are `ExecSC7`'s (`ExecSt.setReg_setReg_same`,
   `ExecSt.setReg_self`, `readMipVal`, `tickShape1..4`), the twins of Rocq's
   reused `MinstretInv` helpers.
6. Rocq's `Print Assumptions` command is not a declaration.

**Rocq → Lean name map.**  `wte_exec_eff_returnM` `wteExecEffReturnM`,
`wte_exec_eff_and_boolM_nil` `wteExecEffAndBoolMNil`,
`wte_exec_eff_or_boolM_nil` `wteExecEffOrBoolMNil`, `wte_if_some_bool3`
`wteIfSomeBool3`, `wte_exec_eff_hartSupports_S` `wteExecEffHartSupportsS`,
`wte_exec_eff_hartSupports_Zicsr` `wteExecEffHartSupportsZicsr`,
`wte_exec_eff_hartSupports_Sstc` `wteExecEffHartSupportsSstc`,
`wte_exec_eff_rec_cE_Zicsr` `wteExecEffRecCEZicsr`,
`wte_exec_eff_currentlyEnabled_S` `wteExecEffCurrentlyEnabledS`,
`wte_exec_eff_currentlyEnabled_Sstc` `wteExecEffCurrentlyEnabledSstc`,
`exec_eff_should_inc_mcycle_Some` `execEffShouldIncMcycleSome`,
`exec_eff_csr_name_write_callback_mip` `execEffCsrNameWriteCallbackMip`,
`exec_eff_external_interrupts_pending_Some` `execEffExternalInterruptsPendingSome`,
`exec_eff_read_mip_include_Some` `execEffReadMipIncludeSome`,
`exec_eff_clint_dispatch_false` `execEffClintDispatchFalse`,
`exec_eff_tick_clock` `execEffTickClock`.  Lean-only: the peel kit
`wteExecEffIte`, `wteEffThenIte`, `wteEffThenSome`, `wteEffThenNone`,
`wteMapIte`, `wteMapSome`, `wteMapNone` and the tactic `wte_run`;
`wteExecEffReadMip` (the exact value, `ExecSC7.readMipVal`);
`wteTickShapeLift`.

**Dropped:** nothing (16 Rocq `Lemma`s; Lean 16 + 9 Lean-only).
-/
import Weak.WeakEffSkel
import Weak.ExecSC7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## Lean-only: the `execEff` peel kit (deviation 5) -/

theorem wteExecEffIte {X : Type} (c : Prop) [Decidable c] (a b : SailM X) (s : ExecSt) :
    execEff (if c then a else b) s = if c then execEff a s else execEff b s := by
  split <;> rfl

theorem wteEffThenIte {X Y : Type} (c : Prop) [Decidable c] (a b : Option (X × ExecSt × List Weff))
    (g : X → ExecSt → Option (Y × ExecSt × List Weff)) :
    effThen (if c then a else b) g = if c then effThen a g else effThen b g := by
  split <;> rfl

theorem wteEffThenSome {X Y : Type} (x : X) (s1 : ExecSt) (es : List Weff)
    (g : X → ExecSt → Option (Y × ExecSt × List Weff)) :
    effThen (some (x, s1, es)) g = (g x s1).map (fun r => (r.1, r.2.1, es ++ r.2.2)) := by
  rcases h : g x s1 with _ | ⟨y, s2, es'⟩ <;> simp [effThen, h]

theorem wteEffThenNone {X Y : Type} (g : X → ExecSt → Option (Y × ExecSt × List Weff)) :
    effThen none g = none := rfl

theorem wteMapIte {A B : Type} (f : A → B) (c : Prop) [Decidable c] (a b : Option A) :
    Option.map f (if c then a else b) = if c then Option.map f a else Option.map f b := by
  split <;> rfl

theorem wteMapSome {A B : Type} (f : A → B) (a : A) : Option.map f (some a) = some (f a) := rfl

theorem wteMapNone {A B : Type} (f : A → B) : Option.map f none = none := rfl

/-- Peel register-only binds under `execEff`: the bind law, `if`s pushed out of
`execEff`/`effThen`/`Option.map`, the register events unfolded to their `FreeM`
nodes, and the closed guards. -/
syntax "wte_run" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| wte_run) => `(tactic| simp (config := { decide := true }) only [execEffBindEq,
      wteEffThenIte, wteEffThenSome, wteEffThenNone, wteMapIte, wteMapSome, wteMapNone, wteExecEffIte,
      readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff, execEffReturnm,
      ↓reduceIte, ite_true, ite_false, Bool.false_eq_true, List.nil_append, List.append_nil])
  | `(tactic| wte_run [$ls,*]) => `(tactic| simp (config := { decide := true }) only [execEffBindEq,
      wteEffThenIte, wteEffThenSome, wteEffThenNone, wteMapIte, wteMapSome, wteMapNone, wteExecEffIte,
      readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit, execEff, execEffReturnm,
      ↓reduceIte, ite_true, ite_false, Bool.false_eq_true, List.nil_append, List.append_nil, $ls,*])

/-! ## 0. The trivial twins -/

/-- Rocq `wte_exec_eff_returnM`. -/
theorem wteExecEffReturnM {X : Type} (x : X) (s : ExecSt) :
    execEff (pure x : SailM X) s = some (x, s, []) := rfl

/-- Rocq `wte_exec_eff_and_boolM_nil` (deviation 2). -/
theorem wteExecEffAndBoolMNil (l r : SailM Bool) (s : ExecSt) (bl : Bool) (sl : ExecSt) :
    execEff l s = some (bl, sl, []) →
    execEff (l >>= fun b => if b then r else pure false) s =
      (if bl then execEff r sl else some (false, sl, [])) := by
  intro h
  rw [execEffBindNil _ _ _ _ _ h]
  cases bl <;> rfl

/-- Rocq `wte_exec_eff_or_boolM_nil` (deviation 2). -/
theorem wteExecEffOrBoolMNil (l r : SailM Bool) (s : ExecSt) (bl : Bool) (sl : ExecSt) :
    execEff l s = some (bl, sl, []) →
    execEff (l >>= fun b => if b then pure true else r) s =
      (if bl then some (true, sl, []) else execEff r sl) := by
  intro h
  rw [execEffBindNil _ _ _ _ _ h]
  cases bl <;> rfl

/-- Rocq `wte_if_some_bool3`. -/
theorem wteIfSomeBool3 {A B : Type} (c : Bool) (x : A) (y : B) :
    (if c then some (true, x, y) else some (false, x, y) : Option (Bool × A × B)) = some (c, x, y) := by
  cases c <;> rfl

/-! ## 1. The extension-enable probes (deviation 3) -/

/-- Rocq `wte_exec_eff_hartSupports_S`. -/
theorem wteExecEffHartSupportsS : hartSupports .Ext_S = true := by decide +kernel

/-- Rocq `wte_exec_eff_hartSupports_Zicsr`. -/
theorem wteExecEffHartSupportsZicsr : hartSupports .Ext_Zicsr = true := by decide +kernel

/-- Rocq `wte_exec_eff_hartSupports_Sstc`. -/
theorem wteExecEffHartSupportsSstc : hartSupports .Ext_Sstc = true := by decide +kernel

/-- Rocq `wte_exec_eff_rec_cE_Zicsr` (on `currentlyEnabled`, no fuel). -/
theorem wteExecEffRecCEZicsr (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Zicsr) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [wteExecEffHartSupportsZicsr]
  rfl

/-- Rocq `wte_exec_eff_currentlyEnabled_S` (deviation 4). -/
theorem wteExecEffCurrentlyEnabledS (s : ExecSt) :
    execEff (currentlyEnabled .Ext_S) s = some (_get_Misa_S (s.regs .misa) == 1#1, s, []) := by
  rw [currentlyEnabled]
  simp only [wteExecEffHartSupportsS, ↓reduceIte]
  wte_run
  cases (_get_Misa_S (s.regs .misa) == 1#1)
  · rfl
  · simp only [↓reduceIte, wteExecEffRecCEZicsr, wteMapSome]

/-- Rocq `wte_exec_eff_currentlyEnabled_Sstc`. -/
theorem wteExecEffCurrentlyEnabledSstc (s : ExecSt) :
    execEff (currentlyEnabled .Ext_Sstc) s = some (true, s, []) := by
  rw [currentlyEnabled]
  simp only [wteExecEffHartSupportsSstc]
  rfl

/-! ## 2. THE CONE, at the empty trace -/

/-- Rocq `exec_eff_should_inc_mcycle_Some`. -/
theorem execEffShouldIncMcycleSome (priv : Privilege) (s : ExecSt) :
    ∃ b : Bool, execEff (should_inc_mcycle priv) s = some (b, s, []) := by
  unfold should_inc_mcycle
  wte_run
  split <;> exact ⟨_, rfl⟩

/-- Rocq `exec_eff_csr_name_write_callback_mip`. -/
theorem execEffCsrNameWriteCallbackMip (V : BitVec 64) (s : ExecSt) :
    execEff (csr_name_write_callback "mip" V) s = some ((), s, []) := rfl

/-- Rocq `exec_eff_external_interrupts_pending_Some`. -/
theorem execEffExternalInterruptsPendingSome (s : ExecSt) :
    ∃ v : BitVec 64, execEff (external_interrupts_pending ()) s = some (v, s, []) := by
  unfold external_interrupts_pending
  cases h : (_get_Misa_S (s.regs .misa) == 1#1) <;>
    wte_run [wteExecEffCurrentlyEnabledS, h] <;> exact ⟨_, rfl⟩

/-- The exact value `read_mip IncludePlatformInterrupts` reads (Lean-only; the
`execEff` twin of `ExecSC7.execReadMip`). -/
theorem wteExecEffReadMip (s : ExecSt) :
    execEff (read_mip .IncludePlatformInterrupts) s = some (readMipVal s, s, []) := by
  unfold read_mip external_interrupts_pending readMipVal
  cases h : (_get_Misa_S (s.regs .misa) == 1#1) <;> wte_run [wteExecEffCurrentlyEnabledS, h]

/-- Rocq `exec_eff_read_mip_include_Some`. -/
theorem execEffReadMipIncludeSome (s : ExecSt) :
    ∃ v : BitVec 64, execEff (read_mip .IncludePlatformInterrupts) s = some (v, s, []) :=
  ⟨_, wteExecEffReadMip s⟩

/-- Rocq `exec_eff_clint_dispatch_false`. -/
theorem execEffClintDispatchFalse (s : ExecSt) :
    ∃ p : BitVec 64, execEff (clint_dispatch false) s = some ((), s.setReg .mip p, []) := by
  unfold clint_dispatch get_config_print_clint
  wte_run [wteExecEffCurrentlyEnabledSstc, execEffCsrNameWriteCallbackMip, wteExecEffReadMip]
  repeat' split
  all_goals first
  | exact ⟨_, rfl⟩
  | exact ⟨_, by simp only [ExecSt.setReg_setReg_same]; rfl⟩

/-- The three-register tower, lifted to the `execEff` result (Lean-only). -/
theorem wteTickShapeLift {L : ExecSt} {R : BitVec 64 → BitVec 64 → BitVec 64 → ExecSt}
    (h : ∃ c t p, L = R c t p) :
    ∃ c t p, (some ((), L, []) : Option (Unit × ExecSt × List Weff)) = some ((), R c t p, []) := by
  obtain ⟨c, t, p, e⟩ := h; exact ⟨c, t, p, by rw [e]⟩

/-- **THE DELIVERABLE.**  Rocq `exec_eff_tick_clock`: `ExecSC7.execTickClock`
with `[]` appended -- the clock tick succeeds at ANY state, writes exactly the
three-register tower, and contributes NOTHING to the effect trace. -/
theorem execEffTickClock (s : ExecSt) :
    ∃ c t p : BitVec 64, execEff (tick_clock ()) s =
      some ((), ((s.setReg .mcycle c).setReg .mtime t).setReg .mip p, []) := by
  obtain ⟨b, hb⟩ := execEffShouldIncMcycleSome (s.regs .cur_privilege) s
  unfold tick_clock clint_dispatch get_config_print_clint
  cases b <;> wte_run [hb, wteExecEffCurrentlyEnabledSstc] <;>
  repeat' (split <;> (try wte_run [execEffCsrNameWriteCallbackMip, wteExecEffReadMip]))
  all_goals first
  | exact wteTickShapeLift (tickShape2 s _ _ _)
  | exact wteTickShapeLift (tickShape1 s _ _)
  | exact wteTickShapeLift (tickShape4 s _ _ _ _)
  | exact wteTickShapeLift (tickShape3 s _ _ _)

end Weak
