/-
Weak: **the deterministic SC evaluator `exec` over the Sail free monad**, its
early-return twin `execR`, the bind/combinator kit, and the ONE bridge to
MachCSL's walkers (`execOfRunRW`, with the `runRead`/`bootRun` corollaries).

Rocq: `iris/RiscvExec.v` @ xxvzwolszwmp (1cc222280) §1–2 and §"exec_bind" /
"exec-leaves", plus the generic `execR` kit of `iris/RiscvTryStep.v` and
`iris/RiscvFetchExec.v` that `ExecCommon.v` needs (`execR`, `execR_bind`,
`execR_liftR`, `exec_catch_early_return`, …).  The model-keyed facts of
`RiscvExec.v` and `ExecCommon.v` are in `Weak/ExecLib.lean`.

The Rocq header, in substance: "A functional partial interpreter [exec]
mirroring the relational [run] of RiscvModelLang, plus the DETERMINISM bridge
… [run]/[prim_step]/RiscvModelLang are UNCHANGED; [exec] is auxiliary."

**Design (notes/weak-port-architecture.md §A, owner decisions 2026-10-06:
route (a); write answers `.Ok (some true)`).**  `exec m s` answers every event
of `m : SailM X` against a FLAT state `ExecSt` -- one register file, a partial
byte map `BMap` (MachCSL's `URunRW.BMap`), the device fabric -- exactly as
Rocq's `RiscvExec.exec` does:
* register reads answer from the file, writes update it;
* a memory access is an MMIO transaction (`devRead`/`devWrite`) when
  `mmioAcc pa n`, else a RAM access: a read must find all `n` bytes in the
  map (`bmRead`, little-endian) and answers `.Ok (w, none)`; a write stores
  them (`bmWrite`, inserting) and answers `.Ok (some true)` (owner decision:
  MachCSL's answer, Rocq's was `inl None`);
* an ifetch is an ordinary RAM read (the weak tier decides fetch semantics
  separately -- O2);
* the announce events (`-D SYMBOLIC`), fences, cache/TLB ops, translation and
  exception markers, cycle counts and messages are silent; `getCycleCount`
  answers `0`;
* a failure node, `choose`, and the legacy `readRam`/`writeRam` events are
  stuck (`none`).
`FreeM` is inductive, so `exec` is structural (no fuel) and evaluates in the
kernel: a closed state's `exec` is decided by `decide +kernel` on any
`DecidableEq` projection of the result (`Weak/ExecLib.lean` §test).

**The bridge.**  `execOfRunRW`: a successful `URunRW.runRW` walk that consumed
no oracle answer (stated for an injective oracle, or for every oracle:
`execOfRunRWAll`) IS the `exec` run on the flat state the walker state stands
for (`toExecSt`: the file `s.file`, the owned bytes `s.mm`, any device
state), provided the owned bytes are RAM bytes -- the result and the
post-state are equal, the device state untouched.  `execOfRunRead` and
`execOfBootRun` are the same for MachCSL's two read-only and register-only walkers.
So every `runRW`/`runRead`/`bootRun` equation MachCSL already proves (the
D50 walk equations, closed by `kernel_rfl`) is an `exec` fact.

**Deviations from Rocq.**
1. State: `ExecSt` (`regs : RegFile`, `mem : BMap`, `dev : DevStates`) for
   Rocq `mstate` (`sregs`, `mem : gmap`, `mdev`); `bmRead`/`bmWrite` for
   `read_bytes`/`write_bytes`.
2. The MMIO test is `mmioAcc pa n = devAddr pa && n != 0` (Rocq:
   `dev_addr pa`).  The two differ only on zero-width accesses (which the
   model never emits); the `n != 0` makes a zero-width access at a device
   address a no-op RAM access, as in `runRW`, so that the bridge needs no side
   condition on the walk.  (Recommendation to the `WeakInterp` porter: use
   `mmioAcc` in `wexec` too, so `WeakBridge` stays arm-for-arm.)
3. A write with no value (`req.value = none`, impossible in Rocq where the
   value is not optional) is stuck, as in `runRW` and `WeakInterp.wexec`.
4. Write answers `.Ok (some true)` (owner decision), Rocq `inl None`.
5. `execR` is not a second interpreter: Lean's early-return monad
   `SailME R X` is `ExceptT (Error ⊕ R) SailM X`, so `execR m s` is `exec` of
   `m.run`, with `.error (.inr r)` the early return (Rocq `inl r`), `.ok x`
   the value (Rocq `inr x`) and `.error (.inl e)` (a model exception raised
   in the `ExceptT` layer; Rocq's stuck `ExtraOutcome (inr _)`) mapped to
   `none`.  Rocq `liftR` is Lean's `liftM` (`ExceptT.lift`),
   `catch_early_return` is `SailME.run`, `returnR` is `pure`.
6. Lean's model has no `bind0`/`returnm`/`returnM` (do-notation binds `Unit`
   results with `fun _ => …`, `pure` is the return): `execBind0*` are stated
   for `m >>= fun _ => n`, `execReturnm`/`execReturnM` for `pure`.
7. The bridge is NEW (Rocq's bridge was `exec_run_det`, to the relational
   `run`, which Lean does not have; see Not ported).

**Name map (Rocq → Lean).**  `mstate` ↦ `ExecSt`, `set_reg` ↦
`ExecSt.setReg`, `exec` ↦ `exec`, `exec_bind` ↦ `execBind`, `exec_bind0` ↦
`execBind0`, `exec_returnm` ↦ `execReturnm`, `exec_returnM` (RiscvTryStep) ↦
`execReturnM`, `bind_Ret` ↦ `bindRet`, `bind_Next` ↦ `bindNext`,
`exec_bind_Some` ↦ `execBindSome`, `exec_bind0_Some` ↦ `execBind0Some`,
`exec_instr_announce` ↦ `execInstrAnnounce`, `exec_branch_announce` ↦
`execBranchAnnounce`, `exec_read_reg` ↦ `execReadReg`, `exec_write_reg` ↦
`execWriteReg`; RiscvFetchExec: `exec_MemRead(_dev)` ↦ `execMemRead(Dev)`,
`exec_MemWrite(_dev)` ↦ `execMemWrite(Dev)`, `execR_bind_Some` ↦
`execRBindSome`, `execR_bind0_Some` ↦ `execRBind0Some`, `execR_returnR_fwd` ↦
`execRReturnRFwd`; RiscvTryStep: `execR` ↦ `execR`, `bindR_Ret`/`bindR_Next`
↦ (none: `ExceptT` bind is not a `FreeM` node, `execRBind` covers them),
`execR_bind` ↦ `execRBind`, `execR_liftR` ↦ `execRLiftR`,
`exec_catch_early_return` ↦ `execCatchEarlyReturn`, `execR_returnR` ↦
`execRReturnR`, `execR_bind0` ↦ `execRBind0`, `execR_liftR_seq` ↦
`execRLiftRSeq`.  Lean-only: `mmioAcc`, `ExecSt.setDev/setMem`, the per-event
step equations `execRegRead`/`execRegWrite`/…, `toExecSt`, `UOrc.inj`,
`runRWDrop`, `execOfRunRW`, `execOfRunRWAll`, `execOfRunRead`,
`execOfBootRun`, `bmRead_isSome_base`, `bmOwned_base`, `bmWrite_dom`, `bmRam`,
`mmioAcc_false_of_base`, `execBindNone`, `execRThrow`, `execError`, `execChoose`,
the tactic `exec_steps`.

**Not ported** (uses checked against `iris/{Weak,Ax,Wk}*.v`):
`exec_run_det`, `run_to_exec` (they relate `exec` to Rocq's relational
`RiscvLang.run`, which has no Lean twin -- Lean's relational semantics is
MachCSL's TSO `evStep`; weak uses: comments only, plus one prose mention of
`run_to_exec` in `WeakFetchEff`); `thread_gen`, `wp_dead`, `wp_exec_step`,
`wp_uart_step`, `wp_disk_step`, `wp_plic_step` (Iris rules of Rocq's SC
`riscv_lang`; the weak tier has its own `WeakExec.wp_wexec_step`; weak uses:
comments only).  RiscvTryStep's `exec_and_boolM_Some`/`exec_or_boolM_Some`:
Lean's model has no `and_boolM`/`or_boolM` (its `&&`/`||` of monadic operands
are inline binds, which `execBindSome` steps).

**Out of scope (the rest of the SC `exec_*` library).**  `iris/{Weak,Ax,Wk}*.v`
also use 198 `exec_*`/`execR_*` names defined in 34 OTHER SC files -- by
count WpMmodeLeafBase 50, RiscvFetchExec 26 (fetch/PMA/PMP leaves), RiscvTryStep
14 (incl. `execR_foreach_ZM_up'_*`, `exec_pmpCheck_machine_none`), WpAmo 9,
SmodePte 9, SmodeCore 9, WpGprCsrwB 8, RiscvExtras 8 (incl.
`exec_split_misaligned_unsplit`), WpLoad 7, … (the Lean model's `untilM` loop
lemma `execR_untilMT_1` is among RiscvFetchExec's).  They are model-keyed leaf
facts of those files, to be derived on demand from MachCSL's walk equations
through `execOfRunRW`/`execOfRunRead` or by `decide +kernel`/`exec_steps`.
-/
import MachCSL.URunRW

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! ## 1. The flat state and the evaluator -/

/-- The flat SC state `exec` runs over (Rocq `mstate`): one hart's register
file, a partial byte map, the device fabric. -/
structure ExecSt where
  regs : RegFile
  mem : BMap
  dev : DevStates

/-- Update one register (Rocq `set_reg`). -/
def ExecSt.setReg (s : ExecSt) (r : Register) (v : RegisterType r) : ExecSt :=
  { s with regs := s.regs.set r v }

/-- Replace the device fabric. -/
def ExecSt.setDev (s : ExecSt) (d : DevStates) : ExecSt := { s with dev := d }

/-- Replace the byte map. -/
def ExecSt.setMem (s : ExecSt) (mm : BMap) : ExecSt := { s with mem := mm }

@[simp] theorem ExecSt.setReg_regs (s : ExecSt) (r : Register) (v : RegisterType r) :
    (s.setReg r v).regs = s.regs.set r v := rfl
@[simp] theorem ExecSt.setReg_mem (s : ExecSt) (r : Register) (v : RegisterType r) :
    (s.setReg r v).mem = s.mem := rfl
@[simp] theorem ExecSt.setReg_dev (s : ExecSt) (r : Register) (v : RegisterType r) :
    (s.setReg r v).dev = s.dev := rfl

/-- Whether an `n`-byte access at `pa` is an MMIO transaction (deviation 2). -/
def mmioAcc (pa : PAddr) (n : Nat) : Bool := devAddr pa && n != 0

/-- **The evaluator** (Rocq `RiscvExec.exec`): run `m` from `s`; `none` if it
gets stuck (a failure, a `choose`, a missing byte, a device refusal). -/
def exec {X : Type} : SailM X → ExecSt → Option (X × ExecSt)
  | .pure x, s => some (x, s)
  | .impure (.error _) _, _ => none
  | .impure (.ok o) k, s =>
    match o, k with
    | .regRead r, k => exec (k (s.regs r)) s
    | .regWrite r v, k => exec (k PUnit.unit) (s.setReg r v)
    | .memRead n _ req, k =>
      if mmioAcc req.pa n then
        match devRead s.dev req.pa n with
        | some (w, d') => exec (k (.Ok (w, none))) (s.setDev d')
        | none => none
      else
        match bmRead s.mem req.pa n with
        | some w => exec (k (.Ok (w, none))) s
        | none => none
    | .memWrite n _ req, k =>
      match req.value with
      | none => none
      | some w =>
        if mmioAcc req.pa n then
          match devWrite s.dev req.pa n w with
          | some d' => exec (k (.Ok (some true))) (s.setDev d')
          | none => none
        else exec (k (.Ok (some true))) (s.setMem (bmWrite s.mem req.pa n w))
    | .barrier _, k => exec (k ()) s
    | .cacheOp _, k => exec (k ()) s
    | .tlbi _, k => exec (k ()) s
    | .translationStart _, k => exec (k ()) s
    | .translationEnd _, k => exec (k ()) s
    | .takeException _, k => exec (k ()) s
    | .returnException _, k => exec (k ()) s
    | .cycleCount, k => exec (k ()) s
    | .getCycleCount, k => exec (k (0 : Nat)) s
    | .message _, k => exec (k ()) s
    | .instrAnnounce _ _, k => exec (k ()) s
    | .branchAnnounce _ _, k => exec (k ()) s
    | .choose _, _ => none
    | .readRam .., _ => none
    | .writeRam .., _ => none

/-! ## 2. Step equations (one per event; all `rfl`) -/

section steps
variable {X : Type}

@[simp] theorem execPure (x : X) (s : ExecSt) : exec (FreeM.pure x : SailM X) s = some (x, s) := rfl

theorem execError (e : Sail.Error exception) (k : Empty → SailM X) (s : ExecSt) :
    exec (FreeM.impure (Eff := Eff RegisterType exception) (.error e) k) s = none := rfl

theorem execRegRead (r : Register) (k : RegisterType r → SailM X) (s : ExecSt) :
    exec (FreeM.impure (.ok (.regRead r)) k) s = exec (k (s.regs r)) s := rfl

theorem execRegWrite (r : Register) (v : RegisterType r) (k : PUnit → SailM X) (s : ExecSt) :
    exec (FreeM.impure (.ok (.regWrite r v)) k) s = exec (k PUnit.unit) (s.setReg r v) := rfl

/-- Rocq `RiscvFetchExec.exec_MemRead`: a RAM read. -/
theorem execMemRead (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (s : ExecSt)
    (h : mmioAcc req.pa n = false) :
    exec (FreeM.impure (.ok (.memRead n va req)) k) s =
      match bmRead s.mem req.pa n with
      | some w => exec (k (.Ok (w, none))) s
      | none => none := by
  simp only [exec, h, Bool.false_eq_true, ↓reduceIte]

/-- Rocq `RiscvFetchExec.exec_MemRead_dev`: an MMIO read. -/
theorem execMemReadDev (n va : Nat) (req : Mem_read_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (BitVec (8 * n) × Option Bool) Arch.abort → SailM X) (s : ExecSt)
    (h : mmioAcc req.pa n = true) :
    exec (FreeM.impure (.ok (.memRead n va req)) k) s =
      match devRead s.dev req.pa n with
      | some (w, d') => exec (k (.Ok (w, none))) (s.setDev d')
      | none => none := by
  simp only [exec, h, ↓reduceIte]

/-- Rocq `RiscvFetchExec.exec_MemWrite`: a RAM write. -/
theorem execMemWrite (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (Option Bool) Arch.abort → SailM X) (s : ExecSt) (w : BitVec (8 * n))
    (hv : req.value = some w) (h : mmioAcc req.pa n = false) :
    exec (FreeM.impure (.ok (.memWrite n va req)) k) s =
      exec (k (.Ok (some true))) (s.setMem (bmWrite s.mem req.pa n w)) := by
  simp only [exec, hv, h, Bool.false_eq_true, ↓reduceIte]

/-- Rocq `RiscvFetchExec.exec_MemWrite_dev`: an MMIO write. -/
theorem execMemWriteDev (n va : Nat) (req : Mem_write_request n va Arch.pa Arch.translation Arch.arch_ak)
    (k : Result (Option Bool) Arch.abort → SailM X) (s : ExecSt) (w : BitVec (8 * n))
    (hv : req.value = some w) (h : mmioAcc req.pa n = true) :
    exec (FreeM.impure (.ok (.memWrite n va req)) k) s =
      match devWrite s.dev req.pa n w with
      | some d' => exec (k (.Ok (some true))) (s.setDev d')
      | none => none := by
  simp only [exec, hv, h, ↓reduceIte]

theorem execChoose (p : Sail.Primitive) (k : p.reflect → SailM X) (s : ExecSt) :
    exec (FreeM.impure (.ok (.choose p)) k) s = none := rfl

end steps

/-! ## 3. Bind (Rocq §"exec_bind") -/

section bind
variable {X Y : Type}

/-- Rocq `bind_Ret`. -/
theorem bindRet (y : X) (f : X → SailM Y) : ((FreeM.pure y : SailM X) >>= f) = f y := rfl

/-- Rocq `bind_Next`. -/
theorem bindNext (c : Eff RegisterType exception) (k : Sail.ArchSem.Effect.ret c → SailM X)
    (f : X → SailM Y) :
    ((FreeM.impure c k : SailM X) >>= f) = FreeM.impure c (fun z => k z >>= f) := rfl

/-- **The bind law** (Rocq `exec_bind`). -/
theorem execBind (m : SailM X) (f : X → SailM Y) :
    ∀ s, exec (m >>= f) s =
      match exec m s with
      | some (x, s1) => exec (f x) s1
      | none => none := by
  induction m with
  | pure x => intro s; rfl
  | impure call k ih =>
    intro s
    cases call with
    | error e => rfl
    | ok o =>
      show exec (FreeM.impure (.ok o) (fun v => k v >>= f)) s = _
      cases o
      case memRead n va req =>
        cases hm : mmioAcc req.pa n
        · simp only [exec, hm, Bool.false_eq_true, ↓reduceIte]
          cases bmRead s.mem req.pa n <;> first | rfl | simp only [ih]
        · simp only [exec, hm, ↓reduceIte]
          cases devRead s.dev req.pa n <;> first | rfl | simp only [ih]
      case memWrite n va req =>
        cases hv : req.value with
        | none => simp only [exec, hv]
        | some w =>
          cases hm : mmioAcc req.pa n
          · simp only [exec, hv, hm, Bool.false_eq_true, ↓reduceIte, ih]
          · simp only [exec, hv, hm, ↓reduceIte]
            cases devWrite s.dev req.pa n w <;> first | rfl | simp only [ih]
      all_goals first | rfl | exact ih _ _ | (simp only [exec]; exact ih _ _)

/-- Rocq `exec_bind0` (deviation 6: `bind0 m n` is `m >>= fun _ => n`). -/
theorem execBind0 (m : SailM Unit) (n : SailM Y) (s : ExecSt) :
    exec (m >>= fun _ => n) s = match exec m s with | some (_, s1) => exec n s1 | none => none := by
  rw [execBind]; cases exec m s with | none => rfl | some p => rfl

/-- Rocq `exec_returnm`. -/
@[simp] theorem execReturnm (x : X) (s : ExecSt) : exec (pure x : SailM X) s = some (x, s) := rfl

/-- Rocq `RiscvTryStep.exec_returnM` (the model's return is `pure`). -/
theorem execReturnM (x : X) (s : ExecSt) : exec (pure x : SailM X) s = some (x, s) := rfl

/-- Rocq `exec_bind_Some`. -/
theorem execBindSome (m : SailM X) (f : X → SailM Y) (s : ExecSt) (v : X) (st : ExecSt)
    (h : exec m s = some (v, st)) : exec (m >>= f) s = exec (f v) st := by
  rw [execBind, h]

/-- Rocq `exec_bind0_Some`. -/
theorem execBind0Some (m : SailM Unit) (n : SailM Y) (s : ExecSt) (u : Unit) (st : ExecSt)
    (h : exec m s = some (u, st)) : exec (m >>= fun _ => n) s = exec n st := by
  rw [execBind, h]

/-- A stuck head sticks the bind. -/
theorem execBindNone (m : SailM X) (f : X → SailM Y) (s : ExecSt) (h : exec m s = none) :
    exec (m >>= f) s = none := by
  rw [execBind, h]

end bind

/-! ## 4. The event leaves (Rocq §"exec-leaves") -/

/-- Rocq `exec_instr_announce`: the announcement is silent. -/
theorem execInstrAnnounce {n : Nat} (w : BitVec n) (s : ExecSt) :
    exec (LeanRV64D.Functions.instr_announce w) s = some ((), s) := rfl

/-- Rocq `exec_branch_announce`. -/
theorem execBranchAnnounce (n : Nat) (a : BitVec n) (s : ExecSt) :
    exec (LeanRV64D.Functions.branch_announce n a) s = some ((), s) := rfl

/-- Rocq `exec_read_reg`. -/
theorem execReadReg (r : Register) (s : ExecSt) : exec (readReg r) s = some (s.regs r, s) := rfl

/-- Rocq `exec_write_reg`. -/
theorem execWriteReg (r : Register) (v : RegisterType r) (s : ExecSt) :
    exec (writeReg r v) s = some (PUnit.unit, s.setReg r v) := rfl

/-- Step a computation under `exec` by unfolding: the register events are
unfolded to their `FreeM` nodes rather than rewritten by `execReadReg` /
`execWriteReg`, whose `X := RegisterType r` does not unify with the model's
`BitVec 64` at `simp`'s reducible transparency.  Extra lemmas in brackets. -/
syntax "exec_steps" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| exec_steps) => `(tactic| simp only [execBind, readReg, writeReg, PreSail.readReg,
      PreSail.writeReg, PreSail.emit, exec, execReturnm])
  | `(tactic| exec_steps [$ls,*]) => `(tactic| simp only [execBind, readReg, writeReg, PreSail.readReg,
      PreSail.writeReg, PreSail.emit, exec, execReturnm, $ls,*])

/-! ## 5. The early-return monad (RiscvTryStep's `execR` kit) -/

section execR
variable {R X Y : Type}

/-- Rocq `RiscvTryStep.execR` (deviation 5): `exec` of the `ExceptT` run, the
early return `inl`, the value `inr`, a model exception stuck. -/
def execR (m : SailME R X) (s : ExecSt) : Option ((R ⊕ X) × ExecSt) :=
  match exec (ExceptT.run m) s with
  | some (.ok x, s') => some (.inr x, s')
  | some (.error (.inr r), s') => some (.inl r, s')
  | some (.error (.inl _), _) => none
  | none => none

/-- Rocq `execR_returnR`. -/
@[simp] theorem execRReturnR (x : X) (s : ExecSt) : execR (pure x : SailME R X) s = some (.inr x, s) :=
  rfl

/-- Rocq `RiscvFetchExec.execR_returnR_fwd`. -/
theorem execRReturnRFwd (x : X) (s : ExecSt) : execR (pure x : SailME R X) s = some (.inr x, s) :=
  rfl

/-- An early return. -/
@[simp] theorem execRThrow (r : R) (s : ExecSt) :
    execR (SailME.throw r : SailME R X) s = some (.inl r, s) := rfl

/-- Rocq `execR_bind`: the early return short-circuits. -/
theorem execRBind (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) :
    execR (m >>= f) s =
      match execR m s with
      | some (.inl r, s') => some (.inl r, s')
      | some (.inr a, s') => execR (f a) s'
      | none => none := by
  unfold execR
  rw [ExceptT.run_bind, execBind]
  rcases h : exec (ExceptT.run m) s with _ | ⟨e | a, s'⟩
  · rfl
  · rcases e with e | r <;> rfl
  · rfl

/-- Rocq `execR_bind0`. -/
theorem execRBind0 (m : SailME R Unit) (n : SailME R X) (s : ExecSt) :
    execR (m >>= fun _ => n) s =
      match execR m s with
      | some (.inl r, s') => some (.inl r, s')
      | some (.inr _, s') => execR n s'
      | none => none := by
  rw [execRBind]
  cases execR m s with
  | none => rfl
  | some p => rcases p with ⟨_ | _, _⟩ <;> rfl

/-- Rocq `RiscvFetchExec.execR_bind_Some`. -/
theorem execRBindSome (m : SailME R Y) (f : Y → SailME R X) (s : ExecSt) (a : Y) (s' : ExecSt)
    (h : execR m s = some (.inr a, s')) : execR (m >>= f) s = execR (f a) s' := by
  rw [execRBind, h]

/-- Rocq `RiscvFetchExec.execR_bind0_Some`. -/
theorem execRBind0Some (m : SailME R Unit) (n : SailME R X) (s s' : ExecSt)
    (h : execR m s = some (.inr (), s')) : execR (m >>= fun _ => n) s = execR n s' := by
  rw [execRBind, h]

/-- Rocq `execR_liftR`: a lifted base computation never returns early. -/
theorem execRLiftR (m : SailM X) (s : ExecSt) :
    execR (liftM m : SailME R X) s =
      match exec m s with
      | some (x, s') => some (.inr x, s')
      | none => none := by
  unfold execR
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e, execBind]
  rcases exec m s with _ | ⟨x, s'⟩ <;> rfl

/-- Rocq `execR_liftR_seq`. -/
theorem execRLiftRSeq (m : SailM Y) (f : Y → SailME R X) (s s' : ExecSt) (x : Y)
    (h : exec m s = some (x, s')) : execR (liftM m >>= f) s = execR (f x) s' := by
  rw [execRBind, execRLiftR, h]

/-- Rocq `exec_catch_early_return`: `SailME.run` back into the base monad. -/
theorem execCatchEarlyReturn (body : SailME X X) (s : ExecSt) :
    exec (SailME.run body) s =
      match execR body s with
      | some (.inl r, s') => some (r, s')
      | some (.inr r, s') => some (r, s')
      | none => none := by
  unfold execR
  show exec (ExceptT.run body >>= _) s = _
  rw [execBind]
  rcases exec (ExceptT.run body) s with _ | ⟨e | a, s'⟩
  · rfl
  · rcases e with e | r <;> rfl
  · rfl

end execR

/-! ## 6. The bridge to MachCSL's walkers -/

/-- The flat state a walker state stands for (any device state). -/
def toExecSt (s : UWSt) (d : DevStates) : ExecSt := ⟨s.file, s.mm, d⟩

/-- An oracle whose answers are pairwise distinct (the `nat` choice is the
index). -/
def UOrc.inj (f : RegFile) : UOrc := fun i =>
  { reg := f
    ch := fun p => match p with
      | .bool => false | .bit => 0 | .int => 0 | .nat => i | .string => ""
      | .fin _ => 0 | .bitvector _ => 0 }

theorem UOrc.inj_injective (f : RegFile) : Function.Injective (UOrc.inj f) := by
  intro i j h
  have := congrArg (fun a : UAns => a.ch .nat) h
  exact this

/-- The walker consumes its oracle from the head: what is left is a suffix. -/
theorem runRWDrop (D : UFoot) {X : Type} (m : SailM X) :
    ∀ (orc : UOrc) (s : UWSt) (x : X) (s' : UWSt) (orc' : UOrc),
      runRW D orc s m = some (x, s', orc') → ∃ j, orc' = orc.drop j := by
  induction m with
  | pure y =>
    intro orc s x s' orc' h
    simp only [runRW, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨0, h.2.2.symm⟩
  | impure call k ih =>
    intro orc s x s' orc' h
    have tl : ∀ j, (UOrc.tail orc).drop j = orc.drop (j + 1) := fun j => by
      funext i; simp only [UOrc.drop, UOrc.tail]; congr 1
    cases call with
    | error e => simp [runRW] at h
    | ok o =>
      cases o <;> simp only [runRW] at h <;> (repeat' split at h) <;>
        first
        | (simp at h; done)
        | exact ih _ _ _ _ _ _ h
        | exact (ih _ _ _ _ _ _ h).elim fun j hj => ⟨j + 1, hj.trans (tl j)⟩

/-- A successful map read of `n ≥ 1` bytes finds the base byte. -/
theorem bmRead_isSome_base (mm : BMap) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (h : bmRead mm pa n = some w) (hn : n ≠ 0) : (mm pa).isSome = true := by
  have := bmRead_spec mm pa n w h 0 (Nat.pos_of_ne_zero hn)
  simp only [BitVec.add_zero] at this
  rw [this]; rfl

/-- An owned footprint of `n ≥ 1` bytes owns its base byte. -/
theorem bmOwned_base (mm : BMap) (pa : PAddr) (n : Nat) (h : bmOwned mm pa n = true) (hn : n ≠ 0) :
    (mm pa).isSome = true := by
  unfold bmOwned at h
  rw [List.all_eq_true] at h
  have := h 0 (List.mem_range.2 (Nat.pos_of_ne_zero hn))
  simpa using this

/-- Writing an owned footprint adds nothing to the map's domain. -/
theorem bmWrite_dom (mm : BMap) (pa : PAddr) (n : Nat) (w : BitVec (8 * n))
    (h : bmOwned mm pa n = true) (a : PAddr) (ha : (bmWrite mm pa n w a).isSome = true) :
    (mm a).isSome = true := by
  unfold bmOwned at h
  rw [List.all_eq_true] at h
  unfold bmWrite at ha
  suffices ∀ (l : List Nat) (m : BMap), (∀ j ∈ l, (mm (pa + BitVec.ofNat 64 j)).isSome = true) →
      (∀ b, (m b).isSome = true → (mm b).isSome = true) →
      (l.foldl (fun m j => bmSet m (pa + BitVec.ofNat 64 j) (nthByte w j)) m a).isSome = true →
      (mm a).isSome = true from
    this _ mm h (fun _ hb => hb) ha
  intro l
  induction l with
  | nil => intro m _ hm ha; exact hm a ha
  | cons j l ih =>
    intro m hl hm ha
    simp only [List.foldl_cons] at ha
    refine ih _ (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')) ?_ ha
    intro b hb
    unfold bmSet at hb
    split at hb
    · subst_vars; exact hl j List.mem_cons_self
    · exact hm b hb

/-- The owned bytes are RAM bytes. -/
def bmRam (mm : BMap) : Prop := ∀ a, (mm a).isSome = true → devAddr a = false

theorem mmioAcc_false_of_base (mm : BMap) (hram : bmRam mm) (pa : PAddr) (n : Nat)
    (h : n ≠ 0 → (mm pa).isSome = true) : mmioAcc pa n = false := by
  unfold mmioAcc
  by_cases hn : n = 0
  · subst hn; simp
  · rw [hram pa (h hn)]

/-- **The bridge** (route (a)'s ONE theorem): a `runRW` walk that consumed no
answer of an injective oracle is the `exec` run on the flat state, with the
same result and post-state, provided the owned bytes are RAM bytes. -/
theorem execOfRunRW (D : UFoot) {X : Type} (m : SailM X) :
    ∀ (orc : UOrc) (s : UWSt) (d : DevStates) (x : X) (s' : UWSt),
      Function.Injective orc → bmRam s.mm →
      runRW D orc s m = some (x, s', orc) → exec m (toExecSt s d) = some (x, toExecSt s' d) := by
  induction m with
  | pure y =>
    intro orc s d x s' _ _ h
    simp only [runRW, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    rfl
  | impure call k ih =>
    intro orc s d x s' hinj hram h
    -- a walk that consumed an oracle answer cannot return the oracle itself
    have noTail : ∀ {Z : Type} (m' : SailM Z) (z : Z) (s'' : UWSt),
        runRW D orc.tail s m' ≠ some (z, s'', orc) := by
      intro Z m' z s'' h'
      obtain ⟨j, hj⟩ := runRWDrop D m' _ _ _ _ _ h'
      have h0 := congrFun hj 0
      simp only [UOrc.drop, UOrc.tail] at h0
      have := hinj h0
      omega
    cases call with
    | error e => simp [runRW] at h
    | ok o =>
      cases o with
      | regRead r =>
        by_cases hr : D.Dr r = true
        · rw [runRW_regRead_dr D orc s r k hr] at h
          exact ih _ orc s d x s' hinj hram h
        · by_cases ha : D.Dany r = true
          · rw [runRW_regRead_any D orc s r k (by simpa using hr) ha] at h
            exact absurd h (noTail _ _ _)
          · simp [runRW, hr, ha] at h
      | regWrite r v =>
        simp only [runRW] at h
        split at h
        · have e : (toExecSt s d).setReg r v = toExecSt ({ s with pin := s.pin.set r v } : UWSt) d := by
            unfold toExecSt ExecSt.setReg
            rw [UWSt.file_setPin]
          show exec (k PUnit.unit) ((toExecSt s d).setReg r v) = _
          rw [e]
          exact ih _ orc _ d x s' hinj hram h
        · exact absurd h (by simp)
      | memRead n va req =>
        simp only [runRW] at h
        split at h
        · exact absurd h (by simp)
        split at h
        · split at h
          · split at h
            · rename_i w hw
              have hm : mmioAcc req.pa n = false :=
                mmioAcc_false_of_base s.mm hram req.pa n (bmRead_isSome_base s.mm req.pa n w hw)
              rw [execMemRead n va req k _ hm]
              show (match bmRead s.mm req.pa n with | some w => _ | none => none) = _
              rw [hw]
              exact ih _ orc { s with rv := true } d x s' hinj hram h
            · exact absurd h (by simp)
          · split at h
            · rename_i w hw
              have hm : mmioAcc req.pa n = false :=
                mmioAcc_false_of_base s.mm hram req.pa n (bmRead_isSome_base s.mm req.pa n w hw)
              rw [execMemRead n va req k _ hm]
              show (match bmRead s.mm req.pa n with | some w => _ | none => none) = _
              rw [hw]
              exact ih _ orc s d x s' hinj hram h
            · exact absurd h (by simp)
        · exact absurd h (by simp)
      | memWrite n va req =>
        simp only [runRW] at h
        split at h
        · split at h
          · exact absurd h (by simp)
          · rename_i w hv
            split at h
            · rename_i hown
              have hm : mmioAcc req.pa n = false :=
                mmioAcc_false_of_base s.mm hram req.pa n (bmOwned_base s.mm req.pa n hown)
              rw [execMemWrite n va req k _ w hv hm]
              have hram' : bmRam (bmWrite s.mm req.pa n w) := fun a ha =>
                hram a (bmWrite_dom s.mm req.pa n w hown a ha)
              exact ih _ orc { s with mm := bmWrite s.mm req.pa n w, rv := false } d x s' hinj hram' h
            · exact absurd h (by simp)
        · exact absurd h (by simp)
      | choose p =>
        simp only [runRW] at h
        exact absurd h (noTail _ _ _)
      | readRam => simp [runRW] at h
      | writeRam => simp [runRW] at h
      | barrier => exact ih _ orc s d x s' hinj hram h
      | cacheOp => exact ih _ orc s d x s' hinj hram h
      | tlbi => exact ih _ orc s d x s' hinj hram h
      | translationStart => exact ih _ orc s d x s' hinj hram h
      | translationEnd => exact ih _ orc s d x s' hinj hram h
      | takeException => exact ih _ orc s d x s' hinj hram h
      | returnException => exact ih _ orc s d x s' hinj hram h
      | cycleCount => exact ih _ orc s d x s' hinj hram h
      | getCycleCount => exact ih _ orc s d x s' hinj hram h
      | message => exact ih _ orc s d x s' hinj hram h
      | instrAnnounce => exact ih _ orc s d x s' hinj hram h
      | branchAnnounce => exact ih _ orc s d x s' hinj hram h

/-- The bridge in the shape MachCSL states its walk facts (`∀ orc, runRW D
orc s m = some (x, s', orc)`). -/
theorem execOfRunRWAll (D : UFoot) {X : Type} (m : SailM X) (s : UWSt) (d : DevStates) (x : X)
    (s' : UWSt) (hram : bmRam s.mm) (h : ∀ orc, runRW D orc s m = some (x, s', orc)) :
    exec m (toExecSt s d) = some (x, toExecSt s' d) :=
  execOfRunRW D m (UOrc.inj s.rs) s d x s' (UOrc.inj_injective _) hram (h _)

/-- The read-only walk (`DecodeBridge.runRead`) is an `exec` run that moves
nothing, at any state agreeing with the reference map. -/
theorem execOfRunRead (dref : (r : Register) → Option (RegisterType r)) {X : Type} (m : SailM X) :
    ∀ (st : ExecSt) (x : X) (b : Bool), (∀ r v, dref r = some v → st.regs r = v) →
      runRead dref m = some (x, b) → exec m st = some (x, st) := by
  induction m with
  | pure y =>
    intro st x b _ h
    simp only [runRead, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | impure call k ih =>
    intro st x b hd h
    cases call with
    | error e => simp [runRead] at h
    | ok o =>
      cases o <;> simp only [runRead] at h <;> (repeat' split at h) <;>
        first
        | (obtain ⟨⟨x', b'⟩, h1, h2⟩ := Option.map_eq_some_iff.1 h
           simp only [Prod.mk.injEq] at h2
           obtain ⟨rfl, -⟩ := h2
           first
           | exact ih _ st x' b' hd h1
           | (rename_i v hv
              show exec (k (st.regs _)) st = _
              rw [hd _ _ hv]
              exact ih _ st x' b' hd h1))
        | (simp at h; done)

/-- The register-only walk (`BootRun.bootRun`) is an `exec` run that moves
no byte and no device. -/
theorem execOfBootRun {X : Type} (m : SailM X) :
    ∀ (f : RegFile) (mm : BMap) (d : DevStates) (x : X) (f' : RegFile),
      bootRun m f = some (x, f') → exec m ⟨f, mm, d⟩ = some (x, ⟨f', mm, d⟩) := by
  induction m with
  | pure y =>
    intro f mm d x f' h
    simp only [bootRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | impure call k ih =>
    intro f mm d x f' h
    cases call with
    | error e => simp [bootRun] at h
    | ok o =>
      cases o <;> simp only [bootRun, reduceCtorEq] at h
      all_goals exact ih _ _ mm d x f' h

end Weak
