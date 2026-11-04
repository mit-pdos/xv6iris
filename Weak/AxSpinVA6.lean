/-
Weak: **the spinlock plan, PHASE 5 item (4), part 6** — the kit for the FAULT arms: the
register-only S-mode EXCEPTION trap tower and the transfer of pin-reading register-only
certificates into `FEC`.

Rocq: `iris/AxSpinVA6.v` @ xxvzwolszwmp.

## What this file proves

* §1 `rfS`: `rfF` minus the pin restriction on READS (a pin may be read, never written) — the
  footprint of `tick_clock` (`rfSTick`).  `FECOfEvARfS`: an `EvA` fact (any image) of an `rfS`
  tree is an `FEC` fact at ANY image and ANY chain — no label, chain untouched (an `rfS` tree has
  no memory / barrier node on any branch).  `FTick`: `AxSpineOk7.sptTickS` transferred.
* §2 THE S-MODE EXCEPTION TOWER (SC `exec`, cause-generic): `trap_handler Supervisor` for ANY
  cause `c` and tval payload `info` (`execTrapHandlerSGen`); `execExceptionDelegateeS` (medeleg bit
  set ⇒ Supervisor); `execHandleExceptionS`: `handle_exception` lands in `xtrapSt` (mstatus :=
  `AxIntr2.trapMs`, elp reset, scause, stval := tval, sepc := pc, priv := S, nextPC := stvec base).
  `xtrapOkS`: the trap state is again in the regime `ctrlOkS` (SIE = 0 is kept by `trapMs`).

## Deviations from Rocq

1. SPELLING (as `AxIntr2` deviation 1): `mstate` ↦ `ExecSt`, `register_lookup r s.(sregs)` ↦
   `s.regs .r`, `set_reg` ↦ `ExecSt.setReg`, `eq_vec x 'b"1" = b` ↦ `(x == 1#1) = b`,
   `update_subrange_vec_dec` ↦ `Sail.BitVec.updateSubrange`, `access_vec_dec v (uint i)` ↦
   the model's `BitVec.access v (BitVec.toNatInt i)`, `stvec_direct` ↦ `AxIntr.stvecDirect`,
   `WpIntrCore.stvec_base` ↦ `stvecBase`, `MstatusBits.trap_ms` ↦ `AxIntr2.trapMs`,
   `IntrDefs.sconf_ms_facts_trap` ↦ `sconfMsFactsTrap`, `seip_reg` ↦ `AxRunClose.pinReg`,
   `Defs.try_catch` ↦ `PreSail.tryCatchAll`, `catch_early_return` ↦ `SailME.run` (stated on
   `rfS (ExceptT.run m)`, as `rfFCatchEarlyReturn`), `liftR` on `ExceptT.run (liftM m)`.
2. `rfS` follows Lean's `rfF` (`AxSpineOk` deviations 2–4) except on reads: the pins are
   `AxRunClose.pinReg` (both `sig_seip` and `sig_meip`), the announce arm demands
   `sfAnnB n w = false`, failure nodes / `choose` / `readRam` / `writeRam` are `True`.
3. Section `XTrapReduce`'s `Let`s `s1 … s9` are the Lean-only `AxSpinVA6.trapS9` (the
   cause-generic twin of `ExecSC7.trapSupS9`); `xtrapSt` is stated through it plus the `nextPC`
   write (as `AxIntr2.trapSt`).  The section hypotheses are premises; `execTrapHandlerSGen` takes
   the trap extension payload `none` (as Rocq).  `exec (currentlyEnabled Ext_S) s = Some (true, s)`
   is kept as a premise of `execExceptionDelegateeS`.
4. `FTick`: the image of `AxSpineOk7.sptTickS` is `imgS t` (Rocq: `img_S` of the state with an
   empty memory); `FECOfEvARfS` transfers it to any image, so the statement is unchanged.
5. TACTICS: Rocq's `rfS_step` / `rfS_unf` / `rfS_cer` / `rfS_auto` and `xlk` are not
   redeclared: `rfSTick` is proved by the local tactic `va6_rfs` (binds / ifs / reads / writes,
   with the register-only callees through the Lean-only `AxSpinVA6.rfSOfRfF`); the `xtrapSt`
   lookups by `simp` over `RegFile.set_*` (as `AxIntr2`).

**Rocq → Lean name map.**  `rfS` `rfS`, `rfS_bind` `rfSBind`, `rfS_bind0` `rfSBind0`,
`rfS_try_catch` `rfSTryCatch`, `rfS_catch_early_return` `rfSCatchEarlyReturn`, `rfS_liftR`
`rfSLiftR`, `rfS_tick` `rfSTick`, `FEC_of_EvA_rfS` `FECOfEvARfS`, `F_tick` `FTick`,
`exec_exception_delegatee_S` `execExceptionDelegateeS`, `exec_trap_handler_S_gen`
`execTrapHandlerSGen`, `exec_handle_exception_S` `execHandleExceptionS`, `xtrap_st` `xtrapSt`,
`exec_handle_exception_trap` `execHandleExceptionTrap`, `xtrap_st_other` `xtrapStOther`,
`xtrap_st_mstatus` `xtrapStMstatus`, `xtrap_st_elp` `xtrapStElp`, `xtrap_st_priv` `xtrapStPriv`,
`xtrap_st_nextPC` `xtrapStNextPC`, `xtrap_ok_S` `xtrapOkS`.  None is in the duplicated-name table.
Lean-only (file-qualified): `AxSpinVA6.rfSOfRfF`, `AxSpinVA6.rfSIte`, `AxSpinVA6.trapS9`; local
tactic `va6_rfs`.

**Dropped:** the Ltacs (deviation 5).  Rocq 1 fixpoint + 1 definition + 18 lemmas + 5 Ltacs;
Lean 20 + 3 Lean-only.  **Not ported:** the `Print Assumptions` lines (the lint's axiom check
covers them).
-/
import Weak.AxSpinVA3
import Weak.AxIntr2
import Weak.AxSpineOk7
import Weak.ExecSC7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. `rfS` and the transfer -/

/-- Rocq `rfS` (deviation 2): `rfF` with pin READS allowed. -/
def rfS {X : Type} : SailM X → Prop
  | .pure _ => True
  | .impure (.error _) _ => True
  | .impure (.ok o) k =>
    match o, k with
    | .regRead _, k => ∀ v, rfS (k v)
    | .regWrite r _, k => ¬ AxRunClose.pinReg r ∧ rfS (k PUnit.unit)
    | .memRead .., _ => False
    | .memWrite .., _ => False
    | .barrier _, _ => False
    | .cacheOp _, k => rfS (k ())
    | .tlbi _, k => rfS (k ())
    | .translationStart _, k => rfS (k ())
    | .translationEnd _, k => rfS (k ())
    | .takeException _, k => rfS (k ())
    | .returnException _, k => rfS (k ())
    | .cycleCount, k => rfS (k ())
    | .getCycleCount, k => rfS (k (0 : Nat))
    | .message _, k => rfS (k ())
    | .instrAnnounce n w, k => sfAnnB n w = false ∧ rfS (k ())
    | .branchAnnounce _ _, k => rfS (k ())
    | .choose _, _ => True
    | .readRam .., _ => True
    | .writeRam .., _ => True

theorem rfSBind {X Y : Type} (m : SailM X) (f : X → SailM Y) :
    rfS m → (∀ x, rfS (f x)) → rfS (m >>= f) := by
  induction m with
  | pure y => intro _ hf; exact hf y
  | impure call k ih =>
    intro hm hf
    cases call with
    | error e => trivial
    | ok o =>
      show rfS (FreeM.impure (.ok o) (fun v => k v >>= f))
      cases o
      case regRead r => exact fun v => ih v (hm v) hf
      case regWrite r v => exact ⟨hm.1, ih _ hm.2 hf⟩
      case instrAnnounce n w => exact ⟨hm.1, ih _ hm.2 hf⟩
      all_goals first | exact hm | trivial | exact ih _ hm hf

theorem rfSBind0 {Y : Type} (m : SailM Unit) (n : SailM Y) :
    rfS m → rfS n → rfS (m >>= fun _ => n) :=
  fun hm hn => rfSBind m (fun _ => n) hm (fun _ => hn)

theorem rfSTryCatch {X : Type} (m : SailM X) (h : Sail.Error exception → SailM X) :
    rfS m → (∀ e, rfS (h e)) → rfS (PreSail.tryCatchAll m h) := by
  induction m with
  | pure y => intro _ _; trivial
  | impure call k ih =>
    intro hm hh
    cases call with
    | error e => exact hh e
    | ok o =>
      show rfS (FreeM.impure (.ok o) (fun r => PreSail.tryCatchAll (k r) h))
      cases o
      case regRead r => exact fun v => ih v (hm v) hh
      case regWrite r v => exact ⟨hm.1, ih _ hm.2 hh⟩
      case instrAnnounce n w => exact ⟨hm.1, ih _ hm.2 hh⟩
      all_goals first | exact hm | trivial | exact ih _ hm hh

theorem rfSCatchEarlyReturn {X : Type} (m : SailME X X) :
    rfS (ExceptT.run m) → rfS (SailME.run m) := by
  intro hm
  show rfS (ExceptT.run m >>= _)
  refine rfSBind _ _ hm (fun e => ?_)
  rcases e with (e | r) | x <;> trivial

theorem rfSLiftR {R X : Type} (m : SailM X) : rfS m → rfS (ExceptT.run (liftM m : SailME R X)) := by
  intro h
  have e : ExceptT.run (liftM m : SailME R X) = m >>= fun a => pure (Except.ok a) := rfl
  rw [e]
  exact rfSBind _ _ h (fun _ => trivial)

/-- (Lean-only) A register-only (`rfF`) tree is `rfS`. -/
theorem AxSpinVA6.rfSOfRfF {X : Type} (m : SailM X) : rfF m → rfS m := by
  induction m with
  | pure y => intro _; trivial
  | impure call k ih =>
    intro hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r => exact fun v => ih v (hm.2 v)
      case regWrite r v => exact ⟨hm.1, ih _ hm.2⟩
      case instrAnnounce n w => exact ⟨hm.1, ih _ hm.2⟩
      all_goals first | exact hm | trivial | exact ih _ hm

/-- (Lean-only) An `if`. -/
theorem AxSpinVA6.rfSIte {X : Type} (c : Prop) [Decidable c] (a b : SailM X)
    (ha : rfS a) (hb : rfS b) : rfS (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb

/-- (deviation 5) The `rfS` walker. -/
local macro "va6_rfs" : tactic => `(tactic| repeat (first
      | with_reducible exact AxSpinVA6.rfSOfRfF _ (AxSpineOk7.rfFShouldIncMcycle _)
      | with_reducible exact AxSpinVA6.rfSOfRfF _ AxSpineOk7.rfFCurrentlyEnabledSstc
      | with_reducible exact AxSpinVA6.rfSOfRfF _ AxSpineOk7.rfFCurrentlyEnabledS
      | (rw [AxSpineOk7.csrMip])
      | (apply rfSBind <;> try intro _)
      | apply AxSpinVA6.rfSIte
      | exact True.intro
      | (simp only [rfS, readReg, writeReg, PreSail.readReg, PreSail.writeReg, PreSail.emit])
      | (refine ⟨?_, ?_⟩)
      | (intro h; rcases h with h | h <;> cases h)
      | (intro _)
      | rfl))

/-- Rocq `rfS_tick`. -/
theorem rfSTick : rfS (tick_clock ()) := by
  unfold tick_clock clint_dispatch read_mip external_interrupts_pending
  va6_rfs

/-- Rocq `FEC_of_EvA_rfS`: THE TRANSFER — an `rfS` tree's `EvA` fact is an `FEC` fact, chain
untouched. -/
theorem FECOfEvARfS (img img' : Image) {X : Type} (QE : Sail.Error exception → ExecSt → Prop)
    (Q : X → ExecSt → Prop) (m : SailM X) (t : ExecSt) (Ks : List ekey) :
    rfS m → EvA img QE Q m t →
    FEC img' (fun Ks' e t' => Ks' = Ks ∧ QE e t') (fun Ks' x t' => Ks' = Ks ∧ Q x t') Ks m t := by
  intro hrf he
  induction he with
  | evRet x t h => exact .fcRet Ks x t ⟨rfl, h⟩
  | evExt e k t h => exact .fcExt Ks e k t ⟨rfl, h⟩
  | evRd r k t _ _ ihs ihn =>
    exact .fcRd Ks r k t (fun hp v => ihs hp v (hrf v)) (fun hn => ihn hn (hrf _))
  | evWr r v k t hr _ ih => exact .fcWr Ks r v k t hr (ih hrf.2)
  | evMrd n va req k t vs h1 h2 h3 _ _ => exact hrf.elim
  | evIa n w k t hs _ ih => exact .fcIa Ks n w k t hs (ih hrf.2)
  | evBa n a k t _ ih => exact .fcBa Ks n a k t (ih hrf)
  | evCo c k t _ ih => exact .fcCo Ks c k t (ih hrf)
  | evTl c k t _ ih => exact .fcTl Ks c k t (ih hrf)
  | evTe f k t _ ih => exact .fcTe Ks f k t (ih hrf)
  | evRx a k t _ ih => exact .fcRx Ks a k t (ih hrf)
  | evTs a k t _ ih => exact .fcTs Ks a k t (ih hrf)
  | evTx a k t _ ih => exact .fcTx Ks a k t (ih hrf)
  | evCc k t _ ih => exact .fcCc Ks k t (ih hrf)
  | evMsg a k t _ ih => exact .fcMsg Ks a k t (ih hrf)
  | evGcc k t _ ih => exact .fcGcc Ks k t (ih hrf)

/-- Rocq `F_tick` (deviation 4): the tick, at the regime — no label, chain untouched, regime
kept, PC kept. -/
theorem FTick (img : Image) (T : PTree) (satp0 : BitVec 64) (t : ExecSt) (Ks : List ekey)
    (Q : List ekey → Unit → ExecSt → Prop) :
    ctrlOkS T satp0 t.regs →
    (∀ t', ctrlOkS T satp0 t'.regs → keepRegs t.regs t'.regs → Q Ks () t') →
    FEC img (fun _ _ _ => False) Q Ks (tick_clock ()) t := by
  intro hc hQ
  have HE := sptTickS t T satp0 t hc
  refine FECMono img _ _ _ _ Ks _ t ?_ ?_ (FECOfEvARfS _ img _ _ _ t Ks rfSTick HE)
  · rintro _ _ _ ⟨_, ⟨⟩⟩
  · rintro Ks' ⟨⟩ t' ⟨rfl, hc', hk⟩
    exact hQ t' hc' hk

/-! # 2. The S-mode exception tower -/

/-- Rocq `exec_exception_delegatee_S`. -/
theorem execExceptionDelegateeS (e : ExceptionType) (medl : BitVec 64) (s : ExecSt) :
    s.regs .medeleg = medl →
    exec (currentlyEnabled .Ext_S) s = some (true, s) →
    bit_to_bool (BitVec.access medl (BitVec.toNatInt (exceptionType_bits_forwards e))) = true →
    exec (exception_delegatee e .Supervisor) s = some (.Supervisor, s) := by
  intro hmedl hes hbit
  unfold exception_delegatee
  exec_run [hmedl, hes, hbit]

/-- (Lean-only, deviation 3) Rocq's `s9` of section `XTrapReduce`: the model's exact write order
of an S-mode trap, for any cause and tval payload. -/
def AxSpinVA6.trapS9 (s : ExecSt) (c : TrapCause) (info : Option (BitVec 64))
    (pc0 ms_v sc_old : BitVec 64) (elp_v : BitVec 1) : ExecSt :=
  -- since 2026-11-04 (no Zicfilp) the trap neither banks `elp` into `SPELP` nor resets `elp`;
  -- `elp_v` is kept (unused) so that the statements over this state are unchanged
  let ms_e := ms_v
  let s1e := s
  let c1 := Sail.BitVec.updateSubrange sc_old (64 - 1) (64 - 1) (bool_to_bit (trapCause_is_interrupt c))
  let c2 := Sail.BitVec.updateSubrange c1 (64 - 2) 0
    (zero_extend (m := 64 - 1) (trapCause_bits_forwards c))
  let ms_a := Sail.BitVec.updateSubrange ms_e 5 5 (_get_Mstatus_SIE ms_e)
  let ms_b := Sail.BitVec.updateSubrange ms_a 1 1 0#1
  let ms_c := Sail.BitVec.updateSubrange ms_b 8 8 1#1
  ((((((((s1e.setReg .scause c1).setReg .scause c2).setReg .mstatus ms_a).setReg .mstatus ms_b).setReg .mstatus
    ms_c).setReg .stval (tval info)).setReg .sepc pc0).setReg .cur_privilege .Supervisor)

/-- Rocq `exec_trap_handler_S_gen` (deviation 3). -/
theorem execTrapHandlerSGen (s : ExecSt) (c : TrapCause) (info : Option (BitVec 64))
    (pc0 ms_v sc_old stvec_v : BitVec 64) (elp_v : BitVec 1)
    (hpriv : s.regs .cur_privilege = .Supervisor) (hms : s.regs .mstatus = ms_v)
    (hsc : s.regs .scause = sc_old) (hstvec : s.regs .stvec = stvec_v) (help : s.regs .elp = elp_v)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true)
    (htvd : trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = .TV_Direct) :
    exec (trap_handler .Supervisor c pc0 info none) s =
      some (stvecBase stvec_v, AxSpinVA6.trapS9 s c info pc0 ms_v sc_old elp_v) := by
  subst hms hsc hstvec help
  unfold trap_handler get_config_print_exception
    get_config_print_interrupt prepare_trap_vector
  exec_run [hartSupportsZicfilp, execTrackTrapS]
  simp (config := { decide := true }) only [ExecSt.setReg_regs, RegFile.set_other, RegFile.set_same,
    execCurrentlyEnabledS, hS, hpriv, execBind, exec, execReturnm, ↓reduceIte]
  exec_run [execTrackTrapS, tvec_addr]
  simp (config := { decide := true }) only [ExecSt.setReg_regs, RegFile.set_other, htvd]
  rfl

/-- Rocq `exec_handle_exception_S`. -/
theorem execHandleExceptionS (s : ExecSt) (c : TrapCause) (info : Option (BitVec 64))
    (pc0 ms_v sc_old stvec_v : BitVec 64) (elp_v : BitVec 1)
    (hpriv : s.regs .cur_privilege = .Supervisor) (hms : s.regs .mstatus = ms_v)
    (hsc : s.regs .scause = sc_old) (hstvec : s.regs .stvec = stvec_v) (help : s.regs .elp = elp_v)
    (hS : (_get_Misa_S (s.regs .misa) == 1#1) = true)
    (htvd : trapVectorMode_forwards (_get_Mtvec_Mode stvec_v) = .TV_Direct) (hpc : s.regs .PC = pc0)
    (e : ExceptionType) (xv : BitVec 64) (hc : c = .Exception e)
    (hinfo : info = xtval_exception_value e xv)
    (hdel : bit_to_bool (BitVec.access (s.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards e))) = true) :
    exec (handle_exception xv e) s =
      some ((), (AxSpinVA6.trapS9 s c info pc0 ms_v sc_old elp_v).setReg .nextPC (stvecBase stvec_v)) := by
  have hES : exec (currentlyEnabled .Ext_S) s = some (true, s) := by
    rw [execCurrentlyEnabledS, hS]
  have hdl := execExceptionDelegateeS e _ s rfl hES hdel
  have hth := execTrapHandlerSGen s c info pc0 ms_v sc_old stvec_v elp_v hpriv hms hsc hstvec help
    hS htvd
  subst hc hinfo
  unfold handle_exception exception_handler make_sync_exception
  exec_run [hpriv, hpc, hdl, get_config_print_exception, hth, execSetNextPc]

/-- Rocq `xtrap_st`: the exception trap state (deviation 3). -/
def xtrapSt (s : ExecSt) (e : ExceptionType) (xv : BitVec 64) : ExecSt :=
  (AxSpinVA6.trapS9 s (.Exception e) (xtval_exception_value e xv) (s.regs .PC) (s.regs .mstatus)
    (s.regs .scause) (s.regs .elp)).setReg .nextPC (stvecBase (s.regs .stvec))

/-- Rocq `exec_handle_exception_trap`. -/
theorem execHandleExceptionTrap (s : ExecSt) (e : ExceptionType) (xv : BitVec 64) :
    s.regs .cur_privilege = .Supervisor →
    (_get_Misa_S (s.regs .misa) == 1#1) = true →
    AxIntr.stvecDirect s.regs →
    bit_to_bool (BitVec.access (s.regs .medeleg)
      (BitVec.toNatInt (exceptionType_bits_forwards e))) = true →
    exec (handle_exception xv e) s = some ((), xtrapSt s e xv) := by
  intro hp hm hd hdel
  exact execHandleExceptionS s (.Exception e) (xtval_exception_value e xv) _ _ _ _ _
    hp rfl rfl rfl rfl hm hd rfl e xv rfl rfl hdel

/-- Rocq `xtrap_st_other`. -/
theorem xtrapStOther (s : ExecSt) (e : ExceptionType) (xv : BitVec 64) (r : Register) :
    r ≠ .mstatus → r ≠ .elp → r ≠ .scause → r ≠ .stval → r ≠ .sepc → r ≠ .cur_privilege →
    r ≠ .nextPC → (xtrapSt s e xv).regs r = s.regs r := by
  intro h1 h2 h3 h4 h5 h6 h7
  simp only [xtrapSt, AxSpinVA6.trapS9, ExecSt.setReg_regs, RegFile.set_other _ _ _ _ h1,
    RegFile.set_other _ _ _ _ h2, RegFile.set_other _ _ _ _ h3, RegFile.set_other _ _ _ _ h4,
    RegFile.set_other _ _ _ _ h5, RegFile.set_other _ _ _ _ h6, RegFile.set_other _ _ _ _ h7]

/-- Rocq `xtrap_st_mstatus`. -/
theorem xtrapStMstatus (s : ExecSt) (e : ExceptionType) (xv : BitVec 64) :
    (xtrapSt s e xv).regs .mstatus = AxIntr2.trapMs (s.regs .elp) (s.regs .mstatus) := by
  simp (disch := decide) only [xtrapSt, AxSpinVA6.trapS9, ExecSt.setReg_regs, RegFile.set_same,
    RegFile.set_other]
  rfl

/-- Rocq `xtrap_st_elp` -- CHANGED 2026-11-04: with no Zicfilp the trap leaves `elp` alone. -/
theorem xtrapStElp (s : ExecSt) (e : ExceptionType) (xv : BitVec 64) :
    (xtrapSt s e xv).regs .elp = s.regs .elp := by
  simp (disch := decide) only [xtrapSt, AxSpinVA6.trapS9, ExecSt.setReg_regs, RegFile.set_same,
    RegFile.set_other]

/-- Rocq `xtrap_st_priv`. -/
theorem xtrapStPriv (s : ExecSt) (e : ExceptionType) (xv : BitVec 64) :
    (xtrapSt s e xv).regs .cur_privilege = .Supervisor := by
  simp (disch := decide) only [xtrapSt, AxSpinVA6.trapS9, ExecSt.setReg_regs, RegFile.set_same,
    RegFile.set_other]

/-- Rocq `xtrap_st_nextPC`. -/
theorem xtrapStNextPC (s : ExecSt) (e : ExceptionType) (xv : BitVec 64) :
    (xtrapSt s e xv).regs .nextPC = stvecBase (s.regs .stvec) := by
  simp only [xtrapSt, ExecSt.setReg_regs, RegFile.set_same]

/-- Rocq `xtrap_ok_S`: the exception trap lands in the (SIE = 0) regime. -/
theorem xtrapOkS (T : PTree) (satp0 : BitVec 64) (s : ExecSt) (e : ExceptionType) (xv : BitVec 64) :
    ctrlOkS T satp0 s.regs → ctrlOkS T satp0 (xtrapSt s e xv).regs := by
  intro hc
  have ho := xtrapStOther s e xv
  obtain ⟨-, h2, h3, h4, h5, h6, h7, h8, -, h10, h11, h12, h13⟩ := hc
  unfold AxSpineOk6.pmpOk at h13
  unfold ctrlOkS AxSpineOk6.pmpOk
  simp (disch := decide) only [xtrapStPriv, xtrapStElp, xtrapStMstatus, ho]
  exact ⟨by first | trivial | rfl, h2, h3, h4, h5, h6, h7,
    sconfMsFactsTrap _ _ h8, AxIntr2.trapMsSIEFalse _ _, h10, h11, h12, h13⟩

end Weak
