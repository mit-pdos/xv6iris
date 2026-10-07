/-
Weak: **X for LOADS and STORES** — the `EvD` spine, the per-instruction data certificate
`ExecD`, the whole-instruction certificate `spineCertD` and the theorems `XMemHoldsM`/`XMemHolds`.

Rocq: `iris/AxSymMem2.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 THE `EvD` SPINE KIT: the twins of `AxSymEngine2`/`AxSpineOk5`'s `run_hart_active` /
`try_step` / `riscv_step` composition lemmas (`EvDHartActiveRvc`, `EvDTryStepActive`,
`EvDRiscvStep`), every image-only sub-computation an `EvA` fact, the instruction's `execute`
an `EvD` fact.
§2 `ExecD ctrlOk rs pc wr dp ins` is the ONLY instruction-specific fact: at every post-fetch
state agreeing with the boundary GPRs (`nextPC = pc + 2`, control ok), `execute ins` performs
its ONE data event (demonic read / validated write, `AxSymMem.EvD`) and ends in a tlb-framed
(the data translation may fill the TLB, as the fetch: AxSpineOk5 FINDING), control-ok state,
with at most one GPR written (`wr d`: the register and value, a function of the data event —
for a load `ext vs`).  It is the `EvD` twin of `XGprWrite`'s `exec (execute ins)` premise.
`spineCertD`: the whole-instruction certificate over the real S-mode spine `SpineOkT`.
§3 `XMemM`: the WPd twin of the SC load/store engines: at a `.pure ()` boundary in the regime,
with `ins` in the text and its certificate `ExecD`, the caller's data-event flow `DResM DPend`
buys a continuation at EVERY next boundary (control ok, PC + 2, GPRs per `gprAfter wr d`, and
the flow's output `DResM d`).  `XMemHoldsM` proves it; `wrLoad`/`wrStore` are the load and
store instances of `wr`; `XLoad`/`XStore` name the two families.

## Deviations from Rocq

1. O2 STAGE C (as `AxSymMem` deviation 1): the section premises `Hloc` and `Hntext` of
   `XMemHoldsM` are DROPPED (`AxSymMem.wpdInstrOfEvDM` no longer takes them).
2. Types as `AxSpineOk5`/`AxSymEngine2`: `mstate` ↦ `ExecSt`, `register_lookup r rs` ↦ `rs r`,
   `set_reg` ↦ `ExecSt.setReg`, `seip_reg` ↦ `AxRunClose.pinReg`, `gpr_agree` ↦ `gprAgree`,
   `mword 5`/`mword 64` ↦ `BitVec 5`/`BitVec 64`.  The GPR `R_bitvector_64 (gpr_of_Z (uint r))`
   is READ as `uxaXget rs r` and WRITTEN by `ExecSt.setGpr rd v` (so `wrState` discards an
   `x0` write; every use carries `rd.toNat ≠ 0`); `Z.eqb (uint r) (uint rd)` ↦ `r = rd`.
   `wrStateLookup`'s premise names the register by `AxSymEngine2.gprReg rd`.
3. Rocq's `evd_step`/`evd_go`/`evd_use`/`evd_useD`/`lk` Ltacs ↦ the Lean-only stepping kit
   `AxSymMem2.evd*` (the `EvD` twins of `AxSymEngine2.ev*`) and the tactic
   `ax_sym_mem2_evd_go` (the twin of `ax_sym2_ev_go`); `lk` ↦ `RegFile.set_same`/`set_other`.
   `EvDReadReg`/`EvDWriteReg`/`EvDLiftRM` are stated on `SailM` (as `EvAReadReg`/`EvALiftRAny`;
   `liftR` ↦ `ExceptT.run (liftM m)`).  `EvDRiscvStep` is the tick split of `riscvStep`.
4. `XMemM`/`XMem` quantify over `{hlc}` (Rocq `HasNoLc`); `X_mem_holds` (a Rocq `Definition`)
   is the theorem `XMemHolds`; `XLoad`/`XStore` are `XMem` at `kind := true`/`false`.

**Rocq → Lean name map.**  `EvD_read_reg` `EvDReadReg`, `EvD_write_reg` `EvDWriteReg`,
`EvD_liftR_M` `EvDLiftRM`, `EvD_hart_active_rvc` `EvDHartActiveRvc`, `EvD_try_step_active`
`EvDTryStepActive`, `EvD_riscv_step` `EvDRiscvStep`, `gpr_after` `gprAfter`, `wr_state`
`wrState`, `ExecD` `ExecD`, `text_ok_m` `textOkM`, `GoodD` `GoodD`, `wr_state_lookup`
`wrStateLookup`, `spine_certD` `spineCertD`, `X_memM` `XMemM`, `X_mem` `XMem`, `X_mem_holdsM`
`XMemHoldsM`, `X_mem_holds` `XMemHolds`, `wr_load` `wrLoad`, `wr_store` `wrStore`,
`wr_load_rd0` `wrLoadRd0`, `wr_store_rd0` `wrStoreRd0`, `X_load` `XLoad`, `X_store` `XStore`.
None is in the duplicated-name table.  Lean-only (file-qualified): the kit `AxSymMem2.evd*`,
`AxSymMem2.gprRegMem`, `AxSymMem2.setGprRegsNeReg`.

**Dropped:** nothing (Rocq 23 definitions/lemmas + 5 Ltacs; Lean 23 + the kit).
**Not ported:** the `Print Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxSymMem
import Weak.AxSpineOk5

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-! # 1. The `EvD` spine kit -/

section spineD
variable (img : Image) (dok : Int → Nat → Prop) (kind : Bool)

theorem EvDReadReg (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop) (r : Register)
    (Q : AxSymMem.Dstate → RegisterType r → ExecSt → Prop) (d : AxSymMem.Dstate) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → Q d (t.regs r) t →
    EvD img dok kind QE Q d (readReg r : SailM _) t :=
  fun hr hq => .evdRd d r _ t (fun h => absurd h hr) (fun _ => .evdRet d _ t hq)

theorem EvDWriteReg (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → PUnit → ExecSt → Prop) (r : Register) (v : RegisterType r)
    (d : AxSymMem.Dstate) (t : ExecSt) :
    ¬ AxRunClose.pinReg r → Q d PUnit.unit (t.setReg r v) →
    EvD img dok kind QE Q d (writeReg r v : SailM _) t :=
  fun hr hq => .evdWr d r v _ t hr (.evdRet d _ _ hq)

theorem EvDLiftRM {R X : Type} (QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop)
    (Q : AxSymMem.Dstate → X → ExecSt → Prop) (m : SailM X) (d : AxSymMem.Dstate) (t : ExecSt) :
    EvD img dok kind (fun _ _ _ => False) Q d m t →
    EvD img dok kind QE
      (fun d' (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q d' x t'
        | .error _ => False)
      d (ExceptT.run (liftM m : SailME R X)) t :=
  EvDLiftRAny img dok kind _ QE Q m d t (fun _ _ _ h => h.elim)

end spineD

/-! ### (Lean-only) the stepping kit (Rocq's `evd_step`/`evd_go`/`evd_use`/`evd_useD`) -/

section kit
variable {img : Image} {dok : Int → Nat → Prop} {kind : Bool}
variable {QE : AxSymMem.Dstate → Sail.Error exception → ExecSt → Prop}

theorem AxSymMem2.evdFactRead {Y : Type} {Q : AxSymMem.Dstate → Y → ExecSt → Prop} {r : Register}
    {f : RegisterType r → SailM Y} {d : AxSymMem.Dstate} {t : ExecSt} (hr : ¬ AxRunClose.pinReg r)
    (H : EvD img dok kind QE Q d (f (t.regs r)) t) : EvD img dok kind QE Q d (readReg r >>= f) t :=
  EvDBind img dok kind QE Q _ f d t (EvDReadReg img dok kind QE r _ d t hr H)

theorem AxSymMem2.evdFactWrite {Y : Type} {Q : AxSymMem.Dstate → Y → ExecSt → Prop} {r : Register}
    {v : RegisterType r} {f : PUnit → SailM Y} {d : AxSymMem.Dstate} {t : ExecSt}
    (hr : ¬ AxRunClose.pinReg r) (H : EvD img dok kind QE Q d (f PUnit.unit) (t.setReg r v)) :
    EvD img dok kind QE Q d (writeReg r v >>= f) t :=
  EvDBind img dok kind QE Q _ f d t (EvDWriteReg img dok kind QE _ r v d t hr H)

theorem AxSymMem2.evdFactPure {X Y : Type} {Q : AxSymMem.Dstate → Y → ExecSt → Prop} {x : X}
    {f : X → SailM Y} {d : AxSymMem.Dstate} {t : ExecSt} (H : EvD img dok kind QE Q d (f x) t) :
    EvD img dok kind QE Q d (pure x >>= f) t := H

/-- An `EvA` fact for the first computation (`evd_use`). -/
theorem AxSymMem2.evdFactQ {X Y : Type} {P : X → ExecSt → Prop}
    {Q : AxSymMem.Dstate → Y → ExecSt → Prop} {m : SailM X} {f : X → SailM Y}
    {d : AxSymMem.Dstate} {t : ExecSt} (Hm : EvA img (fun _ _ => False) P m t)
    (Hf : ∀ x t', P x t' → EvD img dok kind QE Q d (f x) t') :
    EvD img dok kind QE Q d (m >>= f) t :=
  EvDBind img dok kind QE Q m f d t
    (EvDOfEvA' img dok kind _ _ _ _ d m t (fun _ _ h => h.elim) Hf Hm)

/-- An `EvD` fact for the first computation (`evd_useD`). -/
theorem AxSymMem2.evdFactQD {X Y : Type} {P : AxSymMem.Dstate → X → ExecSt → Prop}
    {Q : AxSymMem.Dstate → Y → ExecSt → Prop} {m : SailM X} {f : X → SailM Y}
    {d : AxSymMem.Dstate} {t : ExecSt} (Hm : EvD img dok kind (fun _ _ _ => False) P d m t)
    (Hf : ∀ d' x t', P d' x t' → EvD img dok kind QE Q d' (f x) t') :
    EvD img dok kind QE Q d (m >>= f) t :=
  EvDBind img dok kind QE Q m f d t
    (EvDMono img dok kind _ _ _ _ d m t (fun _ _ _ h => h.elim) Hf Hm)

theorem AxSymMem2.evdFactUse {X Y : Type} {Q : AxSymMem.Dstate → Y → ExecSt → Prop} {m : SailM X}
    {f : X → SailM Y} {d : AxSymMem.Dstate} {t t1 : ExecSt} {a : X}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t)
    (H : EvD img dok kind QE Q d (f a) t1) : EvD img dok kind QE Q d (m >>= f) t :=
  AxSymMem2.evdFactQ Hm (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

/-- The early-return monad's bind, through `ExceptT.run`, with an `EvD` fact first. -/
theorem AxSymMem2.evdFactLiftD {R X Y : Type} {P : AxSymMem.Dstate → X → ExecSt → Prop}
    {Q : AxSymMem.Dstate → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailME R Y} {d : AxSymMem.Dstate} {t : ExecSt}
    (Hm : EvD img dok kind (fun _ _ _ => False) P d m t)
    (Hf : ∀ d' x t', P d' x t' → EvD img dok kind QE Q d' (ExceptT.run (f x)) t') :
    EvD img dok kind QE Q d (ExceptT.run (liftM m >>= f)) t := by
  rw [ExceptT.run_bind]
  apply EvDBind
  refine EvDMono img dok kind _ _ _ _ d _ t (fun _ _ _ h => h) ?_
    (EvDLiftRM img dok kind (R := R) QE P m d t Hm)
  intro d' r t' h
  cases r with
  | ok a => exact Hf d' a t' h
  | error e => exact h.elim

theorem AxSymMem2.evdFactLift {R X Y : Type} {P : X → ExecSt → Prop}
    {Q : AxSymMem.Dstate → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailME R Y} {d : AxSymMem.Dstate} {t : ExecSt}
    (Hm : EvA img (fun _ _ => False) P m t)
    (Hf : ∀ x t', P x t' → EvD img dok kind QE Q d (ExceptT.run (f x)) t') :
    EvD img dok kind QE Q d (ExceptT.run (liftM m >>= f)) t :=
  AxSymMem2.evdFactLiftD (P := fun d' x t' => d' = d ∧ P x t')
    (EvDOfEvA' img dok kind _ _ _ _ d m t (fun _ _ h => h.elim) (fun _ _ h => ⟨rfl, h⟩) Hm)
    (fun _ x t' h => by obtain ⟨rfl, h⟩ := h; exact Hf x t' h)

theorem AxSymMem2.evdRRead {R X : Type}
    {Q : AxSymMem.Dstate → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {r : Register} {f : RegisterType r → SailME R X} {d : AxSymMem.Dstate} {t : ExecSt}
    (hr : ¬ AxRunClose.pinReg r) (H : EvD img dok kind QE Q d (ExceptT.run (f (t.regs r))) t) :
    EvD img dok kind QE Q d (ExceptT.run (liftM (readReg r) >>= f)) t :=
  AxSymMem2.evdFactLift (P := fun x t' => x = t.regs r ∧ t' = t)
    (EvAReadReg img _ r _ t hr ⟨rfl, rfl⟩) (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

theorem AxSymMem2.evdRWrite {R X : Type}
    {Q : AxSymMem.Dstate → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {r : Register} {v : RegisterType r} {f : PUnit → SailME R X} {d : AxSymMem.Dstate}
    {t : ExecSt} (hr : ¬ AxRunClose.pinReg r)
    (H : EvD img dok kind QE Q d (ExceptT.run (f PUnit.unit)) (t.setReg r v)) :
    EvD img dok kind QE Q d (ExceptT.run (liftM (writeReg r v) >>= f)) t :=
  AxSymMem2.evdFactLift (P := fun _ t' => t' = t.setReg r v)
    (EvAWriteReg img _ _ r v t hr rfl) (fun _ _ h => by subst h; exact H)

theorem AxSymMem2.evdRPureBind {R X Y : Type}
    {Q : AxSymMem.Dstate → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop} {x : Y}
    {f : Y → SailME R X} {d : AxSymMem.Dstate} {t : ExecSt}
    (H : EvD img dok kind QE Q d (ExceptT.run (f x)) t) :
    EvD img dok kind QE Q d (ExceptT.run (pure x >>= f)) t := H

theorem AxSymMem2.evdRUse {R X Y : Type}
    {Q : AxSymMem.Dstate → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {m : SailM Y} {f : Y → SailME R X} {d : AxSymMem.Dstate} {t t1 : ExecSt} {a : Y}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t)
    (H : EvD img dok kind QE Q d (ExceptT.run (f a)) t1) :
    EvD img dok kind QE Q d (ExceptT.run (liftM m >>= f)) t :=
  AxSymMem2.evdFactLift Hm (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

theorem AxSymMem2.evdRAnn16 {R X : Type}
    {Q : AxSymMem.Dstate → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {h : BitVec 16} {f : Unit → SailME R X} {d : AxSymMem.Dstate} {t : ExecSt}
    (H : EvD img dok kind QE Q d (ExceptT.run (f ())) t) :
    EvD img dok kind QE Q d (ExceptT.run (liftM (instr_announce h : SailM Unit) >>= f)) t :=
  AxSymMem2.evdFactLift (AxSymEngine2.evInstrAnnounce16 img _ h t)
    (fun _ _ h => by subst h; exact H)

theorem AxSymMem2.evdFactAssoc {X Y Z : Type} {Q : AxSymMem.Dstate → Z → ExecSt → Prop}
    {m : SailM X} {f : X → SailM Y} {g : Y → SailM Z} {d : AxSymMem.Dstate} {t : ExecSt}
    (H : EvD img dok kind QE Q d (m >>= fun x => f x >>= g) t) :
    EvD img dok kind QE Q d ((m >>= f) >>= g) t := by
  rw [bind_assoc]; exact H

theorem AxSymMem2.evdRAssoc {R X Y Z : Type}
    {Q : AxSymMem.Dstate → Except (Sail.Error exception ⊕ R) Z → ExecSt → Prop} {m : SailME R X}
    {f : X → SailME R Y} {g : Y → SailME R Z} {d : AxSymMem.Dstate} {t : ExecSt}
    (H : EvD img dok kind QE Q d (ExceptT.run (m >>= fun x => f x >>= g)) t) :
    EvD img dok kind QE Q d (ExceptT.run ((m >>= f) >>= g)) t := by
  rw [bind_assoc]; exact H

end kit

/-- Rocq's `evd_go` (the `EvD` twin of `ax_sym2_ev_go`): run the register reads/writes, `pure`s
and closed guards. -/
macro "ax_sym_mem2_evd_go" : tactic => `(tactic| repeat (first
  | ((with_reducible refine AxSymMem2.evdRRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | ((with_reducible refine AxSymMem2.evdRWrite ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxSymMem2.evdRAnn16 ?_
  | with_reducible refine AxSymMem2.evdRPureBind ?_
  | with_reducible refine AxSymMem2.evdRAssoc ?_
  | with_reducible refine AxSymMem2.evdFactAssoc ?_
  | ((with_reducible refine AxSymMem2.evdFactRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | ((with_reducible refine AxSymMem2.evdFactWrite ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxSymMem2.evdFactPure ?_
  | (simp (config := { decide := true }) only [↓reduceIte, Bool.false_eq_true,
      get_config_print_instr, get_config_rvfi, ext_fetch_hook, RETIRE_SUCCESS, tick_pc,
      hart_is_active, assert, PreSail.assert])))

section spineD2
variable (img : Image) (dok : Int → Nat → Prop) (kind : Bool)

theorem EvDHartActiveRvc (t t1 : ExecSt) (h : BitVec 16) (i0 ins : instruction) (pc : BitVec 64)
    (Qx : AxSymMem.Dstate → ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
      (dispatchInterrupt (t.regs .cur_privilege)) t →
    EvA img (fun _ _ => False) (fun r t' => r = .F_RVC h ∧ t' = t1) (fetch ()) t →
    EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t1) (ext_decode_compressed h) t1 →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t1) (is_landing_pad_expected ()) t1 →
    EvA img (fun _ _ => False) (fun x t' => x = true ∧ t' = t1) (currentlyEnabled .Ext_Zca) t1 →
    t1.regs .PC = pc →
    EvA img (fun _ _ => False)
      (fun x t' => x = .ExecuteAs ins ∧ t' = t1.setReg .nextPC (BitVec.addInt pc 2))
      (execute i0) (t1.setReg .nextPC (BitVec.addInt pc 2)) →
    EvD img dok kind (fun _ _ _ => False) (fun d x t' => x = RETIRE_SUCCESS ∧ Qx d t') .DPend
      (execute ins) (t1.setReg .nextPC (BitVec.addInt pc 2)) →
    EvD img dok kind (fun _ _ _ => False)
      (fun d x t' => x = .Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) h) ∧ Qx d t') .DPend
      (run_hart_active 0) t := by
  intro Hdisp Hfetch Hdec Hlpad Hzca HPC Hexp Hexec
  subst HPC
  unfold run_hart_active
  apply EvDCatchEarlyReturn
  ax_sym_mem2_evd_go
  refine AxSymMem2.evdRUse Hdisp ?_
  ax_sym_mem2_evd_go
  refine AxSymMem2.evdRUse Hfetch ?_
  ax_sym_mem2_evd_go
  refine AxSymMem2.evdRUse Hdec ?_
  ax_sym_mem2_evd_go
  refine AxSymMem2.evdRUse Hlpad ?_
  ax_sym_mem2_evd_go
  refine AxSymMem2.evdRUse Hzca ?_
  ax_sym_mem2_evd_go
  refine AxSymMem2.evdRUse Hexp ?_
  ax_sym_mem2_evd_go
  refine AxSymMem2.evdFactLiftD Hexec ?_
  rintro d _ t' ⟨rfl, hq⟩
  exact .evdRet _ _ _ ⟨rfl, hq⟩

theorem EvDTryStepActive (t : ExecSt) (b : Bool) (bits : BitVec 32)
    (Qx Qf : AxSymMem.Dstate → ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun x t' => x = b ∧ t' = t)
      (should_inc_minstret (t.regs .cur_privilege)) t →
    (t.setReg .minstret_increment b).regs .hart_state = .HART_ACTIVE () →
    EvD img dok kind (fun _ _ _ => False)
      (fun d x t' => x = .Step_Execute (RETIRE_SUCCESS, bits) ∧ Qx d t') .DPend
      (run_hart_active 0) (t.setReg .minstret_increment b) →
    (∀ d tx, Qx d tx → tx.regs .hart_state = .HART_ACTIVE () ∧
      tx.regs .minstret_increment = b ∧ Qf d (tfinal b tx)) →
    EvD img dok kind (fun _ _ _ => False) (fun d x t' => x = false ∧ Qf d t') .DPend
      (try_step 0 false) t := by
  intro Hsi Hha Hrun Hfin
  unfold try_step
  dsimp only
  ax_sym_mem2_evd_go
  refine AxSymMem2.evdFactUse Hsi ?_
  ax_sym_mem2_evd_go
  apply EvDBind
  ax_sym_mem2_evd_go
  simp only [Hha]
  refine EvDMono img dok kind _ _ _ _ _ _ _ (fun _ _ _ h => h) ?_ Hrun
  rintro d _ tx ⟨rfl, HQ⟩
  obtain ⟨Hhx, Hmix, HQf⟩ := Hfin d tx HQ
  ax_sym_mem2_evd_go
  simp only [Hhx]
  ax_sym_mem2_evd_go
  simp only [Hhx]
  ax_sym_mem2_evd_go
  have hmi : (tx.setReg .PC (tx.regs .nextPC)).regs .minstret_increment = b := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
    exact Hmix
  simp only [hmi]
  cases b <;> ax_sym_mem2_evd_go <;> exact .evdRet _ _ _ ⟨rfl, HQf⟩

theorem EvDRiscvStep (tick : Bool) (t : ExecSt) (Qf Q : AxSymMem.Dstate → ExecSt → Prop) :
    EvD img dok kind (fun _ _ _ => False) (fun d _ t' => Qf d t') .DPend (try_step 0 false) t →
    (∀ d t', Qf d t' → if tick then
        EvA img (fun _ _ => False) (fun _ t'' => Q d t'') (tick_clock ()) t'
      else Q d t') →
    EvD img dok kind (fun _ _ _ => False) (fun d _ t' => Q d t') .DPend (riscvStep tick) t := by
  intro Ht Hk
  unfold riscvStep
  refine AxSymMem2.evdFactQD Ht ?_
  intro d _ t' Hq
  have Hk' := Hk d t' Hq
  cases tick with
  | true => exact EvDOfEvA' img dok kind _ _ _ _ d _ t' (fun _ _ h => h.elim) (fun _ _ h => h) Hk'
  | false => exact .evdRet _ _ _ Hk'

end spineD2

/-! # 2. The data-execute certificate and the whole-instruction certificate -/

/-- The GPR written by the instruction, as a function of the data event. -/
def gprAfter (wr : AxSymMem.Dstate → Option (BitVec 5 × BitVec 64)) (d : AxSymMem.Dstate)
    (rs : RegFile) (r : BitVec 5) : BitVec 64 :=
  match wr d with
  | some (rd, v) => if r = rd then v else uxaXget rs r
  | none => uxaXget rs r

def wrState (wr : AxSymMem.Dstate → Option (BitVec 5 × BitVec 64)) (d : AxSymMem.Dstate)
    (t0 : ExecSt) : ExecSt :=
  match wr d with
  | some (rd, v) => t0.setGpr rd v
  | none => t0

section certD
variable (img : Image) (dok : Int → Nat → Prop) (kind : Bool)

/-- THE PER-INSTRUCTION DATA CERTIFICATE (the `EvD` twin of `XGprWrite`'s
`exec (execute ins)` premise). -/
def ExecD (ctrlOk : RegFile → Prop) (rs : RegFile) (pc : BitVec 64)
    (wr : AxSymMem.Dstate → Option (BitVec 5 × BitVec 64)) (dp : AxSymMem.Dstate → Prop)
    (ins : instruction) : Prop :=
  ∀ t : ExecSt, ctrlOk t.regs → t.regs .nextPC = BitVec.addInt pc 2 → gprAgree t.regs rs →
    EvD img dok kind (fun _ _ _ => False)
      (fun d x t' => x = RETIRE_SUCCESS ∧ d ≠ .DPend ∧ dp d ∧
        ∃ t0, tlbFrame t t0 ∧ ctrlOk t0.regs ∧ t' = wrState wr d t0)
      .DPend (execute ins) t

/-- `instr pc true ins` for a memory instruction: `textOkD` minus the register-only
footprint. -/
def textOkM (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (pc : BitVec 64) (is_rvc : Bool) (ins : instruction) : Prop :=
  is_rvc = true ∧ ∃ h i0, textAt pc h ∧
    (∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t) ∧
    (∀ t : ExecSt, EvA img (fun _ _ => False) (fun x t' => x = .ExecuteAs ins ∧ t' = t)
      (execute i0) t)

end certD

def GoodD (ctrlOk : RegFile → Prop) (rs : RegFile) (pc : BitVec 64)
    (wr : AxSymMem.Dstate → Option (BitVec 5 × BitVec 64)) (dp : AxSymMem.Dstate → Prop)
    (d : AxSymMem.Dstate) (rs' : RegFile) : Prop :=
  d ≠ .DPend ∧ dp d ∧ ctrlOk rs' ∧ rs' .PC = BitVec.addInt pc 2 ∧
    ∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = gprAfter wr d rs r

/-- (Lean-only) The GPR register of an index is a GPR. -/
theorem AxSymMem2.gprRegMem (i : BitVec 5) : AxSymEngine2.gprReg i ∈ uxaGprs := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- (Lean-only) A GPR write leaves every register but its own alone. -/
theorem AxSymMem2.setGprRegsNeReg (s : ExecSt) (i : BitVec 5) (v : BitVec 64) (r : Register)
    (h : r ≠ AxSymEngine2.gprReg i) : (s.setGpr i v).regs r = s.regs r := by
  rcases uxa_bv5_cases i with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | exact RegFile.set_other _ _ _ _ (fun e => h (by subst e; decide))

theorem wrStateLookup (wr : AxSymMem.Dstate → Option (BitVec 5 × BitVec 64))
    (d : AxSymMem.Dstate) (t0 : ExecSt) (r : Register) :
    (∀ rd v, wr d = some (rd, v) → r ≠ AxSymEngine2.gprReg rd) →
    (wrState wr d t0).regs r = t0.regs r := by
  intro Hne
  unfold wrState
  split
  · rename_i rd v E
    exact AxSymMem2.setGprRegsNeReg t0 rd v r (Hne rd v E)
  · rfl

section certD2
variable (img : Image) (dok : Int → Nat → Prop) (kind : Bool)

theorem spineCertD (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (Hsp : SpineOkT img ctrlOk textAt) (rs : RegFile) (pc : BitVec 64) (ins : instruction)
    (wr : AxSymMem.Dstate → Option (BitVec 5 × BitVec 64)) (dp : AxSymMem.Dstate → Prop) :
    ctrlOk rs → rs .PC = pc → textOkM img ctrlOk textAt pc true ins →
    (∀ d rd v, wr d = some (rd, v) → rd.toNat ≠ 0) →
    ExecD img dok kind ctrlOk rs pc wr dp ins →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      EvD img dok kind (fun _ _ _ => False) (fun d _ t' => GoodD ctrlOk rs pc wr dp d t'.regs)
        .DPend (riscvStep tick) t := by
  intro Hct HPC ⟨_, h, i0, Hat, Hdec, Hexp⟩ Hrd0 Hcert tick t Hag
  have Hct_t : ctrlOk t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨b, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment b).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  obtain ⟨t1, Hfr, Hct_1, Hfetch⟩ := Hsp.sptFetch _ pc h Hct_a HPC_a Hat
  have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
  have Hgag : gprAgree (t1.setReg .nextPC (BitVec.addInt pc 2)).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSpineOk5.tlbFrameXget _ _ Hfr,
      ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hct_pc : ctrlOk (t1.setReg .nextPC (BitVec.addInt pc 2)).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inl rfl)) Hct_1
  have Hnpc : (t1.setReg .nextPC (BitVec.addInt pc 2)).regs .nextPC = BitVec.addInt pc 2 := by
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Hexec := Hcert _ Hct_pc Hnpc Hgag
  have Hrun := EvDHartActiveRvc img dok kind (t.setReg .minstret_increment b) t1 h i0 ins pc
    (fun d tx => d ≠ .DPend ∧ dp d ∧ ∃ t0, tlbFrame (t1.setReg .nextPC (BitVec.addInt pc 2)) t0 ∧
      ctrlOk t0.regs ∧ tx = wrState wr d t0)
    (Hsp.sptDisp _ Hct_a) Hfetch (Hdec _ Hct_1) (Hsp.sptLpad _ Hct_1)
    (Hsp.sptZca _ Hct_1) HPC_1 (Hexp _) Hexec
  have Hmi1 : t1.regs .minstret_increment = b := by
    rw [tlbFrameLookup _ _ _ Hfr (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  /- the post-execute state `wrState wr d t0` off the GPRs and `tlb` -/
  have Hlk : ∀ (r : Register) d t0, r ∉ uxaGprs → r ≠ .tlb →
      tlbFrame (t1.setReg .nextPC (BitVec.addInt pc 2)) t0 →
      (wrState wr d t0).regs r = (t1.setReg .nextPC (BitVec.addInt pc 2)).regs r := by
    intro r d t0 Hr Htl Hf0
    rw [wrStateLookup wr d t0 r
      (fun rd _ _ e => Hr (e ▸ AxSymMem2.gprRegMem rd))]
    exact tlbFrameLookup _ _ _ Hf0 Htl
  refine EvDRiscvStep img dok kind tick t (fun d t' => GoodD ctrlOk rs pc wr dp d t'.regs) _ ?_ ?_
  · have HT := EvDTryStepActive img dok kind t b (zero_extend (m := 32) h)
      (fun d tx => d ≠ .DPend ∧ dp d ∧ ∃ t0,
        tlbFrame (t1.setReg .nextPC (BitVec.addInt pc 2)) t0 ∧ ctrlOk t0.regs ∧
        tx = wrState wr d t0)
      (fun d t' => GoodD ctrlOk rs pc wr dp d t'.regs) Hb (Hsp.sptHart _ Hct_a) Hrun ?_
    · exact EvDMono img dok kind _ _ _ _ _ _ t (fun _ _ _ h => h) (fun _ _ _ h => h.2) HT
    · rintro d _ ⟨Hd, Hdp, t0, Hf0, Hc0, rfl⟩
      have Hhs : (wrState wr d t0).regs .hart_state = .HART_ACTIVE () := by
        rw [Hlk _ d t0 (by decide) (by decide) Hf0]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.sptHart _ Hct_1
      have Hmi : (wrState wr d t0).regs .minstret_increment = b := by
        rw [Hlk _ d t0 (by decide) (by decide) Hf0]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hmi1
      have HnpcX : (wrState wr d t0).regs .nextPC = BitVec.addInt pc 2 := by
        rw [Hlk _ d t0 (by decide) (by decide) Hf0]
        exact Hnpc
      refine ⟨Hhs, Hmi, Hd, Hdp, ?_, ?_, ?_⟩
      · have Hct_x : ctrlOk (wrState wr d t0).regs := by
          unfold wrState
          split
          · exact AxSymEngine2.ctrlOkSetGpr ctrlOk Hsp.sptFrame _ _ _ Hc0
          · exact Hc0
        unfold tfinal
        cases b
        · exact Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x
        · exact Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x)
      · unfold tfinal
        cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
          (try rw [RegFile.set_other _ _ _ _ (by decide)]) <;>
          rw [RegFile.set_same] <;> exact HnpcX
      · intro r Hr
        have e : uxaXget (tfinal b (wrState wr d t0)).regs r = uxaXget (wrState wr d t0).regs r := by
          unfold tfinal
          cases b <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
            (try rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]) <;>
            rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
        rw [e]
        unfold wrState gprAfter
        split
        · rename_i rd v Ew
          have Hrd := Hrd0 _ _ _ Ew
          by_cases E : r = rd
          · subst E
            simp only [if_true]
            exact AxFetch3c.gprSetGprSame _ r v Hrd
          · simp only [E, if_false]
            rw [show uxaXget (t0.setGpr rd v).regs r = (t0.setGpr rd v).gpr r from rfl,
              AxFetch3c.gprSetGprNe _ rd r v E]
            unfold ExecSt.gpr
            rw [AxSpineOk5.tlbFrameXget _ _ Hf0]
            exact Hgag r Hr
        · rw [AxSpineOk5.tlbFrameXget _ _ Hf0]
          exact Hgag r Hr
  · intro d t' HG
    cases tick with
    | false => exact HG
    | true =>
      refine EvAMono img _ _ _ _ _ t' (fun _ _ h => h) ?_ (Hsp.sptTick t' HG.2.2.1)
      rintro _ t'' ⟨Hc, Hk1, Hk2⟩
      obtain ⟨Hd, Hdp, -, HG2, HG3⟩ := HG
      exact ⟨Hd, Hdp, Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩

end certD2

/-! # 3. X for memory instructions -/

/-- X_mem: the WPd twin of the SC load/store engines (see the header). -/
def XMemM {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
    (M : Gdexec → Prop) (dok : Int → Nat → Prop) (kind : Bool) (i : Agent) (cpu : CPU)
    (ctrlOk : RegFile → Prop) (textOk : BitVec 64 → Bool → instruction → Prop)
    (ExecOk : RegFile → BitVec 64 → (AxSymMem.Dstate → Option (BitVec 5 × BitVec 64)) →
      (AxSymMem.Dstate → Prop) → instruction → Prop)
    (G : Gdexec → Prop) (Φ : Athread → IProp GF) (Out : Nat → List (BitVec 8) → IProp GF) :
    Prop :=
  ∀ (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (ins : instruction)
    (wr : AxSymMem.Dstate → Option (BitVec 5 × BitVec 64)) (dp : AxSymMem.Dstate → Prop),
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc →
    textOk pc true ins → (∀ d rd v, wr d = some (rd, v) → rd.toNat ≠ 0) →
    ExecOk rs pc wr dp ins →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ DResM M dok kind i Out .DPend -∗
      (∀ (s' : Athread) (rs' : RegFile) (k' : Nat) (d : AxSymMem.Dstate),
         ⌜d ≠ .DPend⌝ -∗ ⌜dp d⌝ -∗ ⌜RetX cpu rs' k' s'⌝ -∗ ⌜ctrlOk rs'⌝ -∗
         ⌜rs' .PC = BitVec.addInt pc 2⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = gprAfter wr d rs r⌝ -∗
         DResM M dok kind i Out d -∗
         wpdM M .MaybeStuck i s' Φ) -∗
      wpdM M .MaybeStuck i s Φ

/-- The riscv.cat instance under the OLD NAME. -/
def XMem {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
    (dok : Int → Nat → Prop) (kind : Bool) (i : Agent) (cpu : CPU)
    (ctrlOk : RegFile → Prop) (textOk : BitVec 64 → Bool → instruction → Prop)
    (ExecOk : RegFile → BitVec 64 → (AxSymMem.Dstate → Option (BitVec 5 × BitVec 64)) →
      (AxSymMem.Dstate → Prop) → instruction → Prop)
    (G : Gdexec → Prop) (Φ : Athread → IProp GF) (Out : Nat → List (BitVec 8) → IProp GF) :
    Prop :=
  XMemM rvwmoCatConsistent dok kind i cpu ctrlOk textOk ExecOk G Φ Out

section xmem
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (img : Image) (dok : Int → Nat → Prop) (kind : Bool) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
variable (Hsp : SpineOkT img ctrlOk textAt)
variable (Htext : ∀ GD, M GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, M GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (HnoRmw : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)

include Hsp Htext Hflow HnoRmw in
theorem XMemHoldsM (G : Gdexec → Prop)
    (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Φ : Athread → IProp GF)
    (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s)
    (Out : Nat → List (BitVec 8) → IProp GF) :
    XMemM M dok kind i cpu ctrlOk (textOkM img ctrlOk textAt) (ExecD img dok kind ctrlOk) G Φ
      Out := by
  intro s rs k pc ins wr dp HRet Hctrl HPC Htx Hrd0 Hcert Hb
  iintro Hd C
  iapply (wpdInstrOfEvDM M img dok kind i Φ cpu G HG Hmid Htext Hflow HnoRmw Out
    (fun d _ t' => GoodD ctrlOk rs pc wr dp d t'.regs) rs k s HRet Hb
    (spineCertD img dok kind ctrlOk textAt Hsp rs pc ins wr dp Hctrl HPC Htx Hrd0 Hcert)) $$ Hd
  iintro %d %t' %rs' %ib' %k' %HG %Hag Hd
  obtain ⟨Hdn, Hdp, Hc, Hpc, Hg⟩ := HG
  have HRet' : RetX cpu rs' k' ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ :=
    ⟨ib', rfl, rfl, rfl, rfl, rfl, regsAgreeRefl _ _⟩
  have Hc' : ctrlOk rs' := Hsp.sptSeip _ _ Hc Hag
  have Hpc' : rs' .PC = BitVec.addInt pc 2 :=
    (Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).trans Hpc
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 → uxaXget rs' r = gprAfter wr d rs r :=
    fun r Hr => (AxSymEngine2.uxaXgetAgree _ _ Hag r).trans (Hg r Hr)
  iapply C $$ %_ %rs' %k' %d %Hdn %Hdp %HRet' %Hc' %Hpc' %Hg' Hd

end xmem

section xmemCat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (dok : Int → Nat → Prop) (kind : Bool) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
variable (Hsp : SpineOkT img ctrlOk textAt)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (HnoRmw : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq rl : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRmw aq rl base n → ¬ dok base n⌝)

include Hsp Htext Hflow HnoRmw in
theorem XMemHolds (G : Gdexec → Prop)
    (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
    (Φ : Athread → IProp GF)
    (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s)
    (Out : Nat → List (BitVec 8) → IProp GF) :
    XMem dok kind i cpu ctrlOk (textOkM img ctrlOk textAt) (ExecD img dok kind ctrlOk) G Φ Out :=
  XMemHoldsM rvwmoCatConsistent img dok kind i cpu ctrlOk textAt Hsp Htext Hflow HnoRmw G HG Φ
    Hmid Out

end xmemCat

/-- THE LOAD instance of `wr`. -/
def wrLoad (rd : BitVec 5) (ext : List (BitVec 8) → BitVec 64) (d : AxSymMem.Dstate) :
    Option (BitVec 5 × BitVec 64) :=
  match d with
  | .DDone vs => some (rd, ext vs)
  | .DPend => none

/-- THE STORE instance of `wr`. -/
def wrStore (_ : AxSymMem.Dstate) : Option (BitVec 5 × BitVec 64) := none

theorem wrLoadRd0 (rd : BitVec 5) (ext : List (BitVec 8) → BitVec 64) :
    rd.toNat ≠ 0 → ∀ d rd' v, wrLoad rd ext d = some (rd', v) → rd'.toNat ≠ 0 := by
  intro H d rd' v h
  cases d with
  | DPend => cases h
  | DDone vs =>
    simp only [wrLoad, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact H

theorem wrStoreRd0 : ∀ d rd' v, wrStore d = some (rd', v) → rd'.toNat ≠ 0 := by
  intro d rd' v h
  cases h

/-- The load family: `XMem` at the load kind. -/
def XLoad {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
    (dok : Int → Nat → Prop) (i : Agent) (cpu : CPU)
    (ctrlOk : RegFile → Prop) (textOk : BitVec 64 → Bool → instruction → Prop)
    (ExecOk : RegFile → BitVec 64 → (AxSymMem.Dstate → Option (BitVec 5 × BitVec 64)) →
      (AxSymMem.Dstate → Prop) → instruction → Prop)
    (G : Gdexec → Prop) (Φ : Athread → IProp GF) (Out : Nat → List (BitVec 8) → IProp GF) :
    Prop :=
  XMem dok true i cpu ctrlOk textOk ExecOk G Φ Out

/-- The store family: `XMem` at the store kind. -/
def XStore {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
    (dok : Int → Nat → Prop) (i : Agent) (cpu : CPU)
    (ctrlOk : RegFile → Prop) (textOk : BitVec 64 → Bool → instruction → Prop)
    (ExecOk : RegFile → BitVec 64 → (AxSymMem.Dstate → Option (BitVec 5 × BitVec 64)) →
      (AxSymMem.Dstate → Prop) → instruction → Prop)
    (G : Gdexec → Prop) (Φ : Athread → IProp GF) (Out : Nat → List (BitVec 8) → IProp GF) :
    Prop :=
  XMem dok false i cpu ctrlOk textOk ExecOk G Φ Out

end Weak
