/-
Weak: **the `AxCert.Cert` SPINE** (whole-instruction certificates for 4-byte instructions whose
`execute` has a `Cert`, e.g. a barrier or an RMW) and the X leaves `fence rw,w` /
`amoswap.w.aq`.

Rocq: `iris/AxCert4.v` @ xxvzwolszwmp.

## The Rocq header, in substance

§1 Cert tactics (Rocq `c_go` / `c_use` = AxSymCtl2's `ev_goC` / `ev_useC` over `Cert`; an `EvA`
fact is used through `CertEvA`, the `BInf` embedding of `CertOfEvA`).
§2 THE SPINE, ported from `AxSymCtl2`: `CertHartActiveBaseT` (fetch / decode / lpad as EvA
facts, `execute ins` as a CERT), `CertTryStepActive`, `CertRiscvStep`; `spineCertX` — the
generic whole-instruction certificate over `SpineOkT` + `SpineFetch4T` at budget `BInf`:
`execute ins` certified from every state of the regime at this pc ending in `wrOpt ow tpc` with
final certificate state in `PX` ⇒ `riscvStep tick` (both ticks) is a `Cert` ending in
`PX ∧ GoodC … none ow` (PC + 4, GPRs by `ow`, control state in the regime).
§3 `certExecuteFence`: `execute (FENCE (0, rw, w, x0, x0))` at every Supervisor state is ONE
barrier node `Barrier_RISCV_rw_w`, the release-pending flag ARMED (FIOM irrelevant for rw,w).
§4 X LEAVES (WPd, continuation form, any post Φ with the fine row-end premises `Hmid`/`Hb`):
`XFenceM` — from a boundary at `pc` holding `fence rw,w`, the WPd holds given the continuation at
the next boundary (PC + 4, GPRs unchanged, regime kept) which learns that the FLAG IS ARMED;
`XAmoM` — the RMW leaf: given the `execute` certificate (`CertAmo`: exclusive read DEMONIC,
exclusive write of `wv rvs`, rd written with `rdv rvs`), the continuation receives the read
bytes `rvs` and the `Out` of the write's flow.  riscv.cat instances `FstDok0`/`XFence`/`XAmo`;
S-mode instances `XFenceS` / `XAmoS` over `AxSpineOk7.spineOkTS`.
RESIDUALS (as Rocq): the S-mode spine has NO 4-byte fetch arm, so `SpineFetch4T` stays a PREMISE
of the S-mode leaves; the decode of the word is a premise; `CertAmo` is a premise (the symbolic
S-mode data translation is open; `AxCert3.ctaCert` is the concrete instance).

## Deviations from Rocq

1. Q7 (as `AxSymCtl2` deviation 2): the 4-byte arm announces the 32-bit word, so
   `CertHartActiveBaseT` takes `sfAnnB 32 w = false`, and `spineCertX` / `XFenceM` / `XAmoM`
   take `Hsf : sfAnnB 32 w = false` right after `textAt4 pc w`.
2. O2 STAGE C (as `AxCert2` deviation 1): the X leaves' section premises are AxCert2's
   (`Htext Hflow Hloc`, then `G HG Φ Hmid`; no `Hntext`); `HnoRmw` (kind `DKSt` / `DKRmw`) is
   discharged by `Dkind` disjointness, `HnoSplit` of the fence leaf likewise.
3. Types / registers as `AxSymCtl2` deviation 3: `regs_agree seip_reg` ↦
   `regsAgree AxRunClose.pinReg`, `uint rd ≠ 0` ↦ `rd.toNat ≠ 0`, `add_vec_int` ↦
   `BitVec.addInt`, `register_lookup r t.(sregs)` ↦ `t.regs r`; `[InvGS_gen hlc GF]` (any hlc);
   Rocq's `Definition … := …M rvwmo_cat_consistent` / S-mode `Definition`s ↦ theorems typed
   `type_of% …`.  `fence_rw_w` is the model's `FENCE (0#4, 3#4, 1#4, x0, x0)`;
   `execute_fence_rw_w`'s right side writes the barrier node `.impure (.ok (.barrier …))`.
4. The Rocq set-locals `rvs_of` / `PX` of `X_amoM` are Lean-only defs `AxCert4.rvsOf` /
   `AxCert4.amoPX`.

**Rocq → Lean name map.**  `Cert_liftR_M` `CertLiftRM`, `Cert_EvA` `CertEvA`,
`Cert_hart_active_base_T` `CertHartActiveBaseT`, `Cert_try_step_active` `CertTryStepActive`,
`Cert_riscv_step` `CertRiscvStep`, `CertX` `CertX`, `spine_certX` `spineCertX`, `fence_rw_w`
`fenceRwW`, `execute_fence_rw_w` `executeFenceRwW`, `cert_execute_fence` `certExecuteFence`,
`dok0` `dok0`, `Fst_dok0M` `FstDok0M`, `X_fenceM` `XFenceM`, `CertAmo` `CertAmo`, `X_amoM`
`XAmoM`, `Fst_dok0` `FstDok0`, `X_fence` `XFence`, `X_amo` `XAmo`, `ctrl_ok_S_priv`
`ctrlOkSPriv`, `X_fence_S` `XFenceS`, `X_amo_S` `XAmoS`.  None is in the duplicated-name table.
Lean-only (file-qualified): the Cert stepping kit `AxCert4.cRBind`, `cFactLift`, `cFactQ`,
`cFactRead`, `cFactWrite`, `cFactPure`, `cFactAssoc`, `cFactUse`, `cRRead`, `cRWrite`,
`cRAnn16`, `cRAnn32`, `cRPureBind`, `cRAssoc`, `cRUse`; `AxCert4.rvsOf`, `AxCert4.amoPX`; tactic
`ax_cert4_go` (Rocq `c_go`).

**Dropped:** nothing (Rocq 21 definitions/lemmas; Lean 21 + 17 Lean-only).
**Not ported:** the Ltacs `nseipX`, `c_step`/`c_go`/`c_use`/`c_useC`, `lk` (the kit above and
`RegFile` rewrites instead), the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxCert2
import Weak.AxSymCtl2

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 1. Cert tactics -/

section ctac
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)

theorem CertLiftRM {R X : Type} (QE' : Cst → Sail.Error exception → ExecSt → Prop)
    (Q : Cst → X → ExecSt → Prop) (m : SailM X) (s : Cst) (t : ExecSt) :
    AxCert.Cert img dok kind (fun _ _ _ => False) Q s m t →
    AxCert.Cert img dok kind QE'
      (fun s' (r : Except (Sail.Error exception ⊕ R) X) t' =>
        match r with
        | .ok x => Q s' x t'
        | .error _ => False)
      s (ExceptT.run (liftM m : SailME R X)) t :=
  CertLiftRAny img dok kind _ QE' Q m s t (fun _ _ _ h => h.elim)

theorem CertEvA {X : Type} (P : X → ExecSt → Prop) (m : SailM X) (d : Cdata) (r : Bool)
    (t : ExecSt) :
    EvA img (fun _ _ => False) P m t →
    AxCert.Cert img dok kind (fun _ _ _ => False) (fun s x t' => s = ⟨d, .BInf, r⟩ ∧ P x t')
      ⟨d, .BInf, r⟩ m t := fun H =>
  CertMono img dok kind _ _ _ _ _ m t (fun _ _ _ h => h.2.elim) (fun _ _ _ h => h)
    (CertOfEvA img dok kind _ _ d r m t H)

end ctac

/-! ### (Lean-only) the stepping kit (Rocq's `c_step`/`c_go`/`c_use` tactics, as lemmas) -/

section kit
variable {img : Image} {dok : Int → Nat → Prop} {kind : Dkind}
  {QE : Cst → Sail.Error exception → ExecSt → Prop}

theorem AxCert4.cRBind {R X Y : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop} {m : SailME R Y}
    {f : Y → SailME R X} {s : Cst} {t : ExecSt}
    (H : AxCert.Cert img dok kind QE (fun s' r t' => match r with
      | .ok a => AxCert.Cert img dok kind QE Q s' (ExceptT.run (f a)) t'
      | .error e => Q s' (.error e) t') s (ExceptT.run m) t) :
    AxCert.Cert img dok kind QE Q s (ExceptT.run (m >>= f)) t := by
  rw [ExceptT.run_bind]
  apply CertBind
  refine CertMono img dok kind _ _ _ _ s _ t (fun _ _ _ h => h) ?_ H
  intro s' r t' h
  cases r with
  | ok a => exact h
  | error e => exact .cRet _ _ _ h

theorem AxCert4.cFactLift {R X Y : Type} {P : Cst → X → ExecSt → Prop}
    {Q : Cst → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop} {m : SailM X}
    {f : X → SailME R Y} {s : Cst} {t : ExecSt}
    (Hm : AxCert.Cert img dok kind (fun _ _ _ => False) P s m t)
    (Hf : ∀ s' x t', P s' x t' → AxCert.Cert img dok kind QE Q s' (ExceptT.run (f x)) t') :
    AxCert.Cert img dok kind QE Q s (ExceptT.run (liftM m >>= f)) t := by
  apply AxCert4.cRBind
  refine CertMono img dok kind _ _ _ _ s _ t (fun _ _ _ h => h) ?_
    (CertLiftRM img dok kind (R := R) QE P m s t Hm)
  intro s' r t' h
  cases r with
  | ok a => exact Hf s' a t' h
  | error e => exact h.elim

theorem AxCert4.cFactQ {X Y : Type} {P : Cst → X → ExecSt → Prop} {Q : Cst → Y → ExecSt → Prop}
    {m : SailM X} {f : X → SailM Y} {s : Cst} {t : ExecSt}
    (Hm : AxCert.Cert img dok kind (fun _ _ _ => False) P s m t)
    (Hf : ∀ s' x t', P s' x t' → AxCert.Cert img dok kind QE Q s' (f x) t') :
    AxCert.Cert img dok kind QE Q s (m >>= f) t :=
  CertBind img dok kind QE Q m f s t
    (CertMono img dok kind _ _ _ _ s m t (fun _ _ _ h => h.elim) Hf Hm)

theorem AxCert4.cFactRead {Y : Type} {Q : Cst → Y → ExecSt → Prop} {r : Register}
    {f : RegisterType r → SailM Y} {s : Cst} {t : ExecSt} (hr : ¬ AxRunClose.pinReg r)
    (H : AxCert.Cert img dok kind QE Q s (f (t.regs r)) t) :
    AxCert.Cert img dok kind QE Q s (readReg r >>= f) t :=
  CertBind img dok kind QE Q _ f s t (CertReadReg img dok kind QE r _ s t hr H)

theorem AxCert4.cFactWrite {Y : Type} {Q : Cst → Y → ExecSt → Prop} {r : Register}
    {v : RegisterType r} {f : PUnit → SailM Y} {s : Cst} {t : ExecSt}
    (hr : ¬ AxRunClose.pinReg r)
    (H : AxCert.Cert img dok kind QE Q s (f PUnit.unit) (t.setReg r v)) :
    AxCert.Cert img dok kind QE Q s (writeReg r v >>= f) t :=
  CertBind img dok kind QE Q _ f s t (CertWriteReg img dok kind QE _ r v s t hr H)

theorem AxCert4.cFactPure {X Y : Type} {Q : Cst → Y → ExecSt → Prop} {x : X}
    {f : X → SailM Y} {s : Cst} {t : ExecSt} (H : AxCert.Cert img dok kind QE Q s (f x) t) :
    AxCert.Cert img dok kind QE Q s (pure x >>= f) t := H

theorem AxCert4.cFactAssoc {X Y Z : Type} {Q : Cst → Z → ExecSt → Prop} {m : SailM X}
    {f : X → SailM Y} {g : Y → SailM Z} {s : Cst} {t : ExecSt}
    (H : AxCert.Cert img dok kind QE Q s (m >>= fun x => f x >>= g) t) :
    AxCert.Cert img dok kind QE Q s ((m >>= f) >>= g) t := by
  rw [bind_assoc]; exact H

/-- use an `EvA` fact (embedded at the current `BInf` state) -/
theorem AxCert4.cFactUse {X Y : Type} {Q : Cst → Y → ExecSt → Prop} {m : SailM X}
    {f : X → SailM Y} {d : Cdata} {r : Bool} {t t1 : ExecSt} {a : X}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t)
    (H : AxCert.Cert img dok kind QE Q ⟨d, .BInf, r⟩ (f a) t1) :
    AxCert.Cert img dok kind QE Q ⟨d, .BInf, r⟩ (m >>= f) t :=
  AxCert4.cFactQ (CertEvA img dok kind _ m d r t Hm)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

theorem AxCert4.cRRead {R X : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {r : Register} {f : RegisterType r → SailME R X} {s : Cst} {t : ExecSt}
    (hr : ¬ AxRunClose.pinReg r) (H : AxCert.Cert img dok kind QE Q s (ExceptT.run (f (t.regs r))) t) :
    AxCert.Cert img dok kind QE Q s (ExceptT.run (liftM (readReg r) >>= f)) t :=
  AxCert4.cFactLift (P := fun s' x t' => s' = s ∧ x = t.regs r ∧ t' = t)
    (CertReadReg img dok kind _ r _ s t hr ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

theorem AxCert4.cRWrite {R X : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {r : Register} {v : RegisterType r} {f : PUnit → SailME R X} {s : Cst} {t : ExecSt}
    (hr : ¬ AxRunClose.pinReg r)
    (H : AxCert.Cert img dok kind QE Q s (ExceptT.run (f PUnit.unit)) (t.setReg r v)) :
    AxCert.Cert img dok kind QE Q s (ExceptT.run (liftM (writeReg r v) >>= f)) t :=
  AxCert4.cFactLift (P := fun s' _ t' => s' = s ∧ t' = t.setReg r v)
    (CertWriteReg img dok kind _ _ r v s t hr ⟨rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

theorem AxCert4.cRAnn16 {R X : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {h : BitVec 16} {f : Unit → SailME R X} {s : Cst} {t : ExecSt}
    (H : AxCert.Cert img dok kind QE Q s (ExceptT.run (f ())) t) :
    AxCert.Cert img dok kind QE Q s
      (ExceptT.run (liftM (instr_announce h : SailM Unit) >>= f)) t :=
  AxCert4.cFactLift (P := fun s' _ t' => s' = s ∧ t' = t)
    (.cIa s 16 h _ t rfl (.cRet _ _ _ ⟨rfl, rfl⟩))
    (fun _ _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

theorem AxCert4.cRAnn32 {R X : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {w : BitVec 32} {f : Unit → SailME R X} {s : Cst} {t : ExecSt} (hw : sfAnnB 32 w = false)
    (H : AxCert.Cert img dok kind QE Q s (ExceptT.run (f ())) t) :
    AxCert.Cert img dok kind QE Q s
      (ExceptT.run (liftM (instr_announce w : SailM Unit) >>= f)) t :=
  AxCert4.cFactLift (P := fun s' _ t' => s' = s ∧ t' = t)
    (.cIa s 32 w _ t hw (.cRet _ _ _ ⟨rfl, rfl⟩))
    (fun _ _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

theorem AxCert4.cRPureBind {R X Y : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop} {x : Y}
    {f : Y → SailME R X} {s : Cst} {t : ExecSt}
    (H : AxCert.Cert img dok kind QE Q s (ExceptT.run (f x)) t) :
    AxCert.Cert img dok kind QE Q s (ExceptT.run (pure x >>= f)) t := H

theorem AxCert4.cRAssoc {R X Y Z : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) Z → ExecSt → Prop} {m : SailME R X}
    {f : X → SailME R Y} {g : Y → SailME R Z} {s : Cst} {t : ExecSt}
    (H : AxCert.Cert img dok kind QE Q s (ExceptT.run (m >>= fun x => f x >>= g)) t) :
    AxCert.Cert img dok kind QE Q s (ExceptT.run ((m >>= f) >>= g)) t := by
  rw [bind_assoc]; exact H

/-- use an `EvA` fact in the early-return monad (embedded at the current `BInf` state) -/
theorem AxCert4.cRUse {R X Y : Type}
    {Q : Cst → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {m : SailM Y} {f : Y → SailME R X} {d : Cdata} {r : Bool} {t t1 : ExecSt} {a : Y}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t)
    (H : AxCert.Cert img dok kind QE Q ⟨d, .BInf, r⟩ (ExceptT.run (f a)) t1) :
    AxCert.Cert img dok kind QE Q ⟨d, .BInf, r⟩ (ExceptT.run (liftM m >>= f)) t :=
  AxCert4.cFactLift (CertEvA img dok kind _ m d r t Hm)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

end kit

/-- Rocq's `c_go`: run the register reads/writes, `pure`s and closed guards. -/
macro "ax_cert4_go" : tactic => `(tactic| repeat (first
  | ((with_reducible refine AxCert4.cRRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | ((with_reducible refine AxCert4.cRWrite ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxCert4.cRAnn16 ?_
  | with_reducible refine AxCert4.cRPureBind ?_
  | with_reducible refine AxCert4.cRAssoc ?_
  | with_reducible refine AxCert4.cFactAssoc ?_
  | ((with_reducible refine AxCert4.cFactRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | ((with_reducible refine AxCert4.cFactWrite ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxCert4.cFactPure ?_
  | (simp (config := { decide := true }) only [↓reduceIte, Bool.false_eq_true,
      get_config_print_instr, get_config_rvfi, ext_fetch_hook, RETIRE_SUCCESS, tick_pc,
      hart_is_active, assert, PreSail.assert])))

/-! # 2. The spine -/

section spineX
variable (img : Image) (dok : Int → Nat → Prop) (kind : Dkind)

theorem CertHartActiveBaseT (t t1 : ExecSt) (w : BitVec 32) (ins : instruction)
    (pc : BitVec 64) (d : Cdata) (r : Bool) (Qx : Cst → ExecSt → Prop)
    (hw : sfAnnB 32 w = false) :
    EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
      (dispatchInterrupt (t.regs .cur_privilege)) t →
    EvA img (fun _ _ => False) (fun r t' => r = .F_Base w ∧ t' = t1) (fetch ()) t →
    EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t1) (ext_decode w) t1 →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t1) (is_landing_pad_expected ()) t1 →
    t1.regs .PC = pc →
    AxCert.Cert img dok kind (fun _ _ _ => False) (fun s x t' => x = RETIRE_SUCCESS ∧ Qx s t')
      ⟨d, .BInf, r⟩ (execute ins) (t1.setReg .nextPC (BitVec.addInt pc 4)) →
    AxCert.Cert img dok kind (fun _ _ _ => False)
      (fun s x t' => x = .Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) w) ∧ Qx s t')
      ⟨d, .BInf, r⟩ (run_hart_active 0) t := by
  intro Hdisp Hfetch Hdec Hlpad HPC Hexec
  subst HPC
  unfold run_hart_active
  apply CertCatchEarlyReturn
  ax_cert4_go
  refine AxCert4.cRUse Hdisp ?_
  ax_cert4_go
  refine AxCert4.cRUse Hfetch ?_
  ax_cert4_go
  refine AxCert4.cRAnn32 hw ?_
  ax_cert4_go
  refine AxCert4.cRUse Hdec ?_
  ax_cert4_go
  refine AxCert4.cRUse Hlpad ?_
  ax_cert4_go
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  ax_cert4_go
  refine AxCert4.cFactLift Hexec ?_
  rintro _ _ t' ⟨rfl, hq⟩
  ax_cert4_go
  exact .cRet _ _ _ ⟨rfl, hq⟩

theorem CertTryStepActive (t : ExecSt) (b : Bool) (bits : BitVec 32) (d : Cdata) (r : Bool)
    (Qx Qf : Cst → ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun x t' => x = b ∧ t' = t)
      (should_inc_minstret (t.regs .cur_privilege)) t →
    (t.setReg .minstret_increment b).regs .hart_state = .HART_ACTIVE () →
    AxCert.Cert img dok kind (fun _ _ _ => False)
      (fun s x t' => x = .Step_Execute (RETIRE_SUCCESS, bits) ∧ Qx s t') ⟨d, .BInf, r⟩
      (run_hart_active 0) (t.setReg .minstret_increment b) →
    (∀ s tx, Qx s tx → tx.regs .hart_state = .HART_ACTIVE () ∧
      tx.regs .minstret_increment = b ∧ Qf s (tfinal b tx)) →
    AxCert.Cert img dok kind (fun _ _ _ => False) (fun s x t' => x = false ∧ Qf s t')
      ⟨d, .BInf, r⟩ (try_step 0 false) t := by
  intro Hsi Hha Hrun Hfin
  unfold try_step
  dsimp only
  ax_cert4_go
  refine AxCert4.cFactUse Hsi ?_
  ax_cert4_go
  apply CertBind
  ax_cert4_go
  simp only [Hha]
  refine CertMono img dok kind _ _ _ _ _ _ _ (fun _ _ _ h => h) ?_ Hrun
  rintro s _ tx ⟨rfl, HQ⟩
  obtain ⟨Hhx, Hmix, HQf⟩ := Hfin s tx HQ
  ax_cert4_go
  simp only [Hhx]
  ax_cert4_go
  simp only [Hhx]
  ax_cert4_go
  have hmi : (tx.setReg .PC (tx.regs .nextPC)).regs .minstret_increment = b := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
    exact Hmix
  simp only [hmi]
  cases b <;> ax_cert4_go <;> exact .cRet _ _ _ ⟨rfl, HQf⟩

theorem CertRiscvStep (tick : Bool) (s : Cst) (t : ExecSt) (Qf Q : Cst → ExecSt → Prop) :
    AxCert.Cert img dok kind (fun _ _ _ => False) (fun s' _ t' => Qf s' t') s (try_step 0 false) t →
    (∀ s' t', Qf s' t' → if tick then
      AxCert.Cert img dok kind (fun _ _ _ => False) (fun s'' _ t'' => Q s'' t'') s' (tick_clock ()) t'
      else Q s' t') →
    AxCert.Cert img dok kind (fun _ _ _ => False) (fun s' _ t' => Q s' t') s (riscvStep tick) t := by
  intro Ht Hk
  unfold riscvStep
  refine CertFact img dok kind _ _ _ _ _ s t Ht ?_
  intro s' _ t' Hq
  have Hk' := Hk s' t' Hq
  cases tick with
  | true => exact Hk'
  | false => exact .cRet _ _ _ Hk'

/-- The execute premise of a non-jumping 4-byte instruction: from every state of the regime at
`pc` (nextPC ticked, GPRs of `rs`), a `Cert` ending in `wrOpt ow tpc` with final certificate
state in `PX`. -/
def CertX (ctrlOk : RegFile → Prop) (rs : RegFile) (pc : BitVec 64) (ins : instruction)
    (ow : Cst → Option (BitVec 5 × BitVec 64)) (s0 : Cst) (PX : Cst → Prop) : Prop :=
  ∀ tpc : ExecSt, ctrlOk tpc.regs → tpc.regs .PC = pc →
    tpc.regs .nextPC = BitVec.addInt pc 4 → gprAgree tpc.regs rs →
    AxCert.Cert img dok kind (fun _ _ _ => False)
      (fun s x t' => x = RETIRE_SUCCESS ∧ PX s ∧ t' = wrOpt (ow s) tpc) s0 (execute ins) tpc

theorem spineCertX (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (textAt4 : BitVec 64 → BitVec 32 → Prop)
    (Hsp : SpineOkT img ctrlOk textAt) (Hf4 : SpineFetch4T img ctrlOk textAt4)
    (rs : RegFile) (pc : BitVec 64) (w : BitVec 32) (ins : instruction)
    (ow : Cst → Option (BitVec 5 × BitVec 64)) (d : Cdata) (r : Bool) (PX : Cst → Prop) :
    ctrlOk rs → rs .PC = pc → textAt4 pc w → sfAnnB 32 w = false →
    (∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w) t) →
    (∀ s, PX s → owOk (ow s)) → (∀ s, PX s → s.csB = .BInf) →
    CertX img dok kind ctrlOk rs pc ins ow ⟨d, .BInf, r⟩ PX →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      AxCert.Cert img dok kind (fun _ _ _ => False)
        (fun s _ t' => PX s ∧ GoodC ctrlOk false rs pc none (ow s) t'.regs)
        ⟨d, .BInf, r⟩ (riscvStep tick) t := by
  intro Hct HPC Htx Hsf Hdec How HPX Hcert tick t Hag
  have Hct_t : ctrlOk t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨b, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment b).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment b).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  obtain ⟨t1, Hfr, Hct1, Hfetch⟩ := Hf4 _ pc w Hct_a HPC_a Htx
  have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
  have Hgag : gprAgree (t1.setReg .nextPC (BitVec.addInt pc 4)).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSpineOk5.tlbFrameXget _ _ Hfr,
      ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hct_pc : ctrlOk (t1.setReg .nextPC (BitVec.addInt pc 4)).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inl rfl)) Hct1
  have HPC_pc : (t1.setReg .nextPC (BitVec.addInt pc 4)).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_1
  have Hnpc_pc : (t1.setReg .nextPC (BitVec.addInt pc 4)).regs .nextPC =
      BitVec.addInt pc 4 := by
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Hexec := Hcert _ Hct_pc HPC_pc Hnpc_pc Hgag
  have Hrun := CertHartActiveBaseT img dok kind _ t1 w ins pc d r
    (fun s t' => PX s ∧ t' = wrOpt (ow s) (t1.setReg .nextPC (BitVec.addInt pc 4))) Hsf
    (Hsp.sptDisp _ Hct_a) Hfetch (Hdec _ Hct1) (Hsp.sptLpad _ Hct1) HPC_1 Hexec
  have Hmi1 : t1.regs .minstret_increment = b := by
    rw [tlbFrameLookup _ _ _ Hfr (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  refine CertRiscvStep img dok kind tick ⟨d, .BInf, r⟩ t
    (fun s t' => PX s ∧ GoodC ctrlOk false rs pc none (ow s) t'.regs) _ ?_ ?_
  · have HT := CertTryStepActive img dok kind t b (zero_extend (m := 32) w) d r
      (fun s t' => PX s ∧ t' = wrOpt (ow s) (t1.setReg .nextPC (BitVec.addInt pc 4)))
      (fun s t' => PX s ∧ GoodC ctrlOk false rs pc none (ow s) t'.regs) Hb
      (Hsp.sptHart _ Hct_a) Hrun ?_
    · exact CertMono img dok kind _ _ _ _ _ _ t (fun _ _ _ h => h) (fun _ _ _ h => h.2) HT
    · rintro s _ ⟨HP, rfl⟩
      have Hct_x := wrNpcCtrl img ctrlOk textAt Hsp (ow s) none _ Hct_pc
      have How' := How s HP
      rw [show wrOpt (ow s) (t1.setReg .nextPC (BitVec.addInt pc 4)) =
        wrOpt (ow s) (npcOpt none (t1.setReg .nextPC (BitVec.addInt pc 4))) from rfl]
      refine ⟨?_, ?_, HP, ?_, ?_, ?_⟩
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.sptHart _ Hct1
      · rw [wrNpcOther _ _ _ _ (by decide) (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hmi1
      · unfold tfinal
        cases b
        · exact Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x
        · exact Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            (Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x)
      · rw [tfinalPC, wrNpcNextPC]
        exact Hnpc_pc
      · intro r Hr
        rw [tfinalGpr, wrNpcGpr _ _ _ _ Hr How']
        exact gprPostAgree _ _ _ _ Hgag Hr
  · rintro s' t' ⟨HP, HG⟩
    cases tick with
    | false => exact ⟨HP, HG⟩
    | true =>
      obtain ⟨d', b', r'⟩ := s'
      have Hb' : b' = .BInf := HPX _ HP
      subst Hb'
      refine CertMono img dok kind _ _ _ _ _ _ t' (fun _ _ _ h => h) ?_
        (CertEvA img dok kind _ _ d' r' t' (Hsp.sptTick t' HG.1))
      rintro _ _ t'' ⟨rfl, Hc, Hk1, Hk2⟩
      obtain ⟨-, HG2, HG3⟩ := HG
      exact ⟨HP, Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩

end spineX

/-! # 3. `execute (FENCE rw,w)` -/

def fenceRwW : instruction :=
  .FENCE (0#4, 3#4, 1#4, regidx.Regidx 0#5, regidx.Regidx 0#5)

theorem executeFenceRwW :
    execute fenceRwW =
      (is_fiom_active () >>= fun _ =>
        (.impure (.ok (.barrier .Barrier_RISCV_rw_w)) (fun _ => pure RETIRE_SUCCESS) :
          SailM ExecutionResult)) := by
  show execute_FENCE 0#4 3#4 1#4 (regidx.Regidx 0#5) (regidx.Regidx 0#5) = _
  unfold execute_FENCE
  refine congrArg (is_fiom_active () >>= ·) ?_
  funext fiom
  cases fiom <;> rfl

theorem certExecuteFence (img : Image) (dok : Int → Nat → Prop) (kind : Dkind) (d : Cdata)
    (r : Bool) (t : ExecSt) :
    t.regs .cur_privilege = .Supervisor →
    AxCert.Cert img dok kind (fun _ _ _ => False)
      (fun s x t' => x = RETIRE_SUCCESS ∧ s = ⟨d, .BInf, true⟩ ∧ t' = t) ⟨d, .BInf, r⟩
      (execute fenceRwW) t := by
  intro Hpriv
  rw [executeFenceRwW]
  apply CertBind
  unfold is_fiom_active
  refine AxCert4.cFactRead (AxSymEngine2.notPin _ (by decide) (by decide)) ?_
  rw [Hpriv]
  refine AxCert4.cFactRead (AxSymEngine2.notPin _ (by decide) (by decide)) ?_
  refine .cRet _ _ _ ?_
  exact .cFence d .BInf r _ _ t rfl (.cRet _ _ _ ⟨rfl, rfl, rfl⟩)

/-! # 4. X leaves -/

/-- no data region: every data premise is vacuous -/
def dok0 : Int → Nat → Prop := fun _ _ => False

/-- (Lean-only, Rocq's set-local `rvs_of`) the read bytes of a completed RMW state. -/
def AxCert4.rvsOf (s : Cst) : List (BitVec 8) :=
  match s.csD with
  | .CRmw _ _ rvs _ _ => rvs
  | _ => []

/-- (Lean-only, Rocq's set-local `PX` of `X_amoM`) the completed-RMW certificate states. -/
def AxCert4.amoPX (aq rl : Bool) (wv : List (BitVec 8) → List (BitVec 8)) (s : Cst) : Prop :=
  ∃ rvs c, s = ⟨.CRmw aq rl rvs (wv rvs) c, .BInf, false⟩

/-- THE RMW `execute` certificate: from every state of the regime at `pc`, `execute ins`
performs the exclusive read (demonic: ANY `rvs`) and the exclusive write of `wv rvs`, ends with
rd := `rdv rvs`, and the certificate state `CRmw aq rl rvs (wv rvs) c`. -/
def CertAmo (img : Image) (dok : Int → Nat → Prop) (ctrlOk : RegFile → Prop) (rs : RegFile)
    (pc : BitVec 64) (ins : instruction) (rd : BitVec 5) (rdv : List (BitVec 8) → BitVec 64)
    (wv : List (BitVec 8) → List (BitVec 8)) (aq rl : Bool) : Prop :=
  ∀ tpc : ExecSt, ctrlOk tpc.regs → tpc.regs .PC = pc →
    tpc.regs .nextPC = BitVec.addInt pc 4 → gprAgree tpc.regs rs →
    AxCert.Cert img dok .DKRmw (fun _ _ _ => False)
      (fun s x t' => x = RETIRE_SUCCESS ∧ ∃ rvs c,
        s = ⟨.CRmw aq rl rvs (wv rvs) c, .BInf, false⟩ ∧ t' = wrOpt (some (rd, rdv rvs)) tpc)
      ⟨.CPend, .BInf, false⟩ (execute ins) tpc

section xleaves
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (M : Gdexec → Prop)
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (textAt4 : BitVec 64 → BitVec 32 → Prop)
variable (Hsp : SpineOkT img ctrlOk textAt) (Hf4 : SpineFetch4T img ctrlOk textAt4)
variable (Hpriv : ∀ rs, ctrlOk rs → rs .cur_privilege = .Supervisor)
variable (Htext : ∀ GD, M GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, M GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (Hloc : ∀ GD ls k, M GD →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢
    |==> ∃ ls', AxirisG.localInterp GD i (k + 1) ls')
variable (G : Gdexec → Prop) (HG : ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (Φ : Athread → IProp GF)
variable (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length →
  ⊢ postLifting Φ i s)

theorem FstDok0M (Out : Nat → List (BitVec 8) → IProp GF) : ⊢ FstM M dok0 i Out := by
  unfold FstM
  iintro %GD %ls %k %data %base %n %_ - - %_ %Hd
  exact (Hd.1 : False).elim

include Hsp Hf4 Hpriv Htext Hflow Hloc HG Hmid in
/-- THE FENCE LEAF.  The continuation is at the next boundary (PC + 4, GPRs unchanged, regime
kept) and learns the release-pending flag is ARMED. -/
theorem XFenceM (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w : BitVec 32) (r : Bool)
    (HRet : RetX cpu rs k s) (Hctrl : ctrlOk rs) (HPC : rs .PC = pc) (Htx : textAt4 pc w)
    (Hsf : sfAnnB 32 w = false)
    (Hdec : ∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = fenceRwW ∧ t' = t) (ext_decode w) t)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ (∀ (t' : ExecSt) (rs' : RegFile) (ib' : Ibch) (k' : Nat),
        ⌜GoodC ctrlOk false rs pc none none t'.regs⌝ -∗
        ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗
        ⌜relpUpd (ebarLabel .Barrier_RISCV_rw_w) r = true⌝ -∗
        wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i s Φ := by
  have Hc : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      AxCert.Cert img dok0 .DKSt (fun _ _ _ => False)
        (fun s' _ t' => s' = ⟨.CPend, .BInf, true⟩ ∧ GoodC ctrlOk false rs pc none none t'.regs)
        ⟨.CPend, .BInf, r⟩ (riscvStep tick) t := by
    intro tick t Hag
    refine spineCertX img dok0 .DKSt ctrlOk textAt textAt4 Hsp Hf4 rs pc w fenceRwW
      (fun _ => none) .CPend r (fun s' => s' = ⟨.CPend, .BInf, true⟩) Hctrl HPC Htx Hsf Hdec
      (fun _ _ => trivial) (fun _ h => by subst h; rfl) ?_ tick t Hag
    intro tpc Hc _ _ _
    refine CertMono img dok0 .DKSt _ _ _ _ _ _ _ (fun _ _ _ h => h) ?_
      (certExecuteFence img dok0 .DKSt .CPend r tpc (Hpriv _ Hc))
    rintro _ _ _ ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  have H0' : ⊢ CResM M dok0 .DKSt i (fun _ _ => (iprop(emp) : IProp GF))
      (⟨.CPend, .BInf, r⟩ : Cst).csD :=
    FstDok0M M i _
  iintro C
  ihave H0 := H0'
  iapply (wpdInstrOfCertM M img dok0 .DKSt i Φ cpu G HG Hmid Htext Hflow Hloc
    (fun h => nomatch h) (fun h => nomatch h) (fun _ _ => (iprop(emp) : IProp GF)) _ ⟨.CPend, .BInf, r⟩
    rs k s HRet trivial Hb Hc) $$ H0
  iintro %s' %t' %rs' %ib' %k' %HQ %Hag %_ -
  obtain ⟨-, HG'⟩ := HQ
  iapply C $$ %t' %rs' %ib' %k' %HG' %Hag %(relpUpdRwW r)

variable (dok : Int → Nat → Prop) (Out : Nat → List (BitVec 8) → IProp GF)
variable (HnoSplit : Dkind.DKRmw = .DKRmw → ∀ GD, M GD → AxirisG.gconstInterp (GF := GF) GD ⊢
  ⌜∀ (k : Nat) (lb : Lbl) (aq : Bool) (base : Int) (n : Nat),
    (AxOpsem.grow GD i)[k]? = some lb → aident lb = .IRead aq base n → ¬ dok base n⌝)

include Hsp Hf4 Htext Hflow Hloc HG Hmid HnoSplit in
/-- THE RMW LEAF (execute certificate as a premise; see the header). -/
theorem XAmoM (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (w : BitVec 32)
    (ins : instruction) (rd : BitVec 5) (rdv : List (BitVec 8) → BitVec 64)
    (wv : List (BitVec 8) → List (BitVec 8)) (aq rl : Bool)
    (HRet : RetX cpu rs k s) (Hctrl : ctrlOk rs) (HPC : rs .PC = pc) (Htx : textAt4 pc w)
    (Hsf : sfAnnB 32 w = false)
    (Hdec : ∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = ins ∧ t' = t) (ext_decode w) t)
    (Hrd : rd.toNat ≠ 0)
    (Hcert : CertAmo img dok ctrlOk rs pc ins rd rdv wv aq rl)
    (Hb : ∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) :
    ⊢ FstM M dok i Out -∗
      (∀ (rvs : List (BitVec 8)) (t' : ExecSt) (rs' : RegFile) (ib' : Ibch) (k' : Nat),
        ⌜GoodC ctrlOk false rs pc none (some (rd, rdv rvs)) t'.regs⌝ -∗
        ⌜regsAgree AxRunClose.pinReg rs' t'.regs⌝ -∗ (∃ kw, Out kw (wv rvs)) -∗
        wpdM M .MaybeStuck i ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ Φ) -∗
      wpdM M .MaybeStuck i s Φ := by
  have Hc : ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      AxCert.Cert img dok .DKRmw (fun _ _ _ => False)
        (fun s' _ t' => AxCert4.amoPX aq rl wv s' ∧
          GoodC ctrlOk false rs pc none (some (rd, rdv (AxCert4.rvsOf s'))) t'.regs)
        ⟨.CPend, .BInf, false⟩ (riscvStep tick) t := by
    intro tick t Hag
    refine spineCertX img dok .DKRmw ctrlOk textAt textAt4 Hsp Hf4 rs pc w ins
      (fun s' => some (rd, rdv (AxCert4.rvsOf s'))) .CPend false (AxCert4.amoPX aq rl wv)
      Hctrl HPC Htx Hsf Hdec (fun _ _ => Hrd) ?_ ?_ tick t Hag
    · rintro _ ⟨_, _, rfl⟩
      rfl
    · intro tpc Hc HP1 HP2 Hga
      refine CertMono img dok .DKRmw _ _ _ _ _ _ _ (fun _ _ _ h => h) ?_
        (Hcert tpc Hc HP1 HP2 Hga)
      rintro _ _ _ ⟨rfl, rvs, c, rfl, rfl⟩
      exact ⟨rfl, ⟨rvs, c, rfl⟩, rfl⟩
  have Hbr : FstM M dok i Out ⊢
      CResM M dok .DKRmw i Out (⟨.CPend, .BInf, false⟩ : Cst).csD := .rfl
  iintro F C
  ihave F := Hbr $$ F
  iapply (wpdInstrOfCertM M img dok .DKRmw i Φ cpu G HG Hmid Htext Hflow Hloc
    (fun h => nomatch h) HnoSplit Out _ ⟨.CPend, .BInf, false⟩ rs k s HRet trivial Hb Hc) $$ F
  iintro %s' %t' %rs' %ib' %k' %HQ %Hag %_ HO
  obtain ⟨⟨rvs, c, rfl⟩, HG'⟩ := HQ
  have Hbr2 : CResM M dok .DKRmw i Out
      (⟨.CRmw aq rl rvs (wv rvs) c, .BInf, false⟩ : Cst).csD ⊢ iprop(∃ kw, Out kw (wv rvs)) := .rfl
  ihave HO := Hbr2 $$ HO
  iapply C $$ %rvs %t' %rs' %ib' %k' %HG' %Hag HO

end xleaves

/-! ### riscv.cat instances under the Rocq names -/

section xleavesCat
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]

theorem FstDok0 : type_of% (FstDok0M (GF := GF) rvwmoCatConsistent) :=
  FstDok0M rvwmoCatConsistent

theorem XFence : type_of% (XFenceM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  XFenceM rvwmoCatConsistent

theorem XAmo : type_of% (XAmoM (hlc := hlc) (GF := GF) rvwmoCatConsistent) :=
  XAmoM rvwmoCatConsistent

end xleavesCat

/-! ### The S-mode kernel regime: the spine is `AxSpineOk7.spineOkTS`; the 4-byte fetch field
`SpineFetch4T` stays a premise. -/

theorem ctrlOkSPriv (T : PTree) (satp0 : BitVec 64) (rs : RegFile) :
    ctrlOkS T satp0 rs → rs .cur_privilege = .Supervisor := fun h => h.1

section xleavesS
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
theorem XFenceS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (textAt4 : BitVec 64 → BitVec 32 → Prop)
    (Hf4 : SpineFetch4T (imgS σi) (ctrlOkS T satp0) textAt4) (i : Agent) (cpu : CPU) :
    type_of% (XFence (hlc := hlc) (GF := GF) (imgS σi) i cpu (ctrlOkS T satp0) (textAtS σi T)
      textAt4 (spineOkTS σi T satp0 hmode hasid hppn) Hf4 (ctrlOkSPriv T satp0)) :=
  XFence (imgS σi) i cpu (ctrlOkS T satp0) (textAtS σi T) textAt4
    (spineOkTS σi T satp0 hmode hasid hppn) Hf4 (ctrlOkSPriv T satp0)

theorem XAmoS (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)
    (hmode : _get_Satp64_Mode (Mk_Satp64 satp0) = 8#4)
    (hasid : zero_extend (m := 16) (satp_to_asid satp0) = 0#16)
    (hppn : BitVec.setWidth 44 (satp_to_ppn satp0) = T.base)
    (textAt4 : BitVec 64 → BitVec 32 → Prop)
    (Hf4 : SpineFetch4T (imgS σi) (ctrlOkS T satp0) textAt4) (i : Agent) (cpu : CPU) :
    type_of% (XAmo (hlc := hlc) (GF := GF) (imgS σi) i cpu (ctrlOkS T satp0) (textAtS σi T)
      textAt4 (spineOkTS σi T satp0 hmode hasid hppn) Hf4) :=
  XAmo (imgS σi) i cpu (ctrlOkS T satp0) (textAtS σi T) textAt4
    (spineOkTS σi T satp0 hmode hasid hppn) Hf4

end xleavesS

end Weak
