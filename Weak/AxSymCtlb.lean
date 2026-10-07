/-
Weak: **the symbolic WPd engine X with ROW-POSITION COUNTING** — part 2 of 2 (Lean-only split
of `iris/AxSymCtl.v`, §4–§5: the counting spine, X reporting the row position, the tail, the
CLOSED block; part 1 is `Weak.AxSymCtl`).

Rocq: `iris/AxSymCtl.v` @ xxvzwolszwmp.  Importers of the Rocq file import this module.

## The Rocq header, in substance

§4 `SpineCnt img ctrlOk textAt cnt`: `SpineOkT` + the COUNTING fetch field (`cnt rs pc` row
items, depends only on the `tlb` register, the fetch WARMS its Sv39 page) + `tick_clock` keeps
the `tlb`.  `textOkC` = `textOkD` + read-freedom of decode/expansion.  `spineCertC`: the budgeted
whole-instruction certificate (RVC arm; exactly `cnt rs pc` row items, `Good`, warm);
`spineStop`: at budget 0 the next step stops at its fetch's first graph read (THE TAIL).  The
spine twins `EvBHartActiveRvc`/`EvBHartActiveStop`/`EvBTryStepActive`/`EvBTryStepStop`/
`EvBRiscvStep`.
§5 `XGprWriteC`: X REPORTING THE ROW POSITION (`k' = k + cnt rs pc`, page warm); `wpdTail`;
`wpdBlockClosed`: `AxSymEngine3`'s `c.mv a0,ra ; c.addiw a0,imm` block as a CLOSED
`wpd s0 (ΦRet cpu (PBlk pc rs0 imm))` (row = exactly the block's graph reads; same-page second
fetch; then the tail).  The S-mode instance (`SpineCnt_S`) is `AxSymCtl4`; closed corollaries
and the concrete probe are `AxSymCtl5`.  NOT HERE (as Rocq): the SIE=1 interrupt arm; the 4-byte
(`F_Base`) arm of `SpineCnt`.

## Deviations from Rocq

1. O2 STAGE C COUNTING (part 1 deviation 1).  `cnt rs pc` counts the fetch's GRAPH reads — the
   page-table walk (`AK_ttw`) — never the i-fetch itself (an admin step, no row item).  Rocq's
   "1 on a TLB hit, 4 on a miss" (`AxSymCtl4.fcnt_S`) is Lean's 0 / 3.  Hence `warm cnt rs pc`
   is "every pc of the page counts 0" (Rocq 1), and `SpineCnt.scFetch`'s warm clause says 0.
2. `SpineCnt`'s field `sc_pos : ∀ rs pc, 1 ≤ cnt rs pc` is DROPPED: in Lean it would make
   `SpineCnt` uninhabited (after any fetch its page counts 0).  It becomes the premise
   `1 ≤ cnt rs pc` of `spineStop` and `wpdTail` (a fetch stops at the row end only when it
   walks).
3. THE TAIL of the closed block.  On a warm page a register-only instruction at the row end is
   NOT stuck in Lean (its fetch is an admin step; it runs to its next boundary), so Rocq's tail
   no longer follows from `text_at (blk_end pc) h3`.  `wpdBlockClosed` replaces that premise
   (and the binder `h3`) by `Htail`: a budget-0 stop certificate (`EvB … (fun _ _ _ => False)
   (riscvStep tick) t 0`) at every regime state at `blkEnd pc` with the page warm and the
   block's GPR values (discharged by `spineStop` on a cold tail page, or by a tail instruction
   whose first graph read is a data read).  The row length is `k0 + cnt rs0 pc` (Rocq `+ 1`:
   the second, same-page fetch reads no graph item).  Lean-only:
   `AxSymCtl.wpdTailOfStop` (the tail from any stop certificate; `wpdTail` is its `spineStop`
   instance) and `AxSymCtl.wpdBlockClosedCold` (Rocq's premise shape `textAt (blkEnd pc) h3`
   plus `∀ rs, warm cnt rs pc → 1 ≤ cnt rs (blkEnd pc)`).  OPEN for the orchestrator (not
   blocking): which tail `AxSymCtl5`'s closed corollaries should use.
4. Section premises: `Hloc` DROPPED (part 1 deviation 1); `seip_reg` ↦ `AxRunClose.pinReg`;
   `svpn_of` ↦ `WeakKpt.svpnOf`; `register_lookup tlb rs` ↦ `rs .tlb`; GPR clauses over
   `uxaXget` at `BitVec 5` with `Z.eqb (uint r) (uint rd)` ↦ `r = rd`, `uint rd ≠ 0` ↦
   `rd.toNat ≠ 0`; `add_vec_int pc 2` ↦ `BitVec.addInt pc 2`; `gpr_of_Z` registers ↦
   `AxSymEngine2.gprReg` (`gprNeTlb`); `vm_compute; discriminate` ↦ `decide`; types as part 1.
5. TACTICS: Rocq `eb_step`/`eb_go`/`eb_use` ↦ the Lean-only kit lemmas `AxSymCtl.eb*` and the
   tactic `ax_sym_ctl_eb_go` (`AxSymEngine2.ax_sym2_ev_go` for `EvB`); `lk` ↦ `RegFile.set_*`
   rewrites; `nseip` ↦ `AxSymEngine2.notPin`.  The spine twins take `t1` (post-fetch state) and
   the read-freedom premises exactly as Rocq; `EvBHartActiveStop`'s post is over `Step`.

**Rocq → Lean name map.**  `EvB_hart_active_rvc` `EvBHartActiveRvc`, `EvB_hart_active_stop`
`EvBHartActiveStop`, `EvB_try_step_active` `EvBTryStepActive`, `EvB_try_step_stop`
`EvBTryStepStop`, `EvB_riscv_step` `EvBRiscvStep`, `SpineCnt` `SpineCnt` (fields `sc_T` `scT`,
`sc_fetch` `scFetch`, `sc_tlb` `scTlb`, `sc_tick` `scTick`; `sc_pos` dropped, deviation 2),
`text_ok_c` `textOkC`, `warm` `warm`, `gpr_ne_tlb` `gprNeTlb`, `spine_cert_C` `spineCertC`,
`spine_stop` `spineStop`, `X_gpr_writeC` `XGprWriteC`, `wpd_tail` `wpdTail`,
`wpd_block_closed` `wpdBlockClosed`; tactics `eb_step`/`eb_go`/`eb_use` ↦ `ax_sym_ctl_eb_go` +
kit.  None is in the duplicated-name table.  Lean-only (file-qualified `AxSymCtl.*`): `ebRBind`,
`ebFactLift`, `ebRUse`, `ebRRead`, `ebRWrite`, `ebRAnn16`, `ebRPureBind`, `ebRAssoc`,
`ebFactAssoc`, `ebFactRead`, `ebFactWrite`, `ebFactPure`, `ebFactUse`, `wpdTailOfStop`,
`wpdBlockClosedCold`.

**Dropped:** nothing (this part: Rocq 14 definitions/lemmas + 4 Ltacs; Lean 14 + 15 Lean-only +
1 tactic; the field `sc_pos` moved to premises, deviation 2).
**Not ported:** the `Print Assumptions` lines (the lint's axiom check covers them).
-/
import Weak.AxSymCtl
import Weak.AxSymEngine3b
import Weak.AxSpineOk5
import Weak.WeakKpt

namespace Weak

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-! # 4. The COUNTING SPINE: `SpineCnt`, `spineCertC` (RVC arm), the TAIL `spineStop` -/

/-! ### (Lean-only) the budgeted stepping kit (Rocq's `eb_step`/`eb_go`/`eb_use`, as lemmas) -/

section ebkit
variable {img : Image} {QE : Sail.Error exception → ExecSt → Prop}

theorem AxSymCtl.ebRBind {R X Y : Type}
    {Q : Nat → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop} {m : SailME R Y}
    {f : Y → SailME R X} {t : ExecSt} {b : Nat}
    (H : EvB img QE (fun b' r t' => match r with
      | .ok a => EvB img QE Q (ExceptT.run (f a)) t' b'
      | .error e => Q b' (.error e) t') (ExceptT.run m) t b) :
    EvB img QE Q (ExceptT.run (m >>= f)) t b := by
  rw [ExceptT.run_bind]
  apply EvBBind
  refine EvBMono img _ _ _ _ _ t b (fun _ _ h => h) ?_ H
  intro b' r t' h
  cases r with
  | ok a => exact h
  | error e => exact .ebRet _ _ _ h

theorem AxSymCtl.ebFactLift {R X Y : Type} {P : Nat → X → ExecSt → Prop}
    {Q : Nat → Except (Sail.Error exception ⊕ R) Y → ExecSt → Prop} {m : SailM X}
    {f : X → SailME R Y} {t : ExecSt} {b : Nat}
    (Hm : EvB img (fun _ _ => False) P m t b)
    (Hf : ∀ b' x t', P b' x t' → EvB img QE Q (ExceptT.run (f x)) t' b') :
    EvB img QE Q (ExceptT.run (liftM m >>= f)) t b := by
  apply AxSymCtl.ebRBind
  refine EvBMono img _ _ _ _ _ t b (fun _ _ h => h) ?_ (EvBLiftRAny img QE P m t b Hm)
  intro b' r t' h
  cases r with
  | ok a => exact Hf b' a t' h
  | error e => exact h.elim

theorem AxSymCtl.ebRUse {R X Y : Type}
    {Q : Nat → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop} {m : SailM Y}
    {f : Y → SailME R X} {t t1 : ExecSt} {a : Y} {b : Nat}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t) (Hn : nrd m)
    (H : EvB img QE Q (ExceptT.run (f a)) t1 b) :
    EvB img QE Q (ExceptT.run (liftM m >>= f)) t b :=
  AxSymCtl.ebFactLift (EvBOfEvA img _ _ m t Hm Hn b)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

theorem AxSymCtl.ebRRead {R X : Type} {Q : Nat → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {r : Register} {f : RegisterType r → SailME R X} {t : ExecSt} {b : Nat}
    (hr : ¬ AxRunClose.pinReg r) (H : EvB img QE Q (ExceptT.run (f (t.regs r))) t b) :
    EvB img QE Q (ExceptT.run (liftM (readReg r) >>= f)) t b :=
  AxSymCtl.ebFactLift (P := fun b' x t' => b' = b ∧ x = t.regs r ∧ t' = t)
    (EvBReadReg img _ r _ t b hr ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H)

theorem AxSymCtl.ebRWrite {R X : Type} {Q : Nat → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {r : Register} {v : RegisterType r} {f : PUnit → SailME R X} {t : ExecSt} {b : Nat}
    (hr : ¬ AxRunClose.pinReg r) (H : EvB img QE Q (ExceptT.run (f PUnit.unit)) (t.setReg r v) b) :
    EvB img QE Q (ExceptT.run (liftM (writeReg r v) >>= f)) t b :=
  AxSymCtl.ebFactLift (P := fun b' _ t' => b' = b ∧ t' = t.setReg r v)
    (EvBWriteReg img _ _ r v t b hr ⟨rfl, rfl⟩)
    (fun _ _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

theorem AxSymCtl.ebRAnn16 {R X : Type} {Q : Nat → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop}
    {h : BitVec 16} {f : Unit → SailME R X} {t : ExecSt} {b : Nat}
    (H : EvB img QE Q (ExceptT.run (f ())) t b) :
    EvB img QE Q (ExceptT.run (liftM (instr_announce h : SailM Unit) >>= f)) t b :=
  AxSymCtl.ebFactLift (P := fun b' _ t' => b' = b ∧ t' = t)
    (.ebIa 16 h _ t b rfl (.ebRet _ _ b ⟨rfl, rfl⟩))
    (fun _ _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact H)

theorem AxSymCtl.ebRPureBind {R X Y : Type}
    {Q : Nat → Except (Sail.Error exception ⊕ R) X → ExecSt → Prop} {x : Y} {f : Y → SailME R X}
    {t : ExecSt} {b : Nat} (H : EvB img QE Q (ExceptT.run (f x)) t b) :
    EvB img QE Q (ExceptT.run (pure x >>= f)) t b := H

theorem AxSymCtl.ebRAssoc {R X Y Z : Type}
    {Q : Nat → Except (Sail.Error exception ⊕ R) Z → ExecSt → Prop} {m : SailME R X}
    {f : X → SailME R Y} {g : Y → SailME R Z} {t : ExecSt} {b : Nat}
    (H : EvB img QE Q (ExceptT.run (m >>= fun x => f x >>= g)) t b) :
    EvB img QE Q (ExceptT.run ((m >>= f) >>= g)) t b := by
  rw [bind_assoc]; exact H

theorem AxSymCtl.ebFactAssoc {X Y Z : Type} {Q : Nat → Z → ExecSt → Prop} {m : SailM X}
    {f : X → SailM Y} {g : Y → SailM Z} {t : ExecSt} {b : Nat}
    (H : EvB img QE Q (m >>= fun x => f x >>= g) t b) : EvB img QE Q ((m >>= f) >>= g) t b := by
  rw [bind_assoc]; exact H

theorem AxSymCtl.ebFactRead {Y : Type} {Q : Nat → Y → ExecSt → Prop} {r : Register}
    {f : RegisterType r → SailM Y} {t : ExecSt} {b : Nat} (hr : ¬ AxRunClose.pinReg r)
    (H : EvB img QE Q (f (t.regs r)) t b) : EvB img QE Q (readReg r >>= f) t b :=
  EvBBind img QE Q _ f t b (EvBReadReg img QE r _ t b hr H)

theorem AxSymCtl.ebFactWrite {Y : Type} {Q : Nat → Y → ExecSt → Prop} {r : Register}
    {v : RegisterType r} {f : PUnit → SailM Y} {t : ExecSt} {b : Nat} (hr : ¬ AxRunClose.pinReg r)
    (H : EvB img QE Q (f PUnit.unit) (t.setReg r v) b) : EvB img QE Q (writeReg r v >>= f) t b :=
  EvBBind img QE Q _ f t b (EvBWriteReg img QE _ r v t b hr H)

theorem AxSymCtl.ebFactPure {X Y : Type} {Q : Nat → Y → ExecSt → Prop} {x : X}
    {f : X → SailM Y} {t : ExecSt} {b : Nat} (H : EvB img QE Q (f x) t b) :
    EvB img QE Q (pure x >>= f) t b := H

theorem AxSymCtl.ebFactUse {X Y : Type} {Q : Nat → Y → ExecSt → Prop} {m : SailM X}
    {f : X → SailM Y} {t t1 : ExecSt} {a : X} {b : Nat}
    (Hm : EvA img (fun _ _ => False) (fun x t' => x = a ∧ t' = t1) m t) (Hn : nrd m)
    (H : EvB img QE Q (f a) t1 b) : EvB img QE Q (m >>= f) t b :=
  EvBBind img QE Q m f t b (EvBMono img _ QE _ _ m t b (fun _ _ h => h.elim)
    (fun _ _ _ h => by obtain ⟨rfl, rfl, rfl⟩ := h; exact H) (EvBOfEvA img _ _ m t Hm Hn b))

end ebkit

/-- Rocq's `eb_go` (file-qualified tactic name; `AxSymEngine2`'s `ax_sym2_ev_go` for `EvB`). -/
macro "ax_sym_ctl_eb_go" : tactic => `(tactic| repeat (first
  | ((with_reducible refine AxSymCtl.ebRRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | ((with_reducible refine AxSymCtl.ebRWrite ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxSymCtl.ebRAnn16 ?_
  | with_reducible refine AxSymCtl.ebRPureBind ?_
  | with_reducible refine AxSymCtl.ebRAssoc ?_
  | with_reducible refine AxSymCtl.ebFactAssoc ?_
  | ((with_reducible refine AxSymCtl.ebFactRead ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | ((with_reducible refine AxSymCtl.ebFactWrite ?_ ?_);
      exact AxSymEngine2.notPin _ (by decide) (by decide))
  | with_reducible refine AxSymCtl.ebFactPure ?_
  | (simp (config := { decide := true }) only [↓reduceIte, Bool.false_eq_true,
      get_config_print_instr, get_config_rvfi, ext_fetch_hook, RETIRE_SUCCESS, tick_pc,
      hart_is_active, assert, PreSail.assert])))

section spineB
variable (img : Image)

theorem EvBHartActiveRvc (t t1 : ExecSt) (h : BitVec 16) (i0 ins : instruction) (pc : BitVec 64)
    (c : Nat) (Qx : ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
      (dispatchInterrupt (t.regs .cur_privilege)) t →
    (∀ b, EvB img (fun _ _ => False) (fun b' r t' => b = b' + c ∧ r = .F_RVC h ∧ t' = t1)
      (fetch ()) t b) →
    EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t1) (ext_decode_compressed h) t1 →
    nrd (ext_decode_compressed h) →
    EvA img (fun _ _ => False) (fun x t' => x = false ∧ t' = t1) (is_landing_pad_expected ()) t1 →
    EvA img (fun _ _ => False) (fun x t' => x = true ∧ t' = t1) (currentlyEnabled .Ext_Zca) t1 →
    t1.regs .PC = pc →
    EvA img (fun _ _ => False)
      (fun x t' => x = .ExecuteAs ins ∧ t' = t1.setReg .nextPC (BitVec.addInt pc 2))
      (execute i0) (t1.setReg .nextPC (BitVec.addInt pc 2)) →
    nrd (execute i0) →
    EvA img (fun _ _ => False) (fun x t' => x = RETIRE_SUCCESS ∧ Qx t') (execute ins)
      (t1.setReg .nextPC (BitVec.addInt pc 2)) →
    nrd (execute ins) →
    ∀ b, EvB img (fun _ _ => False)
      (fun b' x t' => b = b' + c ∧ x = .Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) h) ∧
        Qx t')
      (run_hart_active 0) t b := by
  intro Hdisp Hfetch Hdec Hden Hlpad Hzca HPC Hexp Hexn Hexec Hxn b
  subst HPC
  unfold run_hart_active
  apply EvBCatchEarlyReturn
  ax_sym_ctl_eb_go
  refine AxSymCtl.ebRUse Hdisp (nrdDispatchInterrupt _) ?_
  ax_sym_ctl_eb_go
  refine AxSymCtl.ebFactLift (Hfetch b) ?_
  rintro b1 _ _ ⟨Hb, rfl, rfl⟩
  ax_sym_ctl_eb_go
  refine AxSymCtl.ebRUse Hdec Hden ?_
  ax_sym_ctl_eb_go
  refine AxSymCtl.ebRUse Hlpad nrdLpad ?_
  ax_sym_ctl_eb_go
  refine AxSymCtl.ebRUse Hzca nrdZca ?_
  ax_sym_ctl_eb_go
  refine AxSymCtl.ebRUse Hexp Hexn ?_
  ax_sym_ctl_eb_go
  refine AxSymCtl.ebFactLift (EvBOfEvA img _ _ _ _ Hexec Hxn b1) ?_
  rintro _ _ t' ⟨rfl, rfl, hq⟩
  exact .ebRet _ _ _ ⟨Hb, rfl, hq⟩

/-- THE TAIL: at budget 0 the hart stops at the fetch's first graph read. -/
theorem EvBHartActiveStop (t t1 : ExecSt) (h : BitVec 16) (c : Nat)
    (P : Nat → Step → ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun r t' => r = none ∧ t' = t)
      (dispatchInterrupt (t.regs .cur_privilege)) t →
    EvB img (fun _ _ => False) (fun b' r t' => 0 = b' + c ∧ r = .F_RVC h ∧ t' = t1) (fetch ()) t 0 →
    1 ≤ c →
    EvB img (fun _ _ => False) P (run_hart_active 0) t 0 := by
  intro Hdisp Hfetch Hc
  unfold run_hart_active
  apply EvBCatchEarlyReturn
  ax_sym_ctl_eb_go
  refine AxSymCtl.ebRUse Hdisp (nrdDispatchInterrupt _) ?_
  ax_sym_ctl_eb_go
  refine AxSymCtl.ebFactLift Hfetch ?_
  rintro b1 _ _ ⟨Hb, -, -⟩
  omega

theorem EvBTryStepActive (t : ExecSt) (bb : Bool) (bits : BitVec 32) (c : Nat)
    (Qx Qf : ExecSt → Prop) (b : Nat) :
    EvA img (fun _ _ => False) (fun x t' => x = bb ∧ t' = t)
      (should_inc_minstret (t.regs .cur_privilege)) t →
    (t.setReg .minstret_increment bb).regs .hart_state = .HART_ACTIVE () →
    EvB img (fun _ _ => False)
      (fun b' x t' => b = b' + c ∧ x = .Step_Execute (RETIRE_SUCCESS, bits) ∧ Qx t')
      (run_hart_active 0) (t.setReg .minstret_increment bb) b →
    (∀ tx, Qx tx → tx.regs .hart_state = .HART_ACTIVE () ∧
      tx.regs .minstret_increment = bb ∧ Qf (tfinal bb tx)) →
    EvB img (fun _ _ => False) (fun b' x t' => b = b' + c ∧ x = false ∧ Qf t') (try_step 0 false)
      t b := by
  intro Hsi Hha Hrun Hfin
  unfold try_step
  dsimp only
  ax_sym_ctl_eb_go
  refine AxSymCtl.ebFactUse Hsi (nrdShouldIncMinstret _) ?_
  ax_sym_ctl_eb_go
  apply EvBBind
  ax_sym_ctl_eb_go
  simp only [Hha]
  refine EvBMono img _ _ _ _ _ _ _ (fun _ _ h => h) ?_ Hrun
  rintro b1 _ tx ⟨Hb, rfl, HQ⟩
  obtain ⟨Hhx, Hmix, HQf⟩ := Hfin tx HQ
  ax_sym_ctl_eb_go
  simp only [Hhx]
  ax_sym_ctl_eb_go
  simp only [Hhx]
  ax_sym_ctl_eb_go
  have hmi : (tx.setReg .PC (tx.regs .nextPC)).regs .minstret_increment = bb := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
    exact Hmix
  simp only [hmi]
  cases bb <;> ax_sym_ctl_eb_go <;> exact .ebRet _ _ _ ⟨Hb, rfl, HQf⟩

theorem EvBTryStepStop (t : ExecSt) (bb : Bool) (P : Nat → Bool → ExecSt → Prop) :
    EvA img (fun _ _ => False) (fun x t' => x = bb ∧ t' = t)
      (should_inc_minstret (t.regs .cur_privilege)) t →
    (t.setReg .minstret_increment bb).regs .hart_state = .HART_ACTIVE () →
    EvB img (fun _ _ => False) (fun _ _ _ => False) (run_hart_active 0)
      (t.setReg .minstret_increment bb) 0 →
    EvB img (fun _ _ => False) P (try_step 0 false) t 0 := by
  intro Hsi Hha Hrun
  unfold try_step
  dsimp only
  ax_sym_ctl_eb_go
  refine AxSymCtl.ebFactUse Hsi (nrdShouldIncMinstret _) ?_
  ax_sym_ctl_eb_go
  apply EvBBind
  ax_sym_ctl_eb_go
  simp only [Hha]
  exact EvBMono img _ _ _ _ _ _ _ (fun _ _ h => h) (fun _ _ _ h => h.elim) Hrun

theorem EvBRiscvStep (tick : Bool) (t : ExecSt) (Qf Q : Nat → ExecSt → Prop) (b : Nat) :
    EvB img (fun _ _ => False) (fun b' _ t' => Qf b' t') (try_step 0 false) t b →
    (∀ b' t', Qf b' t' →
      if tick then EvA img (fun _ _ => False) (fun _ t'' => Q b' t'') (tick_clock ()) t'
      else Q b' t') →
    EvB img (fun _ _ => False) (fun b' _ t' => Q b' t') (riscvStep tick) t b := by
  intro Ht Hk
  unfold riscvStep
  refine EvBFact img _ _ _ _ _ t b Ht ?_
  intro b' _ t' Hq
  have Hk' := Hk b' t' Hq
  cases tick with
  | true =>
    exact EvBMono img _ _ _ _ _ t' b' (fun _ _ h => h)
      (fun _ _ _ h => by obtain ⟨rfl, h⟩ := h; exact h) (EvBOfEvA img _ _ _ t' Hk' nrdTickClock b')
  | false => exact .ebRet _ _ _ Hk'

end spineB

/-- THE COUNTING SPINE (deviations 1–2: `cnt` counts the fetch's GRAPH reads — page-table walk
reads, not the i-fetch; warm pages count 0; no `sc_pos`). -/
structure SpineCnt (img : Image) (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (cnt : RegFile → BitVec 64 → Nat) : Prop where
  scT : SpineOkT img ctrlOk textAt
  scFetch : ∀ (t : ExecSt) pc h, ctrlOk t.regs → t.regs .PC = pc → textAt pc h →
    ∃ t1, tlbFrame t t1 ∧ ctrlOk t1.regs ∧
      (∀ pc', WeakKpt.svpnOf pc' = WeakKpt.svpnOf pc → cnt t1.regs pc' = 0) ∧
      ∀ b, EvB img (fun _ _ => False)
        (fun b' r t' => b = b' + cnt t.regs pc ∧ r = .F_RVC h ∧ t' = t1) (fetch ()) t b
  scTlb : ∀ rs rs' pc, rs' .tlb = rs .tlb → cnt rs' pc = cnt rs pc
  scTick : ∀ t : ExecSt, ctrlOk t.regs →
    EvA img (fun _ _ => False)
      (fun _ t' => ctrlOk t'.regs ∧ keepRegs t.regs t'.regs ∧ t'.regs .tlb = t.regs .tlb)
      (tick_clock ()) t

/-- The WPd reading of a compressed instruction for the counting engine: `textOkD` plus
read-freedom of the decode and the expansion. -/
def textOkC (img : Image) (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (pc : BitVec 64) (ins : instruction) : Prop :=
  ∃ h i0, textAt pc h ∧
    (∀ t : ExecSt, ctrlOk t.regs →
      EvA img (fun _ _ => False) (fun x t' => x = i0 ∧ t' = t) (ext_decode_compressed h) t) ∧
    nrd (ext_decode_compressed h) ∧
    (∀ t : ExecSt, EvA img (fun _ _ => False) (fun x t' => x = .ExecuteAs ins ∧ t' = t)
      (execute i0) t) ∧
    nrd (execute i0) ∧
    rf0 (execute ins)

/-- The page of `pc` is warm: every pc of it counts 0 graph reads (deviation 2). -/
def warm (cnt : RegFile → BitVec 64 → Nat) (rs : RegFile) (pc : BitVec 64) : Prop :=
  ∀ pc', WeakKpt.svpnOf pc' = WeakKpt.svpnOf pc → cnt rs pc' = 0

theorem gprNeTlb (z : BitVec 5) : AxSymEngine2.gprReg z ≠ .tlb := by
  rcases uxa_bv5_cases z with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

section certC
variable (img : Image)

/-- THE COUNTING WHOLE-INSTRUCTION CERTIFICATE: at every budget `b`, the step consumes exactly
`cnt rs pc` row items, ends in `Good`, and the page of `pc` is warm afterwards. -/
theorem spineCertC (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (cnt : RegFile → BitVec 64 → Nat) (Hsc : SpineCnt img ctrlOk textAt cnt)
    (rs : RegFile) (pc : BitVec 64) (ins : instruction) (rd : BitVec 5) (wval : BitVec 64) :
    ctrlOk rs → rs .PC = pc → textOkC img ctrlOk textAt pc ins → rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = BitVec.addInt pc 2 →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs → ∀ b,
      EvB img (fun _ _ => False)
        (fun b' _ t' => b = b' + cnt rs pc ∧ Good ctrlOk rs pc rd wval t'.regs ∧
          warm cnt t'.regs pc)
        (riscvStep tick) t b := by
  have Hsp := Hsc.scT
  intro Hct HPC ⟨h, i0, Hat, Hdec, Hden, Hexp, Hexn, Hrf⟩ Hrd Hcert tick t Hag b
  have Hct_t : ctrlOk t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨bb, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment bb).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment bb).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  obtain ⟨t1, Hfr, Hct_1, Hwarm, Hfetch⟩ := Hsc.scFetch _ pc h Hct_a HPC_a Hat
  have Hcnt : cnt (t.setReg .minstret_increment bb).regs pc = cnt rs pc := by
    apply Hsc.scTlb
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
    exact Hag .tlb (AxSymEngine2.notPin _ (by decide) (by decide))
  rw [Hcnt] at Hfetch
  have HPC_1 : t1.regs .PC = pc := (tlbFrameLookup _ _ _ Hfr (by decide)).trans HPC_a
  have Hgag : gprAgree (t1.setReg .nextPC (BitVec.addInt pc 2)).regs rs := by
    intro r _
    simp only [ExecSt.setReg_regs]
    rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide), AxSpineOk5.tlbFrameXget _ _ Hfr,
      ExecSt.setReg_regs, AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
    exact AxSymEngine2.uxaXgetAgree _ _ Hag r
  have Hexec : EvA img (fun _ _ => False)
      (fun x t' => x = RETIRE_SUCCESS ∧
        t' = (t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
      (execute ins) (t1.setReg .nextPC (BitVec.addInt pc 2)) :=
    rf0EvA img _ _ Hrf _ _ _ (Hcert _ (by simp only [ExecSt.setReg_regs, RegFile.set_same]) Hgag)
  have Hrun := EvBHartActiveRvc img (t.setReg .minstret_increment bb) t1 h i0 ins pc (cnt rs pc)
    (fun t' => t' = (t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
    (Hsp.sptDisp _ Hct_a) Hfetch (Hdec _ Hct_1) Hden (Hsp.sptLpad _ Hct_1)
    (Hsp.sptZca _ Hct_1) HPC_1 (Hexp _) Hexn Hexec (nrdOfRf0 _ Hrf) b
  have Hmi1 : t1.regs .minstret_increment = bb := by
    rw [tlbFrameLookup _ _ _ Hfr (by decide)]
    simp only [ExecSt.setReg_regs, RegFile.set_same]
  have Htx1 : ((t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval).regs .tlb = t1.regs .tlb := by
    rw [AxSymEngine2.setGprRegsNe _ rd wval _ (by decide), ExecSt.setReg_regs,
      RegFile.set_other _ _ _ _ (by decide)]
  have Htlb_fin : ∀ bx, (tfinal bx ((t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)).regs .tlb
      = t1.regs .tlb := by
    intro bx
    unfold tfinal
    cases bx
    · simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte]
      rw [RegFile.set_other _ _ _ _ (by decide)]
      exact Htx1
    · simp only [ExecSt.setReg_regs, ↓reduceIte]
      rw [RegFile.set_other _ _ _ _ (by decide), RegFile.set_other _ _ _ _ (by decide)]
      exact Htx1
  refine EvBRiscvStep img tick t
    (fun b' t' => b = b' + cnt rs pc ∧ Good ctrlOk rs pc rd wval t'.regs ∧
      t'.regs .tlb = t1.regs .tlb) _ b ?_ ?_
  · have HT := EvBTryStepActive img t bb (zero_extend (m := 32) h) (cnt rs pc)
      (fun t' => t' = (t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval)
      (fun t' => Good ctrlOk rs pc rd wval t'.regs ∧ t'.regs .tlb = t1.regs .tlb) b Hb
      (Hsp.sptHart _ Hct_a) Hrun ?_
    · exact EvBMono img _ _ _ _ _ t b (fun _ _ h => h)
        (fun _ _ _ h => ⟨h.1, h.2.2.1, h.2.2.2⟩) HT
    · rintro _ rfl
      have Hx := AxSymEngine2.setGprRegsNe (t1.setReg .nextPC (BitVec.addInt pc 2)) rd wval
      refine ⟨?_, ?_, ?_, Htlb_fin bb⟩
      · rw [Hx _ (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hsp.sptHart _ Hct_1
      · rw [Hx _ (by decide)]
        simp only [ExecSt.setReg_regs]
        rw [RegFile.set_other _ _ _ _ (by decide)]
        exact Hmi1
      · have Hct_x := AxSymEngine2.ctrlOkSetGpr ctrlOk Hsp.sptFrame
          (t1.setReg .nextPC (BitVec.addInt pc 2)) rd wval
          (Hsp.sptFrame _ _ _ (Or.inr (Or.inl rfl)) Hct_1)
        refine ⟨?_, ?_, ?_⟩
        · unfold tfinal
          cases bb
          · exact Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x
          · exact Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              (Hsp.sptFrame _ _ _ (Or.inl rfl) Hct_x)
        · unfold tfinal
          cases bb <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
            (try rw [RegFile.set_other _ _ _ _ (by decide)]) <;>
            rw [RegFile.set_same, Hx _ (by decide)] <;>
            simp only [ExecSt.setReg_regs, RegFile.set_same]
        · intro r Hr
          have e : uxaXget (tfinal bb ((t1.setReg .nextPC
              (BitVec.addInt pc 2)).setGpr rd wval)).regs r =
              ((t1.setReg .nextPC (BitVec.addInt pc 2)).setGpr rd wval).gpr r := by
            unfold tfinal ExecSt.gpr
            cases bb <;> simp only [ExecSt.setReg_regs, Bool.false_eq_true, ↓reduceIte] <;>
              (try rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]) <;>
              rw [AxSymEngine2.uxaXgetSetNe _ _ _ (by decide)]
          rw [e]
          by_cases E : r = rd
          · subst E
            simp only [if_true]
            exact AxFetch3c.gprSetGprSame _ r wval Hrd
          · simp only [E, if_false]
            rw [AxFetch3c.gprSetGprNe _ rd r wval E]
            exact Hgag r Hr
  · intro b' t' HG
    cases tick with
    | false =>
      exact ⟨HG.1, HG.2.1, fun pc' Hpc' =>
        (Hsc.scTlb t1.regs t'.regs pc' HG.2.2).trans (Hwarm pc' Hpc')⟩
    | true =>
      refine EvAMono img _ _ _ _ _ t' (fun _ _ h => h) ?_ (Hsc.scTick t' HG.2.1.1)
      rintro _ t'' ⟨Hc, ⟨Hk1, Hk2⟩, Htl⟩
      obtain ⟨Hbb, ⟨-, HG2, HG3⟩, Ht1⟩ := HG
      exact ⟨Hbb, ⟨Hc, Hk1.trans HG2, fun r Hr => (Hk2 r).trans (HG3 r Hr)⟩,
        fun pc' Hpc' => (Hsc.scTlb t1.regs t''.regs pc' (Htl.trans Ht1)).trans (Hwarm pc' Hpc')⟩

/-- THE TAIL CERTIFICATE: at budget 0, from a regime state whose pc holds text and whose fetch
reads the graph (`1 ≤ cnt rs pc`, deviation 2), every path stops at the fetch's first graph
read — no `.pure`. -/
theorem spineStop (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
    (cnt : RegFile → BitVec 64 → Nat) (Hsc : SpineCnt img ctrlOk textAt cnt)
    (rs : RegFile) (pc : BitVec 64) (h : BitVec 16) (P : Nat → Unit → ExecSt → Prop) :
    ctrlOk rs → rs .PC = pc → textAt pc h → 1 ≤ cnt rs pc →
    ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      EvB img (fun _ _ => False) P (riscvStep tick) t 0 := by
  have Hsp := Hsc.scT
  intro Hct HPC Hat Hpos tick t Hag
  have Hct_t : ctrlOk t.regs := Hsp.sptSeip _ _ Hct Hag
  have HPC_t : t.regs .PC = pc := by
    rw [Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))]; exact HPC
  obtain ⟨bb, Hb⟩ := Hsp.sptInc t Hct_t
  have Hct_a : ctrlOk (t.setReg .minstret_increment bb).regs :=
    Hsp.sptFrame _ _ _ (Or.inr (Or.inr (Or.inl rfl))) Hct_t
  have HPC_a : (t.setReg .minstret_increment bb).regs .PC = pc := by
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]; exact HPC_t
  obtain ⟨t1, -, -, -, Hfetch⟩ := Hsc.scFetch _ pc h Hct_a HPC_a Hat
  have Hcnt : cnt (t.setReg .minstret_increment bb).regs pc = cnt rs pc := by
    apply Hsc.scTlb
    rw [ExecSt.setReg_regs, RegFile.set_other _ _ _ _ (by decide)]
    exact Hag .tlb (AxSymEngine2.notPin _ (by decide) (by decide))
  unfold riscvStep
  refine EvBFact img _ (fun _ _ _ => False) P _ _ t 0 ?_ (fun _ _ _ h => h.elim)
  refine EvBTryStepStop img t bb _ Hb (Hsp.sptHart _ Hct_a) ?_
  exact EvBHartActiveStop img _ t1 h _ _ (Hsp.sptDisp _ Hct_a) (Hfetch 0) (Hcnt ▸ Hpos)

end certC

/-! # 5. X WITH THE ROW POSITION, the TAIL, and the CLOSED 2-instruction block -/

section xC
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (cnt : RegFile → BitVec 64 → Nat)
variable (Hsc : SpineCnt img ctrlOk textAt cnt)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)
variable (G : Gdexec → Prop)
  (HG : ∀ GD, rvwmoCatConsistent GD → AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜G GD⌝)
variable (kend : Nat) (HGl : ∀ GD, G GD → (AxOpsem.grow GD i).length = kend)
variable (Φ : Athread → IProp GF)
  (Hmid : ∀ GD s, G GD → midState s → s.atK = (AxOpsem.grow GD i).length → ⊢ postLifting Φ i s)

include Hsc Htext Hflow HG HGl Hmid in
/-- X, REPORTING THE ROW POSITION: after the instruction the thread is at `k + cnt rs pc` (the
fetch's graph reads), with the page warm. -/
theorem XGprWriteC (s : Athread) (rs : RegFile) (k : Nat) (pc : BitVec 64) (ins : instruction)
    (rd : BitVec 5) (wval : BitVec 64) :
    RetX cpu rs k s → ctrlOk rs → rs .PC = pc → textOkC img ctrlOk textAt pc ins →
    rd.toNat ≠ 0 →
    (∀ s_pc : ExecSt,
       s_pc.regs .nextPC = BitVec.addInt pc 2 →
       gprAgree s_pc.regs rs →
       exec (execute ins) s_pc = some (RETIRE_SUCCESS, s_pc.setGpr rd wval)) →
    k ≤ kend →
    (∀ GD s1, G GD → RetX cpu rs k s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ (∀ s' rs' k',
         ⌜RetX cpu rs' k' s'⌝ -∗ ⌜k' = k + cnt rs pc⌝ -∗ ⌜ctrlOk rs'⌝ -∗
         ⌜rs' .PC = BitVec.addInt pc 2⌝ -∗
         ⌜∀ r : BitVec 5, r.toNat ≠ 0 →
            uxaXget rs' r = if r = rd then wval else uxaXget rs r⌝ -∗
         ⌜warm cnt rs' pc⌝ -∗
         wpd .MaybeStuck i s' Φ) -∗
       wpd .MaybeStuck i s Φ := by
  intro HRet Hctrl HPC Htx Hrd Hcert Hk Hb
  iintro C
  iapply (wpdInstrOfEvB img i Φ cpu G HG Hmid Htext Hflow kend HGl
    (fun b' _ t' => kend - k = b' + cnt rs pc ∧ Good ctrlOk rs pc rd wval t'.regs ∧
      warm cnt t'.regs pc)
    rs k s HRet Hk Hb
    (fun tick t Hag => spineCertC img ctrlOk textAt cnt Hsc rs pc ins rd wval Hctrl HPC Htx Hrd
      Hcert tick t Hag (kend - k)))
  iintro %b' %t' %rs' %ib' %k' %HQ %Hag %Hk'
  obtain ⟨Hbb, ⟨Hc, Hpc, Hg⟩, Hw⟩ := HQ
  have HRet' : RetX cpu rs' k' ⟨.PHart cpu (.pure ()) rs' none ib', k'⟩ :=
    ⟨ib', rfl, rfl, rfl, rfl, rfl, regsAgreeRefl _ _⟩
  have Hkk : k' = k + cnt rs pc := by omega
  have Hc' : ctrlOk rs' := Hsc.scT.sptSeip _ _ Hc Hag
  have Hpc' : rs' .PC = BitVec.addInt pc 2 :=
    (Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).trans Hpc
  have Hg' : ∀ r : BitVec 5, r.toNat ≠ 0 →
      uxaXget rs' r = if r = rd then wval else uxaXget rs r :=
    fun r Hr => (AxSymEngine2.uxaXgetAgree _ _ Hag r).trans (Hg r Hr)
  have Hw' : warm cnt rs' pc := fun pc' Hpc'' =>
    (Hsc.scTlb t'.regs rs' pc' (Hag .tlb (AxSymEngine2.notPin _ (by decide) (by decide)))).trans
      (Hw pc' Hpc'')
  iapply C $$ %_ %rs' %k' %HRet' %Hkk %Hc' %Hpc' %Hg' %Hw'

include Htext Hflow HG HGl Hmid in
/-- (Lean-only, deviation 3) THE TAIL from any stop certificate: a boundary AT the row end
whose next step, at budget 0, never reaches `.pure`. -/
theorem AxSymCtl.wpdTailOfStop (s : Athread) (rs : RegFile) :
    RetX cpu rs kend s →
    (∀ GD s1, G GD → RetX cpu rs kend s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    (∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
      EvB img (fun _ _ => False) (fun _ _ _ => False) (riscvStep tick) t 0) →
    ⊢ wpd .MaybeStuck i s Φ := by
  intro HR Hb Hstop
  iapply (wpdInstrOfEvB img i Φ cpu G HG Hmid Htext Hflow kend HGl (fun _ _ _ => False)
    rs kend s HR (Nat.le_refl _) Hb (fun tick t Hag => by rw [Nat.sub_self]; exact Hstop tick t Hag))
  iintro %_ %_ %_ %_ %_ %H
  exact H.elim

include Hsc Htext Hflow HG HGl Hmid in
/-- THE TAIL: a boundary AT the row end whose pc holds text and whose fetch reads the graph
(deviation 2): the next instruction's prefix up to its fetch's first graph read, stuck there. -/
theorem wpdTail (s : Athread) (rs : RegFile) (pc : BitVec 64) (h : BitVec 16) :
    RetX cpu rs kend s → ctrlOk rs → rs .PC = pc → textAt pc h → 1 ≤ cnt rs pc →
    (∀ GD s1, G GD → RetX cpu rs kend s1 → s1.atK = (AxOpsem.grow GD i).length →
      ⊢ postLifting Φ i s1) →
    ⊢ wpd .MaybeStuck i s Φ := by
  intro HR Hc HPC Hat Hpos Hb
  exact AxSymCtl.wpdTailOfStop img i cpu Htext Hflow G HG kend HGl Φ Hmid s rs HR Hb
    (fun tick t Hag => spineStop img ctrlOk textAt cnt Hsc rs pc h _ Hc HPC Hat Hpos tick t Hag)

end xC

/-! ### THE CLOSED BLOCK: `c.mv a0, ra ; c.addiw a0, imm` as a REAL `wpd s0 (ΦRet …)` -/

section blockClosed
variable {hlc : HasLC} {GF : BundledGFunctors} [InvGS_gen hlc GF] [AxirisG GF] [Axpol]
variable (img : Image) (i : Agent) (cpu : CPU)
variable (ctrlOk : RegFile → Prop) (textAt : BitVec 64 → BitVec 16 → Prop)
  (cnt : RegFile → BitVec 64 → Nat)
variable (Hsc : SpineCnt img ctrlOk textAt cnt)
variable (Htext : ∀ GD, rvwmoCatConsistent GD →
  AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜textFixed GD i img⌝)
variable (Hflow : ∀ GD ls k, rvwmoCatConsistent GD →
  (∃ lb aq base n vs, (AxOpsem.grow GD i)[k]? = some lb ∧ aident lb = .IRead aq base n ∧
     imgBytes img base n = some vs) →
  AxirisG.gconstInterp (GF := GF) GD ∗ AxirisG.localInterp GD i k ls ⊢ fetchFlow GD i k)

include Hsc Htext Hflow in
/-- THE CLOSED BLOCK (deviation 3): the row is EXACTLY the block's graph reads, `k0 + cnt rs0 pc`
(the first fetch's walk; the second fetch is on the warm page); after it, the next instruction
at `blkEnd pc` stops at its first graph read (`Htail`). -/
theorem wpdBlockClosed (pc : BitVec 64) (imm : BitVec 6) (s0 : Athread) (rs0 : RegFile)
    (k0 : Nat) :
    RetX cpu rs0 k0 s0 → ctrlOk rs0 → rs0 .PC = pc →
    textOkC img ctrlOk textAt pc ICmv →
    textOkC img ctrlOk textAt (BitVec.addInt pc 2) (ICaddiw imm) →
    WeakKpt.svpnOf (BitVec.addInt pc 2) = WeakKpt.svpnOf pc →
    (∀ rs, ctrlOk rs → rs .PC = blkEnd pc → warm cnt rs pc →
      (∀ r : BitVec 5, r.toNat ≠ 0 →
        AxSymEngine3.gpr r rs = if r = a05 then blkW2 rs0 imm else AxSymEngine3.gpr r rs0) →
      ∀ (tick : Bool) (t : ExecSt), regsAgree AxRunClose.pinReg t.regs rs →
        EvB img (fun _ _ => False) (fun _ _ _ => False) (riscvStep tick) t 0) →
    (∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length = k0 + cnt rs0 pc⌝) →
    ⊢ wpd .MaybeStuck i s0 (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) := by
  intro HR0 Hc0 HPC0 Htx1 Htx2 Hpg Htail Hlen
  have HGl : ∀ GD, (fun GD : Gdexec => (AxOpsem.grow GD i).length = k0 + cnt rs0 pc) GD →
      (AxOpsem.grow GD i).length = k0 + cnt rs0 pc := fun _ h => h
  have HX := XGprWriteC img i cpu ctrlOk textAt cnt Hsc Htext Hflow _ Hlen _ HGl
    (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) (ΦRetMid i cpu _ _)
  have Hbnd : ∀ rs k s1, rs .PC ≠ blkEnd pc → RetX cpu rs k s1 →
      ⊢ postLifting (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) i s1 :=
    fun rs k s1 Hne HR => ΦRetBoundary i cpu _ rs k s1
      (fun rs' Hag Hpc => (Hne
        ((Hag .PC (AxSymEngine2.notPin _ (by decide) (by decide))).symm.trans Hpc)).elim) HR
  iapply (HX s0 rs0 k0 pc ICmv a05 (blkW1 rs0) HR0 Hc0 HPC0 Htx1 (by decide)
    (fun s_pc _ Hag => certCmv rs0 s_pc Hag) (by omega)
    (fun _ s1 _ HR _ => Hbnd rs0 k0 s1 (by rw [HPC0]; exact (addVecInt22Ne pc).symm) HR))
  iintro %s1 %rs1 %k1 %HR1 %Hk1 %Hc1 %HPC1 %Hg1 %Hw1
  have Hv1 : AxSymEngine3.gpr a05 rs1 = blkW1 rs0 := by
    have h := Hg1 a05 (by decide)
    rw [if_pos rfl] at h
    exact h
  have Hne1 : rs1 .PC ≠ blkEnd pc := by
    rw [HPC1]
    exact (addVecIntNe (BitVec.addInt pc 2) 2 ⟨by decide, by decide⟩).symm
  have Hcnt1 : cnt rs1 (BitVec.addInt pc 2) = 0 := Hw1 _ Hpg
  iapply (HX s1 rs1 k1 (BitVec.addInt pc 2) (ICaddiw imm) a05 (blkW2 rs0 imm) HR1 Hc1 HPC1
    Htx2 (by decide)
    (fun s_pc _ Hag => certCaddiw rs1 _ imm s_pc Hv1 Hag) (by omega)
    (fun _ s2 _ HR _ => Hbnd rs1 k1 s2 Hne1 HR))
  iintro %s2 %rs2 %k2 %HR2 %Hk2 %Hc2 %HPC2 %Hg2 %Hw2
  have Hk2' : k2 = k0 + cnt rs0 pc := by omega
  subst Hk2'
  have Hg : ∀ r : BitVec 5, r.toNat ≠ 0 →
      AxSymEngine3.gpr r rs2 = if r = a05 then blkW2 rs0 imm else AxSymEngine3.gpr r rs0 := by
    intro r Hr
    have h2 := Hg2 r Hr
    by_cases E : r = a05
    · rw [if_pos E] at h2
      rw [if_pos E]
      exact h2
    · rw [if_neg E] at h2
      rw [if_neg E]
      have h1 := Hg1 r Hr
      rw [if_neg E] at h1
      exact h2.trans h1
  have Hw2' : warm cnt rs2 pc := fun pc' h => Hw2 pc' (h.trans Hpg.symm)
  iapply (AxSymCtl.wpdTailOfStop img i cpu Htext Hflow _ Hlen _ HGl
    (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) (ΦRetMid i cpu _ _) s2 rs2 HR2 ?_
    (Htail rs2 Hc2 HPC2 Hw2' Hg))
  intro GD s3 _ HR3 _
  refine ΦRetBoundary i cpu _ rs2 _ s3 ?_ HR3
  intro rs' Hag _ r Hr
  have e : AxSymEngine3.gpr r rs' = AxSymEngine3.gpr r rs2 :=
    AxSymEngine2.uxaXgetAgree _ _ Hag r
  rw [e]
  exact Hg r Hr

include Hsc Htext Hflow in
/-- (Lean-only, deviation 3) `wpdBlockClosed` with Rocq's tail premise `textAt (blkEnd pc) h3`,
plus: the tail fetch reads the graph after the block's page is warm. -/
theorem AxSymCtl.wpdBlockClosedCold (pc : BitVec 64) (imm : BitVec 6) (s0 : Athread)
    (rs0 : RegFile) (k0 : Nat) (h3 : BitVec 16) :
    RetX cpu rs0 k0 s0 → ctrlOk rs0 → rs0 .PC = pc →
    textOkC img ctrlOk textAt pc ICmv →
    textOkC img ctrlOk textAt (BitVec.addInt pc 2) (ICaddiw imm) →
    WeakKpt.svpnOf (BitVec.addInt pc 2) = WeakKpt.svpnOf pc →
    textAt (blkEnd pc) h3 →
    (∀ rs, warm cnt rs pc → 1 ≤ cnt rs (blkEnd pc)) →
    (∀ GD, rvwmoCatConsistent GD →
      AxirisG.gconstInterp (GF := GF) GD ⊢ ⌜(AxOpsem.grow GD i).length = k0 + cnt rs0 pc⌝) →
    ⊢ wpd .MaybeStuck i s0 (ΦRet (GF := GF) cpu (PBlk pc rs0 imm)) := by
  intro HR0 Hc0 HPC0 Htx1 Htx2 Hpg Hat3 Hcold Hlen
  exact wpdBlockClosed img i cpu ctrlOk textAt cnt Hsc Htext Hflow pc imm s0 rs0 k0 HR0 Hc0 HPC0
    Htx1 Htx2 Hpg
    (fun rs Hc HPC Hw _ tick t Hag =>
      spineStop img ctrlOk textAt cnt Hsc rs (blkEnd pc) h3 _ Hc HPC Hat3 (Hcold rs Hw) tick t Hag)
    Hlen

end blockClosed

end Weak
