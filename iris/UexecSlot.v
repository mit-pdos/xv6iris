(* ===================================================================== *)
(* UexecSlot.v -- THE TRAPFRAME-KEYED user-execution WP: the per-process    *)
(* form of UexecWp.v's slot, whose precondition is fixed to the state THIS  *)
(* process's own trapframe + memory-view record.                           *)
(*                                                                         *)
(* See claude-notes/projects/user-wp-slot.md (SS1.1's second block is this  *)
(* file, SS3 is what consumes it).  [uexec_wp] is the forall-STATE form --  *)
(* happy with any resume state, which is what the generic safety theorem    *)
(* proves.  [uexec_slot V M] is the SAME SHAPE with the resume state        *)
(* SPECIALIZED to the pair [(V, M)]: the register file and pc userret       *)
(* rebuilds out of [pv_tf V], and the image [M].  Nothing free-standing is  *)
(* left for anyone to discharge at resume -- userret BUILDS the resume      *)
(* state from the residue's trapframe and pages, so the agreement with the  *)
(* residue's data IS the type.                                             *)
(*                                                                         *)
(* THE REGISTER FILE TAKES A DEAD BASE.  [regfile] is a TOTAL function and  *)
(* [userret_gpr b <31 words>] overwrites x1..x31, so [b] survives only at   *)
(* x0 -- which the model treats as architecturally zero.  There is          *)
(* therefore no canonical base to pick and no funext to prove: the base is  *)
(* forall-BOUND IN THE SLOT ([forall b : regfile] below), which says        *)
(* exactly: at whatever the loop happens to hold, since only x0 can         *)
(* differ.                                                                  *)
(*                                                                         *)
(* THE RESUME PC is [ret_pc] of the trapframe's epc word: prepare_return    *)
(* loads sepc from tf->epc and the sret lands at [ret_pc sepc0]             *)
(* (RiscvExtras.v: bit 0 cleared).                                          *)
(*                                                                         *)
(* NO Umode-tier import here.  This is the KERNEL-side type; the movers     *)
(* into the verified-execution vocabulary are UmodeKernelTie.v and the      *)
(* per-program constructors (USyncKernel.v) are above both.  That is also   *)
(* why [tf_resume_gpr_sp] is stated at the literal register index rather    *)
(* than [UmodeAbi.sp_idx] (which is DEFINITIONALLY [mword_of_int 2], so a   *)
(* consumer may pass this lemma straight into a premise spelled with        *)
(* [sp_idx]).                                                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec RiscvExtras.
Require Import RegFile.
Require Import MinstretInv WireInv.
Require Import ProcGeom.     (* [tf_epc_idx] / [tf_sp_idx] / [TFWORDS] *)
Require Import UserPtTree.   (* [uptd] / [user_pt_inv] *)
Require Import UserFrame.    (* [u_regs] *)
Require Import UserExec.     (* [ucfg] / [user_cfg] / [user_mstatus_ok] /
                                [user_trap_frame] *)
Require Import SpecUserret.  (* [userret_gpr] -- the 31-insert register file *)
Require Import ProcDefs.     (* [pprivate] / [pv_tf] / [pv_upt] *)
Require Import UexecWp.      (* [loop_ok] and the forall-state slot *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* SS1 The trapframe as a word reader.                                     *)
(*                                                                         *)
(* [pv_tf V] has length [TFWORDS] = 36 (pinned by [ProcDefs.tf_page]), so   *)
(* the total lookup never reaches its default; keeping it TOTAL is what     *)
(* lets [tf_resume_gpr] / [tf_resume_pc] be plain functions of [V] with no  *)
(* length side condition riding along in the slot's type.                   *)
(* ===================================================================== *)
Definition tf_w (V : pprivate) (i : nat) : mword 64 := pv_tf V !!! i.

(* the pc the sret lands at: tf->epc with bit 0 cleared *)
Definition tf_resume_pc (V : pprivate) : mword 64 := ret_pc (tf_w V tf_epc_idx).

(* The register file userret restores out of this trapframe.  The words are
   [userret_gpr]'s argument order

     vra vsp vgp vtp vt0 vt1 vt2 vs0 vs1 va1..va7 vs2..vs11 vt3..vt6 va0f

   at the trapframe field indices (ProcGeom.v's struct-trapframe comment:
   field index = byte offset / 8)

     ra@40 -> 5   sp@48 -> 6   gp@56 -> 7   tp@64 -> 8
     t0@72 -> 9   t1@80 -> 10  t2@88 -> 11  s0@96 -> 12  s1@104 -> 13
     a0@112 -> 14 (= [tf_arg_idx 0]) ... a7@168 -> 21
     s2@176 -> 22 ... s11@248 -> 31   t3@256 -> 32 ... t6@280 -> 35

   a0 (index 14) appears LAST, as [va0f]: userret loads it last because it
   doubles as the TRAPFRAME base register while the other 30 loads run. *)
Definition tf_resume_gpr (b : regfile) (V : pprivate) : regfile :=
  userret_gpr b
    (tf_w V 5%nat)  (tf_w V 6%nat)  (tf_w V 7%nat)  (tf_w V 8%nat)
    (tf_w V 9%nat)  (tf_w V 10%nat) (tf_w V 11%nat) (tf_w V 12%nat)
    (tf_w V 13%nat)
    (tf_w V 15%nat) (tf_w V 16%nat) (tf_w V 17%nat) (tf_w V 18%nat)
    (tf_w V 19%nat) (tf_w V 20%nat) (tf_w V 21%nat)
    (tf_w V 22%nat) (tf_w V 23%nat) (tf_w V 24%nat) (tf_w V 25%nat)
    (tf_w V 26%nat) (tf_w V 27%nat) (tf_w V 28%nat) (tf_w V 29%nat)
    (tf_w V 30%nat) (tf_w V 31%nat)
    (tf_w V 32%nat) (tf_w V 33%nat) (tf_w V 34%nat) (tf_w V 35%nat)
    (tf_w V 14%nat).

(* ===================================================================== *)
(* SS2 Reading a register back out of the insert chain.                    *)
(*                                                                         *)
(* The peel discipline is completed/user-verified.md's: NEVER [rewrite      *)
(* upd_eq] (the keys are convertible but not syntactically equal, and       *)
(* ssr's keyed matching may miss); go through [apply]/[exact] at explicit   *)
(* arguments so the conversion is the kernel's job.  [vm_compute;           *)
(* discriminate] is CalleeSaved.v's branch (3) of [reg_ne_side] -- both     *)
(* keys are closed literals here, so there is no symbolic value for the     *)
(* reduction to meet.                                                       *)
(* ===================================================================== *)
Local Lemma tf_upd_ne (f : regfile) (k j : regidx) (v w : mword 64) :
  j <> k -> f !!! j = w -> (<[k := v]> f) !!! j = w.
Proof. intros Hne <-. exact (upd_ne f k j v Hne). Qed.

(* the USER sp, at [UmodeAbi.sp_idx] (= [mword_of_int 2], spelled here as
   the literal so this file stays off the Umode tier): the trapframe's
   [tf_sp_idx] word.  This is the one register the verified-program
   constructors need to read back -- a whole-process entry contract asks
   for the stack budget below the entry sp and nothing else. *)
Lemma tf_resume_gpr_sp (b : regfile) (V : pprivate) :
  tf_resume_gpr b V !!! Regidx (mword_of_int 2) = tf_w V tf_sp_idx.
Proof.
  unfold tf_resume_gpr, userret_gpr.
  repeat (apply tf_upd_ne; [ vm_compute; discriminate | ]).
  exact (upd_eq _ (Regidx (mword_of_int 2)) _).
Qed.

(* ===================================================================== *)
(* SS3 THE SLOT.                                                           *)
(*                                                                         *)
(* [uexec_wp]'s shape with [pt := pv_upt V], [g := tf_resume_gpr b V] and   *)
(* [va := tf_resume_pc V].  [h] / [C] / [Rut] / the stale trap CSRs stay    *)
(* forall-bound exactly as in the generic form (the process may resume on   *)
(* any hart, the parked residue is opaque, and mstatus and the stale CSRs   *)
(* are not program-visible state); [b] joins them for the reason in the     *)
(* header.  NOT inside a [CpuId] section: the hart is the FIRST forall.     *)
(* ===================================================================== *)
Definition uexec_slot `{!riscvGS Σ} `{GEN : GenId}
    (V : pprivate) (M : gmap Z (bv 8)) : iProp Σ :=
  (∀ (h : CpuId) (C : ucfg) (Rut : uptd -> iProp Σ) (b : regfile)
     (ms_v sc_v stval_v sepc_v : mword 64),
     ⌜loop_ok C (pv_upt V)⌝ -∗
     ⌜user_mstatus_ok ms_v⌝ -∗
     hw_config (CID := h) -∗ minstret_inv -∗ wire_inv -∗
     u_regs (CID := h) (HART_ACTIVE tt) ms_v sc_v stval_v sepc_v
       (tf_resume_pc V) (tf_resume_pc V) (tf_resume_gpr b V) -∗
     user_pt_inv (CID := h) (pv_upt V) M -∗
     user_cfg (CID := h) C -∗
     Rut (pv_upt V) -∗
     (* the trap seam, paired as in [uexec_wp] (MILESTONE G): the frame goes
        to the kernel, the NEXT WP comes back.  The returned one is typed at
        the GENERAL [uexec_wp], not at another [uexec_slot] -- a verified
        process may hand back any successor, and that is also why this stays
        a plain definition rather than a fixpoint of its own: the recursion
        routes through [uexec_wp]. *)
     ▷ (user_trap_frame (CID := h) C (pv_upt V) Rut ∗ uexec_wp -∗
        WP (Loop : expr riscv_lang)) -∗
     WP (Loop : expr riscv_lang))%I.

(* Same seal, same reason, as [uexec_wp]: it wraps [gpr_file] through
   [u_regs], the [iFrame] landmine class.  The seal does not travel -- a
   file that puts a slot in the proofmode context must
   [Require Import UexecSlot] (and UexecWp) directly. *)
Global Typeclasses Opaque uexec_slot.

(* ===================================================================== *)
(* SS4 The mover -- plug in the generic WP.                                *)
(*                                                                         *)
(* The forall-state form accepts every resume state, so in particular the   *)
(* one [(V, M)] records.  This is what an initializer with no verified      *)
(* program to offer deposits.                                              *)
(* ===================================================================== *)
Lemma uexec_wp_slot `{!riscvGS Σ} `{GEN : GenId}
    (V : pprivate) (M : gmap Z (bv 8)) :
  uexec_wp -∗ uexec_slot V M.
Proof.
  iIntros "H". rewrite /uexec_slot.
  iIntros (h C Rut b ms_v sc_v stval_v sepc_v)
          "%Hlo %Hms Hhw Hmi Hwi Hregs Hpt Hcfg Hrut Hhdl".
  (* [Typeclasses Opaque uexec_wp] blocks [IntoForall], so the seal comes
     off by hand before the instantiation (durable-notes / lane A) -- ON THE
     HYPOTHESIS ONLY: [Hhdl]'s own [uexec_wp] (the returned WP) is what the
     handler premise is stated at and must stay folded. *)
  iEval (rewrite uexec_wp_unfold /uexec_F) in "H".
  iApply ("H" $! h C (pv_upt V) Rut M (tf_resume_gpr b V)
            ms_v sc_v stval_v sepc_v (tf_resume_pc V)
            with "[] [] Hhw Hmi Hwi Hregs Hpt Hcfg Hrut Hhdl").
  - iPureIntro. exact Hlo.
  - iPureIntro. exact Hms.
Qed.
