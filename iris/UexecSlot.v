(* ===================================================================== *)
(* UexecSlot.v -- THE SLOT'S KEY, and the trapframe word readers built on   *)
(* it.  [uvis] is the USER-VISIBLE record a per-process user-execution      *)
(* contract is keyed on -- the trapframe words userret rebuilds the         *)
(* register file and pc out of, the va-keyed image, and the per-page        *)
(* permission view -- with [uvis_of] the projection from the kernel's       *)
(* [ProcDefs.ustate].  Everything below SS2 reads a resume state out of     *)
(* those words: [tf_resume_pc], [tf_resume_gpr], and their peels.           *)
(*                                                                         *)
(* WHAT USED TO BE HERE.  SS3/SS4 held [uexec_slot W] -- UexecWp.v's        *)
(* forall-state WP with the resume state specialized to [W] -- and the      *)
(* mover [uexec_wp_slot].  Milestone J replaced that channel outright: the  *)
(* trap loop runs the KEYED contract of UexecRet.v ([uslot] / [uexec_ret] / *)
(* [ukont] / [uvb]) and the generic [UexecWp.uexec_wp] now enters only      *)
(* through [UexecCond.cond_entry_slot] at the two mint sites.  The KEY and  *)
(* the readers stayed, because UexecRet.v, UexecRound.v, UexecApply.v,      *)
(* SpecUservec.v, TfUser.v and the whole [Uk*] engine are stated on them.   *)
(*                                                                         *)
(* THE KEY IS WHAT THE PROCESS CAN OBSERVE, AND NOTHING ELSE.  A user       *)
(* program sees its registers and its va-keyed bytes; it never sees a page  *)
(* table.  So the REALIZING DESCRIPTOR is NOT in the key -- a contract       *)
(* stated on [uvis] forall-binds whatever table currently realizes the      *)
(* image, and forall is the only form a discharge can meet.  This is also   *)
(* the shape the fork clause needs for the child: same [M], fresh table,    *)
(* the parent's contract applies verbatim.  The descriptor stays exposed in *)
(* [ProcDefs.ustate] / [proc_priv] -- the trap seams and the table-moving   *)
(* specs are keyed on it -- and [uvis_of] is the projection from that state *)
(* to this key.                                                             *)
(*                                                                         *)
(* THE REGISTER FILE TAKES A DEAD BASE.  [regfile] is a TOTAL function and  *)
(* [userret_gpr b <31 words>] overwrites x1..x31, so [b] survives only at   *)
(* x0 -- which the model treats as architecturally zero.  There is          *)
(* therefore no canonical base to pick and no funext to prove: [b] stays a  *)
(* PARAMETER of [tf_resume_gpr] and every consumer forall-binds it, which   *)
(* says exactly: at whatever the loop happens to hold, since only x0 can    *)
(* differ.  ([UexecRet.tf_resume_gpr0] pins it at the zero file.)           *)
(*                                                                         *)
(* THE RESUME PC is [ret_pc] of the trapframe's epc word: prepare_return    *)
(* loads sepc from tf->epc and the sret lands at [ret_pc sepc0]             *)
(* (RiscvExtras.v: bit 0 cleared).                                          *)
(*                                                                         *)
(* NO Umode-tier import here.  These are KERNEL-side types; the movers     *)
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
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import AlignBits.    (* [jalr_ret_id] -- for [ret_pc_idem] *)
Require Import RegFile.
Require Import ProcGeom.     (* [tf_epc_idx] / [tf_sp_idx] / [TFWORDS] *)
Require Import TfUser.       (* [tf_ueq] *)
Require Import UserPtTree.   (* [uptd] / [user_pt_inv] *)
Require Import UserExec.     (* [ucfg] / [user_cfg] / [user_mstatus_ok] /
                                [user_trap_frame] *)
Require Import SpecUserret.  (* [userret_gpr] -- the 31-insert register file *)
Require Import ProcDefs.     (* [pprivate] / [ustate] / [pv_tf] *)
Require Import UserPerm.     (* [uperm] / [perm_of] -- the permission view *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* SS0 THE KEY: the user-visible record.                                   *)
(*                                                                         *)
(* [uvis_tf] is the FULL 36-word trapframe (kernel words 0/1/2/4 -- the     *)
(* kernel satp/sp/trap/hartid -- are dead weight in the key; epc, word 3,   *)
(* is user-visible); a later refinement may restrict it.  [uvis_M] is the  *)
(* va-keyed image at the tier the slot's [user_pt_inv] premise names.      *)
(* [uvis_perm] is the PER-PAGE PERMISSION VIEW (UserPerm.v): the process    *)
(* observes permissions (a store to a read-only page faults), so they are   *)
(* in the key -- as a PROJECTION of the kernel's table and size            *)
(* ([perm_of]), never as stored state; the table's structure stays hidden.  *)
(* Future user-visible state (the fd view, the pid) becomes a FIELD, never  *)
(* an arity change here or at a consumer.                                  *)
(* ===================================================================== *)
Record uvis := MkUvis {
  uvis_tf   : list (mword 64);
  uvis_M    : gmap Z (bv 8);
  uvis_perm : gmap (mword 27) uperm;
  (* THE BREAK.  [p->sz] is not kernel-private state: a program observes it
     by calling [sbrk(0)], so it is part of the resume state the slot is
     keyed on, exactly like the trapframe.  Keeping it here is also what
     lets [usys_mem_ok]'s sbrk row NAME the two sizes instead of
     existentially quantifying them. *)
  uvis_sz   : Z;
}.

(* the projection from the kernel's process state to the slot's key: drop
   the descriptor (and everything else only the kernel reads), keeping its
   permission view *)
Definition uvis_of (U : ustate) : uvis :=
  MkUvis (pv_tf (us_V U)) (us_M U)
         (perm_of (ud_um (pv_upt (us_V U))) (uint (pv_sz (us_V U))))
         (uint (pv_sz (us_V U))).

(* ===================================================================== *)
(* SS1 The trapframe as a word reader.                                     *)
(*                                                                         *)
(* [pv_tf V] has length [TFWORDS] = 36 (pinned by [ProcDefs.tf_page]), so   *)
(* the total lookup never reaches its default; keeping it TOTAL is what     *)
(* lets [tf_resume_gpr] / [tf_resume_pc] be plain functions of the word     *)
(* list with no length side condition riding along in the slot's type.     *)
(* ===================================================================== *)
Definition tf_w (tf : list (mword 64)) (i : nat) : mword 64 := tf !!! i.

(* the pc the sret lands at: tf->epc with bit 0 cleared *)
Definition tf_resume_pc (tf : list (mword 64)) : mword 64 := ret_pc (tf_w tf tf_epc_idx).

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
Definition tf_resume_gpr (b : regfile) (tf : list (mword 64)) : regfile :=
  userret_gpr b
    (tf_w tf 5%nat)  (tf_w tf 6%nat)  (tf_w tf 7%nat)  (tf_w tf 8%nat)
    (tf_w tf 9%nat)  (tf_w tf 10%nat) (tf_w tf 11%nat) (tf_w tf 12%nat)
    (tf_w tf 13%nat)
    (tf_w tf 15%nat) (tf_w tf 16%nat) (tf_w tf 17%nat) (tf_w tf 18%nat)
    (tf_w tf 19%nat) (tf_w tf 20%nat) (tf_w tf 21%nat)
    (tf_w tf 22%nat) (tf_w tf 23%nat) (tf_w tf 24%nat) (tf_w tf 25%nat)
    (tf_w tf 26%nat) (tf_w tf 27%nat) (tf_w tf 28%nat) (tf_w tf 29%nat)
    (tf_w tf 30%nat) (tf_w tf 31%nat)
    (tf_w tf 32%nat) (tf_w tf 33%nat) (tf_w tf 34%nat) (tf_w tf 35%nat)
    (tf_w tf 14%nat).

(* ------------------------------------------------------------------- *)
(* [ret_pc] IS IDEMPOTENT.  It clears bit 0, and a pc with bit 0 already   *)
(* clear is its own return target ([AlignBits.jalr_ret_id] at the zero     *)
(* displacement, which [RiscvExtras.add_vec_zeros_r] collapses).  This is  *)
(* what lets a resume pc be re-read through [tf_resume_pc] any number of   *)
(* times -- notably at the syscall bump, where the trap round names        *)
(* [ret_pc (add_vec_int (tf_w tf tf_epc_idx) 4)] and the loop holds the    *)
(* already-cleared value.  NOTE [WpGprCsrwA.mepc_val] is the SAME term     *)
(* under another name; nothing is redefined here.                          *)
(* ------------------------------------------------------------------- *)
Lemma ret_pc_idem (v : mword 64) : ret_pc (ret_pc v) = ret_pc v.
Proof.
  pose proof (jalr_ret_id (ret_pc v) (ret_pc_aligned v)) as H.
  rewrite add_vec_zeros_r in H. exact H.
Qed.

(* The +4 the compressed [c.addi] form of "epc += 4" produces, in the
   [add_vec_int] spelling [UsysMemOk.bump_tf] uses.  The immediate is a
   6-bit c.addi field, sign-extended to 12 and then to 64. *)
Lemma addv_sext4 (v : mword 64) :
  add_vec v (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6)))
  = add_vec_int v 4.
Proof.
  assert (H4 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6)) : mword 64)
               = mword_of_int 4)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H4. reflexivity.
Qed.

(* [tf_resume_pc] reads only the epc word, so [tf_ueq] transports it *)
Lemma tf_ueq_resume_pc (tf tf' : list (mword 64)) :
  tf_ueq tf tf' -> tf_resume_pc tf = tf_resume_pc tf'.
Proof.
  intros [He _]. unfold tf_resume_pc, tf_w. rewrite He. reflexivity.
Qed.

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

(* THE THREE REGISTERS A WHOLE-PROCESS ENTRY CONTRACT READS BACK, at the
   [UmodeAbi] indices (= [mword_of_int 2] / 10 / 11, spelled here as the
   literals so this file stays off the Umode tier).

   [sp] is the stack budget's base -- every verified program asks for a
   writable run below its entry sp.  [a0] and [a1] are the ABI's argc and
   argv: a program that READS its arguments (echo does; sync does not)
   needs them off the trapframe, since the slot's key is the trapframe and
   nothing else.  They are trapframe words [tf_sp_idx] and [tf_arg_idx 0/1]
   -- and note that [a0] is the LAST insert of [userret_gpr]'s tower (the
   syscall return value overwrites it), so its peel is the shortest.

   All three go through the same discipline: peel with [apply] at explicit
   arguments until the key matches, and never [rewrite upd_eq]. *)
Lemma tf_resume_gpr_sp (b : regfile) (tf : list (mword 64)) :
  tf_resume_gpr b tf !!! Regidx (mword_of_int 2) = tf_w tf tf_sp_idx.
Proof.
  unfold tf_resume_gpr, userret_gpr.
  repeat (apply tf_upd_ne; [ vm_compute; discriminate | ]).
  exact (upd_eq _ (Regidx (mword_of_int 2)) _).
Qed.

Lemma tf_resume_gpr_a0 (b : regfile) (tf : list (mword 64)) :
  tf_resume_gpr b tf !!! Regidx (mword_of_int 10) = tf_w tf (tf_arg_idx 0).
Proof.
  unfold tf_resume_gpr, userret_gpr.
  repeat (apply tf_upd_ne; [ vm_compute; discriminate | ]).
  exact (upd_eq _ (Regidx (mword_of_int 10)) _).
Qed.

Lemma tf_resume_gpr_a1 (b : regfile) (tf : list (mword 64)) :
  tf_resume_gpr b tf !!! Regidx (mword_of_int 11) = tf_w tf (tf_arg_idx 1).
Proof.
  unfold tf_resume_gpr, userret_gpr.
  repeat (apply tf_upd_ne; [ vm_compute; discriminate | ]).
  exact (upd_eq _ (Regidx (mword_of_int 11)) _).
Qed.
