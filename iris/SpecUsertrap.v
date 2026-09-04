(* SpecUsertrap.v -- the public interface of usertrap() (trap.c), stated
   ahead of its proof.  Everything the five cones below it consume is the
   ABSTRACT per-process predicate [usertrap_res] of the module type, which
   the proof will define concretely -- consumers thread it opaquely, so
   refining it does not churn the boundary.

     uint64 usertrap(void)   @ KernelSyms.usertrap, 262 bytes / 90 instrs

   ==== THIS CONTRACT IS IN THE KERNEL TIER, NOT THE TRAMPOLINE'S ========

   The first statement of this file (10892e92) read the boundary off the two
   trampoline halves: it took [tlb_inv_pt kroot], the parked user table, the
   36 trapframe words at the PHYSICAL tier, and [user_cfg].  That is uservec's
   postcondition verbatim, and it cannot be usertrap's precondition, because
   every function usertrap CALLS describes the same objects one tier up and
   the two descriptions are not merely different -- together they are
   UNSATISFIABLE.  Three collisions, one shape (see
   claude-notes/projects/usertrap.md for the long form):

   * THE KERNEL PAGE TABLE.  [tlb_inv_pt kroot] owns [ptree_own 2 1] of the
     kernel tree; the kernel cone reaches the same tree through
     [IntrDefs.sie_cap]'s [strans_inv], whose KPT arm is
     [KptShare.tlb_res_pt], which carries the INVARIANT [kpt_inv root] that
     holds it.  Hold both and one [iInv kptN] gives two exclusive owners of
     one tree, i.e. [False] -- and every leaf's [sr_absorb] opens [kptN], so
     the interior would go through BY ABSURDITY.  usertrap never writes satp
     (only the trampoline halves do), so it has no business owning a tree:
     the kernel table reaches it the way it reaches every other kernel
     function, inside [usertrap_res].  The exclusive/shared seam belongs to
     uservec/userret, which is the only code that needs exclusivity, and
     closing it is completed/kpt-share.md's named follow-up.
   * THE TRAPFRAME PAGE.  [ProcInv.proc_priv] -- which every callee below
     takes, and which usertrap itself needs for [p->trapframe->epc] -- owns
     that page as [tf_page] at the VA tier.  So the words are NOT in this
     contract; the physical<->VA crossing belongs on the trampoline side,
     where the mapping is in scope.
   * [user_cfg]'s mie/mideleg/menvcfg cells ARE [sconf]'s cells, so they ride
     inside [usertrap_res] too.  The one config cell that stays here is the
     one usertrap WRITES: [stvec].

   ==== THE ENTRY PAYLOAD IS prepare_return'S EXIT PAYLOAD ===============

   What is left once those three are out is exactly the state
   [SpecPrepareReturn.v]'s postcondition hands over, with the trap's own
   writes applied -- which is the check that this boundary is the right one:

     stvec at TRAMPOLINE with NO [intr_res] (no kernel handler installed);
     the [sie_gname] 1/4 that lived in [intr_res] still DANGLING; the KPT
     receipt loose; the sret mirror at (SPP = User, SPIE = 1) -- prepare_return
     wrote that pair, the [sret] set SIE := SPIE = 1, and the trap set
     SPP := User, SPIE := SIE = 1, so it comes back UNCHANGED; mstatus with
     SIE = 0 again (prepare_return's [intr_off] cleared it, the sret set it,
     the trap cleared it); scause/stval/sepc at whatever the trap wrote.

   EVERY GHOST FRACTION IS WHERE prepare_return LEFT IT, and the two mstatus
   bits the mirror tracks return to the same values -- so the excursion
   through userret / user mode / uservec moves no ghost at all and
   [usertrap_res] simply carries the mirror halves across it.  That is why
   this contract mentions no ghost variable of its own.

   AND usertrap'S FIRST ACT CLOSES THE LOOP: the [csrw stvec, kernelvec] at
   +0x1e folds the dangling quarter + the stvec cell + [intr_handler_spec
   kernelvec] into a real [IntrDefs.intr_res], hence [trap_csrs] -- precisely
   the [intr_res] prepare_return's [csrci] will unfold again on the way out.
   The C comment ("send interrupts and exceptions to kerneltrap(), since
   we're now in the kernel") IS that fold, and the order is forced: before
   +0x1e this hart has no kernel handler, so nothing there may enable
   interrupts.

   ==== THE POST CROSSES ================================================

   usertrap PARKS -- yield on the timer arm, and every sleeping syscall
   through [SpecSyscall]'s own [wp_next true pj] -- so it may return on a
   different hart and the post has to be a crossing.  The consequence is on
   the CALLER (see eb-generic-sweep.md on [wp_next]'s polarity): the trap-loop
   composition must build its continuation hart-generically.

   ==== WHAT IS STILL OWED (the trampoline dovetail) =====================

   This statement moves the trampoline seam rather than closing it: composing
   uservec -> usertrap -> userret (the Loeb theorem that discharges
   [UserExec.stvec_handler_wp]) owes three conversions -- the kernel table
   exclusive<->shared, the trapframe page physical<->VA, and
   [user_cfg] <-> [sconf]'s cells (which needs [uc_mie C = MIE_S]; sconf pins
   mie and [ucfg] only constrains [mie & ~mideleg = 0]).  All three are
   trampoline-side work and all three are tracked in
   claude-notes/projects/usertrap.md.  [usertrap_ret_ms] and [satp_rooted]
   stay here: they are the shared vocabulary that seam will be stated in, and
   SpecPrepareReturn's post already spells [satp_rooted]'s three conjuncts out
   longhand rather than importing it (this file has no [Require]ing consumer
   yet -- the two Specs that name it, name it in prose). *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import RegFile HartTp WpNext.
Require Import MinstretInv.
Require Import InstrBytes.
Require Import WpGpr.
Require Import KernelText MstatusBits.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import ProcDefs.
Require Import ProcInv.   (* [us_tf] / [us_upt] -- the residue index's updaters *)
Require Import ProcPtOwn.   (* [proc_pt] / [ud_norm] -- the bare residue's vocabulary *)
(* the classes the module type's [usertrap_res] parameter needs -- see the
   note above [Module Type USERTRAP] at the foot of this file *)
Require Import IrefSlots.
Require Import ProcGeom.
Require Import TrampPt UptTree.
Require Import KptShare.   (* [tlb_res_pt] -- the translation slot the parked residue drops *)
Require Import UserPtTree UserExec.
Require Import UexecRound. (* [uround_ok] -- the trap round, on the user-visible state *)
Require Import UexecSlot.  (* [tf_resume_pc] *)
Require Import TfUser.     (* [tf_ueq] *)
Require Import UserPerm.   (* [perm_of] -- the per-page permission view *)
Require Import UsysMemOk.  (* [uecall_scause] *)
Require Import UexecRet.   (* [tf_ueq_resume_gpr0] / [tf_ueq_resume_pc] -- the exec rows' congruences *)
Require Import UexecRetExec.   (* [uslot_x] / [xbundle] -- the exec channel's slot and bundle *)
Require Import UexecExecInst.  (* the [xbundle] instance: the process's exec bundle *)
Require Import FirstTok.       (* [fsabs_env] -- what the loop mints the bundle from *)
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import TimerCap.   (* [sstc_enabled]: the residue's mcounteren pin *)
Local Open Scope Z_scope.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Require Import TsoCtx.


(* the mstatus facts usertrap's return guarantees: exactly userret's
   premises (the sret decodes to User and does not trap) plus the FS/VS
   pins the user-mode invariant carries across the sret
   ([userret_to_user_state_ptm], UserKernelBridge.v). *)
Definition usertrap_ret_ms (ms : mword 64) : Prop :=
  eq_vec (_get_Mstatus_SIE ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_MPRV ms) ('b"1") = false /\
  _get_Mstatus_SXL ms = 'b"10" /\
  eq_vec (_get_Mstatus_TVM ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_MXR ms) ('b"0") = true /\
  eq_vec (_get_Mstatus_TSR ms) ('b"1") = false /\
  eq_vec (_get_Mstatus_FS ms) ('b"00") = true /\
  eq_vec (_get_Mstatus_VS ms) ('b"00") = true /\
  sret_newpriv ms = User /\
  (* the four pins [UserExec.user_mstatus_ok] carries through user mode and
     the bridge therefore asks of the pre-sret value: XS/SD/MPP out of
     [sconf_ms_facts], and SPIE = 1 -- prepare_return's [sret_bits 0 1],
     agreed against [sconf]'s tie at the exit.  Appended, so the existing
     destructurings' last binder absorbs them. *)
  _get_Mstatus_XS ms = extStatus_map_forwards Off /\
  _get_Mstatus_SD ms = ('b"0" : mword 1) /\
  eq_vec (_get_Mstatus_MPP ms) ('b"10") = false /\
  _get_Mstatus_SPIE ms = ('b"1" : mword 1).

(* the satp-value facts both trampoline switches need, shared spec
   vocabulary: [v] is a Sv39, asid-0 satp value rooted at [root]. *)
Definition satp_rooted (v : mword 64) (root : mword 44) : Prop :=
  _get_Satp64_Mode (Mk_Satp64 v) = ('b"1000" : mword 4) /\
  zero_extend' 16 (satp_to_asid (autocast (T := mword) v : mword 64)) = (mword_of_int 0 : mword 16) /\
  autocast (T := mword) (satp_to_ppn (autocast (T := mword) v : mword 64)) = root.

(* WHAT THE TRAP DELIVERED, in the vocabulary the two tiers meet in.

   [trap_mstatus_ok] is the trampoline's pin set (UserExec.v: SIE = 0,
   SPP = User, MPRV = MXR = 0, SXL = 64, TVM = TSR = 0) -- what uservec's
   own [csrw satp] / [sfence] gates need.  [sconf_ms_facts] is the kernel
   tier's (IntrDefs.v), which additionally pins the FS/VS/XS extension
   states, SD and a nominal MPP: it is what [IntrDefs.sconf] carries, so
   usertrap cannot assemble the bundle its callees take without it.  The two
   overlap and neither implies the other.

   [SPIE = 1] is the third: it is what the mirror half inside
   [usertrap_res] agrees with ([IntrDefs.sret_tie]), and it is a fact about
   the code rather than an assumption about the user -- userret's [sret] set
   SPIE := 1, so user mode ran with SIE = 1, so the trap copied SIE into
   SPIE.  Nothing user mode can execute changes it. *)
Definition usertrap_entry_ms (ms : mword 64) : Prop :=
  trap_mstatus_ok ms /\
  sconf_ms_facts ms /\
  _get_Mstatus_SPIE ms = ('b"1" : mword 1).

(* ... AND [trap_mstatus_ok] NOW IMPLIES THE OTHER TWO.  [UserExec.v]'s
   trap predicate carries FS/VS/XS/SD/MPP and SPIE = 1 since 2026-08-21 --
   the user tier preserves them (mstatus is never written in user mode) from
   what userret's sret left.  Before that, uservec's contract had to take
   this implication as a ∀-premise, which was unsatisfiable
   (claude-notes/projects/forkret-park.md §4). *)
Lemma usertrap_entry_ms_of_trap (ms : mword 64) :
  trap_mstatus_ok ms -> usertrap_entry_ms ms.
Proof.
  intro H. pose proof H as H'.
  destruct H' as (HSXL & HMPRV & HMXR & HSPP & HSIE & HTVM & HTSR &
                  HFS & HVS & HXS & HSD & HMPP & HSPIE).
  split; [exact H |]. split; [| exact HSPIE].
  unfold sconf_ms_facts. split_and!; try assumption.
  unfold WpGprCsrwCommon.have_nom_val.
  destruct (eq_vec (_get_Mstatus_MPP ms) ('b"00")); [reflexivity |].
  destruct (eq_vec (_get_Mstatus_MPP ms) ('b"01")); [reflexivity |].
  rewrite HMPP. reflexivity.
Qed.

(* ===================================================================== *)
(* THE TRAP ROUND, as the boundary states it (milestone J1a).             *)
(*                                                                         *)
(* [U] is the process's state AS USERTRAP WAS ENTERED -- the record        *)
(* uservec's save walk left, whose epc word is still the PREVIOUS round's; *)
(* [sepc_v] is the faulting pc the trap delivered and [sc_v] the cause.    *)
(* [tf0] is therefore the entry trapframe as usertrap's own prologue       *)
(* leaves it: the +0x28..+0x2e block writes [p->trapframe->epc =           *)
(* r_sepc()] and nothing else, so [pv_tf] of the record the entry hands on *)
(* IS [tf0] by reflexivity.  ([ret_pc] is [WpGprCsrwA.mepc_val] -- the same *)
(* term under two names; this file already has [ret_pc] in scope.)         *)
(*                                                                         *)
(* THERE IS NO ESCAPE LEFT (stage S8b).  Every ecall is proved for real:   *)
(* exec by [uround_ok]'s own left disjunct, the other twenty-two by the    *)
(* bump plus [UsysMemOk.usys_mem_ok] -- sbrk included, now that the        *)
(* dispatcher's row names the address space's move as a FUNCTION of the    *)
(* two sizes ([SpecSyscall.sysc_sbrk_ok]) and both directions of its       *)
(* permission relation are derivable                                       *)
(* ([UsysMemOkSpec.usys_sbrk_perm_of_row], over                            *)
(* [UsysMemOkSpec.perm_of_grow] and [UserPerm.perm_of_del_run]).           *)
(* ===================================================================== *)
Definition ut_round (sepc_v sc_v : mword 64) (U U' : ustate) : Prop :=
  uround_ok sc_v
    (<[tf_epc_idx := ret_pc sepc_v]> (pv_tf (us_V U)))
    (us_M U) (perm_of (ud_um (pv_upt (us_V U))) (uint (pv_sz (us_V U))))
    (uint (pv_sz (us_V U)))
    (pv_tf (us_V U')) (us_M U')
    (perm_of (ud_um (pv_upt (us_V U'))) (uint (pv_sz (us_V U'))))
    (uint (pv_sz (us_V U'))).

(* THE DESCRIPTOR HALF OF THE ROUND, and the reason it is CONDITIONAL.
   [ut_round] speaks the trapframe, image, permission map and break; it says
   nothing about [p->ofile[]], because for every cause but one there is
   nothing to say -- a page fault or an interrupt runs no kernel code that
   can retype a descriptor, so the states come back on the nose.  The one
   exception is the ecall, where open/close/dup/pipe are exactly the entries
   that move them.

   WHY THE CALLER NEEDS THIS AND NOT MERELY THE RESIDUE'S INDEX.  The loop
   resumes the process at a key, and the key names the descriptor view
   ([UexecSlot.uvis_fd]).  On a transparent trap it must resume at the view
   that TRAPPED -- [UexecApply.uexec_ret_round_slot]'s transparent arm hands
   back the process's own continuation at the same key, and a key with a
   different fd view is a different contract.  So "the kernel did not move
   them" is a fact the loop has to be TOLD; it cannot read it off the
   fragments it holds ([FdSlots.fd_st_agree] against the authority only ever
   says the fragments agree with themselves). *)
Definition ut_fd_kept (sc_v : mword 64) (sts sts' : list fdstate) : Prop :=
  sc_v <> uecall_scause -> sts' = sts.

(* ...AND THE ECALL'S OWN HALF, which used to be missing.  [ut_fd_kept]
   above is the whole statement for four of the five causes and says
   NOTHING for the fifth -- so "close(3) closed slot 3" was proved inside
   sys_close, carried by the dispatcher, and then dropped at this frame.
   This is the row that carries it out, and it is the same table
   [SpecSyscall.sysc_fd_ok] states the dispatch against
   ([UsysMemOk.usys_fd_ok]): eighteen entries move nothing, and open,
   close, dup and pipe each say which slot they changed and to what.

   BOTH TRAPFRAMES ARE READ, AND AT DIFFERENT WORDS.  The number and the
   argument come from the ENTRY trapframe [tf] -- a0 as the kernel FOUND it
   -- and the return value from the OUTGOING one [tf'], whose a0 word is
   what the dispatch's [sd a0,112(s2)] stored over it.  Neither reading is
   disturbed by the epc, which usertrap's prologue rewrites and its
   epilogue bumps ([UsysMemOk.usys_fd_ok_epc]).

   THE TWO HALVES ARE KEPT APART rather than fused into one [if]: the four
   transparent arms prove [ut_fd_kept] by [reflexivity] and have no
   trapframe pair to speak of, while the ecall arm proves this one and
   nothing else.  A fused definition would make every arm carry both
   trapframes to say the half it does not use. *)
Definition ut_fd_ecall (sc_v : mword 64) (tf tf' : list (mword 64))
    (sts sts' : list fdstate) : Prop :=
  sc_v = uecall_scause ->
  UsysMemOk.usys_fd_ok (UsysMemOk.usys_num tf) tf
    (tf' !!! tf_arg_idx 0) sts sts'.

(* THE ROW READS THE OUTGOING TRAPFRAME AT ONE WORD ONLY, so a tail that
   parks a DIFFERENT record -- prepare_return re-arms the four kernel words
   on the way out -- carries the row across by agreeing at that word.
   [TfUser.tf_ueq_arg] is what supplies the agreement. *)
(* ...and the ENTRY trapframe likewise, at the TWO words the row reads: a7
   for the number and a0 for the argument.  Nothing else about the frame
   matters, which is why this is stated at two lookups rather than at
   [TfUser.tf_ueq] -- the caller that wants it (uservec, restating the row
   at [tf_of g] after the save walk) has an epc rewrite in between, and
   [tf_ueq] is not blind to the epc. *)
Lemma ut_fd_ecall_in (sc_v : mword 64) (tf1 tf2 tf' : list (mword 64))
    (sts sts' : list fdstate) :
  tf1 !!! tf_arg_idx 7 = tf2 !!! tf_arg_idx 7 ->
  tf1 !!! tf_arg_idx 0 = tf2 !!! tf_arg_idx 0 ->
  ut_fd_ecall sc_v tf1 tf' sts sts' -> ut_fd_ecall sc_v tf2 tf' sts sts'.
Proof.
  intros H7 H0 H Hc.
  rewrite <- (UsysMemOk.usys_num_arg_cong _ _ H7).
  exact (UsysMemOk.usys_fd_ok_arg_cong _ tf1 tf2 _ _ _ H0 (H Hc)).
Qed.

Lemma ut_fd_ecall_out (sc_v : mword 64) (tf tf1 tf2 : list (mword 64))
    (sts sts' : list fdstate) :
  tf1 !!! tf_arg_idx 0 = tf2 !!! tf_arg_idx 0 ->
  ut_fd_ecall sc_v tf tf1 sts sts' -> ut_fd_ecall sc_v tf tf2 sts sts'.
Proof. intros He H Hc. rewrite <- He. exact (H Hc). Qed.

(* ...AND PIPE'S JOIN, carried out of the ecall arm beside the row above.
   [ut_fd_ecall] says pipe opened two free slots and [ut_round]'s image half
   says it wrote up to eight bytes at a0; ONLY THIS says the bytes name the
   slots, which is the whole of pipe() to the program that called it.  Same
   two trapframes, read at the same two words, so the two travel together
   and cross the prologue's epc rewrite by the same lemma
   ([UsysMemOk.usys_pipe_ok_epc]).  See [UsysMemOk.v]'s SS2c. *)
Definition ut_pipe_ecall (sc_v : mword 64) (tf tf' : list (mword 64))
    (M M' : gmap Z (bv 8)) (sts sts' : list fdstate) : Prop :=
  sc_v = uecall_scause ->
  UsysMemOk.usys_pipe_ok (UsysMemOk.usys_num tf) tf
    (tf' !!! tf_arg_idx 0) M M' sts sts'.

(* the two congruences, in the shapes [ut_fd_ecall] has them: the entry
   frame at a7 and a0, the outgoing frame at a0. *)
Lemma ut_pipe_ecall_in (sc_v : mword 64) (tf1 tf2 tf' : list (mword 64))
    (M M' : gmap Z (bv 8)) (sts sts' : list fdstate) :
  tf1 !!! tf_arg_idx 7 = tf2 !!! tf_arg_idx 7 ->
  tf1 !!! tf_arg_idx 0 = tf2 !!! tf_arg_idx 0 ->
  ut_pipe_ecall sc_v tf1 tf' M M' sts sts' ->
  ut_pipe_ecall sc_v tf2 tf' M M' sts sts'.
Proof.
  intros H7 H0 H Hc.
  rewrite <- (UsysMemOk.usys_num_arg_cong _ _ H7).
  exact (UsysMemOk.usys_pipe_ok_arg_cong _ tf1 tf2 _ _ _ _ _ H0 (H Hc)).
Qed.

Lemma ut_pipe_ecall_out (sc_v : mword 64) (tf tf1 tf2 : list (mword 64))
    (M M' : gmap Z (bv 8)) (sts sts' : list fdstate) :
  tf1 !!! tf_arg_idx 0 = tf2 !!! tf_arg_idx 0 ->
  ut_pipe_ecall sc_v tf tf1 M M' sts sts' ->
  ut_pipe_ecall sc_v tf tf2 M M' sts sts'.
Proof. intros He H Hc. rewrite <- He. exact (H Hc). Qed.

(* the quiet reading, for the four non-ecall causes: they never reach the
   dispatch, so the guard is unreachable through [sc_v]. *)
Lemma ut_pipe_ecall_quiet (sc_v : mword 64) (tf tf' : list (mword 64))
    (M M' : gmap Z (bv 8)) (sts sts' : list fdstate) :
  sc_v <> uecall_scause -> ut_pipe_ecall sc_v tf tf' M M' sts sts'.
Proof. intros Hne Hc. contradiction (Hne Hc). Qed.

(* ===================================================================== *)
(* THE EXEC CHANNEL THROUGH USERTRAP (lane E3b).  The process offers its    *)
(* exec bundle at an exec ecall ([ut_exec_in]: [UexecExecInst.exec_xbundle]  *)
(* at the trapping key, i.e. [SpecSyscall.sysc_exec_in] at the record       *)
(* usertrap was entered at) and gets the kernel's answer back               *)
(* ([ut_exec_out]: [SpecSyscall.sysc_exec_out] re-spelled at the round's    *)
(* entry trapframe).  Both are guarded on the CAUSE and the NUMBER, so the  *)
(* four transparent arms discharge them by refuting the guard.              *)
(*                                                                          *)
(* THE FAILURE ARM IS DELIBERATELY [UexecRound.uround_ok]'s returning       *)
(* disjunct at [r = -1] -- the bump plus [UsysMemOk.usys_mem_ok]'s exec     *)
(* row -- so the U-mode loop pays it with the returning-arm proof it        *)
(* already has ([UexecApplyX.uexec_ret_x_round_slot]).  It is stated at    *)
(* the round's OWN entry trapframe (the prologue's epc rewrite applied,    *)
(* exactly [ut_round]'s) because the bump reads the epc.                   *)
(* ===================================================================== *)
Definition ut_exec_in `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
    (sc_v : mword 64) (tf : list (mword 64)) (U : ustate) (sts : list fdstate)
    : iProp Σ :=
  (⌜sc_v = uecall_scause /\ usys_num tf = USYS_exec⌝ -∗
     xbundle uslot_x (uvis_of U sts))%I.

Definition ut_exec_out `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
    (sc_v : mword 64) (tf : list (mword 64)) (M : gmap Z (bv 8))
    (π : gmap (mword 27) uperm) (szv : Z)
    (U' : ustate) (sts sts' : list fdstate) : iProp Σ :=
  (⌜sc_v = uecall_scause /\ usys_num tf = USYS_exec⌝ -∗
     (⌜exists r : mword 64,
         uround_bump_ok tf (pv_tf (us_V U')) r
         /\ usys_mem_ok USYS_exec tf r M π szv (us_M U')
              (perm_of (ud_um (pv_upt (us_V U'))) (uint (pv_sz (us_V U'))))
              (uint (pv_sz (us_V U')))
         /\ sts' = sts⌝                       (* failed: the returning shape at r = -1 *)
      ∨ uslot_x (uvis_of U' sts')                     (* loadable: the new image's slot *)
      ∨ ⌜pv_tf (us_V U') !!! tf_arg_idx 0 <> (mword_of_int (-1) : mword 64)⌝))%I.   (* the gap *)

(* the quiet readings, for the four non-ecall causes *)
Lemma ut_exec_in_quiet `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
    (sc_v : mword 64) (tf : list (mword 64)) (U : ustate) (sts : list fdstate) :
  sc_v <> uecall_scause -> ⊢ ut_exec_in sc_v tf U sts.
Proof.
  intros Hne. rewrite /ut_exec_in. iIntros "%Hc". exfalso. exact (Hne (proj1 Hc)).
Qed.

Lemma ut_exec_out_quiet `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
    (sc_v : mword 64) (tf : list (mword 64)) (M : gmap Z (bv 8))
    (π : gmap (mword 27) uperm) (szv : Z)
    (U' : ustate) (sts sts' : list fdstate) :
  sc_v <> uecall_scause -> ⊢ ut_exec_out sc_v tf M π szv U' sts sts'.
Proof.
  intros Hne. rewrite /ut_exec_out. iIntros "%Hc". exfalso. exact (Hne (proj1 Hc)).
Qed.

(* the pre row's key congruence: the bundle reads the image, the a1 word
   and the descriptor view off its key, and the guard the number -- which
   is what carries it across the prologue's epc rewrite and uservec's save
   walk ([UexecRetExec.xbundle_cong]) *)
Lemma ut_exec_in_cong `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
    (sc_v : mword 64) (tf tf' : list (mword 64)) (U U' : ustate)
    (sts : list fdstate) :
  usys_num tf = usys_num tf' ->
  us_M U = us_M U' ->
  tf_w (pv_tf (us_V U)) (tf_arg_idx 1) = tf_w (pv_tf (us_V U')) (tf_arg_idx 1) ->
  ut_exec_in sc_v tf U sts -∗ ut_exec_in sc_v tf' U' sts.
Proof.
  intros Hn HM Ha1. rewrite /ut_exec_in. iIntros "H %Hc".
  iDestruct ("H" with "[%]") as "H";
    [ split; [exact (proj1 Hc) | rewrite Hn; exact (proj2 Hc)] |].
  iEval (rewrite (xbundle_cong uslot_x (uvis_of U sts) (uvis_of U' sts)
                    HM Ha1 eq_refl)) in "H".
  iExact "H".
Qed.

(* ...and the post row's: across a tail that re-keys the parked record in
   the four kernel words (prepare_return) or the descriptor's derived
   field (uservec's renormalisation), and across uservec's save walk on the
   entry side.  The row reads the entry frame at the number, the epc and
   the resume projections, the exit record at its resume projections, its
   a0 word, image, permission map and break -- all inside [tf_ueq]'s
   reach. *)
Lemma ut_exec_out_ueq `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
    (sc_v : mword 64) (tf tf' : list (mword 64)) (M : gmap Z (bv 8))
    (π : gmap (mword 27) uperm) (szv : Z)
    (U' U'' : ustate) (sts sts' : list fdstate) :
  tf_ueq tf tf' ->
  tf_ueq (pv_tf (us_V U')) (pv_tf (us_V U'')) ->
  us_M U'' = us_M U' ->
  perm_of (ud_um (pv_upt (us_V U''))) (uint (pv_sz (us_V U'')))
    = perm_of (ud_um (pv_upt (us_V U'))) (uint (pv_sz (us_V U'))) ->
  pv_sz (us_V U'') = pv_sz (us_V U') ->
  ut_exec_out sc_v tf M π szv U' sts sts' -∗
  ut_exec_out sc_v tf' M π szv U'' sts sts'.
Proof.
  intros Hu Hu' HM Hpi Hsz. rewrite /ut_exec_out. iIntros "H %Hc".
  iDestruct ("H" with "[%]") as "[%Hf | [Hs | %Hg]]";
    [ split; [exact (proj1 Hc) | rewrite (tf_ueq_num tf tf' Hu); exact (proj2 Hc)]
    | | | ].
  - iLeft. iPureIntro. destruct Hf as (r & [Hb1 Hb2] & Hm & Hst).
    exists r. split; [split |].
    + rewrite <- (tf_ueq_resume_gpr0 _ _ Hu'). rewrite <- (tf_ueq_resume_gpr0 _ _ Hu).
      exact Hb1.
    + rewrite <- (tf_ueq_resume_pc _ _ Hu'). unfold tf_w.
      rewrite <- (tf_ueq_epc _ _ Hu). exact Hb2.
    + split; [| exact Hst]. rewrite HM Hpi Hsz.
      exact (usys_mem_ok_ueq _ _ _ _ _ _ _ _ _ _ Hu Hm).
  - iRight. iLeft.
    iEval (rewrite (uslot_x_key_cong (uvis_of U' sts') (uvis_of U'' sts')
                      (tf_ueq_resume_gpr0 _ _ Hu') (tf_ueq_resume_pc _ _ Hu')
                      (eq_sym HM) (eq_sym Hpi) (f_equal uint (eq_sym Hsz)) eq_refl))
      in "Hs".
    iExact "Hs".
  - iRight. iRight. iPureIntro.
    rewrite <- (tf_ueq_arg _ _ 0 ltac:(lia) Hu'). exact Hg.
Qed.

(* THE PROLOGUE'S OWN MOVE: [U'] is [U] with the epc word rewritten, which
   is what usertrap's +0x28..+0x2e block does and all it does.  Every block
   below the entry carries this (or the round it grows into) as a premise. *)
Definition ut_pro (sepc_v : mword 64) (U U' : ustate) : Prop :=
  pv_tf (us_V U') = <[tf_epc_idx := ret_pc sepc_v]> (pv_tf (us_V U))
  /\ pv_upt (us_V U') = pv_upt (us_V U)
  /\ pv_sz (us_V U') = pv_sz (us_V U)
  /\ us_M U' = us_M U.

(* THE ENTRY INSTANCE: at the record the prologue hands on, the round has
   done nothing yet, so every arm of the relation is an identity. *)
Lemma ut_round_entry (sepc_v sc_v : mword 64) (U U' : ustate) :
  (* the entry instance is available only where the dispatch has already
     ruled the ecall arm out -- which is exactly the four arms that take
     it; on the ecall arm the round has real content from the first step. *)
  sc_v <> uecall_scause ->
  ut_pro sepc_v U U' -> ut_round sepc_v sc_v U U'.
Proof.
  intros Hne (Htf & Hupt & Hsz & HM). unfold ut_round, uround_ok.
  destruct (decide (sc_v = uecall_scause)) as [Heq | _]; [ contradiction (Hne Heq) | ].
  rewrite Htf Hupt Hsz HM. unfold uround_id_ok.
  split_and!; reflexivity.
Qed.

(* A BLOCK THAT DOES NOT MOVE THE USER-VISIBLE STATE relays the round. *)
Lemma ut_round_same (sepc_v sc_v : mword 64) (U U' U'' : ustate) :
  pv_tf (us_V U'') = pv_tf (us_V U') ->
  perm_of (ud_um (pv_upt (us_V U''))) (uint (pv_sz (us_V U'')))
    = perm_of (ud_um (pv_upt (us_V U'))) (uint (pv_sz (us_V U'))) ->
  us_M U'' = us_M U' ->
  (* the break is user-visible now, so "does not move the user-visible
     state" has to say so *)
  pv_sz (us_V U'') = pv_sz (us_V U') ->
  ut_round sepc_v sc_v U U' -> ut_round sepc_v sc_v U U''.
Proof.
  intros H1 H2 H3 H4 H. unfold ut_round in H |- *.
  rewrite H1 H2 H3 H4. exact H.
Qed.

(* ...and one that moves it only in the four KERNEL words (prepare_return). *)
Lemma ut_round_ueq (sepc_v sc_v : mword 64) (U U' U'' : ustate) :
  tf_ueq (pv_tf (us_V U')) (pv_tf (us_V U'')) ->
  perm_of (ud_um (pv_upt (us_V U''))) (uint (pv_sz (us_V U'')))
    = perm_of (ud_um (pv_upt (us_V U'))) (uint (pv_sz (us_V U'))) ->
  us_M U'' = us_M U' ->
  pv_sz (us_V U'') = pv_sz (us_V U') ->
  ut_round sepc_v sc_v U U' -> ut_round sepc_v sc_v U U''.
Proof.
  intros Hu H2 H3 H4 H. unfold ut_round in H |- *. rewrite H2 H3 H4.
  eapply uround_ok_ueq_r; [ exact Hu | exact H ].
Qed.

(* The statement, parameterized over the abstract kernel-internal resource
   [R : uptd -> mword 64 -> iProp Σ]: [R pt ksp] is everything usertrap needs
   beyond the machine state above, for the process whose user page table is
   [pt] and whose kernel stack top is [ksp].  The module type instantiates it
   with its own [usertrap_res].

   The key is (pt, ksp) and not the process's ghost names because those are
   the only two the TRAMPOLINE knows: the proof's definition existentially
   packages the rest (the fd-table name, the slot index, the pid, the private
   record [V] with [pv_upt V = pt], the stack budget, the per-cpu frame) --
   see claude-notes/projects/usertrap.md.  [ksp] appears because [sie_cap] is
   keyed on sp, which is what the [m !!! sp = ksp] premise below licenses. *)
Definition usertrap_post `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (R : uptd -> mword 64 -> ustate -> list fdstate -> iProp Σ)
    (pt : uptd) (ksp : mword 64) (m : regfile)
    (mie_v menvcfg0 : mword 64)
    (* THE ROUND'S ENTRY STATE (milestone J1a).  [U] is the process's state
       AS USERTRAP WAS ENTERED -- the record uservec's save walk left, whose
       epc word is still the PREVIOUS round's; [sepc_v] is the faulting pc
       the trap delivered and [sc_v] the cause.  [tf0] below is therefore the
       entry trapframe as usertrap's own prologue leaves it (the
       +0x28..+0x2e block writes [epc := r_sepc()]), which is the user-visible
       trapframe the round starts from. *)
    (U : ustate) (sts : list fdstate) (sepc_v sc_v : mword 64) : iProp Σ :=
  let ret_tgt : mword 64 := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  ( ∀ (pt' : uptd) (mf : regfile)
      (ms' usatp uepc sc' stval' mdv0 : mword 64) (U' : ustate)
      (* THE ROUND MAY HAVE MOVED THE DESCRIPTOR STATES, and the post names
         where they landed -- open/close/dup/pipe are the entries that do.
         ∃-bound with [U'] for the same reason: the round chooses. *)
      (sts' : list fdstate),
    (* ---- THE ROUND, as a relation on the user-visible state -------------
       [UexecRound.uround_ok] keyed on the cause, exactly as the dispatch's
       own [c.li a5,8; bne] is: an ecall either was exec (whose successor WP
       is a kernel MINT, so the row says nothing) or bumped the trapframe and
       moved the image/permission map by what the entry's own syscall row
       allows; anything else resumes the trapped state on the nose.
       J1a's temporary escape for the ecall arm (S7), narrowed to sbrk at
       S8, is GONE at S8b: every entry, sbrk included, proves the row.
       The third premise is prepare_return's [csrw sepc, p->trapframe->epc]
       read back through [tf_resume_pc]: the pc the sret lands at IS the
       resume trapframe's own. *)
    ⌜pv_upt (us_V U') = pt'⌝ -∗
    ⌜ut_round sepc_v sc_v U U'⌝ -∗
    (* ...and its descriptor half, on both sides of the cause: nothing moved
       unless this was an ecall, and if it was, the syscall table says what
       did. *)
    ⌜ut_fd_kept sc_v sts sts'⌝ -∗
    ⌜ut_fd_ecall sc_v (pv_tf (us_V U)) (pv_tf (us_V U')) sts sts'⌝ -∗
    (* ...and pipe's join, off the same pair -- see [ut_pipe_ecall] *)
    ⌜ut_pipe_ecall sc_v (pv_tf (us_V U)) (pv_tf (us_V U'))
                   (us_M U) (us_M U') sts sts'⌝ -∗
    ⌜ret_pc uepc = tf_resume_pc (pv_tf (us_V U'))⌝ -∗
    (* [mideleg]'s VALUE is not pinned to whatever usertrap was handed at
       entry -- unlike [mie_v]/[menvcfg0] (each a unique architectural
       constant, so their exit value provably equals the entry one),
       [mideleg] is a genuine existential inside [IntrDefs.sconf], and
       nothing tracks "the same witness" across usertrap's internal
       instruction-step lemmas (which carry [sconf] opaquely, never
       re-destructuring it) -- so the caller only gets a FRESH value
       satisfying the same mask, discovered at the exit. *)
    ⌜and_vec mie_v (not_vec mdv0) = zeros' 64⌝ -∗
    (* THE TRAPFRAME PAGE IS THE ONE THING THAT CANNOT MOVE, and the ROOT IS
       NOT.  The first draft promised [ud_root pt' = ud_root pt] as well, on
       the strength of the vmfault arm (which only inserts leaves).  It is
       FALSE on the syscall arm: exec() replaces the address space wholesale,
       so [SpecSyscall]'s post pins [ud_tfp] and nothing else, and no proof of
       the stronger conjunct exists.  Nothing wanted it either -- what the
       trampoline needs is that the satp usertrap RETURNS is rooted at the
       table it hands over, which is [satp_rooted usatp (ud_root pt')]
       below. *)
    ⌜ud_tfp pt' = ud_tfp pt⌝ -∗
    (* the pure facts the trampoline halves need about it, which the process
       block's [proc_pt_at] carries -- and there are TWO of them, not three.
       [udata_cov (ud_um pt') (ud_data pt')] used to be here and is NOT
       provable: [ProcPtOwn] deliberately retired the field-to-field coupling
       between [ud_um] and [ud_data] ("the footprint derived from [um]", its
       §1), so [proc_pt] says nothing about [ud_data]; and on the syscall arm
       the descriptor is whatever the table entry left, of which
       [SpecSyscall]'s post pins only [ud_tfp].  Nor is it usertrap's fact to
       state: the trampoline needs it beside the process's memory, and
       the conversion that BUILDS that resource -- the page-footprint side of
       the dovetail, conversion 2 -- derives the footprint from [ud_um] and so
       establishes the coverage by construction ([ProcPtOwn.ud_pas_cov]).
       Asking for it here would be asking usertrap to prove a property of a
       resource it never holds. *)
    ⌜upt_acc_wf (ud_um pt')⌝ -∗
    ⌜upt_map_wf (ud_um pt')⌝ -∗
    (* sret-ready, and still a legal S-mode configuration *)
    ⌜usertrap_ret_ms ms'⌝ -∗
    ⌜sconf_ms_facts ms'⌝ -∗
    ⌜callee_saved m mf⌝ -∗
    ⌜mf !!! Regidx (mword_of_int 4 : mword 5) = cid_word⌝ -∗
    (* the return value: MAKE_SATP(p->pagetable) *)
    ⌜mf !!! Regidx (mword_of_int 10 : mword 5) = usatp⌝ -∗
    ⌜satp_rooted usatp (ud_root pt')⌝ -∗
    hart_state ↦ᵣ HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ Supervisor -∗
    mstatus ↦ᵣ ms' -∗
    scause ↦ᵣ sc' -∗
    stval ↦ᵣ stval' -∗
    (* the user pc to resume, which prepare_return's [csrw sepc] wrote *)
    sepc ↦ᵣ uepc -∗
    (* THE VECTOR IS BACK AT uservec, and still owned outright: after
       prepare_return this hart has no kernel handler installed, which is
       what forbids re-enabling interrupts before the sret. *)
    stvec ↦ᵣ (mword_of_int TRAMPOLINE : mword 64) -∗
    pc_is ret_tgt -∗
    gpr_file mf -∗
    (* the three [sconf] cells usertrap borrowed for its own call and hands
       back UNCHANGED (usertrap never writes them) -- see [wp_usertrap_body]'s
       matching entry premise. *)
    mie ↦ᵣ mie_v -∗
    mideleg ↦ᵣ mdv0 -∗
    menvcfg ↦ᵣ menvcfg0 -∗
    (* [hw_config]/[minstret_inv], AT THE RESUMING HART.  Both are persistent
       and ride at the head of [sconf] -- [wp_usertrap_body]'s own entry
       premise hands them in as a free borrow (see its comment) on the
       strength that "persistent costs the caller nothing", but that is only
       true AT ONE HART: usertrap may cross to a different hart before it
       returns (the whole reason [R] above is hart-indexed), and a caller's
       pre-crossing copy is a DIFFERENT resource from the post-crossing one
       (same shape, different hart index, indistinguishable on the page).
       The proof already has the resuming hart's own copies on hand at this
       exact point -- [ut_ret2] unpacks them straight out of [sconf] just
       like [ut_dup_hw] does -- so exposing them here costs nothing new to
       prove, only to thread through. *)
    hw_config -∗
    minstret_inv -∗
    R pt' ksp U' sts' -∗
    (* THE EXEC CHANNEL'S ANSWER (lane E3b), at the round's entry trapframe
       and the record the round left -- see [ut_exec_out] *)
    ut_exec_out sc_v (<[tf_epc_idx := ret_pc sepc_v]> (pv_tf (us_V U)))
      (us_M U) (perm_of (ud_um (pv_upt (us_V U))) (uint (pv_sz (us_V U))))
      (uint (pv_sz (us_V U))) U' sts sts' -∗
    WP (Loop : expr riscv_lang)).

(* [R] IS A HART-INDEXED FAMILY, AND IT HAS TO BE.  usertrap is handed the
   kernel-side bundle at the hart the TRAP came in on and gives it back at the
   hart it RESUMES on -- the two are different whenever the function parks
   (yield, and every sleeping syscall through [SpecSyscall]'s own crossing),
   and everything inside [UsertrapRes.ut_res] except the stack is per-hart
   ([sie_arm], [cpu_own], [cpu_claim], the [sconf] closer's register cells,
   the SIE ghost).  Written as a plain [uptd -> mword 64 -> iProp Σ] the
   post's [R] is pinned to the ENTRY hart, and no proof of it exists: the tail
   rebuilds the bundle out of what prepare_return handed back, which is at the
   resuming hart ([ProofUsertrapTail.ut_ret2], whose whole reason for being
   its own section is that hart).  So [R] takes the hart: [R CID] going in,
   [R CID'] coming out, where [CID'] is the crossing's own binder.  The
   module type below supplies [fun h => usertrap_res (CID := h)]. *)
Definition wp_usertrap_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (R : CpuId -> uptd -> mword 64 -> ustate -> list fdstate -> iProp Σ)
    (pt : uptd) (j : nat)
    (m : regfile) (ms_v sc_v stval_v sepc_v ksp : mword 64)
    (mie_v mdv0 menvcfg0 : mword 64) (U : ustate) (sts : list fdstate) :=
  let pcE : mword 64 := mword_of_int KernelSyms.usertrap in
  let pj := proc_addr j in
  (* the trap delivered a legal S-mode configuration -- see above *)
  usertrap_entry_ms ms_v ->
  (j < NPROC)%nat ->
  (* calling convention: sp = the process's kernel stack top (uservec loaded
     it out of the trapframe's kernel_sp), tp = this hart's id (myproc),
     ra = uva 0x9c, i.e. userret -- usertrap RETURNS INTO userret. *)
  m !!! Regidx (mword_of_int 2 : mword 5) = ksp ->
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* the three [sconf] pins usertrap needs of the CSRs it borrows -- see the
     matching conjunct of [mie]/[mideleg]/[menvcfg] below *)
  mie_v = MIE_S ->
  and_vec mie_v (not_vec mdv0) = zeros' 64 ->
  menvcfg0 = MENVCFG_S ->
  kernel_text -∗ pc_is pcE -∗
  (* [hw_config]/[minstret_inv] are persistent, so borrowing a copy for the
     duration of the call costs the caller nothing -- unlike [mie]/
     [mideleg]/[menvcfg] below, which usertrap needs at FULL ownership
     (it assembles [IntrDefs.sconf], hence [sie_cap_gpr], out of them for its
     own internal kernel-tier step lemmas) and must therefore borrow and
     give back explicitly, exactly like every other loose cell here.
     [usertrap_post] hands a copy back too, in spite of that -- NOT because
     the call could otherwise lose them (a persistent proposition is never
     consumed), but because usertrap may CROSS HARTS before it returns, and
     the entry copy is a resource AT THE ENTRY HART, silent on any other
     one.  A caller that needs [hw_config] again after the call (uservec's
     tail does, to reach userret) needs it AT THE RESUMING HART, which only
     [usertrap_post] itself is in a position to hand over. *)
  hw_config -∗ minstret_inv -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  cur_privilege ↦ᵣ Supervisor -∗
  mstatus ↦ᵣ ms_v -∗
  scause ↦ᵣ sc_v -∗
  stval ↦ᵣ stval_v -∗
  sepc ↦ᵣ sepc_v -∗
  (* NO KERNEL HANDLER IS INSTALLED: the cell is owned raw, at the
     trampoline, and the [csrw stvec] at +0x1e is what turns it into an
     [intr_res].  The dangling SIE quarter that pairs with it rides inside
     [R] -- see the header. *)
  stvec ↦ᵣ (mword_of_int TRAMPOLINE : mword 64) -∗
  mie ↦ᵣ mie_v -∗
  mideleg ↦ᵣ mdv0 -∗
  menvcfg ↦ᵣ menvcfg0 -∗
  gpr_file m -∗
  (* everything kernel-side, abstractly, AT THE ENTRY HART *)
  R CID pt ksp U sts -∗
  (* the process's exec bundle, owed only at an exec ecall -- [ut_exec_in] *)
  ut_exec_in sc_v (pv_tf (us_V U)) U sts -∗
  (* THE CROSSING: usertrap parks (yield, and every sleeping syscall), so it
     may return on a different hart -- and the bundle comes back at THAT
     hart, which is why [R] is a family (see the note above). *)
  wp_next true pj (fun (CID' : CpuId) =>
    usertrap_post (CID := CID') (R CID') pt ksp m mie_v menvcfg0 U sts sepc_v sc_v) -∗
  WP (Loop : expr riscv_lang).

(* THE MODULE TYPE'S INSTANCE LIST IS THE UNION OF THE FIVE CONES', NOT THE
   BOUNDARY'S.  [wp_usertrap_body] above needs almost none of these -- its
   own statement is register cells, [wp_next] and the abstract [R] -- but
   [usertrap_res] is a PARAMETER, so its type has to be the one its
   instantiation has, and [UsertrapRes.ut_res] is the union of syscall's /
   devintr's / vmfault's / printk-general's / kexit's environments.  It is
   SpecKexit.v's list verbatim (kexit is the deepest of the five, and the
   other four add no class of their own).  A consumer that only wants the
   boundary pays nothing for them: they are Sigma constraints, discharged by
   whatever Sigma the whole-system composition is built over. *)
(* SPLIT OUT so the definition can be checked against it WHERE IT IS WRITTEN.
   [UsertrapRes.v] defines the bundle long before ProofUsertrap can seal
   USERTRAP (its [wp_usertrap] is the whole proof), and a parameter's instance
   list that does not admit its instantiation is a thing to discover there
   rather than at the seal.  [UsertrapRes.UtResFits] is a
   [<: USERTRAP_RES], which makes that mechanical. *)
Require Import UserFd.   (* [ufdG] -- the class a minted user slot needs *)
Module Type USERTRAP_RES.
  (* the kernel-internal resources usertrap consumes, for the process whose
     user page table is [pt] and whose kernel stack top is [ksp]: defined
     concretely by the proof (as [UsertrapRes.ut_res SY.syscall_env], the
     functor's syscall environment being the one piece that is itself still
     abstract); threaded opaquely by consumers. *)
  Parameter usertrap_res :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx},
      uptd -> mword 64 -> ustate -> list fdstate -> iProp Σ.

  (* THE TRAPFRAME BORROW.  [usertrap_res] owns the trapframe page at the
     VA tier internally (via [ProcInv.proc_priv]/[tf_page]) -- it is the
     ONE OWNER, per [UsertrapRes.ut_own]'s own header comment -- but uservec
     ALSO owns the same page's bytes, at the physical tier, as [tf_pa]
     cells (SpecUserret.v's vocabulary), for the whole 44-instruction save/
     restore walk.  Rather than have [usertrap_res] itself borrow-and-return
     the page (which would ripple [wp_usertrap_body]'s type and, through it,
     ONLY every internal usertrap block that already threads [usertrap_res]
     opaquely -- no external file), this accessor lets a HOLDER of
     [usertrap_res] pull [tf_page] out for a moment and hand back a
     (possibly different) one to reseal it -- exactly the shape uservec's
     tail needs: open, convert its own [tf_pa] cells in, close. Concrete
     proof: [UsertrapRes.usertrap_res_tf_open], via [proc_priv_split] +
     [ut_own_priv]. *)
  (* THE PARKED FORM: [usertrap_res] WITHOUT THE TRANSLATION SLOT.
     [usertrap_res] owns [satp] (its internal [strans_inv] sits in the KPT
     arm, i.e. [KptShare.tlb_res_pt]) -- right for the state usertrap RUNS
     in, and impossible for anything parked across user execution, where
     [UptTree.utlb_inv_pt] owns [satp] at the USER root instead.  Holding
     both is contradictory, so a consumer that took [usertrap_res] beside a
     user-mode table would be vacuous rather than wrong-looking.  uservec
     therefore takes the PARKED residue, and its exit switch's own
     [tlb_res_pt] is exactly what completes it; userret's entry switch takes
     that back out.  Concrete: [UsertrapRes.ut_res_parked]. *)
  Parameter usertrap_res_parked :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx},
      uptd -> mword 64 -> ustate -> list fdstate -> iProp Σ.

  (* uservec's move: the switch just installed the kernel table, so the
     residue can be completed into the state usertrap consumes. *)
  Parameter usertrap_res_tlb_close :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (kroot : mword 44) (U : ustate) (sts : list fdstate),
      usertrap_res_parked pt ksp U sts -∗ tlb_res_pt kroot -∗ usertrap_res pt ksp U sts.

  (* userret's move: its entry switch is about to install the USER table, so
     it needs the kernel one back out first.  The root is existential --
     nothing outside pins which table the slot holds, and userret is
     parametric in it. *)
  Parameter usertrap_res_tlb_open :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      usertrap_res pt ksp U sts -∗
      ∃ kroot : mword 44, tlb_res_pt kroot ∗ usertrap_res_parked pt ksp U sts.

  (* THE BARE FORM: the parked residue WITHOUT THE USER ADDRESS SPACE.
     [usertrap_res_parked] fixed ONE of four overlaps with the user tier
     (satp).  The other three are all [proc_pt], which rides inside
     [usertrap_res] via [ProcInv.proc_priv]: the user page-table TREE
     ([ptree_own 2 (DfracOwn 1)]) and the user DATA PAGES, which
     [UserPtTree.user_pt_inv] carries too.  So the parked form is still
     unsatisfiable beside a user-mode frame, and it is the BARE form that
     parks across user execution.  Concrete: [UsertrapRes.ut_res_bare].

     What the bare form still HAS is everything the kernel genuinely owns
     while user code runs -- including [p->pagetable]/[p->trapframe] (cells
     that merely name the table) and the trapframe page itself (physical
     tier, U = 0 leaf, unreachable from user mode).  That is why
     [usertrap_res_tf_open] below is stated on THIS form: the trapframe is
     available in exactly the window the address space is not. *)
  Parameter usertrap_res_bare :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx},
      uptd -> mword 64 -> ustate -> list fdstate -> iProp Σ.

  (* uservec's move, one tier under [_tlb_close]: its exit switch converted
     the user table back to a [pt_frame], and the pages never moved, so
     [ProcPtOwn.user_pt_inv_open] rebuilds [proc_pt] and this reseals it
     into the residue. *)
  Parameter usertrap_res_pt_close :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      usertrap_res_bare pt ksp U sts -∗ (∃ M : gmap Z (bv 8), proc_pt pt M) -∗
      ∃ Mz : gmap Z (bv 8), usertrap_res_parked pt ksp (upd_usM U Mz) sts.

  (* userret's move: the address space is about to be installed again, so
     it comes back out, to be split into the tree the entry switch consumes
     and the pages [ProcPtOwn.user_pt_inv_close] hands the user tier. *)
  Parameter usertrap_res_pt_open :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      usertrap_res_parked pt ksp U sts -∗ (∃ M : gmap Z (bv 8), proc_pt pt M) ∗ usertrap_res_bare pt ksp U sts.

  (* ---- THE SAME TWO CROSSINGS AT THE NAMED LAZY IMAGE (milestone J, S3).
     The pair above is stated at the MAPPED view with the image quantified,
     which is all the uservec seam needed while [uservec_post] handed back
     [UserPtTree.user_pt_any pt'].  Once the round's post names its image --
     and once the loop hands user execution a [UexecRet.uvb] whose image
     conjunct is [user_ptm_inv pt sz M] -- the crossing has to carry the
     name in BOTH directions: the entry image is what [UsysMemOk.usys_mem_ok]
     relates the exit one to.

     THE SIZE IS FORCED, THE IMAGE IS NOT.  The residue's [ut_own] holds
     [ProcPtOwn.proc_ptm] at the process's own [p->sz]
     ([uint (pv_sz (us_V U))]) -- that is the view [proc_priv] splits into --
     so both directions are stated there and neither takes [sz] as a free
     parameter.  The image is free on the close: the BARE residue owns none
     of the user bytes, so it re-parks at whatever image comes back, and the
     index moves by [upd_usM].

     The [_pt_] pair STAYS: other callers speak the mapped view.  Concretes:
     [UsertrapRes.ut_res_ptm_open] / [ut_res_ptm_close] -- the existing
     proofs minus the one weakening step ([proc_ptm_pt] / [proc_pt_ptm_any]). *)
  Parameter usertrap_res_ptm_close :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (M : gmap Z (bv 8)) (sts : list fdstate),
      usertrap_res_bare pt ksp U sts -∗
      proc_ptm pt (uint (pv_sz (us_V U))) M -∗
      usertrap_res_parked pt ksp (upd_usM U M) sts.

  Parameter usertrap_res_ptm_open :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      usertrap_res_parked pt ksp U sts -∗
      proc_ptm pt (uint (pv_sz (us_V U))) (us_M U) ∗ usertrap_res_bare pt ksp U sts.

  (* THE FOOTPRINT RENORMALISATION.  The bare residue reads its descriptor
     only through [ud_root]/[ud_tfp]/[ud_um] -- [proc_pt], the one conjunct
     whose user-side partner names [ud_data], is what it just gave up -- so
     it may be re-keyed on [ProcPtOwn.ud_norm].  That is what lets the trap
     loop hand the user tier a descriptor whose [udata_cov] side condition
     holds by construction, which is the fact this file's [usertrap_post]
     explains it cannot ask usertrap for. *)
  (* THE DESCRIPTOR VIEW, BORROWED OUT OF THE RUNNING RESIDUE -- the fd half
     of what [usertrap_res_ptm_open] does for the image.  The trap loop puts
     what comes out into [UexecRet.uvb] as its [Rfd fdv] and hands it back at
     the trap; the closer is ∀-GENERAL in the states, which is what lets a
     syscall retype a descriptor.  The AUTHORITY does not move -- it rides in
     [ProcInv.ofile_slot], hence inside the residue -- so the kernel keeps the
     array and the process only ever gets the view. *)
  (* BOTH BORROWS AT ONCE -- see [UsertrapRes.ut_res_bare_fd_tf_open] for why
     userret's entry cannot get them by two applications. *)
  Parameter usertrap_res_bare_fd_tf_open :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
    usertrap_res_bare pt ksp U sts -∗
    FdSlots.fd_frags (pv_fdg (us_V U)) sts ∗
    ∃ kroot : mword 44,
      kpt_inv kroot ∗ ⌜tf_kernel_words_ok kroot ksp (pv_tf (us_V U))⌝ ∗
      tf_page (ud_tfp pt) (pv_tf (us_V U)) ∗
      own_context cur_ctx ∗
      (∀ (ws' : list (mword 64)) (sts' : list fdstate),
         ⌜tf_kernel_words_ok kroot ksp ws'⌝ -∗ tf_page (ud_tfp pt) ws' -∗
         FdSlots.fd_frags (pv_fdg (us_V U)) sts' -∗ own_context cur_ctx -∗
         usertrap_res_bare pt ksp (us_tf U ws') sts').

  Parameter usertrap_res_bare_fd_open :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      usertrap_res_bare pt ksp U sts -∗
      FdSlots.fd_frags (pv_fdg (us_V U)) sts ∗
      own_context cur_ctx ∗
      (∀ sts' : list fdstate,
         FdSlots.fd_frags (pv_fdg (us_V U)) sts' -∗ own_context cur_ctx -∗
         usertrap_res_bare pt ksp U sts').

  Parameter usertrap_res_bare_norm :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      usertrap_res_bare pt ksp U sts -∗
      usertrap_res_bare (ud_norm pt) ksp (us_upt U (ud_norm pt)) sts.

  (* THE PER-HART CSRs, borrowed out of the parked residue.  [IntrDefs.
     hart_csrs] -- [sscratch] at an arbitrary value, [medeleg] at
     [MEDELEG_S], the two state-enable pins at zero -- lives in [cpu_priv],
     hence inside the [cpu_own] this residue already carries, because that
     is the bundle a migration re-delivers.  Two consumers, both needing the
     bare form: uservec borrows [sscratch] across its save walk (its own
     [csrw sscratch,a0] at +0x00 writes it and the [csrr] at +0x76 reads it
     back, so a value-agnostic invariant would not serve), and the trap loop
     hands the three pinned cells to [UserExec.user_cfg] for the user phase,
     parking the closer wand in their place.  Concrete:
     [UsertrapRes.ut_res_bare_csrs_open]. *)
  Parameter usertrap_res_csrs_open :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      usertrap_res_bare pt ksp U sts -∗
      hart_csrs ∗ (hart_csrs -∗ usertrap_res_bare pt ksp U sts).

  (* THE TIMER CAPABILITY'S mcounteren PIN.  The U tier needs
     [mcounteren ↦ᵣ□] and it cannot come from [hw_config] (timerinit writes
     mcounteren after that bundle is frozen); the residue carries it inside
     [devintr_caps_any]'s [timer_cap], at every hart.  Persistent, so it is
     handed straight back.  Concrete: [UsertrapRes.ut_res_bare_sstc]. *)
  Parameter usertrap_res_sstc :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      usertrap_res_bare pt ksp U sts -∗ sstc_enabled ∗ usertrap_res_bare pt ksp U sts.

  (* ... AND BOTH AT ONCE, which is what uservec needs: its save walk holds
     the trapframe page open across the same stretch its [csrw sscratch,a0] /
     [csrr t0,sscratch] pair holds the [sscratch] cell.  Each single accessor
     consumes the whole sealed residue, so neither composes with the other's
     remainder -- simultaneous borrows of a sealed bundle come out of ONE
     opener.  Concrete: [UsertrapRes.ut_res_bare_tf_csrs_open]. *)
  Parameter usertrap_res_tf_csrs_open :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      usertrap_res_bare pt ksp U sts -∗
      ∃ kroot : mword 44,
        kpt_inv kroot ∗ ⌜tf_kernel_words_ok kroot ksp (pv_tf (us_V U))⌝ ∗
        tf_page (ud_tfp pt) (pv_tf (us_V U)) ∗ hart_csrs ∗ own_context cur_ctx ∗
        (∀ ws' : list (mword 64),
           ⌜tf_kernel_words_ok kroot ksp ws'⌝ -∗ tf_page (ud_tfp pt) ws' -∗ hart_csrs -∗ own_context cur_ctx -∗
           usertrap_res_bare pt ksp (us_tf U ws') sts).

  (* THE TRAPFRAME BOUND ON [p->sz], off the residue.  Milestone J's resume
     obligation ([UexecRet.uvb]'s [⌜UserPerm.usz_ok sz⌝]) is a fact about
     the process block, and across user execution the loop holds no block
     -- only this residue.  Pure conclusion, so a caller keeps the bundle.
     Concrete: [UsertrapRes.ut_res_bare_sz]. *)
  Parameter usertrap_res_bare_sz :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      usertrap_res_bare pt ksp U sts -∗ ⌜uint (pv_sz (us_V U)) <= uvm_maxsz⌝.

  (* THE APPLICATION-SIDE FS INVARIANT, off the bare residue: the one
     persistent fact the trap loop needs of the kernel to mint the
     process's exec bundle ([UexecExecMint]).  Concrete:
     [UsertrapRes.ut_res_bare_fsabs] at the syscall environment's own
     projection ([SpecSyscall.SYSCALL.syscall_env_fsabs]). *)
  Parameter usertrap_res_bare_fsabs :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      usertrap_res_bare pt ksp U sts -∗
      FirstTok.fsabs_env ∗ usertrap_res_bare pt ksp U sts.

  (* NO SLOT ACCESSOR HERE (milestone J, S6).  The residue used to carry the
     ∀-state [UexecWp.uexec_wp] as [ut_own]'s last conjunct, and this module
     type exported [usertrap_res_uwp_acc] / [usertrap_res_run_open] to pull
     it out and put one back each round.  The trap loop now runs the keyed
     per-process contract ([UexecRet.uslot] / [uexec_ret]) and FRAMES it
     across [wp_uservec_pt] -- projects/user-wp-slot.md SS4c, refutation
     R-a -- so the residue carries no WP and neither accessor has a reader. *)
  Parameter usertrap_res_tf_open :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (pt : uptd) (ksp : mword 64) (U : ustate) (sts : list fdstate),
      (* THE CROSS-ROUND HISTORICAL FACT, bare and undischarged -- see
         [ProcGeom.tf_kernel_words_ok]'s own header. *)
      usertrap_res_bare pt ksp U sts -∗
      ∃ kroot : mword 44,
        kpt_inv kroot ∗ ⌜tf_kernel_words_ok kroot ksp (pv_tf (us_V U))⌝ ∗
        tf_page (ud_tfp pt) (pv_tf (us_V U)) ∗
        own_context cur_ctx ∗
        (∀ ws' : list (mword 64),
           ⌜tf_kernel_words_ok kroot ksp ws'⌝ -∗ tf_page (ud_tfp pt) ws' -∗
         own_context cur_ctx -∗
           usertrap_res_bare pt ksp (us_tf U ws') sts).

End USERTRAP_RES.

Module Type USERTRAP.
  Include USERTRAP_RES.
  Parameter wp_usertrap :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ} `{!ufdG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (pt : uptd) (j : nat)
      (m : regfile) (ms_v sc_v stval_v sepc_v ksp : mword 64)
      (mie_v mdv0 menvcfg0 : mword 64) (U : ustate) (sts : list fdstate),
      wp_usertrap_body (fun h : CpuId => usertrap_res (CID := h))
        pt j m ms_v sc_v stval_v sepc_v ksp mie_v mdv0 menvcfg0 U sts.
End USERTRAP.
