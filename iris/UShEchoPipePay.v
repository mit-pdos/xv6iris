(* ===================================================================== *)
(*  UShEchoPipePay.v -- SH'S EXEC OF /echo WITH fd 1 = A PIPE'S WRITE END  *)
(*  (design claude-notes/design/app-pipe.md SS4.3g, hole H3; lane          *)
(*  PIPE-EXEC-ECHO).                                                      *)
(*                                                                       *)
(*  [UShEchoPay.sh_exec_sup_echo_wq_holds_at] is the landed discharge of   *)
(*  sh's echo supply, and its (E) half is the CONSOLE slot                 *)
(*  ([UShEchoPay.echo_slot_of_kexec_at_at], over [UEchoOut]'s entry at     *)
(*  fd 1 = [UkSh.ush_fd1p]).  The pipeline round's LEFT child execs the    *)
(*  same image with fd 1 = the pipe's write end, so it needs the same      *)
(*  supply at the OTHER slot.  This file is the second discharge, and it  *)
(*  costs no walk: the (W) half (the pin's resolution), the (L) half      *)
(*  ([echo_elf_loadable]) and the taint arm are the mould's verbatim, and *)
(*  the (E) half is the CALLER'S entry -- the tree route's                *)
(*  ([UkPipeEntries.pe_echo_image_entry_alloc]; the per-program           *)
(*  [UEchoPipe.ep_image_entry] was deleted by the pipe sweep).            *)
(*                                                                       *)
(*  THREE THINGS ARE PARAMETERS HERE THAT THE MOULD RESOLVED, because     *)
(*  this supply is not about the ERA's stage at all -- echo writes NO      *)
(*  console byte at a pipe (design SS5.2), so no [LinkRec]/[StageRec], no   *)
(*  [Wc] family and no cursor appear:                                     *)
(*                                                                       *)
(*   - [Cr], the lend, with ONE law: [box (Cr -* ep_pay pn gp L)].  The    *)
(*     round's lend is [ep_pay pn gp L * wcur gL (1/2) 0 * ...]; what      *)
(*     this file needs of it is only that echo's own payload comes out.    *)
(*     The REFUND is [Cr] WHOLE beside the ledger fragment, exactly as in  *)
(*     the mould -- a failed exec hands the lend back untouched and the    *)
(*     diagnostic's exit is paid from it.                                 *)
(*   - [Qv], the child's exit payload (constant in the status, as          *)
(*     [UkShRun.wp_kshr_fork1] forces), with two laws: what echo's own     *)
(*     exit pays it with ([ep_exit]) and what the kill pays it with        *)
(*     ([app_taint]).                                                     *)
(*   - [T], the era's taint proposition, exactly as [sh_echo_slot] takes   *)
(*     it.                                                                *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import ProcGeom.          (* [NOFILE] / [NSTD] *)
Require Import UexecRet UexecSG.
Require Import UkRun.
Require Import UserFd.
Require Import ElfUser.
Require Import FsImg.
Require Import FsEchoPin.
Require Import ExecEntry.         (* [image_entry] / [image_entry_taint] *)
Require Import UexecExecInst.
Require Import PipeNames.
Require Import PipeQueue.
Require Import PipeReg.
Require Import PipeProto.         (* [pnames] / [pipe_inv] *)
Require Import UkShEcho.
Require Import UkShPipe.        (* [ush_pipe_call] *)
Require Import UShPipeCall.     (* H1: the paid stub at a real registrar *)
Require Import EchoDisc.
Require Import UShEcho.           (* the pinned bundle's inputs *)
Require Import UShExecPin.      (* [ush_fd1pipe] / [image_entry_pay_mono], re-exported *)
Require Import UEchoPipe.         (* [ep_pay] / [ep_pay_of_alloc] *)
Require User.EchoSyms.
Local Open Scope Z_scope.
Import Defs.

(* re-exported from [UShExecPin], where they now live: consumers keep
   writing [UShEchoPipePay.ush_fd1pipe] / [UShEchoPipePay.image_entry_pay_mono] *)
Notation ush_fd1pipe := UShExecPin.ush_fd1pipe.
Notation image_entry_pay_mono := UShExecPin.image_entry_pay_mono.

Section UShEchoPipePay.
  (* [UEchoPipe.v]'s binder list (the file whose entry this applies), PLUS
     [uartGhostG] -- which [UShEcho.sh_echo_slot] carries and which
     [UexecRet.uslot] does NOT, so adding it cannot make the two entries'
     slots different terms.  [uprogSG] is deliberately NOT a section
     variable, for [UShEchoPay.v]'s reason: the supply's deposit is at the
     ambient (kernel) instance while echo's own entry runs at
     [uprogSG_free], and the two have to be nameable side by side. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!pipeProtoG Σ}.
  (* THE ERA'S CONSOLE CREDENTIAL, opaque, as [UEchoPipe.v] takes it: echo
     writes no console byte at a pipe, so whatever the fork lent crosses
     this entry untouched inside [ep_frame]. *)
  Context (Wq : iProp Σ).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* =================================================================== *)
  (*  1.  THE fd-1 ROW, AND ONE GENERIC MOVE ON THE EXEC CHANNEL          *)
  (* =================================================================== *)

  (* [ush_fd1pipe] (the fd-1 row at a pipe's write end) and
     [image_entry_pay_mono] (the entry's contravariance in its payload)
     moved to [UShExecPin] so that file need not import this one; they
     are re-exported below, after the section, under their old names. *)

  (* =================================================================== *)
  (*  2.  THE SUPPLY, AT A CALLER'S ENTRY                                 *)
  (* =================================================================== *)

  (* (lane REPOINT-PIPE; design program-specs SS3.4g.)  The pipe sweep
     deleted the form that built [UEchoPipe.ep_image_entry] here out of
     echo's lend; this one takes the entry from the caller, at every
     image the exec can produce, so the pipeline's round can hand
     over the TREE-ROUTE entry ([UkPipeEntries.pe_echo_image_entry_alloc])
     without this file naming the pipeline's instance.  It is now the
     generic supply [UShExecPin.sh_exec_sup_x_of_entry]'s instance at the
     pipe row [ush_fd1pipe γp] (lane user-once C3). *)
  Lemma sh_exec_sup_echo_pipe_of_entry
      (ws : list (list (bv 8))) (Qv Cr T : iProp Σ) (γp : pipe_names)
      `{!Persistent T} `{!Timeless T} :
    EchoDisc.line_ok ws ->
    □ (∀ (M : gmap Z (bv 8)) (s0 t : Z) (g : nat -> bv 8)
         (sts : list fdstate) (cs : gset gname) (pidv : mword 32)
         (rb : bool),
         ⌜echo_node_img ws M s0 t g⌝ -∗
         ⌜UkShEcho.echo_argv_bytes ws g⌝ -∗
         ⌜length sts = NOFILE⌝ -∗
         ⌜take NSTD sts !! 1%nat = Some (FdOpen rb true (FdPipe γp))⌝ -∗
         UkRun.urun_nopipe sts -∗
         image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64)
           sts FsImg.ROOTINO ProcDefs.secc_all cs pidv (fun _ : Z => Qv) Cr uslot) -∗
    □ (app_taint -∗ Qv) -∗
    UShEcho.sh_echo_slot T -∗
    UkShEcho.sh_exec_sup_echo_at (ush_fd1pipe γp) ws (fun _ : Z => Qv) Cr.
  Proof using ghost_varG0 ghost_varG1 ufdG0.
    intros Hokws. iIntros "#Hent #Hkt #Hslot".
    assert (Hhead : ws !!! 0%nat = echo_pl).
    { rewrite (list_lookup_total_correct ws 0%nat _ (EchoDisc.line_ok_head ws Hokws)).
      vm_compute. reflexivity. }
    iApply (UShExecPin.sh_exec_sup_x_of_entry (ush_fd1pipe γp) ws echo_pl
              FsEchoPin.era0_echo_pins [FsImg.ROOTINO; FsEchoPin.ECHO_INO] FsEchoPin.ECHO_INO
              ElfUser.echo_elf T Qv Cr (ExecWords.line_ok_exec_ok ws Hokws) Hhead echo_elf_loadable
              sh_echo_pin_resolves with "[] Hkt [Hslot]").
    - iIntros "!>" (M s0 t g sts cs pidv) "%Himg %Hb %Hlen %Hfd Hnp".
      destruct Hfd as [rb Hfd].
      iApply ("Hent" $! M s0 t g sts cs pidv rb with "[%] [%] [%] [%] Hnp"); done.
    - iApply (UShExecPin.sh_pin_slot_echo with "Hslot").
  Qed.

  (* =================================================================== *)
  (*  3.  H1'S INSTANCE: THE PAID pipe(2) STUB AT ECHO'S OWN REGISTRAR    *)
  (*                                                                      *)
  (*  [UShPipeCall.ush_pipe_call_paid] is generic in the registrar.  This  *)
  (*  is the instance design SS4.3g names -- [UEchoPipe.ep_pay_of_alloc],  *)
  (*  which is [PipeProto.pipe_proto_alloc]'s quintuple read echo-side:    *)
  (*  the registration goes to the registry, the WRITE half of the         *)
  (*  protocol (the handle, the left side token, the era's credential and  *)
  (*  the write permit at zero) becomes echo's [ep_pay], and the reader's  *)
  (*  permit and right side token come back to sh for cat and for the      *)
  (*  round's two waits.                                                   *)
  (*                                                                      *)
  (*  WHAT [Wq] IS AND WHO SUPPLIES IT.  [Wq] is the ERA'S CONSOLE         *)
  (*  CREDENTIAL, opaque here and in [UEchoPipe.v]: at the pipeline round  *)
  (*  it is what sh's fork lent the LEFT child ([UkShFork.ushf_wq]'s left  *)
  (*  arm).  echo at a pipe writes NO console byte, so the credential is   *)
  (*  not spent -- it rides [ep_frame] across the entry and comes back out *)
  (*  of [ep_exit] ([UEchoPipe.ep_exit_payL] hands it back beside          *)
  (*  [side_L]).  The runcmd child is what supplies it HERE, out of its    *)
  (*  own lend, at the instant of [pipe(2)]: it is the one linear resource *)
  (*  the registrar consumes.                                              *)
  (* =================================================================== *)
  Definition ep_reg_pay (L : list (bv 8)) (γp : pipe_names) : iProp Σ :=
    (∃ pn : pnames, rtok pn ∗ side_R pn ∗ ep_pay Wq pn γp L)%I.

  Lemma ep_registrar_of_wq (L : list (bv 8)) :
    Wq -∗
    ∀ γp : pipe_names,
      pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗ pipe_reg γp ∗ ep_reg_pay L γp.
  Proof using Wq.
    iIntros "HWq" (γp) "Hfrag".
    iMod (ep_pay_of_alloc Wq γp L with "Hfrag HWq")
      as (pn) "(#Hreg & Hr & HR & Hpay)".
    iModIntro. iFrame "Hreg". iExists pn. iFrame "Hr HR Hpay".
  Qed.

  Lemma ush_pipe_call_echo_pay `{PSx : uprogSG Σ}
      (Hfree : forall k : Z, free_num k -> psok k)
      (N : uk_names Σ) `{!ukn_const N}
      (l : list fdstate) (L : list (bv 8)) :
    fd_lowest_closed l = None ->
    Wq -∗ udepw_law (PS := PSx) 21 -∗
    UkShPipe.ush_pipe_call (SG := uexecSG_xv6) (PS := PSx) N l
      (ep_reg_pay L).
  Proof using Wq ghost_varG0 ghost_varG1 ufdG0.
    intros Hnone. iIntros "HWq Hcl".
    iApply (UShPipeCall.ush_pipe_call_paid (PS := PSx) Hfree N l
              (ep_reg_pay L) Hnone with "[HWq] Hcl").
    iApply (ep_registrar_of_wq L with "HWq").
  Qed.

End UShEchoPipePay.
