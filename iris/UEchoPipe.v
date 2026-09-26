(* ===================================================================== *)
(*  UEchoPipe.v -- ECHO AT fd 1 = A PIPE WRITE END: THE PAYLOAD VOCABULARY *)
(*  (design/app-pipe.md SS5.2; lanes ECHO-PIPE and ECHO-PIPE-2.)          *)
(*                                                                       *)
(*  The cursor ([ep_cur]), the halt ([ep_stuck] / [ep_halt]: a mid-line   *)
(*  cursor WITH the read end's shot, or the taint), the frame that        *)
(*  crosses the entry untouched ([ep_frame]: the side token and the era's *)
(*  console credential [Wq] -- echo writes no console byte at a pipe),    *)
(*  the exit payload ([ep_exit]) and the lend ([ep_pay]), with the lend's *)
(*  anti-vacuity mint at [pipe(2)] ([ep_pay_of_alloc]) and what sh reads  *)
(*  off the exit ([ep_exit_payL], [PipeProto.pipe_payL]'s three arms).    *)
(*                                                                       *)
(*  echo's ENTRY at a pipe is the tree route's                            *)
(*  ([UkPipeEntries.pe_echo_image_entry]); the per-program walk that used *)
(*  to pay it here ([ep_image_entry] over [UkEcho]'s walk) was deleted by *)
(*  the pipe sweep once REPOINT-PIPE left it without consumers.           *)
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
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserPerm.
Require Import UserPtTree.
Require Import UmodeArith.
Require Import ProcGeom.
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require Import ExecEntry.               (* [image_entry] -- the exec channel *)
Require Import SpecKexec.               (* [kexec_image_ok] *)
Require Import UkRun UkRunSys.
Require Import UexecExecInst.           (* THE INSTANCES: [uexecSG_xv6] etc. *)
Require Import SpecSysRead.             (* [sys_rw_count] *)
Require Import PipeQueue.               (* [pipe_wpay], [pipe_wpost], ... *)
Require Import PipeReg.                 (* [pipe_reg] *)
Require Import PipeProto.               (* THE PROTOCOL *)
Require Import UkWriteLeaf.
Require Import UkReadRows.              (* [std_fd_st_of_key] *)
Require Import UkWritePipe.             (* the ledger-slot pipe deposit *)
Require Import UkAbi.
Require Import UserHeap.
Require Import UCodeEcho.
Require Import UkEcho.
Require Import UEchoKernel.
Require Import LineWords.
Require Import EchoDisc.
Require Import UEchoOut.                (* THE MOULD: [out_argv_at] etc. *)
Require Import ElfUser.                 (* [echo_elf] *)
Require Import UkShEcho.                (* [echo_argv_bytes] *)
Require Import UShEcho.                 (* [echo_node_img], the room bound *)
Require Import UShEchoOut.              (* [echo_out_argv_of_image] *)
Require Import CtxIdDefs.
Require User.EchoSyms.
Local Open Scope Z_scope.
Import Defs.

Section UEchoPipe.
  (* [UEchoOut.v]'s binder list MINUS the link/stage record (echo prints no
     console byte at a pipe) PLUS the protocol's ghosts.  NO [uexecSG]
     section variable, for [UEchoOut]'s reason: this file reads row 16's
     CONCRETE arm, so the instance must be the ambient xv6 one. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!pipeProtoG Σ}.
  Context `{PS : uprogSG Σ}.

  (* THE ERA'S CONSOLE CREDENTIAL, OPAQUE -- [UEchoFile]'s [Wq].  echo
     writes no console byte at a pipe, so whatever the fork lent (the
     block credential) crosses this entry untouched. *)
  Context (Wq : iProp Σ).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  S1  THE CURSOR, THE HALT, AND THE PROTOCOL'S MISSING ARM            *)
  (* =================================================================== *)

  (* WHERE ECHO IS: the write permit at [c] and the history's lower bound
     at the line's first [c] bytes.  It IS [PipeProto.pipe_wQ pn L c 0]
     read at an absolute cursor, which is what makes the four writes
     compose ([pipe_wQ pn L c k = ep_cur pn L (c + k)], definitionally). *)
  Definition ep_cur (pn : pnames) (L : list (bv 8)) (c : nat) : iProp Σ :=
    (wcur pn c ∗ pws_lb pn (take c L))%I.

  (* THE HALT: the line and the pipe have diverged (a write stopped short
     because the writer was killed or the read end was shut), or the
     application is tainted.  Nothing about the pipe's contents is claimed
     -- which is exactly design SS4.2's [PExecR] world, where the console
     shows the right child's diagnostic and the pipe is irrelevant. *)
  (* ...AND IT CARRIES (P4)'S SHOT (lane PIPE-PROTO-2): the only way a
     write stops short without the taint is the READ END SHUT, and the
     writer's own observation node records that as [ro_shot pn].  The shot
     is what makes the halt SELF-FUNDING -- every later write is paid from
     it by [PipeProto.pipe_wpay_of_inv_after_short] -- and it is what makes
     the halt READABLE by sh, since it is [pipe_payL]'s third arm. *)
  Definition ep_stuck (pn : pnames) (L : list (bv 8)) : iProp Σ :=
    (∃ c : nat, ⌜(c <= length L)%nat⌝ ∗ ep_cur pn L c ∗ ro_shot pn)%I.

  Definition ep_halt (pn : pnames) (L : list (bv 8)) : iProp Σ :=
    (ep_stuck pn L ∨ app_taint)%I.

  (* WHAT HOLDS BETWEEN TWO OF ECHO'S WRITES. *)
  Definition ep_ok (pn : pnames) (L : list (bv 8)) (c : nat) : iProp Σ :=
    (ep_cur pn L c ∨ ep_halt pn L)%I.

  (* WHAT CROSSES THE ENTRY UNTOUCHED: the side token the runcmd child lent
     its LEFT child (design SS4.2, as amended) and the era's console
     credential. *)
  Definition ep_frame (pn : pnames) : iProp Σ := (side_L pn ∗ Wq)%I.

  Definition ep_car (pn : pnames) (L : list (bv 8)) (c : nat) : iProp Σ :=
    (ep_frame pn ∗ ep_ok pn L c)%I.

  (* THE EXIT PAYLOAD: the frame back, and the cursor at the line's end --
     or the halt. *)
  Definition ep_exit (pn : pnames) (L : list (bv 8)) : iProp Σ :=
    ep_car pn L (length L).

  (* THE LEND [ExecEntry.image_entry]'s [Pay] slot carries: the protocol's
     handle, the frame, and the write permit at ZERO with
     the empty lower bound -- design SS5.2's [Pay] exactly. *)
  Definition ep_pay (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      : iProp Σ :=
    (pipe_inv pn γp L ∗ ep_frame pn ∗ wcur pn 0%nat ∗ pws_lb pn [])%I.

  (* ...AND THE ANTI-VACUITY EXHIBIT: echo's WHOLE lend is minted at
     [pipe(2)] itself ([PipeProto.pipe_proto_alloc], which is
     [UkReadPipe.wp_uk_pipe_read_end]'s registrar premise), with nothing
     owed and nothing left dangling -- the rest of the quintuple (the
     registration, the reader's permit and the right side token) goes to
     the registry, cat and sh.  Since lane PIPE-PROTO-2 this is an
     UNCONDITIONAL fupd: ECHO-PIPE's version concluded at
     [ep_derail -* ep_pay], and that wand is gone. *)
  Lemma ep_pay_of_alloc (γp : pipe_names) (L : list (bv 8)) :
    pipe_qfrag (pn_queue γp) pst0 -∗ Wq ={⊤}=∗
    ∃ pn : pnames,
      pipe_reg γp ∗ rtok pn ∗ side_R pn ∗ ep_pay pn γp L.
  Proof using .
    iIntros "Hfrag HWq".
    iMod (pipe_proto_alloc γp L with "Hfrag")
      as (pn) "(#Hinv & Hw & Hr & HL & HR & #Hreg)".
    rewrite /wtok.
    iMod (pws_lb_of_inv pn γp L 0%nat with "Hinv Hw") as "[Hw #Hlb]".
    iModIntro. iExists pn. iFrame "Hreg Hr HR".
    rewrite /ep_pay /ep_frame.
    iFrame "Hinv HL HWq Hw". rewrite take_0. iExact "Hlb".
  Qed.

  (* ...AND WHAT SH CAN READ OFF THE EXIT.  The good arm is
     [PipeProto.pipe_payL]'s left one -- "the line is in".  The HALT is NOT
     [pipe_payL]'s right arm unless the cursor never moved: [pipe_payL] has
     [pws_lb pn L \/ wtok pn], the two ENDS of the range, and a write that
     stopped in the middle is neither.  That is the lane's second finding. *)
  Lemma ep_exit_payL (pn : pnames) (L : list (bv 8)) :
    ep_exit pn L -∗ side_L pn ∗ Wq ∗ (pipe_payL pn L ∨ app_taint).
  Proof using .
    rewrite /ep_exit /ep_car /ep_frame /ep_ok /ep_cur /ep_halt /ep_stuck
            /pipe_payL.
    iIntros "[[$ $] [[Hw Hlb] | [H | #Ht]]]".
    - rewrite take_ge; [ | lia ]. iLeft. by iLeft.
    - iDestruct "H" as (c) "(_ & [Hw _] & #Hsh)".
      iLeft. iRight. iRight. iExists c. iFrame "Hw Hsh".
    - iRight. iExact "Ht".
  Qed.

End UEchoPipe.
