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
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import ProcGeom.          (* [NOFILE] / [NSTD] *)
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun.
Require Import UserFd.
Require Import ChildTok.
Require Import ElfFile ElfUser.
Require Import PageGeom.
Require Import UmodeAbi.
Require Import FsImg.
Require Import FsEchoPin.
Require Import SpecKexec.
Require Import ExecEntry.         (* [image_entry] / [image_entry_taint] *)
Require Import FsAbsDefs.         (* [anode] / [MkAnode] / [AFile] *)
Require Import ExecRun.           (* the U-TIER EXEC RULE *)
Require Import UShKernel.
Require Import KexecDefs.
Require Import UexecExecInst.
Require Import PipeNames.
Require Import PipeQueue.
Require Import PipeReg.
Require Import PipeProto.         (* [pnames] / [pipe_inv] *)
Require Import UCodeEcho.
Require Import UkSh UkShFork UkShEcho.
Require Import UkShPipe.        (* [ush_pipe_call] *)
Require Import UShPipeCall.     (* H1: the paid stub at a real registrar *)
Require Import LineWords.
Require Import EchoDisc.
Require Import UEchoOut.
Require Import UShEcho.           (* the pinned bundle's inputs *)
Require Import UShEchoOut.
Require Import UEchoPipe.         (* [ep_pay] / [ep_pay_of_alloc] *)
Require User.EchoSyms.
Local Open Scope Z_scope.
Import Defs.

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

  (* [UkSh.ush_fd1p] one descriptor kind over: the child's fd 1 is the
     WRITE end of THIS pipe.  [UkShEcho.sh_exec_sup_echo_at] takes the row
     as a parameter (lane SH-CHILD-2 made it one for the redirect child's
     file row), so no landed definition moves. *)
  Definition ush_fd1pipe (γp : pipe_names) (l : list fdstate) : Prop :=
    exists rb : bool, l !! 1%nat = Some (FdOpen rb true (FdPipe γp)).

  (* the exec channel's entry is CONTRAVARIANT in its linear payload, and
     that is the whole of the seam between the round's lend and echo's own *)
  Lemma image_entry_pay_mono (f : elf_bytes) (M : gmap Z (bv 8))
      (av : mword 64) (sts : list fdstate) (cw : Z) (secc : mword 64) (cs : gset gname)
      (pidv : mword 32) (Q : Z -> iProp Σ) (P P' : iProp Σ)
      (X : uvis -d> iPropO Σ) :
    □ (P' -∗ P) -∗
    image_entry f M av sts cw secc cs pidv Q P X -∗
    image_entry f M av sts cw secc cs pidv Q P' X.
  Proof using .
    iIntros "#Hw #He". rewrite /image_entry.
    iIntros "!>" (na alen afun W') "%Hok %Hcw %Hlz %Hscw %Hch %Hpid %Hargs Hp HP".
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] [%] Hp [HP]");
      [ exact Hok | exact Hcw | exact Hlz | exact Hscw | exact Hch | exact Hpid
      | exact Hargs | ].
    iApply ("Hw" with "HP").
  Qed.

  (* =================================================================== *)
  (*  2.  THE SUPPLY, AT A CALLER'S ENTRY                                 *)
  (* =================================================================== *)

  (* (lane REPOINT-PIPE; design program-specs SS3.4g.)  The pipe sweep
     deleted the form that built [UEchoPipe.ep_image_entry] here out of
     echo's lend; this one takes the entry from the caller, at every
     image the exec can produce, so the pipeline's round can hand
     over the TREE-ROUTE entry ([UkPipeEntries.pe_echo_image_entry_alloc])
     without this file naming the pipeline's instance.  The caller's entry
     is at the round's WHOLE lend [Cr]; the ledger fragment is spent at
     the exec.  No [udep] and no exit wand: only the deleted entry read
     them. *)
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
    intros Hokws.
    iIntros "#Hent #Hkt (#Hinv & #Hcl & #Hgen)".
    rewrite /UkShEcho.sh_exec_sup_echo_at.
    iIntros "!>" (N' m pc s0 t g ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd1 Hstd #Hcmd Hcr".
    destruct Hfd1 as [rb Hl1].
    iAssert (image_entry_taint T (fun _ : Z => Qv) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "HT Hmp".
      iApply ("Hgen" $! Qv W' with "HT Hmp []"). iExact "Hkt". }
    iApply (udepw_at_refR_of_sup N' m pc
              (mword_of_int s0) (mword_of_int (t + 8))
              FsImg.ROOTINO T echo_pl ElfUser.echo_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I
              _ echo_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr]").
    { iIntros "!> $". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜ echo_node_img ws M s0 t g ⌝)%I as %Himg.
    { iApply (echo_node_img_of_cmd ws _ _ _ M pm sz s0 t g Hokws
                with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hlen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    assert (Hl1' : take NSTD fdv !! 1%nat
                   = Some (FdOpen rb true (FdPipe γp)))
      by (rewrite Hl; exact Hl1).
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr".
    { iPureIntro.
      exact (sh_echo_path_of_holds ws Hokws M s0 t g Himg Hbytes). }
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin FsEchoPin.era0_echo_pins T FsImg.ROOTINO
                echo_pl [FsImg.ROOTINO; FsEchoPin.ECHO_INO]
                FsEchoPin.ECHO_INO
                (MkAnode (AFile ElfUser.echo_elf) 1%nat) sh_echo_pin_resolves
                with "Hcl Hinv"). }
    iSplitR "Hstd Hcr".
    { rewrite Hpeq.
      iPoseProof ("Hent" $! M s0 t g fdv cs pidv rb
                    with "[%] [%] [%] [%] Hnp0") as "#He";
        [ exact Himg | exact Hbytes | exact Hlen | exact Hl1' | ].
      iApply (image_entry_pay_mono ElfUser.echo_elf M
                (mword_of_int (t + 8) : mword 64) fdv FsImg.ROOTINO ProcDefs.secc_all cs pidv
                (fun _ : Z => Qv) Cr
                (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I uslot with "[] He").
      iIntros "!> [_ Hc]". iExact "Hc". }
    iFrame "Hstd Hcr".
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
