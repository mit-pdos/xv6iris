(* ===================================================================== *)
(* UkSyncEntry.v -- sync's ENTRY THEOREM, [sync_image_entry]              *)
(* (claude-notes/design/sync.md section 3).                               *)
(*                                                                        *)
(* The mould is [UkSeccEntry.secc_image_entry]: [image_entry_of_at] ->    *)
(* the node sh built reads the argv ([UShEcho.echo_args_det_x_holds]) ->  *)
(* the room ([UShSync.sync_room_of_det_x]) -> the key's geometry          *)
(* ([UShSync.sync_kexec_pages] / [sync_kexec_entry_rows]) -> the slot's   *)
(* constructor ([UkRun.uslot_of_urun]) -> the program                     *)
(* ([UkSync.wp_ksync_start]).                                             *)
(*                                                                        *)
(* WHAT THE ENTRY IS HANDED.  [Pay] is ANY resource [P] the exec'ing      *)
(* process lends the program, and the exit payload [Q] is a status-      *)
(* independent one; the persistent premise [sync_pay P (Q_opt None)      *)
(* (Q (-1))] is what /sync spends AFTER [sync()] returned                 *)
(* ([UkSync.wp_ksync_main]), its second premise the kernel's receipt.    *)
(* The union's round lends the round's credential and pays PEND at RAN    *)
(* ([UShURound.uHchild_sync]).  The program reads neither its argv nor    *)
(* its table, so the entry takes no row about either.                     *)
(*                                                                        *)
(* THE ECALL LEAF AT THIS INSTANCE ([ksync_leaf_xv6], sync K4): 22's rows *)
(* are the optional hook and its receipt, readable here and nowhere       *)
(* below, so this is where [UkSync.ksync_leaf] is discharged -- at EVERY  *)
(* hook, through the receipt-keeping quiet leaf.  THE HOOK RIDES THE LEND *)
(* (sync SY3-A4): [image_entry] is a [□], so the linear hook reaches the  *)
(* program inside [Pay := P ∗ hook_opt gen_id oQ], and the receipt       *)
(* [Q_opt oQ] is what [sync_pay] is handed.                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import ProcGeom ProcDefs.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun.
Require Import UserFd.
Require Import ElfUser.
Require Import SpecKexec.
Require Import ExecEntry.
Require Import UexecExecInst.         (* THE INSTANCES: [uexecSG_xv6], [xfam_at] *)
Require Import UEchoKernel.           (* [uvis_sp] / [uvis_argc] *)
Require Import ExecWords.
Require Import UkShEcho.
Require Import UShEcho.
Require Import UCodeSync.
Require Import UkRunSys UkSync.
Require Import UShSync.
Require Import CtxIdDefs.
Require Import SyncHook.              (* [hook_opt] / [Q_opt]: row 22 *)
Require User.SyncSyms.
Local Open Scope Z_scope.
Import Defs.

Section UkSyncEntry.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{PS : UexecSG.uprogSG Σ}.

  (* ------------------------------------------------------------------- *)
  (*  THE ECALL LEAF, AT EVERY HOOK                                       *)
  (*                                                                     *)
  (*  22 passes every number guard of the receipt-keeping quiet leaf     *)
  (*  ([UkRunSys.wp_uk_ecall_quiet_recv]); the deposit is the point      *)
  (*  family at the record's payload WITH the hook ([xfam_sy]), supplied  *)
  (*  at the cwd the fragment names ([UkRun.udepwf_at]) out of the hook   *)
  (*  alone ([sbundle_at_sync_intro]), and the receipt is read back off   *)
  (*  the post ([spost_at_sync_elim]) -- the mould is                     *)
  (*  [UInitConsK.init_cons_sup_mknod].  At [None] it is                  *)
  (*  [UkSync.ksync_leaf_none]'s leaf, at this instance.                  *)
  (* ------------------------------------------------------------------- *)
  Lemma ksync_leaf_xv6 (N : uk_names Σ) (oQ : option (iProp Σ)) :
    ⊢ ksync_leaf N oQ.
  Proof using .
    iIntros (h m avail c Hn) "#Hcode Hrun Hcwd Hhook Hcont".
    iApply (wp_uk_ecall_quiet_recv (SG := uexecSG_xv6) N h m (mword_of_int 0x36a) 22 avail
              (xfam_sy oQ (xfam_at (ukn_pay N) xfam_pt)) c Hn
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(lia) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hcwd [Hhook]").
    { iApply (uis_sync_36a with "Hcode"). }
    { rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
      iIntros (M pm sz fdv gn cs pidv) "_ Hheap Hufd".
      iFrame "Hheap Hufd".
      iApply (sbundle_at_sync_intro uslot).
      cbn [sy_oQ xfam_sy]. iExact "Hhook". }
    assert (E36a : add_vec_int (mword_of_int 0x36a : mword 64) 4
                   = mword_of_int 0x36e)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E36a.
    iIntros (h' r W cs') "_ _ _ _ Hpost Hcwd Hrun".
    iDestruct (spost_at_sync_elim uslot _ W with "Hpost") as "HQ".
    iEval (cbn [sy_oQ xfam_sy]) in "HQ".
    iApply ("Hcont" $! h' r with "HQ Hcwd Hrun").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE ENTRY                                                           *)
  (* ------------------------------------------------------------------- *)
  Lemma sync_image_entry (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (P : iProp Σ) (oQ : option (iProp Σ)) :
    (forall x y : Z, Q x = Q y) ->
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    □ sync_pay P (Q_opt oQ) (Q (-1)) -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.sync_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw ProcDefs.secc_all cs pidv Q (P ∗ hook_opt gen_id oQ) uslot.
  Proof using ghost_varG0 ghost_varG1 ufdG0.
    intros HQc Hok Himg Hbytes Hfdl.
    iIntros "#Hpay #Hnpw #Hdep".
    iApply image_entry_of_at. iIntros "!>" (na alen afun) "%Hargs".
    destruct (UShEcho.echo_args_det_x_holds ws Hok Mn sv t gn na alen afun
                Himg Hbytes Hargs) as (Hna & Halen & Hafun).
    pose proof (UShSync.sync_room_of_det_x ws na alen Hok Hna Halen) as Hroom.
    rewrite /image_entry_at.
    iIntros "!>" (W') "%Hokk %Hcwv %Hlzf %Hscf _ _ Hmp [HP Hhook]".
    destruct (UShSync.sync_kexec_pages na alen afun sts W' Hokk)
      as (Hpc & Hsub & Hsub2 & Hx & Hdw & Hwr & Hrp).
    destruct (UShSync.sync_kexec_entry_rows na alen afun sts W' Hokk Hroom
                Hfdl Hwr Hrp)
      as (Hroom336 & Hal8 & Hszv & Hstkrow & Hargsrow & Havd & Havs
          & Hfdlen & Hstop).
    pose proof (kexec_image_ok_fd _ na alen afun sts W' Hokk) as Hfd.
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite Hfd; iExact "Hnpw" | ].
    iApply (uslot_of_urun W' 42 Q Hal8
              ltac:(unfold uvis_sp in Hroom336; lia) Hstkrow Hfdlen Hstop Hlzf Hscf
              with "Hdep Hnpw' Hmp").
    (* sync makes no descriptor call, no chdir, no fork and no getpid, so
       its ledger, its children and its pid are dropped here; its working
       directory's fragment goes to the ecall leaf, whose supplier is fixed
       at it *)
    iIntros (N h) "%Hpayeq %Hsz Hszf #Ht _ Hcwf _ _ Hrun".
    pose proof (UkRun.ukn_const_of_eq N Q Hpayeq HQc) as Hc.
    rewrite Hpc.
    iApply (wp_ksync_start N oQ h (tf_resume_gpr0 (uvis_tf W')) _ 38 P
              (uvis_cwd W') eq_refl with "[] [] Hhook Hcwf HP [] Hrun").
    - iApply (sync_code_of_text (ukn_t N) (uvis_M W') (uvis_perm W') Hsub Hx
                with "Ht").
    - iApply (ksync_leaf_xv6 N oQ).
    - rewrite Hpayeq. iExact "Hpay".
  Qed.

End UkSyncEntry.
