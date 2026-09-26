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
(* independent one; the persistent premise [sync_pay P (Q (-1))] is what *)
(* /sync spends AFTER [sync()] returned ([UkSync.wp_ksync_main]).  The   *)
(* union's round lends the round's credential and pays PEND at RAN        *)
(* ([UShURound.uHchild_sync]); SY3 adds the kernel's durability receipt   *)
(* to [sync_pay].  The program reads neither its argv nor its table, so   *)
(* the entry takes no row about either.                                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import ProcGeom ProcDefs.
Require Import UsysMemOk UserPerm UexecSlot UexecRet UexecSG UexecWp.
Require Import UserHeap UkRun.
Require Import UserFd UserCwd UserChildren.
Require Import ChildTok.
Require Import ElfFile ElfUser.
Require Import UmodeArith UmodeAbi.
Require Import SpecKexec.
Require Import ExecEntry.
Require Import UexecExecInst.         (* THE INSTANCES: [uexecSG_xv6], [xfam_at] *)
Require Import UkAbi.
Require Import UShKernel.
Require Import UEchoKernel.           (* [uvis_sp] / [uvis_argc] *)
Require Import LineWords EchoDisc ExecWords.
Require Import UkShEcho.
Require Import UShEcho.
Require Import UCodeSync.
Require Import UkRunSys UkSync.
Require Import UShSync.
Require Import CtxIdDefs.
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
  (*  THE ENTRY                                                           *)
  (* ------------------------------------------------------------------- *)
  Lemma sync_image_entry (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (P : iProp Σ) :
    (forall k : Z, free_num k -> psok k) ->
    (forall x y : Z, Q x = Q y) ->
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    □ sync_pay P (Q (-1)) -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.sync_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw ProcDefs.secc_all cs pidv Q P uslot.
  Proof using GEN PS fileG0 ghost_varG0 ghost_varG1 riscvGS0 ufdG0 xv6G0 Σ.
    intros Hps HQc Hok Himg Hbytes Hfdl.
    iIntros "#Hpay #Hnpw #Hdep".
    iApply image_entry_of_at. iIntros "!>" (na alen afun) "%Hargs".
    destruct (UShEcho.echo_args_det_x_holds ws Hok Mn sv t gn na alen afun
                Himg Hbytes Hargs) as (Hna & Halen & Hafun).
    pose proof (UShSync.sync_room_of_det_x ws na alen Hok Hna Halen) as Hroom.
    rewrite /image_entry_at.
    iIntros "!>" (W') "%Hokk %Hcwv %Hlzf %Hscf _ _ Hmp HP".
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
       its ledger, its working directory, its children and its pid are
       dropped here *)
    iIntros (N h) "%Hpayeq %Hsz Hszf #Ht _ _ _ _ Hrun".
    pose proof (UkRun.ukn_const_of_eq N Q Hpayeq HQc) as Hc.
    rewrite Hpc.
    iApply (wp_ksync_start N Hps h (tf_resume_gpr0 (uvis_tf W')) _ 38 P
              eq_refl with "[] HP [] Hrun").
    - iApply (sync_code_of_text (ukn_t N) (uvis_M W') (uvis_perm W') Hsub Hx
                with "Ht").
    - rewrite Hpayeq. iExact "Hpay".
  Qed.

End UkSyncEntry.
