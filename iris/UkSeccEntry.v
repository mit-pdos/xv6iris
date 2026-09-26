(* ===================================================================== *)
(* UkSeccEntry.v -- seccomp's ENTRY THEOREM, [secc_image_entry].          *)
(*                                                                        *)
(* Design: claude-notes/design/seccomp.md SS7 and the S3 rulings.  The     *)
(* mould is [UkTreeEntry.grep_image_entry_env_c]: [image_entry_of_at] ->  *)
(* the node sh built reads the argv ([UShEcho.echo_args_det_x_holds]) ->  *)
(* the room ([UShSecc.secc_room_of_det_x]) -> the key's geometry           *)
(* ([UShSecc.secc_kexec_pages] / [secc_kexec_entry_rows]) -> the slot's   *)
(* constructor at the WHOLE TABLE'S VIEW ([UkRun.uslot_of_urun_ro_at]) ->  *)
(* the program ([UkSeccMain.wp_ksecc_start]).                              *)
(*                                                                        *)
(* WHAT THE ENTRY IS HANDED.  [Pay] is the ERA CREDENTIAL and the table's  *)
(* universe rows, [riscv_wild (S gen_id) ∗ secc_rows sts]; the persistent  *)
(* context is the generic user WP [uexec_wp] (what [useccomp_mint] needs   *)
(* beside the credential) and the two rows every entry takes ([udep],      *)
(* [urun_nopipe]).  The credential pays both halves of the program:       *)
(*   - its fd-2 diagnostics, through [UexecSecc.secc_cons_pay] at the      *)
(*     console row the entry's [sts] carries at 2 ([secc_wdep_of_pay]);    *)
(*   - the child after row 23, through [UexecSecc.useccomp_mint] at the    *)
(*     masked key, whose table the child's ledger view bounds and whose    *)
(*     rows are [sts]'s ([secc_univ_of_mint]).                             *)
(* The exit payload [Q] is any payload that is free ([forall s, ⊢ Q s]):  *)
(* seccomp's parent owes its own parent nothing it could produce.         *)
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
Require Import ConsoleInv.            (* [CONSOLE] *)
Require Import UCodeSeccomp.
Require Import UkRunSys UkSeccMain.
Require Import UShSecc.
Require Import UexecSecc.
Require Import CtxIdDefs.
Require User.SeccompSyms.
Local Open Scope Z_scope.
Import Defs.

(* THE TABLE VIEW BOUNDS THE ROWS: a slot the view shows open may have been
   closed, and a closed row is in the universe *)
Section UkSeccRows.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId}.

  Lemma secc_rows_tab_le (fdv v : list fdstate) :
    tab_le fdv v -> secc_rows v -∗ secc_rows fdv.
  Proof using .
    intros [_ H]. iIntros "#Hr". rewrite /secc_rows.
    iApply big_sepL_intro. iIntros "!>" (k st Hk).
    destruct (H k st Hk) as [Hv | [-> _]].
    - iApply (big_sepL_lookup with "Hr"). exact Hv.
    - rewrite /secc_row. done.
  Qed.
End UkSeccRows.

Section UkSeccEntry.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.

  (* THE WRITE DEPOSIT, out of the credential: fd 2 of the ledger is a
     writable console, and the universe's console payer answers any write
     there at the trivial families *)
  Lemma secc_wdep_of_pay (N : uk_names Σ) (l : list fdstate) (rb2 : bool) :
    l !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    secc_cons_pay -∗ secc_wdep N l.
  Proof using .
    intros Hl2. iIntros "#Hc". rewrite /secc_wdep.
    iIntros "!>" (m pc) "%Hfd".
    iExists (xfam_at (ukn_pay N) xfam_pt). rewrite /udepwf_K.
    iSplitR; [ done | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htk _ Hh Hf". iFrame "Hh Hf".
    rewrite /sbundle_at /= /xv6_sbundle.
    destruct (decide (16 = USYS_exec)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (16 = 5)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (16 = 9)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (16 = 15)) as [He | _]; [ exfalso; discriminate He | ].
    destruct (decide (16 = 16)) as [_ | He]; [ | exfalso; exact (He eq_refl) ].
    rewrite /xfam_at /xfam_pt /xfam_exec /xfam_exec_at /=.
    iApply (secc_filewrite_in with "Hc").
    assert (Hst : fd_st_of_key (xk_a (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) 0)
                    (uvis_fd (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all))
                  = FdOpen rb2 true (FdDevice CONSOLE)).
    { cbn [uvis_fd uvis_of_run]. unfold fd_st_of_key.
      change (xk_a (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all) 0)
        with (m !!! Regidx (mword_of_int 10 : mword 5)).
      cbv zeta. rewrite Hfd.
      case_decide as Hdec; [ | exfalso; apply Hdec; unfold NOFILE; lia ].
      change (Z.to_nat 2) with 2%nat.
      rewrite <- (lookup_take fdv NSTD 2%nat ltac:(unfold NSTD; lia)).
      rewrite Htk Hl2. reflexivity. }
    rewrite Hst. rewrite /secc_row. done.
  Qed.

  (* THE UNIVERSE AT THE KEY'S TABLE, out of the minter *)
  Lemma secc_univ_of_mint (sts : list fdstate) :
    riscv_wild (S gen_id) -∗ □ uexec_wp -∗ secc_rows sts -∗ secc_univ sts.
  Proof using .
    iIntros "#Hw #Hwp #Hr".
    iDestruct (useccomp_mint with "Hw Hwp") as "#Hmint".
    rewrite /secc_univ. iIntros "!>" (W) "%Hm %Hle Hp".
    iApply ("Hmint" with "[] Hp"). iModIntro.
    rewrite /secc_key. iSplit; [ by iPureIntro | ].
    iApply (secc_rows_tab_le _ _ Hle with "Hr").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  THE ENTRY                                                           *)
  (* ------------------------------------------------------------------- *)
  Lemma secc_image_entry (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (rb2 : bool) :
    (forall k : Z, free_num k -> psok k) ->
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    (forall s : Z, ⊢ Q s) ->
    □ uexec_wp -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.seccomp_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw ProcDefs.secc_all cs pidv Q
      (riscv_wild (S gen_id) ∗ secc_rows sts) uslot.
  Proof using GEN PS fileG0 ghost_varG0 ghost_varG1 riscvGS0 ufdG0 xv6G0 Σ.
    intros Hps Hok Himg Hbytes Hfdl Hcons HQ.
    iIntros "#Hwp #Hnpw #Hdep".
    iApply image_entry_of_at. iIntros "!>" (na alen afun) "%Hargs".
    destruct (UShEcho.echo_args_det_x_holds ws Hok Mn sv t gn na alen afun
                Himg Hbytes Hargs) as (Hna & Halen & Hafun).
    pose proof (UShSecc.secc_room_of_det_x ws na alen Hok Hna Halen) as Hroom.
    rewrite /image_entry_at.
    iIntros "!>" (W') "%Hokk %Hcwv %Hlzf %Hscf _ _ Hmp [#Hwild #Hrows]".
    destruct (UShSecc.secc_kexec_pages na alen afun sts W' Hokk)
      as (Hpc & Hsub & Hsub2 & Hx & Hdw & Hwr & Hrp).
    destruct (UShSecc.secc_kexec_entry_rows na alen afun sts W' Hokk Hroom
                Hfdl Hwr Hrp)
      as (Hroom336 & Hal8 & Hszv & Hstkrow & Hargsrow & Havd & Havs
          & Hfdlen & Hstop).
    pose proof (kexec_image_ok_fd _ na alen afun sts W' Hokk) as Hfd.
    pose proof (uka_argc _ _ _ _ _ _ Hargsrow) as Hargc.
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite Hfd; iExact "Hnpw" | ].
    iApply (uslot_of_urun_ro_at W' 42 Q Hal8
              ltac:(unfold uvis_sp in Hroom336; lia) Hstkrow Hfdlen Hstop Hlzf Hscf
              with "Hdep Hnpw' Hmp").
    iIntros (N h) "%Hpayeq %Hsz Hszf #Ht Hstd Hcwf Hchf _ _ Hrun".
    rewrite Hpc.
    assert (Ha0 : tf_resume_gpr0 (uvis_tf W') !!! Regidx (mword_of_int 10 : mword 5)
                  = mword_of_int (Z.of_nat (Z.to_nat (uvis_argc W')))).
    { rewrite (Z2Nat.id (uvis_argc W') ltac:(lia)).
      unfold uvis_argc. symmetry. apply moi_of_uint. }
    iApply (wp_ksecc_start Hps N h (tf_resume_gpr0 (uvis_tf W'))
              (Z.to_nat (uvis_argc W')) 42
              (take NSTD (uvis_fd W')) (uvis_fd W') (uvis_sz W') (uvis_cwd W')
              (uvis_ch W')
              ltac:(intros s; rewrite Hpayeq; exact (HQ s))
              Ha0 ltac:(rewrite Z2Nat.id; lia) ltac:(lia)
              with "[] [] [] [] Hstd Hszf Hcwf Hchf Hrun").
    - iApply (seccomp_code_of_text (ukn_t N) (uvis_M W') (uvis_perm W') Hsub Hx
                with "Ht").
    - iApply (seccomp_rodata_of_text (ukn_t N) (uvis_M W') (uvis_perm W')
                Hsub2 Hx with "Ht").
    - iApply (secc_wdep_of_pay N (take NSTD (uvis_fd W')) rb2
                ltac:(rewrite Hfd; exact Hcons)).
      iApply (secc_cons_pay_of_wild with "Hwild").
    - rewrite Hfd. iApply (secc_univ_of_mint with "Hwild Hwp Hrows").
  Qed.

End UkSeccEntry.
