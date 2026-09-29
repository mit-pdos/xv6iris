(* ===================================================================== *)
(*  UShUModSync.v -- THE [sync] LINE'S SHAPE MODULE (shape-modules S1,    *)
(*  step 2; design: claude-notes/design/shape-modules.md sections 2 and   *)
(*  5).                                                                   *)
(*                                                                        *)
(*  Everything the round needs of the [sync] line, in one file: its words *)
(*  and bytes (moved from [UShUModBase]), the sync child's law at the     *)
(*  union's credential [uHchild_sync] (moved from [UShURound]'s S2y), the *)
(*  module [mod_sync] ([UkShShape.shape_mod]: the family [LSync], the     *)
(*  line predicate [usync_lp], first byte not 'c', room 68) and the body  *)
(*  law at the sync line [usync_body_law], the generic                    *)
(*  [UkShShape.ushf_body_law_of_mod]'s instance.  The round lists the    *)
(*  module in [UShUPipes.union_mods] and folds the body law over the list *)
(*  ([UkShShape.ushf_body_law_mods]) at the child law.                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import ExecEntry.
Require Import UkRun.
Require Import SyncHook.  (* [Q_opt]: the sync round's receipt *)
Require Import UexecExecInst.
Require Import WpUart.
Require Import FsImg.
Require Import AppCfg.
Require Import UserPerm.
Require Import UserPtTree.
Require Import LineWords.
Require Import EchoOut.
Require Import FileDisc.
Require Import FileState.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import ExecWords.
Require Import UkShDiagAt.
Require Import ElfUser.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShEcho.
Require Import UkShFork.
Require Import LinkRec.
Require Import FileLinksLine.
Require Import LineModelLinks.
Require Import GenLinksLine.
Require Import UShPanic.
Require Import PipeOut.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInstAt.
Require Import UShURoundDefs.
Require UkFileIface.
Require UShExecPin.
Require FsSyncPin.
Require UShSync.
Require UkSyncEntry.
Require UkSync.                   (* [sync_pay] *)
Require Import CtxIdDefs.
Require Import UShUModBase.       (* the pure preamble, shared with the shape modules *)
Require Import UShUModX.          (* the whole-lend child laws' shared prologue *)
Require Import UkShShape.
Local Open Scope Z_scope.
Import Defs.

Local Notation U := ulmG.
Local Notation K := ulmG_hooks.

(* ---- the [sync] line's words and bytes (sync design section 3) ---- *)
Definition usync_lp (ws : list (list (bv 8))) (g : nat -> bv 8) (k len : nat) : Prop :=
  ws = FileDisc.uline_ws LSync /\ UkSh.ush_line_at LSync g k len.

Lemma usync_ws_exec_ok : exec_ok (FileDisc.uline_ws LSync).
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma usync_line : LineWords.wl_line (FileDisc.uline_ws LSync) = FileDisc.line_bytes LSync.
Proof using. vm_compute. reflexivity. Qed.

Lemma usync_xline (gb : nat -> bv 8) (len : nat) :
  UkSh.ush_line_at LSync gb 0%nat len ->
  UkShEcho.ush_xline_is (FileDisc.uline_ws LSync) gb 0%nat len.
Proof using.
  intros (Hu & Hlen & Hby). split; [exact usync_ws_exec_ok |].
  rewrite usync_line. exact (conj Hlen Hby).
Qed.

(* its first byte is 's', not the 'c' of a [cd] *)
Lemma usync_lp0 (ws : list (list (bv 8))) (g : nat -> bv 8) (k len : nat) :
  usync_lp ws g k len -> bv_unsigned (g k) <> 99%Z.
Proof using.
  intros (_ & _ & Hlen & Hby).
  assert (Hpos : (0 < len)%nat) by (rewrite Hlen; vm_compute; lia).
  pose proof (Hby 0%nat Hpos) as H0. rewrite Nat.add_0_r in H0. rewrite H0.
  vm_compute. discriminate.
Qed.

Lemma usync_lp_of_at (f : nat -> bv 8) (k len : nat) :
  UkSh.ush_line_at LSync f k len ->
  usync_lp (FileDisc.uline_ws LSync) (fun j : nat => f (k + j)%nat) 0%nat len.
Proof using.
  intros (Hu & Hlen & Hby). split; [reflexivity |].
  split_and!; [exact Hu | exact Hlen |]. intros j Hj. exact (Hby j Hj).
Qed.

(* sh's [exec sync failed] *)
Lemma usync_execfail_bytes0 :
  UkShDiagAt.ush_execfail_bytes FileDisc.alt_execsync FileDisc.cmd_sync.
Proof using.
  rewrite /UkShDiagAt.ush_execfail_bytes. split_and!.
  - vm_compute. lia.
  - intros p Hp.
    assert (Hl : (p < length FileDisc.alt_execsync)%nat)
      by (vm_compute in Hp |- *; lia).
    exact (list_lookup_lookup_total_lt FileDisc.alt_execsync p Hl).
  - intros p Hp.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x1298)
             (fun q : nat => FileDisc.alt_execsync !!! q) 0%nat 5%nat);
      [vm_compute; reflexivity | lia].
  - intros j Hj.
    assert (Hj4 : (j < 4)%nat) by (vm_compute in Hj; lia).
    destruct j as [| [| [| [| j]]]]; try lia; vm_compute; reflexivity.
  - intros p Hp.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x1298)
             (fun q : nat => FileDisc.alt_execsync !!! (q + 2)%nat)
             7%nat 8%nat);
      [vm_compute; reflexivity | lia].
Qed.

Lemma usync_execfail_bytes :
  UkShDiagAt.ush_execfail_bytes FileDisc.alt_execsync
    (FileDisc.uline_ws LSync !!! 0%nat).
Proof using. exact usync_execfail_bytes0. Qed.

(* ---- THE MODULE: the sync line as the round sees it ---- *)
Lemma usync_lp_at (lu : FileDisc.uline) (f : nat -> bv 8) (k len : nat) :
  lu = LSync -> UkSh.ush_line_at lu f k len ->
  usync_lp (FileDisc.uline_ws lu) (fun j : nat => f (k + j)%nat) 0%nat len.
Proof using . intros -> H. exact (usync_lp_of_at f k len H). Qed.

Lemma usync_Dc_le : (68 <= 68 + UkSh.ush_Dpipe)%nat.
Proof using . lia. Qed.

Definition mod_sync : shape_mod :=
  {| sm_D := fun l => l = LSync; sm_Lp := usync_lp; sm_head := HeadNotC;
     sm_Dc := 68%nat; sm_Dc_le := usync_Dc_le; sm_lp0 := usync_lp0;
     sm_lp_at := usync_lp_at |}.

Section UShUModSync.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  (* NO [ghost_varG Σ Z] BINDER ([UShRound]'s header): the redirect child's
     pins name [Xv6Cameras.offbox_offG] *)
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context `{HfifR : !UkFileIface.fifRegG Σ}.

  Context (ug : union_gn) (r : file_names).
  Local Notation gf := (ugn_file ug).
  Context (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl gf)) r).
  Context (s0 : fstate).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = ucl ug).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = file_taint (fgn_cl gf)).
  (* the era credential at the union IS the era's wild token ([union_ifc]),
     and the reader-side one is the open premise (seccomp design 10.12) *)
  Context (Hwild : @riscv_wild Σ (@riscv_fixedGS Σ _) = usecc_tok ug).
  Context (Hrdw : ush_rdwild_of_shape ug).
  (* THE RECORD'S SYNC-HOOK FAMILY IS THE UNION'S (sync SY3-A4): the seam
     through which /sync's lend carries the hook sh mints *)
  Context (Hhk : @riscv_sync_hook Σ (@riscv_fixedGS Σ _) = union_hk file_pred (fgn_cl gf)).

  Local Notation T := (file_taint (fgn_cl gf)).
  Local Notation FI := (union_link_inst_at ug s0).
  Local Notation PA := (union_params_at ug s0).

  (* the pipeline's two shapes: parameters until C9f2 names them *)
  Context (PT : list (bv 8) -> nat -> iProp Σ) (PD : list (bv 8) -> iProp Σ).

  Local Notation Wcl := (uWcl ug s0).
  Local Notation Wcf := (uWcf ug r s0).
  Local Notation Wcu := (uWcu ug r s0 PT PD).
  Local Notation Wbu := (uWbf ug r s0).
  Local Notation PRE := (ush_pre_at ug r s0).
  Local Notation DONE := (ush_done_at ug r s0).

  #[local] Instance usr_T_pers0 : Persistent T | 0.
  Proof using . rewrite /file_taint /echo_taint. apply _. Qed.
  #[local] Instance usr_links_pers0 : Persistent (union_links ug) | 0
    := union_links_persistent ug.

  Local Notation uHktaint' := (UShURoundDefs.uHktaint ug Hkill).
  Local Notation uWcu_taint' := (UShURoundDefs.uWcu_taint ug r s0 PT PD).

  (* =================================================================== *)
  (*  S2y  THE sync CHILD (sync design section 3)                         *)
  (*                                                                     *)
  (*  An EXEC line with no redirect, whose every alternative moves no    *)
  (*  file: the lend goes to /sync whole, and /sync's exit pays the      *)
  (*  round's credential at RAN once [sync()] has returned -- nothing on *)
  (*  the console (it prints nothing), the block still owed whole, the   *)
  (*  deed PEND at [RSyncRan].  The prompt is then the block's first     *)
  (*  byte, and sh files RAN from the deed at its [$], as the redirect   *)
  (*  line's [RFRan sel] is filed.  The exec failure and the out-of-      *)
  (*  memory death are the record's own blocks beside the deed as found. *)
  (* =================================================================== *)

  (* /sync's RECEIPT (sync SY3-A4): the deed at PEND ([RSyncRan], the
     identity) and the round's record, both built by the hook *)
  Definition usync_q (I : list (bv 8)) : iProp Σ :=
    (ush_pend_at ug r s0 I ∗ usync_rec ug s0 I)%I.

  (* THE PAYMENT AT RAN: the round's credential at the block's head, beside
     the receipt, is the position-0 credential -- the block still owed
     whole, the deed PEND with the record beside it *)
  Lemma usync_ran_pay (I : list (bv 8)) :
    ⊢ UkSync.sync_pay (Wcl I 3%nat) (usync_q I) (UkShFork.ushf_wq Wcu I).
  Proof using .
    rewrite /UkSync.sync_pay /UkShFork.ushf_wq /usync_q. iIntros "Hc [Hd Hr]".
    iApply (uWcu_of ug r s0 PT PD I 0%nat). rewrite uWcf_0. iRight. iFrame "Hc Hd Hr".
  Qed.

  (* THE LEND (sync SY3-A4): the round's lend at its head splits into the
     credential /sync keeps and THE HOOK, minted through the seam out of
     the deed's half, the round position, the line's witness and the
     running claim's registration ([AppFile.union_hook_file]); the hook's
     receipt is the deed at PEND and the round's record ([usync_q]) *)
  Lemma usync_lend (I : list (bv 8)) :
    ul I = LSync -> (0 < nlines I)%nat ->
    ⊢ Wcu I 3%nat -∗ Wcl I 3%nat ∗ hook_opt gen_id (Some (usync_q I)).
  Proof using Hhk.
    intros Hul Hpos. iIntros "Hc".
    iDestruct (uWcu_3_nw ug r s0 PT PD I ltac:(rewrite Hul; reflexivity) with "Hc") as "Hc".
    rewrite uWcf_S3. iDestruct "Hc" as "[Hc [Hd Hw]]". iFrame "Hc".
    rewrite /hook_opt Hhk.
    (* the taint's hook: every piece back, the receipt out of the taint *)
    iAssert (T -∗ union_hk file_pred (fgn_cl gf) gen_id (usync_q I))%I as "Htaint".
    { iIntros "#HT". rewrite /union_hk. iIntros (Ih rh rh') "_ _ _ Hg Hp Htk".
      iModIntro. iModIntro. iFrame "Hg Hp Htk". rewrite /usync_q. iSplitL.
      - iApply (ush_deed_taint ug r with "HT").
      - by iLeft. }
    rewrite {1}/ush_deed_at. iDestruct "Hd" as "[Hd | #HT]"; [| by iApply "Htaint"].
    rewrite /uline_wit. iDestruct "Hw" as "[Hw | #HT]"; [| by iApply "Htaint"].
    iDestruct "Hd" as (cs s v) "(Hown & %Htie & #Hty & #Hpin & #Hcs & %Hnw & Hup)".
    iDestruct "Hup" as (vf n) "(#Hvf & Hpos & %Hn & #Hrr)".
    rewrite /FileLinksLine.flw. iDestruct "Hw" as (vf') "[#Hvf' #Hfl]".
    iDestruct (file_era_pin_agree with "Hvf Hvf'") as %<-.
    set (ls := (fe_base vf ++ UnionAdm.ulines_in I)%list).
    assert (Hlst : stdpp.list_basics.list.last ls = Some LSync).
    { rewrite /ls last_app (ulines_in_last I Hpos) Hul. reflexivity. }
    assert (Hls : length ls = (length (fe_base vf) + nlines I)%nat).
    { rewrite /ls length_app UnionAdm.ulines_in_length. reflexivity. }
    rewrite /fown. iDestruct "Hown" as "[Hdd Htk]".
    iApply (union_hook_file (fgn_cl gf) gen_id r s ls n (usync_q I) Hlst ltac:(lia)
              with "Hdd Hpos Hfl Hrr").
    iSplit.
    - (* the append: the deed PEND at /sync's run, the record beside it *)
      iIntros "Hdd Hpos" (Ls) "#Hnew". rewrite /usync_q. iSplitL.
      + rewrite /ush_pend_at /ush_deed_at. iLeft. iExists cs, s, v.
        rewrite /fown. iFrame "Hdd Htk Hty Hpin Hcs".
        iSplitR.
        { iPureIntro. destruct Htie as [Hlen Hcon]. exists (ualt_code (UR RSyncRan)).
          rewrite /upend_tie_at ulm_term_R ulm_cont_R ulm_step_R Hul.
          split_and!; [exact Hlen | exact Hpos | | reflexivity | reflexivity | exact Hcon].
          apply (ulm_ok_R' _ LSync RSyncRan ltac:(intros; discriminate)). exact Logic.I. }
        iSplitR; [by iPureIntro |].
        iExists vf, (length ls). iFrame "Hvf Hpos Hrr". iPureIntro. lia.
      + iRight. iRight. iExists v, cs, vf, Ls. iFrame "Hpin Hcs Hvf".
        iSplitR; [iPureIntro; exact (proj1 Htie) |].
        rewrite -(proj2 Htie). iExact "Hnew".
    - (* the taint: the receipt out of it *)
      iIntros "#HT _ _". rewrite /usync_q. iSplitL.
      + iApply (ush_deed_taint ug r with "HT").
      + by iLeft.
  Qed.

  (* an entry is contravariant in its lend *)
  Local Lemma image_entry_lend (f : ElfFile.elf_bytes) (M : gmap Z (bv 8)) (av : mword 64)
      (sts : list fdstate) (cw : Z) (secc : mword 64) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay Pay' : iProp Σ) (X : UexecSlot.uvis -d> iPropO Σ) :
    □ (Pay' -∗ Pay) -∗ image_entry f M av sts cw secc cs pidv Q Pay X -∗
    image_entry f M av sts cw secc cs pidv Q Pay' X.
  Proof using .
    iIntros "#Hc #He". rewrite /image_entry.
    iIntros "!>" (na alen afun W') "H1 H2 H3 H4 H5 H6 H7 Hmy HP".
    iApply ("He" with "H1 H2 H3 H4 H5 H6 H7 Hmy"). iApply ("Hc" with "HP").
  Qed.

  (* THE EXEC SUPPLY: [exec sync] at the union's /sync entry, at the
     HOOK (sync SY3-A4): the lend is split at the entry into the credential
     and the hook ([usync_lend]); an exec failure hands the lend back whole *)
  Lemma usync_exec_sup (I : list (bv 8)) (vw : list fdstate) :
    ul I = LSync -> (0 < nlines I)%nat ->
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShExecPin.sh_sync_slot T -∗
      □ (app_taint -∗ UkShFork.ushf_wq Wcu I) -∗
      UkShEcho.sh_exec_sup_echo_at_v (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG)
        ucat_rows (FileDisc.uline_ws LSync)
        (fun _ : Z => UkShFork.ushf_wq Wcu I) (Wcu I 3%nat) vw.
  Proof using Hhk.
    intros Hul Hpos. iIntros "#Hdep #Hslot #Hkt".
    iPoseProof (usync_ran_pay I) as "#Hpay".
    iApply (UShExecPin.sh_exec_sup_x_of_entry_v (ghost_varG0 := offbox_offG)
              ucat_rows (FileDisc.uline_ws LSync) UShExecPin.sync_pl
              FsSyncPin.era0_sync_pins [FsImg.ROOTINO; FsSyncPin.SYNC_INO]
              FsSyncPin.SYNC_INO ElfUser.sync_elf T
              (UkShFork.ushf_wq Wcu I) (Wcu I 3%nat) vw
              usync_ws_exec_ok eq_refl UShSync.sync_elf_loadable
              UShExecPin.sh_sync_pin_resolves with "[] Hkt Hslot").
    iIntros "!>" (M sa t gn sts cs pidv) "%Himg %Hbytes %Hlen %Hrows %_ #Hnp".
    iApply (image_entry_lend with "[]").
    { iIntros "!> Hc". iApply (usync_lend I Hul Hpos with "Hc"). }
    iApply (UkSyncEntry.sync_image_entry (PS := uprogSG_free) (ghost_varG0 := offbox_offG)
              (FileDisc.uline_ws LSync) M sa t gn sts FsImg.ROOTINO cs pidv
              (fun _ : Z => UkShFork.ushf_wq Wcu I) (Wcl I 3%nat) (Some (usync_q I))
              (fun _ _ => eq_refl) usync_ws_exec_ok Himg Hbytes Hlen
              with "[] Hnp Hdep").
    iModIntro. cbn [Q_opt]. iExact "Hpay".
  Qed.

  (* THE EXEC FAILED: [exec sync failed], the record's block at
     [RSyncExec] beside the deed as the round found it *)
  Lemma usync_execfail_law (I : list (bv 8)) :
    ul I = LSync -> (0 < nlines I)%nat ->
    ⊢ union_links ug -∗
      UkShDiag.ush_execfail_law_at (PS := uprogSG_free) (ghost_varG0 := offbox_offG)
        FileDisc.alt_execsync (13 + length (FileDisc.uline_ws LSync !!! 0%nat))%nat
        (Wcu I 3%nat) (Wcu I 0%nat).
  Proof using .
    intros Hul Hpos. iIntros "#Hlk".
    assert (Hnw : uwild (ul I) = false) by (rewrite Hul; reflexivity).
    assert (Hnp : forall p n, ul I <> LPipe p n) by (rewrite Hul; intros; discriminate).
    iPoseProof (UShPanic.ush_diag_law_hold_at_alt (PS := uprogSG_free)
                  (ghost_varG0 := offbox_offG) FI (PRE I) I (ualt_code (UR RSyncExec))
                  with "[] [] []") as "#Hx".
    { iLeft. iPureIntro. rewrite ufi_wild Hnw. discriminate. }
    { iApply ufi_rnd_free. intros Hq. vm_compute in Hq. discriminate Hq. }
    { cbn [lk_links union_link_inst_at gen_link_inst]. iExact "Hlk". }
    assert (Hab : lk_ab FI I (ualt_code (UR RSyncExec)) = FileDisc.alt_execsync).
    { change (lk_ab FI I (ualt_code (UR RSyncExec)))
        with (lm_ab U K I (ualt_code (UR RSyncExec))).
      rewrite (ulm_ab_R' I RSyncExec Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl) Hul.
      reflexivity. }
    assert (Hn : (length FileDisc.alt_execsync - 2
                  = 13 + length (FileDisc.uline_ws LSync !!! 0%nat))%nat)
      by (vm_compute; reflexivity).
    iEval (rewrite Hab Hn) in "Hx".
    rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    iDestruct (uWcu_3_nw ug r s0 PT PD I Hnw with "Hc") as "Hc". rewrite uWcf_S3.
    iDestruct ("Hx" $! N l with "[%] [Hc]") as (Pf) "(H0 & #Hs & #He)";
      [exact Hfd | rewrite /uWcl; iExact "Hc" |].
    iExists Pf. iFrame "H0 Hs". iIntros "!> Hp".
    iDestruct ("He" with "Hp") as (v) "(#Hpin & Hblk & Hpre)".
    iApply (uWcu_of ug r s0 PT PD I 0%nat).
    iApply (uWcf0_of_post_pre_id ug r s0 I (ualt_code (UR RSyncExec)) v
              (ulm_apr_R' I RSyncExec Hnp ltac:(rewrite Hul; exact Logic.I) eq_refl eq_refl)
              Hnw ltac:(by vm_compute) Hpos
              ltac:(intros s; rewrite ulm_step_R Hul; reflexivity)
              with "Hpin Hblk Hpre").
  Qed.

  (* ---- THE sync CHILD'S LAW ---- *)
  Lemma uHchild_sync :
    ⊢ union_links ug -∗
      udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShExecPin.sh_sync_slot T -∗
      UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG) T Wcu usync_lp 68.
  Proof using Hkill Hhk inG0.
    iIntros "#Hlk #Hdep #Hslot".
    iApply (ushf_child_law_of_x ug r s0 Hkill PT PD usync_lp (fun l => l = LSync)
              FsSyncPin.era0_sync_pins with "[] Hslot").
    - intros ws g len [-> H]. by exists LSync.
    - intros l g len ->. exact (usync_xline g len).
    - intros l b -> _ Hf Hw. rewrite (FileDisc.fline_ok_sync_words b Hf Hw).
      exact uline_of_u_sync.
    - iIntros "!>" (I l -> _ Hul Hpos) "#Hkq Hc". iRight.
      iExists (Wcu I 3%nat), (Wcu I 0%nat), FileDisc.alt_execsync. iFrame "Hc".
      iSplit; [iPureIntro; exact usync_execfail_bytes |].
      iSplit; [iIntros "!>" (vw _);
               iApply (usync_exec_sup I vw Hul Hpos with "Hdep Hslot Hkq") |].
      iSplitR; [iApply (uHoom ug r s0 PT PD I ltac:(by rewrite Hul) Hpos with "Hlk") |].
      iSplitR; [iApply (usync_execfail_law I Hul Hpos with "Hlk") |].
      iIntros "!> $".
  Qed.

  (* THE BODY LAW at the sync line, from its child law: the generic
     wrapper's instance *)
  Lemma usync_body_law (N : uk_names Σ) `{Hp : !ukn_const N} (γp : gname)
      (Pm : list (bv 8) -> iProp Σ) (sz : Z) :
    8344 <= sz -> UserPtTree.pgroundup sz = sz -> usz_ok (sz + 65536) ->
    UkShFork.ushf_kill_law Wcu -∗
    UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) T Wcu usync_lp 68 -∗
    UkShDiag.ush_panic_law (PS := uprogSG_free) Wcu Wbu -∗
    UkShFork.ushf_body_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm (sm_D mod_sync) sz.
  Proof using .
    intros Hszlo Hszal Hszok. iIntros "#Hkl #Hchl #Hplaw".
    iApply (UkShShape.ushf_body_law_of_mod (PS := uprogSG_free) (SG := uexecSG_xv6)
              (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm (fun k H => H)
              mod_sync sz Hszlo Hszal Hszok with "Hkl [] Hplaw").
    rewrite /UkShShape.sm_law. cbn [sm_Lp sm_Dc mod_sync]. iExact "Hchl".
  Qed.

End UShUModSync.
