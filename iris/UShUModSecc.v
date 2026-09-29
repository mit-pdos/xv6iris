(* ===================================================================== *)
(*  UShUModSecc.v -- THE [seccomp x] LINE'S SHAPE MODULE (shape-modules   *)
(*  S1, step 3; design: claude-notes/design/shape-modules.md sections 2   *)
(*  and 5).                                                               *)
(*                                                                        *)
(*  Everything the round needs of the [seccomp x] line, in one file: its  *)
(*  words and bytes (moved from [UShUModBase]), the seccomp child's law   *)
(*  at the union's credential [uHchild_secc] (moved from [UShURound]'s    *)
(*  S2s), the module [mod_secc] ([UkShShape.shape_mod]: the family        *)
(*  [LSecc _], the line predicate [usecc_lp], first byte not 'c', room    *)
(*  68) and the body law at the seccomp line [usecc_body_law], the        *)
(*  generic [UkShShape.ushf_body_law_of_mod]'s instance.  The round lists *)
(*  the module in [UShUPipes.union_mods] and folds the body law over the  *)
(*  list ([UkShShape.ushf_body_law_mods]) at the child law.               *)
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
Require Import UkRun.
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
Require Import UShPanic.
Require Import PipeOut.
Require Import UnionDisc.
Require Import UnionDiscDec.
Require Import UnionOut.
Require Import UnionLinks.
Require Import UnionLinkInstAt.
Require Import UShURoundDefs.
Require UkFileIface.
Require FsSeccPin.
Require UexecSecc.
Require UShSecc.
Require UShExecPin.
Require UkSeccEntry.
Require LinkUserinit.            (* [UG.uexec_wp_gen]: the generic user WP *)
Require Import CtxIdDefs.
Require Import UShUModBase.       (* the pure preamble, shared with the shape modules *)
Require Import UShUModX.          (* the whole-lend child laws' shared prologue *)
Require Import UkShShape.
Local Open Scope Z_scope.
Import Defs.

Local Notation U := ulmG.
Local Notation K := ulmG_hooks.

(* ---- the [seccomp x] line's words and bytes (seccomp lane S4) ---- *)
Definition usecc_lp (ws : list (list (bv 8))) (g : nat -> bv 8) (k len : nat) : Prop :=
  exists wsx : list (list (bv 8)),
    ws = FileDisc.uline_ws (LSecc wsx) /\ UkSh.ush_line_at (LSecc wsx) g k len.

Lemma usecc_ws_exec_ok (wsx : list (list (bv 8))) :
  FileDisc.secc_ok wsx -> exec_ok (FileDisc.uline_ws (LSecc wsx)).
Proof using.
  intros Hok. pose proof (FileDisc.secc_ok_wf wsx Hok) as Hwf.
  destruct Hok as (_ & _ & H10 & Hl). cbn [FileDisc.uline_ws].
  split_and!; [exact Hwf | cbn [length]; lia | exact H10 | exact Hl].
Qed.

Lemma usecc_xline (wsx : list (list (bv 8))) (gb : nat -> bv 8) (len : nat) :
  UkSh.ush_line_at (LSecc wsx) gb 0%nat len ->
  UkShEcho.ush_xline_is (FileDisc.uline_ws (LSecc wsx)) gb 0%nat len.
Proof using.
  intros (Hu & Hlen & Hby). split; [exact (usecc_ws_exec_ok wsx Hu) |].
  exact (conj Hlen Hby).
Qed.

(* its first byte is 's', not the 'c' of a [cd] *)
Lemma usecc_lp0 (ws : list (list (bv 8))) (g : nat -> bv 8) (k len : nat) :
  usecc_lp ws g k len -> bv_unsigned (g k) <> 99%Z.
Proof using.
  intros (wsx & _ & _ & Hlen & Hby).
  assert (Hc7 : length FileDisc.cmd_seccomp = 7%nat) by (vm_compute; reflexivity).
  assert (Hpos : (0 < len)%nat)
    by (rewrite Hlen /FileDisc.line_bytes length_app /=; lia).
  pose proof (Hby 0%nat Hpos) as H0. rewrite Nat.add_0_r in H0. rewrite H0.
  rewrite /FileDisc.line_bytes /FileDisc.line_body /wl_body.
  rewrite lookup_total_app_l; [| rewrite length_app; lia].
  rewrite lookup_total_app_l; [| lia].
  vm_compute. discriminate.
Qed.

Lemma usecc_lp_of_at (wsx : list (list (bv 8))) (f : nat -> bv 8) (k len : nat) :
  UkSh.ush_line_at (LSecc wsx) f k len ->
  usecc_lp (FileDisc.uline_ws (LSecc wsx)) (fun j : nat => f (k + j)%nat) 0%nat len.
Proof using.
  intros (Hu & Hlen & Hby). exists wsx. split; [reflexivity |].
  split_and!; [exact Hu | exact Hlen |]. intros j Hj. exact (Hby j Hj).
Qed.

(* sh's [exec seccomp failed] *)
Lemma usecc_execfail_bytes0 :
  UkShDiagAt.ush_execfail_bytes FileDisc.alt_execsecc FileDisc.cmd_seccomp.
Proof using.
  rewrite /UkShDiagAt.ush_execfail_bytes. split_and!.
  - vm_compute. lia.
  - intros p Hp.
    assert (Hl : (p < length FileDisc.alt_execsecc)%nat)
      by (vm_compute in Hp |- *; lia).
    exact (list_lookup_lookup_total_lt FileDisc.alt_execsecc p Hl).
  - intros p Hp.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x1298)
             (fun q : nat => FileDisc.alt_execsecc !!! q) 0%nat 5%nat);
      [vm_compute; reflexivity | lia].
  - intros j Hj.
    assert (Hj7 : (j < 7)%nat) by (vm_compute in Hj; lia).
    destruct j as [| [| [| [| [| [| [| j]]]]]]]; try lia; vm_compute; reflexivity.
  - intros p Hp.
    apply (UkShDiag.ush_bytes_of_forallb (UkShDiag.shd_lit 0x1298)
             (fun q : nat => FileDisc.alt_execsecc !!! (q + 5)%nat)
             7%nat 8%nat);
      [vm_compute; reflexivity | lia].
Qed.

Lemma usecc_execfail_bytes (wsx : list (list (bv 8))) :
  UkShDiagAt.ush_execfail_bytes FileDisc.alt_execsecc
    (FileDisc.uline_ws (LSecc wsx) !!! 0%nat).
Proof using. exact usecc_execfail_bytes0. Qed.

(* ---- THE MODULE: the seccomp line as the round sees it ---- *)
Lemma usecc_lp_at (lu : FileDisc.uline) (f : nat -> bv 8) (k len : nat) :
  (exists wsx : list (list (bv 8)), lu = LSecc wsx) -> UkSh.ush_line_at lu f k len ->
  usecc_lp (FileDisc.uline_ws lu) (fun j : nat => f (k + j)%nat) 0%nat len.
Proof using . intros [wsx ->] H. exact (usecc_lp_of_at wsx f k len H). Qed.

Lemma usecc_Dc_le : (68 <= 68 + UkSh.ush_Dpipe)%nat.
Proof using . lia. Qed.

Definition mod_secc : shape_mod :=
  {| sm_D := fun l => exists wsx : list (list (bv 8)), l = LSecc wsx; sm_Lp := usecc_lp; sm_head := HeadNotC;
     sm_Dc := 68%nat; sm_Dc_le := usecc_Dc_le; sm_lp0 := usecc_lp0; sm_lp_at := usecc_lp_at |}.

Section UShUModSecc.
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
  (*  S2s  THE seccomp CHILD (seccomp lane S4)                            *)
  (*                                                                     *)
  (*  A [seccomp x] line is WILD: the lend the read left is the wild     *)
  (*  shape (the clean arm's deed refutes the line, or is the taint).    *)
  (*  The child execs /seccomp at the parent's ok view; the entry's Pay  *)
  (*  is the era token (the union's [riscv_wild]), the reader-side       *)
  (*  credential (the open premise [Hrdw]) and the rows the view         *)
  (*  guarantees ([UexecSecc.ush_view_secc_rows]); every payload is the  *)
  (*  shape's, and the exec-failed diagnostic goes through the licence.  *)
  (* =================================================================== *)

  (* the diagnostic through the era's licence, at any bytes *)
  Lemma usecc_execfail_law (I : list (bv 8)) (dg : list (bv 8)) (n : nat) :
    ⊢ UkShDiag.ush_execfail_law_at (PS := uprogSG_free) (ghost_varG0 := offbox_offG) dg n
        (useccomp_shape ug I) (useccomp_shape ug I).
  Proof using Hcons.
    rewrite /UkShDiag.ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd2 #Hsh". destruct Hfd2 as [rb Hl2].
    iExists (fun _ : nat => useccomp_shape ug I).
    iSplitR; [iExact "Hsh" |]. iSplit.
    - iIntros "!>" (p b) "%Hb %Hlt".
      iApply (UShPanic.ksh_w1_of_step (PS := uprogSG_free) (ghost_varG0 := offbox_offG)
                N (useccomp_shape ug I) (useccomp_shape ug I) l rb b Hl2).
      iIntros "!>" (Φ) "_ HΦ".
      iPoseProof "Hsh" as "[Htok _]".
      iApply (union_write_link_wild ug Hcons (S gen_id) b Φ with "[Htok] [HΦ]").
      + iApply (usecc_tok_of_at with "Htok").
      + iApply "HΦ". iExact "Hsh".
    - iIntros "!> H". iExact "H".
  Qed.

  (* ---- THE EXEC SUPPLY: [exec seccomp] at the parent's ok view ---- *)
  Lemma usecc_exec_sup (I : list (bv 8)) (wsx : list (list (bv 8))) (vw : list fdstate) :
    FileDisc.secc_ok wsx -> ush_view_ok vw ->
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShExecPin.sh_secc_slot T -∗
      useccomp_shape ug I -∗
      UkShEcho.sh_exec_sup_echo_at_v (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG)
        ucat_rows (FileDisc.uline_ws (LSecc wsx))
        (fun _ : Z => UkShFork.ushf_wq Wcu I)
        (useccomp_shape ug I) vw.
  Proof using Hwild Hrdw.
    intros Hok Hvok. iIntros "#Hdep #Hslot #Hsh".
    iPoseProof LinkUserinit.UG.uexec_wp_gen as "#Hwp".
    iAssert (□ (∀ s : Z, UkShFork.ushf_wq Wcu I))%I as "#HQ".
    { iIntros "!>" (_). rewrite /UkShFork.ushf_wq.
      iApply (uWcu_wild ug r s0 PT PD I 0%nat with "Hsh"). }
    iApply (UShExecPin.sh_exec_sup_x_of_entry_v (ghost_varG0 := offbox_offG)
              ucat_rows (FileDisc.uline_ws (LSecc wsx)) UShExecPin.secc_pl
              FsSeccPin.era0_secc_pins [FsImg.ROOTINO; FsSeccPin.SECC_INO]
              FsSeccPin.SECC_INO ElfUser.seccomp_elf T
              (UkShFork.ushf_wq Wcu I) (useccomp_shape ug I) vw
              (usecc_ws_exec_ok wsx Hok) eq_refl UShSecc.secc_elf_loadable
              UShExecPin.sh_secc_pin_resolves with "[] [] Hslot").
    - iIntros "!>" (M sa t gn sts cs pidv) "%Himg %Hbytes %Hlen %Hrows %Htab #Hnp".
      destruct Hrows as (_ & _ & [rb2 Hr2]).
      iPoseProof (UexecSecc.ush_view_secc_rows vw sts Hvok Htab) as "#Hrows".
      iPoseProof (UkSeccEntry.secc_image_entry (PS := uprogSG_free) (ghost_varG0 := offbox_offG)
                    (FileDisc.uline_ws (LSecc wsx)) M sa t gn sts FsImg.ROOTINO cs pidv
                    (fun _ : Z => UkShFork.ushf_wq Wcu I) rb2
                    (fun k H => H) (usecc_ws_exec_ok wsx Hok) Himg Hbytes Hlen Hr2
                    with "HQ Hwp Hnp Hdep") as "He".
      iApply (UShExecPin.image_entry_pay_mono with "[] He").
      iIntros "!> _". rewrite Hwild.
      iSplitR; [iPoseProof "Hsh" as "[Htok _]"; iApply (usecc_tok_of_at with "Htok") |].
      iSplitR; [iApply (Hrdw I with "Hsh") | iExact "Hrows"].
    - iIntros "!> _". iApply ("HQ" $! 0%Z).
  Qed.

  (* ---- THE seccomp CHILD'S LAW ---- *)
  Lemma uHchild_secc :
    ⊢ udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
      UShExecPin.sh_secc_slot T -∗
      UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
        (ghost_varG0 := offbox_offG) T Wcu usecc_lp 68.
  Proof using Hwild Hrdw Hkill Hcons.
    iIntros "#Hdep #Hslot".
    iApply (ushf_child_law_of_x ug r s0 Hkill PT PD usecc_lp
              (fun l => exists wsx, l = LSecc wsx) FsSeccPin.era0_secc_pins
              with "[] Hslot").
    - intros ws g len (wsx & -> & H). exists (LSecc wsx). eauto.
    - intros l g len [wsx ->]. exact (usecc_xline wsx g len).
    - intros l b [wsx ->] Hok Hf Hw.
      destruct (FileDisc.fline_ok_secc_words b wsx Hf Hw) as [_ ->].
      exact (uline_of_u_secc wsx Hok).
    - iIntros "!>" (I l [wsx ->] Hok Hul _) "_ Hcr".
      iDestruct (uWcu_3 ug r s0 PT PD I with "Hcr") as "[Hcr | #Hsh]".
      { (* the clean arm: its deed refutes the wild line, or is the taint *)
        rewrite uWcf_S3. iDestruct "Hcr" as "[_ [Hpre _]]".
        rewrite {1}/ush_deed_at. iDestruct "Hpre" as "[Hpre | #HT]"; [| by iLeft].
        iDestruct "Hpre" as (cs s v') "(_ & _ & _ & _ & _ & %Hnw & _)".
        rewrite Hul in Hnw. discriminate Hnw. }
      (* the wild arm: the shape is the walk's [Cr] and [Cd] *)
      iRight. iExists (useccomp_shape ug I), (useccomp_shape ug I), FileDisc.alt_execsecc.
      iSplitR; [iPureIntro; exact (usecc_execfail_bytes wsx) |].
      iSplitR; [iExact "Hsh" |].
      iSplitR; [iIntros "!>" (vw Hvok);
                iApply (usecc_exec_sup I wsx vw Hok Hvok with "Hdep Hslot Hsh") |].
      iSplitR; [iApply usecc_execfail_law |]. iSplitR; [iApply usecc_execfail_law |].
      iIntros "!> H". rewrite /UkShFork.ushf_wq. iApply (uWcu_wild ug r s0 PT PD I 0%nat with "H").
  Qed.

  (* THE BODY LAW at the seccomp line, from its child law: the generic
     wrapper's instance *)
  Lemma usecc_body_law (N : uk_names Σ) `{Hp : !ukn_const N} (γp : gname)
      (Pm : list (bv 8) -> iProp Σ) (sz : Z) :
    8344 <= sz -> UserPtTree.pgroundup sz = sz -> usz_ok (sz + 65536) ->
    UkShFork.ushf_kill_law Wcu -∗
    UkShFork.ushf_child_law_at (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) T Wcu usecc_lp 68 -∗
    UkShDiag.ush_panic_law (PS := uprogSG_free) Wcu Wbu -∗
    UkShFork.ushf_body_law (PS := uprogSG_free) (SG := uexecSG_xv6)
      (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm (sm_D mod_secc) sz.
  Proof using .
    intros Hszlo Hszal Hszok. iIntros "#Hkl #Hchl #Hplaw".
    iApply (UkShShape.ushf_body_law_of_mod (PS := uprogSG_free) (SG := uexecSG_xv6)
              (ghost_varG0 := offbox_offG) N γp T Wcu Wbu Pm (fun k H => H)
              mod_secc sz Hszlo Hszal Hszok with "Hkl [] Hplaw").
    rewrite /UkShShape.sm_law. cbn [sm_Lp sm_Dc mod_secc]. iExact "Hchl".
  Qed.

End UShUModSecc.
