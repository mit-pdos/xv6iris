(* ===================================================================== *)
(* UkUnionEntries.v -- THE FILE LINES' PROGRAM ENTRIES AT THE UNION       *)
(* RECORD (cut C9f1; design: claude-notes/design/union.md section 3,      *)
(* 'Dispatch', review item S5).                                           *)
(*                                                                        *)
(* [UkFileEntries]' three entries -- echo at the console, echo > f, cat f *)
(* -- with the file interface [UkFileIface.file_iface] instantiated at    *)
(* the UNION's link record: the model [UnionDisc.ulmG], the parameters    *)
(* [UnionLinkInstAt.union_params_at] at the round's boot state and the    *)
(* links bundle [UnionLinks.union_links].  The glue is the interface's    *)
(* parameter-generic one ([fif_exit_k_cons_g], [fif_exit_k_redir_g],      *)
(* [fif_env_res_g]).                                                      *)
(*                                                                        *)
(* WHAT CHANGED AGAINST THE FILE'S ENTRIES.  The codes are the union's    *)
(* ([UnionDisc.ualt_code (UR a)]), and the console exit of BOTH console   *)
(* entries hands the round's post at the parameters' own boot state --  *)
(* [gwc_post] at [union_params_at s0] -- and the core's deed back: cat    *)
(* no longer pays through [UCatLend.catq_cat] but through the same glue   *)
(* as echo, at the code the drained console names.  cat's lend is the    *)
(* round's cursor opened ([UkConsOut.cons_cur] at the block's first      *)
(* byte), with the round's state tied to the deed's content.             *)
(*                                                                        *)
(* SEAM (d) (union.md, the later widening): cat's argument facts are      *)
(* stated POSITIONALLY over the file name's length ([ucat_f_tail]), never *)
(* at a one-byte name.                                                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import ProcGeom.
Require Import UserPerm UexecSlot UexecRet UexecSG.
Require Import UserHeap UkRun.
Require Import UserFd UserCwd.
Require Import ChildTok.
Require Import ElfFile ElfUser.
Require Import UmodeArith UmodeAbi.
Require Import SpecKexec.
Require Import ExecEntry.
Require Import UexecExecInst.
Require Import UkAbi.
Require Import UCodeEcho UCodeCat.
From User Require EchoInstrs EchoData.
Require Import UEchoKernel.
Require Import UShKernel.
Require Import LineWords EchoDisc ExecWords.
Require Import UkShEcho.
Require Import UShEcho.
Require Import UEchoOut.
Require Import UShEchoOut.
Require Import UShCat.
Require Import FsImgCheck.
Require Import ProgTree UkTree UkStub UkHandler.
Require Import UkEcho UkEchoTree.
Require Import UkCatMain UkCatTree.
Require Import UkTreeEntry.
Require Import CtxIdDefs.
Require User.EchoSyms User.CatSyms.
Require Import AppCfg AppInv AppFile AppFileCons FileOpen FsCfg FsImg.
Require Import EchoOut.
Require Import FileState FileDisc FileOut.
Require Import LineModel LineModelInst LineModelLinks.
Require Import FileLinks FileLinksLine FileLinkGen FileHooks.
Require Import GenLinksLine.
Require Import ConsoleInv.
Require Import UkConsOut ProgTreeFile.
Require Import UCatOut.
Require Import FsInitPin FsShPin FsEchoPin FsCatPin FsGrepPin.
Require Import UkFileDev FileWrite UEchoFile.
Require Import UkFileIface.
Require UkFileEntries.
Require Import PipeOut.
Require Import UnionDisc UnionOut UnionLinks UnionLinkInst UnionLinkInstAt.
Local Open Scope Z_scope.
Import Defs.

Local Notation U := ulmG.

(* ===================================================================== *)
(*  0.  PURE: cat's file name, positionally (seam (d)), and the union's   *)
(*      bodies at the file lines                                          *)
(* ===================================================================== *)

(* [UkTreeEntry.cat_f_tail] over the name's own length *)
Lemma ucat_f_tail (ws : list (list (bv 8))) :
  length ws = 2%nat ->
  UkShEcho.echo_alen ws 1%nat = length FsImgCheck.fname_f ->
  (forall j : nat, (j < length FsImgCheck.fname_f)%nat ->
     wl_line ws !!! (UkShEcho.echo_off ws 1%nat + j)%nat
     = FsImgCheck.fname_f !!! j) ->
  drop 1 ws = [FsImgCheck.fname_f].
Proof.
  intros Hws2 Hlen Hf.
  destruct ws as [| w0 [| w1 [| w2 r]]]; cbn in Hws2; try (exfalso; lia).
  cbn [drop]. f_equal.
  unfold UkShEcho.echo_alen in Hlen. change ([w0; w1] !!! 1%nat) with w1 in Hlen.
  apply (list_eq_same_length w1 FsImgCheck.fname_f (length w1));
    [symmetry; exact Hlen | reflexivity |].
  intros j x y Hj Hx Hy.
  pose proof (Hf j ltac:(lia)) as H. unfold UkShEcho.echo_off in H.
  rewrite (wl_line_word [w0; w1] 1%nat w1 j eq_refl Hj) in H.
  rewrite (list_lookup_total_correct _ _ _ Hx) (list_lookup_total_correct _ _ _ Hy) in H.
  exact H.
Qed.

(* a file line's alternative at the union: the file's continuation at the
   round's state *)
Lemma ulm_abs_R (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : ralt) :
  lm_abs U s0 cs I (ualt_code (UR a))
  = cont (lm_upto U cs s0 (bodies_of I) (nlines I - 1)) (lm_line_at U I) a.
Proof.
  rewrite /lm_abs. change (lm_cont ulmG) with ucont. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_code. reflexivity.
Qed.

Lemma ulm_cons_adm_R (s0 : fstate) (cs : list nat) (I : list (bv 8)) (a : ralt) :
  uline_nopipe (lm_line_at U I) -> ralt_ok (lm_line_at U I) a ->
  cons_adm U s0 cs I (ualt_code (UR a)).
Proof.
  intros Hnp Hok. rewrite /cons_adm.
  change (lm_ok ulmG) with (uok adm_u_g). change (lm_dec ulmG) with ualt_dec.
  change (lm_term ulmG) with uterm. rewrite ualt_dec_code.
  split; [| reflexivity].
  revert Hnp Hok. destruct (lm_line_at U I) as [ws | ws Nf | Nf | p n]; intros Hnp Hok;
    cbn [uok]; [exact Hok | exact Hok | exact Hok |].
  exfalso. exact (Hnp p n eq_refl).
Qed.

(* echo's body at the console, at code 0 *)
Lemma ulm_echo_body (s0 : fstate) (cs : list nat) (I : list (bv 8))
    (ws : list (list (bv 8))) :
  lm_line_at U I = LEcho ws ->
  lm_body U s0 cs I 0%nat = wl_line (drop 1 ws).
Proof.
  intros Hfl. rewrite /lm_body /lm_abs.
  change (lm_cont ulmG) with ucont. change (lm_dec ulmG) with ualt_dec.
  rewrite ualt_dec_0 Hfl. cbn [ucont].
  replace (ralt_dec 0%nat) with (REcho 0%nat) by (vm_compute; reflexivity).
  cbn [cont uline_ws]. rewrite EchoDisc.line_alts_of_0.
  rewrite length_app UCatOut.cat_prompt_len.
  replace (length (wl_line (drop 1 ws)) + 2 - 2)%nat with (length (wl_line (drop 1 ws))) by lia.
  rewrite take_app_length. reflexivity.
Qed.

Lemma ulm_echo_adm (s0 : fstate) (cs : list nat) (I : list (bv 8))
    (ws : list (list (bv 8))) :
  lm_line_at U I = LEcho ws -> cons_adm U s0 cs I 0%nat.
Proof.
  intros Hfl. rewrite /cons_adm.
  change (lm_ok ulmG) with (uok adm_u_g). change (lm_dec ulmG) with ualt_dec.
  change (lm_term ulmG) with uterm. rewrite ualt_dec_0 Hfl.
  split; [| reflexivity]. cbn [uok].
  replace (ralt_dec 0%nat) with (REcho 0%nat) by (vm_compute; reflexivity).
  simpl. lia.
Qed.

(* cat's two bodies at a present content, its one at an absent one *)
Lemma ulm_cat_body_ran (s0 : fstate) (cs : list nat) (I : list (bv 8))
    (content : list (bv 8)) :
  lm_line_at U I = LCat_f ->
  (lm_upto U cs s0 (bodies_of I) (nlines I - 1) : fstate) !! fname_f = Some content ->
  lm_body U s0 cs I (ualt_code (UR RCRan)) = content.
Proof.
  intros Hfl Hst. rewrite /lm_body ulm_abs_R Hfl.
  rewrite (UCatOut.cat_cont_ran_some _ content Hst).
  rewrite length_app UCatOut.cat_prompt_len.
  replace (length content + 2 - 2)%nat with (length content) by lia.
  rewrite take_app_length. reflexivity.
Qed.

Lemma ulm_cat_body_ran_none (s0 : fstate) (cs : list nat) (I : list (bv 8)) :
  lm_line_at U I = LCat_f ->
  (lm_upto U cs s0 (bodies_of I) (nlines I - 1) : fstate) !! fname_f = None ->
  lm_body U s0 cs I (ualt_code (UR RCRan)) = cat_dg_open fname_f.
Proof.
  intros Hfl Hst. rewrite /lm_body ulm_abs_R Hfl (UCatOut.cat_cont_ran_absent _ Hst)
    fif_cat_dg_open.
  apply (bool_decide_unpack _). vm_compute. exact Logic.I.
Qed.

Lemma ulm_cat_body_noopen (s0 : fstate) (cs : list nat) (I : list (bv 8)) :
  lm_line_at U I = LCat_f ->
  lm_body U s0 cs I (ualt_code (UR RCNoOpen)) = cat_dg_open fname_f.
Proof.
  intros Hfl. rewrite /lm_body ulm_abs_R Hfl UCatOut.cat_cont_noopen fif_cat_dg_open.
  apply (bool_decide_unpack _). vm_compute. exact Logic.I.
Qed.

(* ===================================================================== *)
(*  1.  THE LENDS: the console device out of the round's cursor          *)
(* ===================================================================== *)
Section UkUnionLend.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Local Notation UT := (file_taint (fgn_cl gf)).
  Local Notation PA := (union_params_at ug).
  Local Notation LK := (union_links ug).
  #[local] Instance uel_links_pers0 : Persistent LK | 0 := union_links_persistent ug.

  (* echo's lend at the console: the block at its first byte, code 0 *)
  Lemma uecho_lend (sb : fstate) (v : era_pins) (I : list (bv 8))
      (ws : list (list (bv 8))) :
    lm_line_at U I = LEcho ws ->
    (Z.of_nat (length (wl_line (drop 1 ws))) < 2 ^ 31)%Z ->
    LK -∗ era_pin (fgn_echo gf) (S gen_id) v -∗
    gwc_blk U (PA sb) (S gen_id) v I 0%nat 0%nat -∗
    cons_dev_atc U (PA sb) LK [0%nat] v I [wl_line (drop 1 ws)].
  Proof using .
    intros Hfl Hshort. iIntros "#Hlk #Hpin Hb".
    assert (Hs : cons_short [wl_line (drop 1 ws)]).
    { unfold cons_short. constructor; [exact Hshort | constructor]. }
    rewrite /gwc_blk. iDestruct "Hb" as "[Hb | #HT]"; last first.
    { iApply (cons_dev_atc_taint U (PA sb) LK [0%nat] v I _ Hs with "Hlk HT"). }
    iDestruct "Hb" as (ps cs s1 pos) "(%Hw & Ht & #Hps & #Hcs & #HI & #HW)".
    assert (Hbodies : lm_body U s1 cs I <$> [0%nat] = [wl_line (drop 1 ws)]).
    { cbn [fmap list_fmap]. rewrite (ulm_echo_body s1 cs I ws Hfl). reflexivity. }
    rewrite -Hbodies.
    iApply (cons_dev_atc_of_blk0 U (PA sb) LK [0%nat] v I ps cs s1 pos [0%nat] Hw
              ltac:(intros x Hx; exact Hx)
              ltac:(constructor; [exact (ulm_echo_adm s1 cs I ws Hfl) | constructor])
              ltac:(rewrite Hbodies; exact Hs)
              with "Hlk Hpin [Ht]").
    rewrite /cons_cur. iFrame "Ht Hps Hcs HI HW".
  Qed.

  (* cat's lend: the round's cursor at the block's first byte, the round's
     state named ([content]) -- the console owing the content or the
     diagnostic at a present file, the diagnostic at an absent one *)
  Definition ucat_alts (content : option (list (bv 8))) : list (list (bv 8)) :=
    match content with
    | Some bs => [bs; cat_dg_open fname_f]
    | None => [cat_dg_open fname_f]
    end.

  Lemma ucat_lend (sb : fstate) (v : era_pins) (ps cs : list nat) (I : list (bv 8))
      (pos : nat) (content : option (list (bv 8))) :
    lm_wr_blk_t U ps cs sb I pos -> lm_line_at U I = LCat_f ->
    (lm_upto U cs sb (bodies_of I) (nlines I - 1) : fstate) !! fname_f = content ->
    cons_short (ucat_alts content) ->
    LK -∗ era_pin (fgn_echo gf) (S gen_id) v -∗
    cons_cur U (PA sb) v ps cs sb I pos 0%nat 0%nat -∗
    cons_dev_atc U (PA sb) LK [ualt_code (UR RCRan); ualt_code (UR RCNoOpen)] v I
      (ucat_alts content).
  Proof using .
    intros Hw Hfl Hst Hs. iIntros "#Hlk #Hpin Hc".
    assert (Hnp : uline_nopipe (lm_line_at U I)) by (rewrite Hfl; intros ? ? ?; discriminate).
    destruct content as [bs |].
    - assert (Hbodies : lm_body U sb cs I <$> [ualt_code (UR RCRan); ualt_code (UR RCNoOpen)]
                        = [bs; cat_dg_open fname_f]).
      { cbn [fmap list_fmap].
        rewrite (ulm_cat_body_ran sb cs I bs Hfl Hst) (ulm_cat_body_noopen sb cs I Hfl).
        reflexivity. }
      cbn [ucat_alts]. rewrite -Hbodies.
      iApply (cons_dev_atc_of_blk0 U (PA sb) LK
                [ualt_code (UR RCRan); ualt_code (UR RCNoOpen)] v I ps cs sb pos
                [ualt_code (UR RCRan); ualt_code (UR RCNoOpen)] Hw
                ltac:(intros x Hx; exact Hx)
                ltac:(constructor;
                      [ apply (ulm_cons_adm_R sb cs I RCRan Hnp); rewrite Hfl; exact Logic.I |];
                      constructor;
                      [ apply (ulm_cons_adm_R sb cs I RCNoOpen Hnp); rewrite Hfl; exact Logic.I
                      | constructor ])
                ltac:(rewrite Hbodies; exact Hs)
                with "Hlk Hpin Hc").
    - assert (Hbodies : lm_body U sb cs I <$> [ualt_code (UR RCRan)]
                        = [cat_dg_open fname_f]).
      { cbn [fmap list_fmap]. rewrite (ulm_cat_body_ran_none sb cs I Hfl Hst). reflexivity. }
      cbn [ucat_alts]. rewrite -Hbodies.
      iApply (cons_dev_atc_of_blk0 U (PA sb) LK
                [ualt_code (UR RCRan); ualt_code (UR RCNoOpen)] v I ps cs sb pos
                [ualt_code (UR RCRan)] Hw
                ltac:(intros x Hx; apply elem_of_list_singleton in Hx as ->; constructor)
                ltac:(constructor;
                      [ apply (ulm_cons_adm_R sb cs I RCRan Hnp); rewrite Hfl; exact Logic.I
                      | constructor ])
                ltac:(rewrite Hbodies; exact Hs)
                with "Hlk Hpin Hc").
  Qed.

  Lemma ucat_lend_taint (sb : fstate) (v : era_pins) (I : list (bv 8))
      (content : option (list (bv 8))) :
    cons_short (ucat_alts content) ->
    LK -∗ UT -∗
    cons_dev_atc U (PA sb) LK [ualt_code (UR RCRan); ualt_code (UR RCNoOpen)] v I
      (ucat_alts content).
  Proof using .
    intros Hs. iIntros "#Hlk #HT".
    iApply (cons_dev_atc_taint U (PA sb) LK _ v I _ Hs with "Hlk HT").
  Qed.
End UkUnionLend.

(* ===================================================================== *)
(*  2.  THE ENTRIES                                                       *)
(* ===================================================================== *)
Section UkUnionEntries.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ, !pipeOutG Σ}.
  Context `{!fifRegG Σ}.
  Context (ug : union_gn).
  Local Notation gf := (ugn_file ug).
  Local Notation c := (fgn_cl gf).
  Local Notation UT := (file_taint (fgn_cl gf)).
  Local Notation PA := (union_params_at ug).
  Local Notation LK := (union_links ug).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = ucl ug).

  Local Instance ue_echo_code_persistent (N : uk_names Σ) :
    Persistent (up_code (echo_prog N)).
  Proof using . simpl. apply _. Qed.
  Local Instance ue_cat_code_persistent (N : uk_names Σ) :
    Persistent (up_code (cat_prog N)).
  Proof using . simpl. apply _. Qed.

  (* ------------------------------------------------------------------- *)
  (*  echo AT THE CONSOLE                                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma uecho_cons_image_entry (ws : list (list (bv 8))) (M : gmap Z (bv 8))
      (s0 t : Z) (gb : nat -> bv 8) (sts : list fdstate)
      (cw : Z) (cs : gset gname) (pidv : mword 32)
      (v : era_pins) (sb : fstate) (I0 : list (bv 8))
      (r : file_names) (q : Qp) (s : dst)
      (rb : bool) (jo : option Z) (Q : Z -> iProp Σ) (F : iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    EchoDisc.line_ok ws ->
    UShEcho.echo_node_img ws M s0 t gb ->
    UkShEcho.echo_argv_bytes ws gb ->
    length sts = NOFILE ->
    cw = FsImg.ROOTINO ->
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    lm_line_at U I0 = LEcho ws ->
    (Z.of_nat (length (wl_line (drop 1 ws))) < 2 ^ 31)%Z ->
    □ (app_taint -∗ UT) -∗ □ (UT -∗ app_taint) -∗
    □ (gwc_post U (PA sb) (S gen_id) v I0 0%nat -∗ fdq r q s -∗ F -∗ Q (-1)) -∗
    □ (UT -∗ Q (-1)) -∗
    file_cons_cred c r jo -∗
    app_inv fsc_fs -∗
    era_pin (fgn_echo gf) (S gen_id) v -∗
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64) sts
      cw ProcDefs.secc_all cs pidv Q
      (gwc_blk U (PA sb) (S gen_id) v I0 0%nat 0%nat ∗ fdq r q s ∗ F) uslot.
  Proof using Hcons fifRegG0 ufdG0.
    intros HQc Heq Hline Himg Hbytes Hfdl Hcw Hl1 Hfl Hshort.
    iIntros "#Hbr #Hkc #HQ #HQt #Hmade #Hinv #Hpin #Hnpw #Hdep".
    iPoseProof (union_links_holds ug Hcons) as "#Hlk".
    assert (Hne : drop 1 ws <> []).
    { pose proof (line_ok_ge2 ws Hline) as H2. intros Hd.
      apply (f_equal length) in Hd. rewrite length_drop in Hd. simpl in Hd. lia. }
    set (w0 := fun _ : nat => FDCons v I0 [0%nat]).
    assert (Hw0 : forall d, d ∈ [0%nat] -> forall i γo, w0 d <> FDIn false i γo)
      by (intros; discriminate).
    assert (Hrd : fif_wr [0%nat] w0 = false) by reflexivity.
    set (E := cons_env (wl_line (drop 1 ws)) (fif_files (snd <$> s))).
    rewrite /image_entry.
    iIntros "!>" (na alen afun W') "%Hok' %Hcw' %Hlz %Hscw %Hch %Hpid %Hargs Hmp HPay".
    iApply uslot_bupd.
    iMod (fif_reg_alloc w0) as (γreg) "Hpool". iModIntro.
    set (I := fun (N' : uk_names Σ) (Hpq : ukn_pay N' = Q) =>
                file_iface gf r Heq N' (echo_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                  (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
                  (echo_stub_close N') (echo_stub_exit N') γreg [0%nat] w0 q s Hw0
                  U (PA sb) LK
                  (LINKS_pers := union_links_persistent ug)
                  (union_links_gl_w_at ug sb) (union_links_gl_blk_at ug sb)
                  (union_links_gl_taint_at ug sb)).
    iPoseProof (echo_image_entry_env_c ws M s0 t gb sts cw cs pidv Q
                  (own γreg (fif_pool ∅ w0)
                   ∗ (gwc_blk U (PA sb) (S gen_id) v I0 0%nat 0%nat ∗ fdq r q s ∗ F))%I
                  I E {[0%nat]}
                  Hline Himg Hbytes Hfdl (echo_conforms ws _ Hne)
                  (echo_tree_safe _ _) (fif_dp0 [0%nat] eq_refl)
                  with "[] Hnpw Hdep") as "#He".
    { iIntros "!>" (N' Hpq) "Hstd Hcwd (Hpool & Hb & Hdq & HF)".
      (* the exit wand: the drained console's post at code 0 *)
      iAssert (fif_exit_k gf r N' γreg [0%nat] w0 q s U (PA sb) LK)%I
        with "[HF]" as "Hk".
      { iApply (fif_exit_k_cons_g gf r N' γreg [0%nat] w0 q s U (PA sb) LK [0%nat] v I0 F
                  eq_refl eq_refl eq_refl with "[] HF").
        iIntros "!>" (a) "%Ha Hpost Hdq HF".
        apply elem_of_list_singleton in Ha as ->.
        rewrite Hpq. iApply ("HQ" with "Hpost Hdq HF"). }
      iApply (fif_env_res_g gf r Heq N' (echo_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
                (echo_stub_close N') (echo_stub_exit N') γreg [0%nat] w0 q s Hw0
                U (PA sb) LK (LINKS_pers := union_links_persistent ug)
                (union_links_gl_w_at ug sb) (union_links_gl_blk_at ug sb)
                (union_links_gl_taint_at ug sb)
                E (take NSTD sts) eq_refl
                ltac:(cbn [E cons_env pe_fd]; intros fd d; rewrite lookup_singleton_Some;
                      intros [_ <-]; reflexivity)
                ltac:(cbn [E cons_env pe_fd]; intros fd d; rewrite lookup_singleton_Some;
                      intros [<- _]; split; [unfold NSTD; lia | by exists rb])
                ltac:(cbn [E cons_env pe_fd]; intros fd d; rewrite lookup_singleton_Some;
                      unfold NOFILE; intros [<- _]; lia)
                ltac:(discriminate)
                ltac:(intros; reflexivity)
                ltac:(cbn [E cons_env pe_paths]; intros p Hp; by apply elem_of_nil in Hp)
                ltac:(cbn [E cons_env pe_files]; apply fif_files_f)
                with "Hstd [Hcwd] Hk [] [Hdq] Hpool [Hb]").
      - by rewrite Hcw.
      - rewrite /fif_env. iFrame "Hbr Hkc Hinv". iSplitR; [| rewrite /fif_cred Hrd; by iExists jo].
        iIntros "!> HT". rewrite Hpq. iApply ("HQt" with "HT").
      - rewrite /fif_dq Hrd. iExact "Hdq".
      - iIntros "Htk". cbn [E cons_env pe_dev]. case_decide as Hc0; [| done]. simpl.
        iExists v, I0, [0%nat]. iFrame "Htk".
        iApply (uecho_lend ug sb v I0 ws Hfl Hshort with "Hlk Hpin Hb"). }
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] [%] Hmp [Hpool HPay]");
      [ exact Hok' | exact Hcw' | exact Hlz | exact Hscw | exact Hch | exact Hpid | exact Hargs | ].
    iFrame "Hpool HPay".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  cat f                                                               *)
  (* ------------------------------------------------------------------- *)
  (* [UkFileEntries.cat_image_entry_env_f_c] at the positional file name *)
  Lemma ucat_image_entry_env_c (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ)
      {Dp : list nat}
      (I : forall N' : uk_names Σ, ukn_pay N' = Q -> ep_ifaceP (Dp := Dp) N' (cat_prog N'))
      (E : penv) (ds : gset nat) :
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    length ws = 2%nat ->
    UkShEcho.echo_alen ws 1%nat = length FsImgCheck.fname_f ->
    (forall j : nat, (j < length FsImgCheck.fname_f)%nat ->
       wl_line ws !!! (UkShEcho.echo_off ws 1%nat + j)%nat
       = FsImgCheck.fname_f !!! j) ->
    conforms E (cat_tree [sb "cat"; FsImgCheck.fname_f]) ->
    safe_fds (dom (pe_fd E)) (cat_tree [sb "cat"; FsImgCheck.fname_f]) ->
    dp_in Dp ds ->
    □ (∀ (N' : uk_names Σ) (Hpq : ukn_pay N' = Q),
         UserFd.ustd (ukn_fd N') (take NSTD sts) -∗
         UserCwd.ucwd (ukn_cwd N') cw -∗
         Pay -∗
         env_res N' (cat_prog N') (I N' Hpq) E ds) -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw ProcDefs.secc_all cs pidv Q Pay uslot.
  Proof using .
    intros Hok Himg Hbytes Hfdl Hws2 Halen Hfname Hc Hs Hdp.
    assert (Htail : cat_tree ws = cat_tree [sb "cat"; FsImgCheck.fname_f]).
    { apply cat_tree_tail. rewrite (ucat_f_tail ws Hws2 Halen Hfname). reflexivity. }
    rewrite <- Htail in Hc, Hs.
    iIntros "#Henv #Hnpw #Hdep".
    iApply (cat_image_entry_env_c ws Mn sv t gn sts cw cs pidv Q Pay I E ds
              Hok Himg Hbytes Hfdl Hc Hs Hdp with "Henv Hnpw Hdep").
  Qed.

  (* THE ENTRY: cat at the union record.  The lend is the round's cursor
     at the block's first byte (the credential opened at [sb]), sh's deed
     fraction and a frame; the exit hands the round's post at the code
     the drained console names, the deed and the frame. *)
  Lemma ucat_image_entry (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (v : era_pins) (ps0 cs0 : list nat) (sq : fstate) (I0 : list (bv 8)) (P : nat)
      (r : file_names) (q : Qp) (s : dst)
      (rb rb2 : bool) (jo : option Z) (Q : Z -> iProp Σ) (F : iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    lm_wr_blk_t U ps0 cs0 sq I0 P ->
    lm_line_at U I0 = LCat_f ->
    lm_upto U cs0 sq (bodies_of I0) (nlines I0 - 1) = dst_content s ->
    (forall (i : Z) (bs : list (bv 8)), s = Some (i, bs) ->
       (Z.of_nat (length bs) < 2 ^ 31)%Z) ->
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    length ws = 2%nat ->
    UkShEcho.echo_alen ws 1%nat = length FsImgCheck.fname_f ->
    (forall j : nat, (j < length FsImgCheck.fname_f)%nat ->
       wl_line ws !!! (UkShEcho.echo_off ws 1%nat + j)%nat
       = FsImgCheck.fname_f !!! j) ->
    cw = FsImg.ROOTINO ->
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    □ (app_taint -∗ UT) -∗ □ (UT -∗ app_taint) -∗
    □ (∀ a : nat, ⌜a ∈ [ualt_code (UR RCRan); ualt_code (UR RCNoOpen)]⌝ -∗
         gwc_post U (PA sq) (S gen_id) v I0 a -∗ fdq r q s -∗ F -∗ Q (-1)) -∗
    □ (UT -∗ Q (-1)) -∗
    file_cons_cred c r jo -∗
    app_inv fsc_fs -∗
    era_pin (fgn_echo gf) (S gen_id) v -∗
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw ProcDefs.secc_all cs pidv Q
      (cons_cur U (PA sq) v ps0 cs0 sq I0 P 0%nat 0%nat ∗ fdq r q s ∗ F) uslot.
  Proof using Hcons fifRegG0 ufdG0.
    intros HQc Heq Hwb Hfl Htie Hshort Hok Himg Hbytes Hfdl Hws2 Halen Hfname Hcw Hl1 Hl2.
    iIntros "#Hbr #Hkc #HQ #HQt #Hmade #Hinv #Hpin #Hnpw #Hdep".
    iPoseProof (union_links_holds ug Hcons) as "#Hlk".
    assert (Hs : cons_short (ucat_alts (snd <$> s))).
    { unfold cons_short. destruct s as [[i bs] |].
      - cbn [ucat_alts fmap option_fmap option_map snd].
        constructor; [exact (Hshort i bs eq_refl) |]. constructor; [| constructor].
        cbv beta. rewrite fif_cat_dg_open. vm_compute. reflexivity.
      - cbn [ucat_alts fmap option_fmap option_map].
        constructor; [| constructor]. cbv beta. rewrite fif_cat_dg_open. vm_compute. reflexivity. }
    assert (Hconf : conforms (cat_env0 (ucat_alts (snd <$> s)) (fif_files (snd <$> s))
                                [FileDisc.fname_f])
                      (cat_tree [sb "cat"; FsImgCheck.fname_f])).
    { rewrite -fif_fname_img. destruct s as [[i bs] |].
      - cbn [ucat_alts fmap option_fmap option_map snd].
        apply cat_file_conforms. exact (fif_files_f (Some bs)).
      - cbn [ucat_alts fmap option_fmap option_map].
        apply cat_file_absent_conforms. exact (fif_files_f None). }
    set (C := [ualt_code (UR RCRan); ualt_code (UR RCNoOpen)]).
    set (w0 := fun _ : nat => FDCons v I0 C).
    assert (Hw0 : forall d, d ∈ [0%nat] -> forall i γo, w0 d <> FDIn false i γo)
      by (intros; discriminate).
    assert (Hrd : fif_wr [0%nat] w0 = false) by reflexivity.
    rewrite /image_entry.
    iIntros "!>" (na alen afun W') "%Hok' %Hcw' %Hlz %Hscw %Hch %Hpid %Hargs Hmp HPay".
    iApply uslot_bupd.
    iMod (fif_reg_alloc w0) as (γreg) "Hpool". iModIntro.
    set (I := fun (N' : uk_names Σ) (Hpq : ukn_pay N' = Q) =>
                file_iface gf r Heq N' (cat_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                  (cat_stub_read N') (cat_stub_write N') (cat_stub_open N')
                  (cat_stub_close N') (cat_stub_exit N') γreg [0%nat] w0 q s Hw0
                  U (PA sq) LK
                  (LINKS_pers := union_links_persistent ug)
                  (union_links_gl_w_at ug sq) (union_links_gl_blk_at ug sq)
                  (union_links_gl_taint_at ug sq)).
    iPoseProof (ucat_image_entry_env_c ws Mn sv t gn sts cw cs pidv Q
                  (own γreg (fif_pool ∅ w0)
                   ∗ (cons_cur U (PA sq) v ps0 cs0 sq I0 P 0%nat 0%nat ∗ fdq r q s ∗ F))%I
                  I (cat_env0 (ucat_alts (snd <$> s)) (fif_files (snd <$> s))
                       [FileDisc.fname_f]) {[0%nat]}
                  Hok Himg Hbytes Hfdl Hws2 Halen Hfname Hconf
                  (cat_tree_safe _ _) (fif_dp0 [0%nat] eq_refl)
                  with "[] Hnpw Hdep") as "#He".
    { iIntros "!>" (N' Hpq) "Hstd Hcwd (Hpool & Hc & Hdq & HF)".
      destruct (fif_cat_env_pure w0 (take NSTD sts) rb rb2 v I0 _ (ucat_alts (snd <$> s))
                  (fif_files (snd <$> s)) eq_refl Hl1 Hl2) as (Hd0 & Hrow & Hbnd).
      iAssert (fif_exit_k gf r N' γreg [0%nat] w0 q s U (PA sq) LK)%I
        with "[HF]" as "Hk".
      { iApply (fif_exit_k_cons_g gf r N' γreg [0%nat] w0 q s U (PA sq) LK C v I0 F
                  eq_refl eq_refl eq_refl with "[] HF").
        iIntros "!>" (a) "%Ha Hpost Hdq HF".
        rewrite Hpq. iApply ("HQ" $! a with "[%] Hpost Hdq HF"). exact Ha. }
      iApply (fif_env_res_g gf r Heq N' (cat_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                (cat_stub_read N') (cat_stub_write N') (cat_stub_open N')
                (cat_stub_close N') (cat_stub_exit N') γreg [0%nat] w0 q s Hw0
                U (PA sq) LK (LINKS_pers := union_links_persistent ug)
                (union_links_gl_w_at ug sq) (union_links_gl_blk_at ug sq)
                (union_links_gl_taint_at ug sq)
                (cat_env0 (ucat_alts (snd <$> s)) (fif_files (snd <$> s))
                   [FileDisc.fname_f])
                (take NSTD sts) eq_refl Hd0 Hrow Hbnd ltac:(discriminate)
                ltac:(intros; reflexivity)
                ltac:(cbn [cat_env0 pe_paths]; intros p; rewrite elem_of_list_singleton;
                      intros ->; split; [done | exact Hrd])
                ltac:(cbn [cat_env0 pe_files]; apply fif_files_f)
                with "Hstd [Hcwd] Hk [] [Hdq] Hpool [Hc]").
      - by rewrite Hcw.
      - rewrite /fif_env. iFrame "Hbr Hkc Hinv". iSplitR; [| rewrite /fif_cred Hrd; by iExists jo].
        iIntros "!> HT". rewrite Hpq. iApply ("HQt" with "HT").
      - rewrite /fif_dq Hrd. iExact "Hdq".
      - iIntros "Htk". cbn [cat_env0 pe_dev]. case_decide as Hc0; [| done]. simpl.
        iExists v, I0, C. iFrame "Htk".
        iApply (ucat_lend ug sq v ps0 cs0 I0 P (snd <$> s) Hwb Hfl
                  (eq_trans (f_equal (fun t : fstate => t !! fname_f) Htie) (dst_content_f s)) Hs
                  with "Hlk Hpin Hc"). }
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] [%] Hmp [Hpool HPay]");
      [ exact Hok' | exact Hcw' | exact Hlz | exact Hscw | exact Hch | exact Hpid | exact Hargs | ].
    iFrame "Hpool HPay".
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  echo > f                                                            *)
  (* ------------------------------------------------------------------- *)
  Lemma uefile_image_entry (sb : fstate) (ws : wordline) (M : gmap Z (bv 8))
      (s0 t : Z) (gb : nat -> bv 8) (sts : list fdstate)
      (cw : Z) (cs : gset gname) (pidv : mword 32)
      (r : file_names) (Wq : iProp Σ)
      (i : Z) (γo : gname) (rb : bool)
      (Q : Z -> iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    EchoDisc.line_ok ws ->
    UShEcho.echo_node_img ws M s0 t gb ->
    UkShEcho.echo_argv_bytes ws gb ->
    length sts = NOFILE ->
    cw = FsImg.ROOTINO ->
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO -> i <> GREP_INO ->
    □ (UEchoFile.ef_exit c r Wq i γo ws -∗ Q (-1)) -∗
    □ (app_taint -∗ UT) -∗
    □ (UT -∗ app_taint) -∗
    □ (UT -∗ Q (-1)) -∗
    app_inv fsc_fs -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64) sts
      cw ProcDefs.secc_all cs pidv Q (UEchoFile.ef_pay c r Wq i γo ws) uslot.
  Proof using fifRegG0 fileOutG0 pipeOutG0 ufdG0.
    intros HQc Heq Hline Himg Hbytes Hfdl Hcw Hl1 Hi1 Hi2 Hi3 Hi4 Hi5.
    iIntros "#HQ #Hbr #Hkc #HQt #Hinv #Hnpw #Hdep".
    pose proof (UkFileEntries.efe_drop1_ne ws Hline) as Hne.
    pose proof (UkFileEntries.efe_words_nn ws Hline) as Hnn.
    assert (Hwok : fif_out_ok i ws).
    { unfold fif_out_ok. split_and!; [exact Hi1 | exact Hi2 | exact Hi3 | exact Hi4 | exact Hi5 |].
      exact (UkFileEntries.efe_chunks_short ws Hline). }
    set (w0 := fun _ : nat => FDFile i γo ws).
    assert (Hw0 : forall d, d ∈ [0%nat] -> forall i' γo', w0 d <> FDIn false i' γo')
      by (intros; discriminate).
    assert (Hwr : fif_wr [0%nat] w0 = true) by reflexivity.
    set (E := pipe_env (DOutM (echo_chunks ws)) (fif_files (snd <$> (None : dst)))).
    rewrite /image_entry.
    iIntros "!>" (na alen afun W') "%Hok' %Hcw' %Hlz %Hscw %Hch %Hpid %Hargs Hmp HPay".
    iApply uslot_bupd.
    iMod (fif_reg_alloc w0) as (γreg) "Hpool". iModIntro.
    set (I := fun (N' : uk_names Σ) (Hpq : ukn_pay N' = Q) =>
                file_iface gf r Heq N' (echo_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                  (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
                  (echo_stub_close N') (echo_stub_exit N') γreg [0%nat] w0 1%Qp None Hw0
                  U (PA sb) LK
                  (LINKS_pers := union_links_persistent ug)
                  (union_links_gl_w_at ug sb) (union_links_gl_blk_at ug sb)
                  (union_links_gl_taint_at ug sb)).
    iPoseProof (echo_image_entry_env_c ws M s0 t gb sts cw cs pidv Q
                  (own γreg (fif_pool ∅ w0) ∗ UEchoFile.ef_pay c r Wq i γo ws)%I
                  I E {[0%nat]}
                  Hline Himg Hbytes Hfdl (echo_file_conforms ws _ Hne Hnn)
                  (echo_tree_safe _ _) (fif_dp0 [0%nat] eq_refl)
                  with "[] Hnpw Hdep") as "#He".
    { iIntros "!>" (N' Hpq) "Hstd Hcwd (Hpool & HWq & Hc)".
      iAssert (fif_exit_k gf r N' γreg [0%nat] w0 1%Qp None U (PA sb) LK)%I
        with "[HWq]" as "Hk".
      { iApply (fif_exit_k_redir_g gf r N' γreg [0%nat] w0 1%Qp None U (PA sb) LK
                  i γo ws Wq eq_refl eq_refl with "[] HWq").
        iIntros "!> Hx". rewrite Hpq. iApply ("HQ" with "Hx"). }
      iApply (fif_env_res_g gf r Heq N' (echo_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
                (echo_stub_close N') (echo_stub_exit N') γreg [0%nat] w0 1%Qp None Hw0
                U (PA sb) LK (LINKS_pers := union_links_persistent ug)
                (union_links_gl_w_at ug sb) (union_links_gl_blk_at ug sb)
                (union_links_gl_taint_at ug sb)
                E (take NSTD sts) eq_refl
                ltac:(cbn [E pipe_env pe_fd]; intros fd d; rewrite lookup_singleton_Some;
                      intros [_ <-]; reflexivity)
                ltac:(cbn [E pipe_env pe_fd]; intros fd d; rewrite lookup_singleton_Some;
                      intros [<- _]; split; [unfold NSTD; lia | by exists rb])
                ltac:(cbn [E pipe_env pe_fd]; intros fd d; rewrite lookup_singleton_Some;
                      unfold NOFILE; intros [<- _]; lia)
                ltac:(discriminate)
                ltac:(intros; reflexivity)
                ltac:(cbn [E pipe_env pe_paths]; intros p Hp; by apply elem_of_nil in Hp)
                ltac:(cbn [E pipe_env pe_files]; apply fif_files_f)
                with "Hstd [Hcwd] Hk [] [] Hpool [Hc]").
      - by rewrite Hcw.
      - rewrite /fif_env. iFrame "Hbr Hkc Hinv".
        iIntros "!> HT". rewrite Hpq. iApply ("HQt" with "HT").
      - iApply (fif_dq_wr r [0%nat] w0 1%Qp None Hwr).
      - iIntros "Htk". cbn [E pipe_env pe_dev]. case_decide as Hc0; [| done]. simpl.
        iExists i, γo, ws. iFrame "Htk". iExists 0%nat.
        iSplit; [done |]. iSplit; [iPureIntro; exact Hwok |].
        rewrite /file_out.
        iApply (UEchoFile.efany_of c r i γo ws 0%nat [] ltac:(constructor) with "Hc"). }
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] [%] Hmp [Hpool HPay]");
      [ exact Hok' | exact Hcw' | exact Hlz | exact Hscw | exact Hch | exact Hpid | exact Hargs | ].
    iFrame "Hpool HPay".
  Qed.
End UkUnionEntries.
