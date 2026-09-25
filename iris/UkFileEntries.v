(* ===================================================================== *)
(* UkFileEntries.v -- THE FILE APPLICATION'S PROGRAM ENTRIES FROM THE     *)
(* TREE ROUTE (program-specs cut 5, lane E): the entries the round        *)
(* consumes, reproduced as corollaries of the entries at a handler        *)
(* parameter ([UkTreeEntry]) at the file application's instance          *)
(* ([UkFileIface.file_iface]) and its exit wand ([fif_exit_k]).           *)
(*                                                                        *)
(* Design: claude-notes/design/program-specs.md SS3.4e.  Nothing here is  *)
(* consumed yet; the round still applies the landed entries.              *)
(*                                                                        *)
(* THE INTERFACE AT A CONSTANT PAYLOAD.  [file_iface] exists only at a   *)
(* record whose payload is status-independent (its [ukn_const N] binder: *)
(* the free handler and the exit spend the payload at the kill status),  *)
(* so the entries are [UkTreeEntry]'s [_c] forms, whose interface reads   *)
(* the pay fact, and the record's constancy is [ukn_const_of_eq] off it   *)
(* and the constancy of [Q] every landed entry states.                    *)
(*                                                                        *)
(* THE REGISTRY IS BORN AT THE ENTRY.  [file_iface] is indexed by its    *)
(* registry's name, and nothing the round lends carries one, so each      *)
(* corollary allocates it inside the slot ([UexecRet.uslot_bupd]) and     *)
(* hands its whole pool to the environment beside the landed payment.    *)
(* That is the one CLASS the statements gain ([fifRegG]).                 *)
(*                                                                        *)
(* WHAT IS HERE: cat f at the landed statement plus two pure facts      *)
(* (section 2); echo at the console at the file application's record     *)
(* (section 3: the landed entry is generic in the era's link record, and *)
(* the exit glue has to hand the round's deed back); and echo > f at the  *)
(* instance's WRITE MODE, where the core holds no deed (section 4, lane   *)
(* DEED-SPLIT).                                                           *)
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
Require Import ProcGeom.              (* [NOFILE] *)
Require Import UserPerm UexecSlot UexecRet UexecSG.
Require Import UserHeap UkRun.
Require Import UserFd UserCwd.
Require Import ChildTok.
Require Import ElfFile ElfUser.
Require Import UmodeArith UmodeAbi.
Require Import SpecKexec.             (* [kexec_image_ok] and its readings *)
Require Import ExecEntry.             (* [image_entry] / [image_entry_of_at] *)
Require Import UexecExecInst.         (* THE INSTANCES: [uexecSG_xv6] *)
Require Import UkAbi.                 (* [uka_argc] *)
Require Import UCodeEcho UCodeCat.
From User Require EchoInstrs EchoData.
Require Import UEchoKernel.           (* [uvis_sp] / [uvis_av] / [uvis_argc], [echo_args] *)
Require Import UShKernel.             (* [uimg_sub_union_l] *)
Require Import LineWords EchoDisc ExecWords.
Require Import UkShEcho.              (* [echo_argv_bytes] / [echo_alen] / [echo_off] *)
Require Import UShEcho.               (* echo's key geometry *)
Require Import UEchoOut.              (* [echo_out_argv] *)
Require Import UShEchoOut.            (* [echo_out_argv_of_image] *)
Require Import UShCat.                (* cat's key geometry and [cat_entry_run] *)
Require Import FsImgCheck.            (* [fname_f] *)
Require Import ProgTree UkTree UkStub UkHandler.
Require Import UkEcho UkEchoTree.
Require Import UkCatMain UkCatTree.
Require Import UkTreeEntry.           (* the argv bridges, the .rodata fact *)
Require Import CtxIdDefs.
Require User.EchoSyms User.CatSyms.
Require Import AppCfg AppInv AppFile AppFileCons FileOpen FsCfg FsImg.
Require Import EchoOut.               (* [ps_lb] / [cs_lb] and their comparisons *)
Require Import FileState FileDisc FileOut.
Require Import LineModel LineModelInst LineModelLinks.
Require Import FileLinks FileLinksLine FileLinkGen FileHooks.
Require Import GenLinksLine.          (* [gwc_blk] / [gwc_post] *)
Require Import ConsoleInv.             (* [CONSOLE] *)
Require Import UkConsOut ProgTreeFile.
Require Import UCatOut UCatLend.      (* [cch], [catq_cat], [cat_lend] *)
Require Import FsInitPin FsShPin FsEchoPin FsCatPin.   (* the four image inodes *)
Require Import UkFileDev FileWrite UEchoFile.         (* [file_out], [ef_pay], [ef_exit] *)
Require Import UkFileIface.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  0.  THE ROUND'S CURSOR IS PINNED BY ITS BOUNDS (pure)                  *)
(* ===================================================================== *)

(* two block-first cursors of one input whose prologue lists line up are
   the same cursor: the block pins the prologue's settled rounds from
   below ([lm_pro_pin]) and its tail from above ([lm_wr_tail]) *)
Lemma blk_t_ps_app (M : lmodel) (ps z cs : list nat) (s : lm_st M) (I : list (bv 8))
    (P P' : nat) :
  lm_wr_blk_t M ps cs s I P -> lm_wr_blk_t M (ps ++ z) cs s I P' -> z = [].
Proof.
  intros [Hw _] [_ Ht].
  pose proof (lm_wr_blk_started M ps cs s I P Hw) as Hst.
  destruct Hw as (Hpin & _).
  assert (Hk : (lm_pro_idx M cs (length cs) < pro_rounds ps)%nat)
    by (apply Hpin; rewrite Hst; lia).
  unfold lm_wr_tail in Ht.
  rewrite (pro_from_app_le (S (lm_pro_idx M cs (length cs))) ps z ltac:(lia)) in Ht.
  by apply app_eq_nil in Ht as [_ Hz].
Qed.

Lemma blk_t_pins (M : lmodel) (ps cs ps0 cs0 t : list nat) (s : lm_st M)
    (I : list (bv 8)) (pos P : nat) :
  lm_wr_blk_t M ps cs s I pos -> lm_wr_blk_t M ps0 cs0 s I P ->
  (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
  (cs ++ t `prefix_of` cs0 \/ cs0 `prefix_of` cs ++ t) ->
  ps = ps0 /\ cs = cs0 /\ pos = P.
Proof.
  intros Hw Hw0 Hps Hcs.
  pose proof (lm_wr_blk_lines M ps cs s I pos (proj1 Hw)) as Hn.
  pose proof (lm_wr_blk_lines M ps0 cs0 s I P (proj1 Hw0)) as Hn0.
  assert (Hlen : length cs = length cs0) by lia.
  assert (Hc : cs = cs0).
  { destruct Hcs as [[k Hk] | [k Hk]].
    - assert (H1 : take (length cs) cs0 = cs)
        by (rewrite Hk -app_assoc take_app_length; done).
      rewrite Hlen take_ge in H1; [by symmetry | lia].
    - assert (H1 : take (length cs) (cs ++ t) = take (length cs) (cs0 ++ k))
        by (by rewrite Hk).
      rewrite take_app_length Hlen take_app_length in H1. exact H1. }
  subst cs0. clear Hcs Hlen Hn0.
  assert (Hp : ps = ps0).
  { destruct Hps as [[z ->] | [z ->]].
    - by rewrite (blk_t_ps_app M ps z cs s I pos P Hw Hw0) app_nil_r.
    - by rewrite (blk_t_ps_app M ps0 z cs s I P pos Hw0 Hw) app_nil_r. }
  subst ps0. split; [done | split; [done |]].
  destruct Hw as [(_ & _ & _ & H1) _]. destruct Hw0 as [(_ & _ & _ & H2) _]. lia.
Qed.

(* ===================================================================== *)
(*  1.  cat's ENTRY AT THE LINE `cat f`, IN THE [_c] FORM                  *)
(* ===================================================================== *)

Section UkFileEntriesTree.
  (* [UkTreeEntry]'s binders, verbatim *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.

  (* [UkTreeEntry.cat_image_entry_env_f]'s shape over
     [UkTreeEntry.cat_image_entry_env_c] *)
  Lemma cat_image_entry_env_f_c (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
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
    UkShEcho.echo_alen ws 1%nat = 1%nat ->
    (forall j : nat, (j < 1)%nat ->
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
      cw cs pidv Q Pay uslot.
  Proof using .
    intros Hok Himg Hbytes Hfdl Hws2 Halen1 Hfname Hc Hs Hdp.
    assert (Htail : cat_tree ws = cat_tree [sb "cat"; FsImgCheck.fname_f]).
    { apply cat_tree_tail. rewrite (cat_f_tail ws Hws2 Halen1 Hfname). reflexivity. }
    rewrite <- Htail in Hc, Hs.
    iIntros "#Henv #Hnpw #Hdep".
    iApply (cat_image_entry_env_c ws Mn sv t gn sts cw cs pidv Q Pay I E ds
              Hok Himg Hbytes Hfdl Hc Hs Hdp with "Henv Hnpw Hdep").
  Qed.

End UkFileEntriesTree.

(* ===================================================================== *)
(*  2.  cat f FROM THE TREE                                                *)
(* ===================================================================== *)

Section UkFileEntriesCat.
  (* cat's entry binders (the deleted [UCatKernel]'s), and the registry's
     class *)
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context `{!fifRegG Σ}.
  Context (g : file_gn).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).

  Local Instance fe_cat_code_persistent (N : uk_names Σ) :
    Persistent (up_code (cat_prog N)).
  Proof using . simpl. apply _. Qed.

  (* the round's cursor, pinned: what the drained console hands back at
     ANY block-first cursor of the round is the payload at the lend's *)
  Lemma cch_pins (v : era_pins) (ps cs ps0 cs0 : list nat) (s0 : fstate)
      (I0 : list (bv 8)) (a pos P p : nat) :
    lm_wr_blk_t file_lm ps cs s0 I0 pos -> lm_wr_blk_t file_lm ps0 cs0 s0 I0 P ->
    ps_lb v ps -∗ ps_lb v ps0 -∗ cs_lb v (UCatOut.catcs cs a p) -∗ cs_lb v cs0 -∗
    ⌜ps = ps0 /\ cs = cs0 /\ pos = P⌝.
  Proof using .
    intros Hw Hw0. iIntros "#Hps #Hps0 #Hcs #Hcs0".
    iDestruct (ps_lb_cmp with "Hps Hps0") as %Hpc.
    iDestruct (cs_lb_cmp with "Hcs Hcs0") as %Hcc.
    iPureIntro.
    assert (Ht : exists t, UCatOut.catcs cs a p = cs ++ t).
    { destruct p; [exists []; by rewrite app_nil_r | by exists [a]]. }
    destruct Ht as [t Ht]. rewrite Ht in Hcc.
    exact (blk_t_pins file_lm ps cs ps0 cs0 t s0 I0 pos P Hw Hw0 Hpc Hcc).
  Qed.

  Lemma catq_cat_pin (v : era_pins) (vf : file_era) (ps cs ps0 cs0 : list nat)
      (s0 : fstate) (I0 : list (bv 8)) (pos P : nat)
      (r : file_names) (q : Qp) (s : dst) (x : Z) :
    lm_wr_blk_t file_lm ps cs s0 I0 pos -> lm_wr_blk_t file_lm ps0 cs0 s0 I0 P ->
    ps_lb v ps0 -∗ cs_lb v cs0 -∗
    UCatLend.catq_cat g (fgn_cl g) r q s v vf ps cs s0 I0 pos x -∗
    UCatLend.catq_cat g (fgn_cl g) r q s v vf ps0 cs0 s0 I0 P x.
  Proof using .
    intros Hw Hw0. iIntros "#Hps0 #Hcs0 [Hf Hd]".
    rewrite /UCatLend.catq_cat. iFrame "Hd".
    rewrite /UCatOut.catq_filed /UCatOut.cch.
    iDestruct "Hf" as "[[(Ht & #Hps & #Hcs & #HI & #Hf0) | #HT] | [(Ht & #Hps & #Hcs & #HI & #Hf0) | #HT]]".
    - iDestruct (cch_pins v ps cs ps0 cs0 s0 I0 _ pos P _ Hw Hw0 with "Hps Hps0 Hcs Hcs0")
        as %(-> & -> & ->).
      iLeft. iLeft. iFrame "Ht Hps Hcs HI Hf0".
    - iLeft. by iRight.
    - iDestruct (cch_pins v ps cs ps0 cs0 s0 I0 _ pos P _ Hw Hw0 with "Hps Hps0 Hcs Hcs0")
        as %(-> & -> & ->).
      iRight. iLeft. iFrame "Ht Hps Hcs HI Hf0".
    - iRight. by iRight.
  Qed.

  (* a tainted round's exit wand: the payload off the taint in the core *)
  Lemma fif_exit_k_taint (r : file_names) (N : uk_names Σ) (γreg : gname)
      (D0 : list nat) (w0 : nat -> fdev) (qf : Qp) (sf : dst) :
    file_taint (fgn_cl g) -∗ fif_exit_k g r N γreg D0 w0 qf sf file_lm (file_params g) (file_links g).
  Proof using .
    iIntros "#HT". rewrite /fif_exit_k.
    iIntros (fdm l vs w files paths dv ds) "_ _ Hcore _ _".
    iDestruct "Hcore" as "(_ & _ & _ & _ & _ & _ & _ & #(_ & _ & Hpay & _))".
    iApply ("Hpay" with "HT").
  Qed.

  (* THE ONE ENTRY, at the environment the round lends, at either state of
     `f`: [alts] is what the console owes, and the lend's cursor is turned
     into the console device by [lendw] ([fif_cat_lend_some/none]) *)
  Lemma cat_entry_of_tree_at (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (v : era_pins) (vf : file_era) (ps0 cs0 : list nat) (s0 : fstate)
      (I0 : list (bv 8)) (P : nat)
      (r : file_names) (q : Qp) (s : dst)
      (rb rb2 : bool) (jo : option Z) (Q : Z -> iProp Σ) (F : iProp Σ)
      (alts : list (list (bv 8))) :
    (forall x y : Z, Q x = Q y) ->
    file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r ->
    lm_wr_blk_t file_lm ps0 cs0 s0 I0 P ->
    fline I0 = LCat ->
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    length ws = 2%nat ->
    UkShEcho.echo_alen ws 1%nat = 1%nat ->
    (forall j : nat, (j < 1)%nat ->
       wl_line ws !!! (UkShEcho.echo_off ws 1%nat + j)%nat
       = FsImgCheck.fname_f !!! j) ->
    cw = FsImg.ROOTINO ->
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    conforms (cat_env0 alts (fif_files (snd <$> s)) [FileDisc.fname_f])
      (cat_tree [sb "cat"; FsImgCheck.fname_f]) ->
    □ (UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 0%nat -∗
       cons_dev_atc file_lm (file_params g) (file_links g)
         [ralt_enc RCRan; ralt_enc RCNoOpen] v I0 alts) -∗
    □ (app_taint -∗ file_taint (fgn_cl g)) -∗ □ (file_taint (fgn_cl g) -∗ app_taint) -∗
    □ (UCatLend.catq_cat g (fgn_cl g) r q s v vf ps0 cs0 s0 I0 P (-1) -∗ F -∗ Q (-1)) -∗
    □ (file_taint (fgn_cl g) -∗ Q (-1)) -∗
    file_cons_cred (fgn_cl g) r jo -∗
    app_inv fsc_fs -∗
    file_era_pin g (S gen_id) vf -∗
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q
      (UCatLend.cat_lend g r q s v vf ps0 cs0 s0 I0 P ∗ F) uslot.
  Proof using Hcons fifRegG0 ufdG0.
    intros HQc Heq Hwb Hfl Hok Himg Hbytes Hfdl Hws2 Halen1 Hfname Hcw Hl1 Hl2 Hconf.
    iIntros "#Hlendw #Hbr #Hkc #HQ #HQt #Hmade #Hinv #Hfp #Hnpw #Hdep".
    set (w0 := fun _ : nat => FDCons v I0 [ralt_enc RCRan; ralt_enc RCNoOpen]).
    assert (Hw0 : forall d, d ∈ [0%nat] -> forall i γo, w0 d <> FDIn false i γo)
      by (intros; discriminate).
    assert (Hrd : fif_wr [0%nat] w0 = false) by reflexivity.
    rewrite /image_entry.
    iIntros "!>" (na alen afun W') "%Hok' %Hcw' %Hlz %Hch %Hpid %Hargs Hmp HPay".
    iApply uslot_bupd.
    iMod (fif_reg_alloc w0) as (γreg) "Hpool". iModIntro.
    set (I := fun (N' : uk_names Σ) (Hpq : ukn_pay N' = Q) =>
                file_iface g r Heq N' (cat_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                  (cat_stub_read N') (cat_stub_write N') (cat_stub_open N')
                  (cat_stub_close N') (cat_stub_exit N') γreg [0%nat] w0 q s Hw0
                  file_lm (file_params g) (file_links g)
                  (LINKS_pers := file_links_persistent g)
                  (file_links_gl_w g) (file_links_gl_blk g) (file_links_gl_taint g)).
    iPoseProof (cat_image_entry_env_f_c ws Mn sv t gn sts cw cs pidv Q
                  (own γreg (fif_pool ∅ w0)
                   ∗ (UCatLend.cat_lend g r q s v vf ps0 cs0 s0 I0 P ∗ F))%I
                  I (cat_env0 alts (fif_files (snd <$> s)) [FileDisc.fname_f]) {[0%nat]}
                  Hok Himg Hbytes Hfdl Hws2 Halen1 Hfname Hconf
                  (cat_tree_safe _ _) (fif_dp0 [0%nat] eq_refl)
                  with "[] Hnpw Hdep") as "#He".
    { iIntros "!>" (N' Hpq) "Hstd Hcwd (Hpool & (Hdq & Hcch) & HF)".
      destruct (fif_cat_env_pure w0 (take NSTD sts) rb rb2 v I0 _ alts
                  (fif_files (snd <$> s)) eq_refl Hl1 Hl2) as (Hd0 & Hrow & Hbnd).
      (* the exit wand, off the lend's bounds or the taint *)
      iAssert (fif_exit_k g r N' γreg [0%nat] w0 q s file_lm (file_params g) (file_links g) ∗ UCatOut.cch g v vf ps0 cs0 s0 I0
                 (ralt_enc RCRan) P 0%nat)%I with "[Hcch HF]" as "[Hk Hcch]".
      { rewrite {2}/UCatOut.cch.
        iDestruct "Hcch" as "[(Ht & #Hps0 & #Hcs0 & #HI & #Hf0) | #HT]"; last first.
        { iSplitL; [iApply (fif_exit_k_taint with "HT") | by iRight]. }
        iSplitL "HF"; [| iLeft; iFrame "Ht Hps0 Hcs0 HI Hf0"].
        iApply (fif_exit_k_cat g r N' γreg [0%nat] w0 q s v vf I0 s0 F eq_refl eq_refl Hfl
                  with "Hfp Hf0 [] HF").
        iIntros "!>" (ps cs1 pos) "%Hw Hq HF".
        iDestruct (catq_cat_pin with "Hps0 Hcs0 Hq") as "Hq"; [exact Hw | exact Hwb |].
        rewrite Hpq. iApply ("HQ" with "Hq HF"). }
      iApply (fif_env_res g r Heq Hcons N' (cat_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                (cat_stub_read N') (cat_stub_write N') (cat_stub_open N')
                (cat_stub_close N') (cat_stub_exit N') γreg [0%nat] w0 q s Hw0
                (cat_env0 alts (fif_files (snd <$> s)) [FileDisc.fname_f])
                (take NSTD sts) eq_refl Hd0 Hrow Hbnd ltac:(discriminate)
                ltac:(intros; reflexivity)
                ltac:(cbn [cat_env0 pe_paths]; intros p; rewrite elem_of_list_singleton;
                      intros ->; split; [done | exact Hrd])
                ltac:(cbn [cat_env0 pe_files]; apply fif_files_f)
                with "Hstd [Hcwd] Hk [] [Hdq] Hpool [Hcch]").
      - by rewrite Hcw.
      - rewrite /fif_env. iFrame "Hbr Hkc Hinv". iSplitR; [| rewrite /fif_cred Hrd; by iExists jo].
        iIntros "!> HT". rewrite Hpq. iApply ("HQt" with "HT").
      - rewrite /fif_dq Hrd. iExact "Hdq".
      - iIntros "Htk". cbn [cat_env0 pe_dev]. case_decide as Hc0; [| done]. simpl.
        iExists v, I0, _. iFrame "Htk". iApply ("Hlendw" with "Hcch"). }
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp [Hpool HPay]");
      [ exact Hok' | exact Hcw' | exact Hlz | exact Hch | exact Hpid | exact Hargs | ].
    iFrame "Hpool HPay".
  Qed.

  (* THE COROLLARY: the statement of the per-program cat entry the file
     sweep deleted ([UCatKernel.cat_child_of_entry]), with the two facts
     the tree route needs that the landed entry never asks for:
     the round's block cursor's TAIL ([wr_tail_f], which the round holds as the second half of its
     [wr_blk_t_f]) and the content's C-int bound ([UkConsOut.cons_short]:
     the kernel reads a console write's count as an int) *)
  Lemma cat_child_of_entry_of_tree (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (v : era_pins) (vf : file_era) (ps0 cs0 : list nat) (s0 : fstate)
      (I0 : list (bv 8)) (P : nat)
      (c : file_fixed) (r : file_names) (q : Qp) (s : dst)
      (rb rb2 : bool) (jo : option Z) (Q : Z -> iProp Σ) (F : iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    c = fgn_cl g ->
    UCatOut.cat_stage ps0 cs0 s0 I0 P ->
    cat_tie cs0 s0 I0 s ->
    exec_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    length ws = 2%nat ->
    UkShEcho.echo_alen ws 1%nat = 1%nat ->
    (forall j : nat, (j < 1)%nat ->
       wl_line ws !!! (UkShEcho.echo_off ws 1%nat + j)%nat
       = FsImgCheck.fname_f !!! j) ->
    cw = FsImg.ROOTINO ->
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    fd_lowest_closed (take NSTD sts) = None ->
    (* THE TWO FACTS THE TREE ROUTE ADDS *)
    wr_tail_f ps0 cs0 ->
    (forall (i : Z) (bs : list (bv 8)), s = Some (i, bs) ->
       (Z.of_nat (length bs) < 2 ^ 31)%Z) ->
    □ (app_taint -∗ file_taint c) -∗ □ (file_taint c -∗ app_taint) -∗
    □ (UCatLend.catq_cat g c r q s v vf ps0 cs0 s0 I0 P (-1) -∗ F -∗ Q (-1)) -∗
    □ (file_taint c -∗ Q (-1)) -∗
    file_cons_cred c r jo -∗
    app_inv fsc_fs -∗
    era_pin (fgn_echo g) (S gen_id) v -∗
    file_era_pin g (S gen_id) vf -∗
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q
      (UCatLend.cat_lend g r q s v vf ps0 cs0 s0 I0 P ∗ F) uslot.
  Proof using Hcons fifRegG0 ufdG0.
    intros HQc Heq Hgc Hst Htie Hok Himg Hbytes Hfdl Hws2 Halen1 Hfname
           Hcw Hl1 Hl2 Hnone Htail Hshort.
    subst c.
    iIntros "#Hbr #Hkc #HQ #HQt #Hmade #Hinv #Hpin #Hfp #Hnpw #Hdep".
    (* the stage and its tail are the round's block cursor *)
    assert (Hwb : lm_wr_blk_t file_lm ps0 cs0 s0 I0 P).
    { rewrite -wr_blk_t_f_lm. split; [| exact Htail].
      destruct Hst as (Hr & Hn & _ & HP & Hpin0). split_and!; assumption. }
    assert (Hfl : fline I0 = LCat) by (destruct Hst as (_ & _ & Hl & _); exact Hl).
    iPoseProof (file_links_holds g Hcons) as "#Hlk".
    destruct s as [[i bs] |].
    - iApply (cat_entry_of_tree_at ws Mn sv t gn sts cw cs pidv v vf ps0 cs0 s0 I0 P
                r q (Some (i, bs)) rb rb2 jo Q F [bs; cat_dg_open FileDisc.fname_f]
                HQc Heq Hwb Hfl Hok Himg Hbytes Hfdl Hws2 Halen1 Hfname Hcw Hl1 Hl2
                with "[] Hbr Hkc HQ HQt Hmade Hinv Hfp Hnpw Hdep").
      + rewrite -fif_fname_img.
        apply cat_file_conforms. by apply fif_files_some with (i := i).
      + iIntros "!> Hc".
        iApply (fif_cat_lend_some g v vf ps0 cs0 s0 I0 P i bs Hwb Hfl Htie
                  (Hshort i bs eq_refl) with "Hlk Hpin Hfp Hc").
    - iApply (cat_entry_of_tree_at ws Mn sv t gn sts cw cs pidv v vf ps0 cs0 s0 I0 P
                r q None rb rb2 jo Q F [cat_dg_open FileDisc.fname_f]
                HQc Heq Hwb Hfl Hok Himg Hbytes Hfdl Hws2 Halen1 Hfname Hcw Hl1 Hl2
                with "[] Hbr Hkc HQ HQt Hmade Hinv Hfp Hnpw Hdep").
      + rewrite -fif_fname_img.
        apply cat_file_absent_conforms. by apply fif_files_none.
      + iIntros "!> Hc".
        iApply (fif_cat_lend_none g v vf ps0 cs0 s0 I0 P Hwb Hfl Htie
                  with "Hlk Hpin Hfp Hc").
  Qed.

End UkFileEntriesCat.

(* ===================================================================== *)
(*  3.  echo AT THE CONSOLE FROM THE TREE, at the file application        *)
(*                                                                       *)
(*  The landed entry the round runs echo at the console on is            *)
(*  [UShEchoPay.echo_slot_of_kexec_at_at] (through                        *)
(*  [sh_exec_sup_echo_wq_holds_at_D], which [UShRound.Hchild_echo] is    *)
(*  one application of), and it is GENERIC in the era's link record: no  *)
(*  application's instance can reproduce it.  What the tree route gives  *)
(*  is its image slot at the FILE application's record                   *)
(*  ([FileLinkInst.file_link_inst_at]: the lend is [gwc_blk] at the      *)
(*  state-pinned parameters, the block's end [gwc_post] there), with the *)
(*  resource that rides beside the cursor -- sh's deed fraction, the     *)
(*  round's [Hold] -- handed in and handed BACK at the exit.             *)
(*                                                                       *)
(*  The handing back is the point: the core's deed is, at this round,    *)
(*  sh's own and must come back for the round's next prompt credential.  *)
(*  So the glue passes the deed to the round's wand beside the post.      *)
(* ===================================================================== *)

Section UkFileEntriesEcho.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context `{!fifRegG Σ}.
  Context (g : file_gn).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).

  (* THE GLUE, THREE, RETURNING THE DEED: the console exit with the core's
     deed handed to the round's wand beside the post *)
  Lemma fif_exit_k_echo_cons_d (r : file_names) (N : uk_names Σ) (γreg : gname)
      (D0 : list nat) (w0 : nat -> fdev) (qf : Qp) (sf : dst)
      (v : era_pins) (vf : file_era) (I0 : list (bv 8)) (s0 : fstate)
      (C : list nat) (F : iProp Σ) :
    D0 = [0%nat] -> w0 0%nat = FDCons v I0 C ->
    file_era_pin g (S gen_id) vf -∗ f0_lb vf s0 -∗
    □ (∀ a : nat, ⌜a ∈ C⌝ -∗ ⌜exists cs, cons_adm file_lm s0 cs I0 a⌝ -∗
         gwc_post file_lm (file_params_at g s0) (S gen_id) v I0 a -∗
         fdq r qf sf -∗ F -∗ ukn_pay N (-1)) -∗
    F -∗ fif_exit_k g r N γreg D0 w0 qf sf file_lm (file_params g) (file_links g).
  Proof using .
    intros HD0 Hw. iIntros "#Hvf #Hf0 #HQ HF".
    iIntros (fdm l vs w files paths dv ds) "%Hdr %Hdom Hcore _ Hdev".
    iDestruct "Hcore" as "(_ & _ & %Hok & _ & Htoks & _ & Hdq & #(_ & _ & Hpay & _))".
    iEval (rewrite (fif_dq_rd r D0 w0 qf sf ltac:(by rewrite (fif_wr_0 D0 w0 HD0) Hw)))
      in "Hdq".
    iDestruct (fif_exit_dev0 g r γreg D0 w0 sf fdm l vs dv ds HD0 Hdr Hdom Hok
                 with "Hdev") as "(%Hd0 & %Hv0 & Hd0)".
    rewrite Hw in Hv0.
    destruct (dv 0%nat) as [alts | | cs' | | S' | | | | | | |]; simpl in Hd0; simpl;
      try (iDestruct "Hd0" as "[]").
    - iDestruct "Hd0" as (v' I' C') "[Htk Hd]".
      iDestruct (fif_toks_agree γreg vs 0%nat _ _ _ Hv0 with "Htoks Htk") as "(%Heqv & _ & _)".
      injection Heqv as <- <- <-.
      iDestruct (fif_cons_drained_post g C v vf I0 s0 alts Hd0 with "Hvf Hf0 Hd")
        as "[#HT | Hd]".
      { iApply ("Hpay" with "HT"). }
      iDestruct "Hd" as (a) "(%HaC & %Hadm & Hpost)".
      iApply ("HQ" $! a with "[%] [%] [Hpost] Hdq HF"); [exact HaC | exact Hadm |].
      iApply (gwc_post_file_at g s0 vf v I0 a with "Hvf Hf0 Hpost").
    - iDestruct "Hd0" as (i γo ws) "[Htk _]".
      iDestruct (fif_toks_agree γreg vs 0%nat _ _ _ Hv0 with "Htoks Htk") as "(%Heqv & _ & _)".
      discriminate Heqv.
    - iDestruct "Hd0" as (s i γo p) "(Htk & _)".
      iDestruct (fif_toks_agree γreg vs 0%nat _ _ _ Hv0 with "Htoks Htk") as "(%Heqv & _ & _)".
      discriminate Heqv.
  Qed.

  (* the lend at the state-pinned parameters is the lend at the era's *)
  Lemma gwc_blk_forget_at (sb : fstate) (k : nat) (v : era_pins) (I : list (bv 8))
      (a i : nat) :
    gwc_blk file_lm (file_params_at g sb) k v I a i -∗
    gwc_blk file_lm (file_params g) k v I a i.
  Proof using .
    rewrite /gwc_blk fif_gT fif_gW fif_gT_at fif_gW_at.
    iIntros "[Hb | HT]"; [iLeft | by iRight].
    iDestruct "Hb" as (ps cs s1 pos) "(%Hw & Ht & Hps & Hcs & HI & [HW _])".
    iExists ps, cs, s1, pos. by iFrame "Ht Hps Hcs HI HW".
  Qed.

  (* ...and its boot-state witness, at the round's own state *)
  Lemma gwc_blk_f0 (sb : fstate) (k : nat) (v : era_pins) (I : list (bv 8))
      (a i : nat) :
    gwc_blk file_lm (file_params_at g sb) k v I a i -∗
    file_taint (fgn_cl g) ∨ ∃ vf : file_era, file_era_pin g k vf ∗ f0_lb vf sb.
  Proof using .
    rewrite /gwc_blk fif_gT_at fif_gW_at.
    iIntros "[Hb | #HT]"; [iRight | by iLeft].
    iDestruct "Hb" as (ps cs s1 pos) "(_ & _ & _ & _ & _ & [HW %Hs])". subst s1.
    rewrite /f0w. iDestruct "HW" as "[_ HW]". iExact "HW".
  Qed.

  Local Instance fe_echo_code_persistent (N : uk_names Σ) :
    Persistent (up_code (echo_prog N)).
  Proof using . simpl. apply _. Qed.

  (* THE ENTRY: echo at the console, at the file application, from the
     tree.  The lend is the round's block credential at the block's first
     byte and sh's deed fraction beside it; what echo hands back is the
     block written up to its prompt, the deed, and the frame *)
  Lemma echo_cons_image_entry_of_tree (ws : list (list (bv 8))) (M : gmap Z (bv 8))
      (s0 t : Z) (gb : nat -> bv 8) (sts : list fdstate)
      (cw : Z) (cs : gset gname) (pidv : mword 32)
      (v : era_pins) (sb : fstate) (I0 : list (bv 8))
      (c : file_fixed) (r : file_names) (q : Qp) (s : dst)
      (rb : bool) (jo : option Z) (Q : Z -> iProp Σ) (F : iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    c = fgn_cl g ->
    EchoDisc.line_ok ws ->
    UShEcho.echo_node_img ws M s0 t gb ->
    UkShEcho.echo_argv_bytes ws gb ->
    length sts = NOFILE ->
    cw = FsImg.ROOTINO ->
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    fline I0 = LEcho ws ->
    (Z.of_nat (length (wl_line (drop 1 ws))) < 2 ^ 31)%Z ->
    □ (app_taint -∗ file_taint c) -∗ □ (file_taint c -∗ app_taint) -∗
    □ (gwc_post file_lm (file_params_at g sb) (S gen_id) v I0 0%nat -∗
       fdq r q s -∗ F -∗ Q (-1)) -∗
    □ (file_taint c -∗ Q (-1)) -∗
    file_cons_cred c r jo -∗
    app_inv fsc_fs -∗
    era_pin (fgn_echo g) (S gen_id) v -∗
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q
      (gwc_blk file_lm (file_params_at g sb) (S gen_id) v I0 0%nat 0%nat
       ∗ fdq r q s ∗ F) uslot.
  Proof using Hcons fifRegG0 ufdG0.
    intros HQc Heq Hgc Hline Himg Hbytes Hfdl Hcw Hl1 Hfl Hshort.
    subst c.
    iIntros "#Hbr #Hkc #HQ #HQt #Hmade #Hinv #Hpin #Hnpw #Hdep".
    iPoseProof (file_links_holds g Hcons) as "#Hlk".
    assert (Hne : drop 1 ws <> []).
    { pose proof (line_ok_ge2 ws Hline) as H2. intros Hd.
      apply (f_equal length) in Hd. rewrite length_drop in Hd. simpl in Hd. lia. }
    set (w0 := fun _ : nat => FDCons v I0 [0%nat]).
    assert (Hw0 : forall d, d ∈ [0%nat] -> forall i γo, w0 d <> FDIn false i γo)
      by (intros; discriminate).
    assert (Hrd : fif_wr [0%nat] w0 = false) by reflexivity.
    set (E := cons_env (wl_line (drop 1 ws)) (fif_files (snd <$> s))).
    rewrite /image_entry.
    iIntros "!>" (na alen afun W') "%Hok' %Hcw' %Hlz %Hch %Hpid %Hargs Hmp HPay".
    iApply uslot_bupd.
    iMod (fif_reg_alloc w0) as (γreg) "Hpool". iModIntro.
    set (I := fun (N' : uk_names Σ) (Hpq : ukn_pay N' = Q) =>
                file_iface g r Heq N' (echo_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                  (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
                  (echo_stub_close N') (echo_stub_exit N') γreg [0%nat] w0 q s Hw0
                  file_lm (file_params g) (file_links g)
                  (LINKS_pers := file_links_persistent g)
                  (file_links_gl_w g) (file_links_gl_blk g) (file_links_gl_taint g)).
    iPoseProof (echo_image_entry_env_c ws M s0 t gb sts cw cs pidv Q
                  (own γreg (fif_pool ∅ w0)
                   ∗ (gwc_blk file_lm (file_params_at g sb) (S gen_id) v I0 0%nat 0%nat
                      ∗ fdq r q s ∗ F))%I
                  I E {[0%nat]}
                  Hline Himg Hbytes Hfdl (echo_conforms ws _ Hne)
                  (echo_tree_safe _ _) (fif_dp0 [0%nat] eq_refl)
                  with "[] Hnpw Hdep") as "#He".
    { iIntros "!>" (N' Hpq) "Hstd Hcwd (Hpool & Hb & Hdq & HF)".
      iDestruct (gwc_blk_f0 with "Hb") as "#Hf0".
      iDestruct (gwc_blk_forget_at with "Hb") as "Hb".
      (* the exit wand, off the lend's boot-state witness or the taint *)
      iAssert (fif_exit_k g r N' γreg [0%nat] w0 q s file_lm (file_params g) (file_links g))%I with "[HF]" as "Hk".
      { iDestruct "Hf0" as "[#HT | (%vf & #Hvf & #Hf0)]".
        { iApply (fif_exit_k_taint with "HT"). }
        iApply (fif_exit_k_echo_cons_d r N' γreg [0%nat] w0 q s v vf I0 sb [0%nat] F
                  eq_refl eq_refl with "Hvf Hf0 [] HF").
        iIntros "!>" (a) "%Ha _ Hpost Hdq HF".
        apply elem_of_list_singleton in Ha as ->.
        rewrite Hpq. iApply ("HQ" with "Hpost Hdq HF"). }
      iApply (fif_env_res g r Heq Hcons N' (echo_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
                (echo_stub_close N') (echo_stub_exit N') γreg [0%nat] w0 q s Hw0
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
        iApply (fif_echo_lend g v I0 ws Hfl Hshort with "Hlk Hpin Hb"). }
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp [Hpool HPay]");
      [ exact Hok' | exact Hcw' | exact Hlz | exact Hch | exact Hpid | exact Hargs | ].
    iFrame "Hpool HPay".
  Qed.

End UkFileEntriesEcho.

(* ===================================================================== *)
(*  4.  echo > f FROM THE TREE                                             *)
(*                                                                       *)
(*  At the WRITE MODE of the instance (lane DEED-SPLIT: the entry device *)
(*  is `f` held for writing, [UkFileIface.fif_wr]) the core holds no     *)
(*  deed, so the redirect child's lend -- the era's credential [Wq] and   *)
(*  the cursor [efq] at no chunk, whose [file_wq] carries the child's     *)
(*  whole share -- is exactly what the environment needs: the cursor is  *)
(*  the write device at chunk 0, [Wq] rides in the exit wand            *)
(*  ([UkFileIface.fif_exit_k_redir]), and the core's deed and cred are    *)
(*  [emp]/[True].  The statement is the landed one's plus what the free   *)
(*  handler and the instance's core read (listed at the lemma).          *)
(* ===================================================================== *)

(* the line's pure facts the tree route reads off [line_ok] *)
Lemma efe_drop1_ne (ws : list (list (bv 8))) : EchoDisc.line_ok ws -> drop 1 ws <> [].
Proof.
  intros Hl Hd. pose proof (line_ok_ge2 ws Hl) as H2.
  apply (f_equal length) in Hd. rewrite length_drop in Hd. simpl in Hd. lia.
Qed.

Lemma efe_words_nn (ws : list (list (bv 8))) :
  EchoDisc.line_ok ws -> Forall (fun w => w <> []) (drop 1 ws).
Proof.
  intros Hl.
  pose proof (line_ok_wf ws Hl) as Hwf. unfold wl_wf in Hwf.
  apply (Forall_drop _ 1) in Hwf.
  apply (proj2 (Forall_forall (fun w : list (bv 8) => w <> []) (drop 1 ws))).
  intros w Hw Heq. subst w.
  pose proof (wl_word_pos [] (proj1 (Forall_forall _ _) Hwf [] Hw)) as H. simpl in H. lia.
Qed.

Lemma efe_args_chunks_short (n : nat) (args : list (list (bv 8))) :
  (1 <= n)%nat -> Forall (fun a => (length a <= n)%nat) args ->
  Forall (fun ch => (length ch <= n)%nat) (echo_args_chunks args).
Proof.
  intros Hn. induction args as [| a rest IH]; intros Hf; [constructor |].
  apply Forall_cons_1 in Hf as [Ha Hr].
  destruct rest as [| a' rest'].
  - cbn [echo_args_chunks]. constructor; [exact Ha |].
    constructor; [simpl; lia | constructor].
  - change (echo_args_chunks (a :: a' :: rest'))
      with (a :: [wl_sp] :: echo_args_chunks (a' :: rest')).
    constructor; [exact Ha |]. constructor; [simpl; lia |]. exact (IH Hr).
Qed.

Lemma efe_chunks_short (ws : list (list (bv 8))) :
  EchoDisc.line_ok ws ->
  Forall (fun ch => (length ch <= EchoDisc.line_max)%nat) (echo_chunks ws).
Proof.
  intros Hl. unfold echo_chunks.
  apply efe_args_chunks_short; [unfold EchoDisc.line_max; lia |].
  apply Forall_lookup. intros k w Hk. rewrite lookup_drop in Hk.
  pose proof (wl_off_lt_line ws (1 + k) w (length w) Hk ltac:(lia)) as H.
  destruct Hl as (_ & _ & _ & _ & Hlen). lia.
Qed.

Section UkFileEntriesRedir.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context `{!fifRegG Σ}.
  Context (g : file_gn).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).

  Local Instance fe_redir_code_persistent (N : uk_names Σ) :
    Persistent (up_code (echo_prog N)).
  Proof using . simpl. apply _. Qed.

  (* THE ENTRY: the statement of the per-program redirect entry the file
     sweep deleted ([UEchoFile.efile_image_entry]), at the file
     application's claim [c = fgn_cl g] (the instance's console needs the
     era's record, [Hcons]), with [udep] at the section's deposit instance
     ([PS := uprogSG_free] is the landed one's), and FOUR premises the
     landed entry does not take:
       - [cw = FsImg.ROOTINO]: the instance's core holds the cwd at the
         root (its opens resolve `f` there);
       - [□ (file_taint c -∗ app_taint)] and [□ (file_taint c -∗ Q (-1))]:
         the free handler's taint ([UkFreeHandler.fh_taint]) raises the
         machine's taint and pays the exit from the application's taint
         alone, at every hole of the tree;
       - the registry's class [fifRegG] (the registry is born in the slot). *)
  Lemma efile_image_entry_of_tree (ws : wordline) (M : gmap Z (bv 8))
      (s0 t : Z) (gb : nat -> bv 8) (sts : list fdstate)
      (cw : Z) (cs : gset gname) (pidv : mword 32)
      (c : file_fixed) (r : file_names) (Wq : iProp Σ)
      (i : Z) (γo : gname) (rb : bool)
      (Q : Z -> iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    file_app = MkAppcfg file_names (file_pred c) r ->
    c = fgn_cl g ->
    EchoDisc.line_ok ws ->
    UShEcho.echo_node_img ws M s0 t gb ->
    UkShEcho.echo_argv_bytes ws gb ->
    length sts = NOFILE ->
    cw = FsImg.ROOTINO ->
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    □ (UEchoFile.ef_exit c r Wq i γo ws -∗ Q (-1)) -∗
    □ (app_taint -∗ file_taint c) -∗
    □ (file_taint c -∗ app_taint) -∗
    □ (file_taint c -∗ Q (-1)) -∗
    app_inv fsc_fs -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q (UEchoFile.ef_pay c r Wq i γo ws) uslot.
  Proof using Hcons fifRegG0 ufdG0.
    intros HQc Heq Hgc Hline Himg Hbytes Hfdl Hcw Hl1 Hi1 Hi2 Hi3 Hi4.
    subst c.
    iIntros "#HQ #Hbr #Hkc #HQt #Hinv #Hnpw #Hdep".
    pose proof (efe_drop1_ne ws Hline) as Hne.
    pose proof (efe_words_nn ws Hline) as Hnn.
    assert (Hwok : fif_out_ok i ws).
    { unfold fif_out_ok. split_and!; [exact Hi1 | exact Hi2 | exact Hi3 | exact Hi4 |].
      exact (efe_chunks_short ws Hline). }
    set (w0 := fun _ : nat => FDFile i γo ws).
    assert (Hw0 : forall d, d ∈ [0%nat] -> forall i' γo', w0 d <> FDIn false i' γo')
      by (intros; discriminate).
    assert (Hwr : fif_wr [0%nat] w0 = true) by reflexivity.
    set (E := pipe_env (DOutM (echo_chunks ws)) (fif_files (snd <$> (None : dst)))).
    rewrite /image_entry.
    iIntros "!>" (na alen afun W') "%Hok' %Hcw' %Hlz %Hch %Hpid %Hargs Hmp HPay".
    iApply uslot_bupd.
    iMod (fif_reg_alloc w0) as (γreg) "Hpool". iModIntro.
    set (I := fun (N' : uk_names Σ) (Hpq : ukn_pay N' = Q) =>
                file_iface g r Heq N' (echo_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                  (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
                  (echo_stub_close N') (echo_stub_exit N') γreg [0%nat] w0 1%Qp None Hw0
                  file_lm (file_params g) (file_links g)
                  (LINKS_pers := file_links_persistent g)
                  (file_links_gl_w g) (file_links_gl_blk g) (file_links_gl_taint g)).
    iPoseProof (echo_image_entry_env_c ws M s0 t gb sts cw cs pidv Q
                  (own γreg (fif_pool ∅ w0) ∗ UEchoFile.ef_pay (fgn_cl g) r Wq i γo ws)%I
                  I E {[0%nat]}
                  Hline Himg Hbytes Hfdl (echo_file_conforms ws _ Hne Hnn)
                  (echo_tree_safe _ _) (fif_dp0 [0%nat] eq_refl)
                  with "[] Hnpw Hdep") as "#He".
    { iIntros "!>" (N' Hpq) "Hstd Hcwd (Hpool & HWq & Hc)".
      (* the exit wand: [Wq] framed, the cursor read off the drained device *)
      iAssert (fif_exit_k g r N' γreg [0%nat] w0 1%Qp None file_lm (file_params g) (file_links g))%I with "[HWq]" as "Hk".
      { iApply (fif_exit_k_redir g r N' γreg [0%nat] w0 1%Qp None i γo ws Wq eq_refl eq_refl
                  with "[] HWq").
        iIntros "!> Hx". rewrite Hpq. iApply ("HQ" with "Hx"). }
      iApply (fif_env_res g r Heq Hcons N' (echo_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
                (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
                (echo_stub_close N') (echo_stub_exit N') γreg [0%nat] w0 1%Qp None Hw0
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
      - (* [fif_cred] is [True] at the write mode; the frame closes it *)
        rewrite /fif_env. iFrame "Hbr Hkc Hinv".
        iIntros "!> HT". rewrite Hpq. iApply ("HQt" with "HT").
      - iApply (fif_dq_wr r [0%nat] w0 1%Qp None Hwr).
      - iIntros "Htk". cbn [E pipe_env pe_dev]. case_decide as Hc0; [| done]. simpl.
        iExists i, γo, ws. iFrame "Htk". iExists 0%nat.
        iSplit; [done |]. iSplit; [iPureIntro; exact Hwok |].
        rewrite /file_out.
        iApply (UEchoFile.efany_of (fgn_cl g) r i γo ws 0%nat [] ltac:(constructor) with "Hc"). }
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp [Hpool HPay]");
      [ exact Hok' | exact Hcw' | exact Hlz | exact Hch | exact Hpid | exact Hargs | ].
    iFrame "Hpool HPay".
  Qed.

End UkFileEntriesRedir.
