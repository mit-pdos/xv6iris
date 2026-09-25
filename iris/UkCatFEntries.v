(* ===================================================================== *)
(* UkCatFEntries.v -- [cat f] AT THE HEAD OF THE N-STAGE ROUND, AS AN     *)
(* ENTRY (union.md C9d', item 4).                                         *)
(*                                                                        *)
(* [pse_catf_image_entry_gen] is [UkTreeEntry.cat_image_entry_env_c] at   *)
(* the producer's merged registry [UkCatFIface.cif_iface], the registry   *)
(* allocated INSIDE the slot ([UexecRet.uslot_bupd]), at the producer    *)
(* device ([ProgTreePipes.catp_env]) protected: its [Pay] is the stage's *)
(* lend [UkCatFIface.cif_catf_lend] -- the first pipe's permit, the      *)
(* family writer unfired with its kits, the deed -- and its exit wand to *)
(* the payload [Q].  [pse_catf_image_entry] is the present file (the     *)
(* deed's content is the round's line [L]); [pse_catf_image_entry_absent] *)
(* its twin (no `f`: the refused open, and nothing on the pipe).         *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra Require Import functions.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UkRun UkRunSys.
Require Import UCodeCat.
Require User.CatSyms.
Require Import FdSlots ProcGeom UserFd UserCwd UserHeap.
Require Import UexecSG UexecSlot UexecRet.
Require Import UexecExecInst.
Require Import ConsoleInv.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import FsCfg AppCfg AppInv FsImg FsImgCheck.
Require Import LineWords LineBytes EchoDisc ExecWords.
Require Import EchoOut AppEcho.
Require Import LineModel LineModelLinks.
Require Import GenOut FileDisc.
Require Import AppFile AppFileCons FileOpen.
Require Import PipesDisc PipeBothNPure PipeBothN PipeOutN PipesView.
Require Import PipeOut PipeNames PipeProto.
Require Import CtxIdDefs.
Require Import ExecArgs ExecEntry.
Require Import ElfFile ElfUser.
Require Import ProgTree ProgTreePipes UkTree UkStub.
Require Import UkCatTree.
Require Import UkHandler.
Require Import UkShMain UkShEcho UShEcho.
Require Import UkTreeEntry.
Require Import UkPipesIface UkCatFIface.
Local Open Scope Z_scope.
Import Defs.

(* the one protected device, a producer device *)
Lemma cfe_nodup0 (x : cfdev) : stdpp.base.NoDup ([(0%nat, x)].*1).
Proof using . cbn. apply NoDup_singleton. Qed.

Lemma cfe_dp0 (x : cfdev) : dp_in ([(0%nat, x)].*1) {[0%nat]}.
Proof using . intros d Hd. cbn in Hd. apply elem_of_list_singleton in Hd as ->. set_solver. Qed.

Lemma cfe_kdp0 (pn : pnames) (gp : pipe_names) (w : wid) (A X : list (list (bv 8))) :
  forall dk, dk ∈ [(0%nat, UDProd pn gp w A X)] ->
             exists pn' gp' w' A' X', dk.2 = UDProd pn' gp' w' A' X'.
Proof using .
  intros dk Hdk. apply elem_of_list_singleton in Hdk as ->. by exists pn, gp, w, A, X.
Qed.

Section UkCatFEntries.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{PS : UexecSG.uprogSG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pipesNG Σ, !cifRegG Σ}.
  #[local] Existing Instance eo_turn | 0.

  Context (cf : file_fixed) (rf : file_names).
  Context (Heq : file_app = MkAppcfg file_names (file_pred cf) rf).
  Context (g : pipe_gn).
  Context (M : lmodel) (V : pview M) (G : gen_cparams M) (sd : lm_st M).
  Context (WA : gen_wa M G sd).
  Hypothesis Hext : forall k l, gext WA k l = pext g k l.
  Local Notation T := (gcT G).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = peclV g M G sd WA).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ HRg) = T).
  Hypothesis Hsup : ⊢ □ (T -∗ app_sup).
  Context (v : era_pins) (I : list (bv 8)) (sR : lm_st M) (lR : pline').
  Hypothesis HlR : pv_line V (lineV M I) = Some lR.
  Hypothesis Hfc : fc_ok (pv_fc V sR).
  Context (Hadmit : pns_admV V lR) (Hplok : pl_ok lR).
  Context (L : list (bv 8)) (HL31 : pns_short L).
  Context (TERM : wid -> list (bv 8) -> bool)
          (TOK : (wid -> option (list (bv 8))) -> list wid -> Prop).
  Context (dep : wid -> list (bv 8) -> iProp Σ) (dep_tl : forall w s, Timeless (dep w s)).
  Context (γc γm : wid -> gname).

  Local Instance cfe_cat_code_persistent (N' : uk_names Σ) :
    Persistent (up_code (cat_prog N')).
  Proof using . simpl. apply _. Qed.

  (* THE INSTANCE AT THE MINTED RECORD *)
  Definition cfe_iface (γreg : gname) (kds : list (nat * cfdev))
      (Hkds : stdpp.base.NoDup kds.*1)
      (Hkdp : forall dk, dk ∈ kds -> exists pn gp w A X, dk.2 = UDProd pn gp w A X)
      (qf : Qp) (sf : dst) (N' : uk_names Σ) (HNc : ukn_const N') :
      ep_ifaceP (Dp := kds.*1) N' (cat_prog N') :=
    cif_iface cf rf Heq g M V G sd WA Hext Hcons Hkill Hsup v I sR lR HlR Hfc Hadmit Hplok L HL31
      TERM TOK dep dep_tl γc γm N' (cat_prog N') (HNc := HNc)
      (cat_stub_read N') (cat_stub_write N') (cat_stub_open N')
      (cat_stub_close N') (cat_stub_exit N') γreg kds Hkds Hkdp qf sf.

  Local Notation LEND qf sf pn gp w A X ds xs Q :=
    (cif_catf_lend cf rf g M V G v I sR lR L TERM TOK dep γc γm qf sf pn gp w A X ds xs Q).

  (* THE ENTRY, at either state of `f` *)
  Lemma pse_catf_image_entry_gen (f : list (bv 8)) (Mn : gmap Z (bv 8)) (sv t : Z)
      (gn : nat -> bv 8) (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (pn : pnames) (gp : pipe_names) (w : wid)
      (A X ds xs : list (list (bv 8))) (qf : Qp) (sf : dst) (rb1 rb2 : bool) :
    (forall x y : Z, Q x = Q y) ->
    uname f ->
    exec_ok (prod_words (PrCatF f)) ->
    UShEcho.echo_node_img (prod_words (PrCatF f)) Mn sv t gn ->
    UkShEcho.echo_argv_bytes (prod_words (PrCatF f)) gn ->
    length sts = NOFILE -> cw = FsImg.ROOTINO ->
    take NSTD sts !! 1%nat = Some (FdOpen rb1 true (FdPipe gp)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    (snd <$> sf !! f = Some L /\ cat_dg_open f ∈ xs /\ [] ∈ ds /\ cat_dg_write ∈ ds)
    \/ (sf !! f = None /\ cat_dg_open f ∈ xs) ->
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts cw cs pidv Q
      (LEND qf sf pn gp w A X ds xs Q) uslot.
  Proof using HL31 Hadmit Hcons Heq Hext Hfc Hkill HlR Hplok Hsup cifRegG0 dep_tl ufdG0.
    intros HQc Hf Hok Hnode Hab Hfdl Hcw Hl1 Hl2 Hcase.
    rewrite /uname in Hf. subst f.
    iIntros "#Hnpw #Hdep".
    set (wv := fun _ : nat => UDProd pn gp w A X).
    set (kds := [(0%nat, UDProd pn gp w A X)]).
    set (files := files_of (dst_content sf)).
    assert (Hfs : files fname_f = snd <$> sf !! fname_f) by exact (dst_content_lookup sf fname_f).
    assert (Hc : conforms (catp_env (DProd [L; []] xs ds) files [fname_f])
                   (cat_tree (prod_words (PrCatF fname_f)))).
    { change (cat_tree (prod_words (PrCatF fname_f))) with (cat_tree [sb "cat"; fname_f]).
      destruct Hcase as [(Hs & Hx & Hn & Hw) | (Hs & Hx)].
      - apply (cat_file_prod_conforms_gen fname_f L); [rewrite Hfs; exact Hs | by left
                                                     | by right; left | exact Hx | exact Hn | exact Hw].
      - apply (cat_file_prod_absent_conforms_gen fname_f); [rewrite Hfs Hs; reflexivity
                                                           | by right; left | exact Hx]. }
    rewrite /image_entry.
    iIntros "!>" (na alen afun W') "%Hokk %Hcwv %Hlz %Hch %Hpid %Hargs Hmp HPay".
    iApply uslot_bupd.
    iMod (cif_reg_alloc wv) as (γreg) "Hpool". iModIntro.
    set (If := fun (N' : uk_names Σ) (Hpq : ukn_pay N' = Q) =>
                 cfe_iface γreg kds (cfe_nodup0 _) (cfe_kdp0 pn gp w A X) qf sf N'
                   (ukn_const_of_eq N' Q Hpq HQc)).
    iPoseProof (cat_image_entry_env_c (PS := PS) (prod_words (PrCatF fname_f)) Mn sv t gn sts cw cs
                  pidv Q (own γreg (cif_pool ∅ wv) ∗ LEND qf sf pn gp w A X ds xs Q)%I
                  If (catp_env (DProd [L; []] xs ds) files [fname_f]) {[0%nat]}
                  Hok Hnode Hab Hfdl Hc (cat_tree_safe _ _) (cfe_dp0 _)
                  with "[] Hnpw Hdep") as "#He".
    { iIntros "!>" (N' Hpq) "Hstd Hcwd [Hpool Hlend]".
      rewrite /If /cfe_iface. subst cw.
      iEval (rewrite -Hpq) in "Hlend".
      iApply (cif_catf_env_res cf rf Heq g M V G sd WA Hext Hcons Hkill Hsup v I sR lR HlR Hfc
                Hadmit Hplok L HL31 TERM TOK dep dep_tl γc γm N' (cat_prog N')
                (HNc := ukn_const_of_eq N' Q Hpq HQc)
                (cat_stub_read N') (cat_stub_write N') (cat_stub_open N')
                (cat_stub_close N') (cat_stub_exit N') γreg kds (cfe_nodup0 _)
                (cfe_kdp0 pn gp w A X) qf sf pn gp w A X ds xs (take NSTD sts) rb1 rb2 wv files
                eq_refl eq_refl Hl1 Hl2 Hfs
                with "Hstd Hcwd Hpool Hlend"). }
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp [Hpool HPay]");
      [ exact Hokk | exact Hcwv | exact Hlz | exact Hch | exact Hpid | exact Hargs | ].
    iFrame "Hpool HPay".
  Qed.

  (* `f` PRESENT: its content is the round's line *)
  Lemma pse_catf_image_entry (f : list (bv 8)) (Mn : gmap Z (bv 8)) (sv t : Z)
      (gn : nat -> bv 8) (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (pn : pnames) (gp : pipe_names) (w : wid)
      (qf : Qp) (sf : dst) (i : Z) (rb1 rb2 : bool) :
    (forall x y : Z, Q x = Q y) ->
    uname f -> sf !! f = Some (i, L) ->
    exec_ok (prod_words (PrCatF f)) ->
    UShEcho.echo_node_img (prod_words (PrCatF f)) Mn sv t gn ->
    UkShEcho.echo_argv_bytes (prod_words (PrCatF f)) gn ->
    length sts = NOFILE -> cw = FsImg.ROOTINO ->
    take NSTD sts !! 1%nat = Some (FdOpen rb1 true (FdPipe gp)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts cw cs pidv Q
      (LEND qf sf pn gp w [[]; cat_dg_write] [cat_dg_open f]
         [[]; cat_dg_write] [cat_dg_open f] Q) uslot.
  Proof using HL31 Hadmit Hcons Heq Hext Hfc Hkill HlR Hplok Hsup cifRegG0 dep_tl ufdG0.
    intros HQc Hf HsN Hok Hnode Hab Hfdl Hcw Hl1 Hl2.
    apply (pse_catf_image_entry_gen f Mn sv t gn sts cw cs pidv Q pn gp w _ _ _ _ qf _ rb1 rb2
             HQc Hf Hok Hnode Hab Hfdl Hcw Hl1 Hl2).
    left. split_and!; [by rewrite HsN | by left | by left | by right; left].
  Qed.

  (* ...and ABSENT: the refused open's report, nothing on the pipe *)
  Lemma pse_catf_image_entry_absent (f : list (bv 8)) (Mn : gmap Z (bv 8)) (sv t : Z)
      (gn : nat -> bv 8) (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (pn : pnames) (gp : pipe_names) (w : wid)
      (qf : Qp) (sf : dst) (rb1 rb2 : bool) :
    (forall x y : Z, Q x = Q y) ->
    uname f -> sf !! f = None ->
    exec_ok (prod_words (PrCatF f)) ->
    UShEcho.echo_node_img (prod_words (PrCatF f)) Mn sv t gn ->
    UkShEcho.echo_argv_bytes (prod_words (PrCatF f)) gn ->
    length sts = NOFILE -> cw = FsImg.ROOTINO ->
    take NSTD sts !! 1%nat = Some (FdOpen rb1 true (FdPipe gp)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts cw cs pidv Q
      (LEND qf sf pn gp w [[]] [cat_dg_open f] [[]] [cat_dg_open f] Q) uslot.
  Proof using HL31 Hadmit Hcons Heq Hext Hfc Hkill HlR Hplok Hsup cifRegG0 dep_tl ufdG0.
    intros HQc Hf HsN Hok Hnode Hab Hfdl Hcw Hl1 Hl2.
    apply (pse_catf_image_entry_gen f Mn sv t gn sts cw cs pidv Q pn gp w _ _ _ _ qf _ rb1 rb2
             HQc Hf Hok Hnode Hab Hfdl Hcw Hl1 Hl2).
    right. split; [exact HsN | by left].
  Qed.
End UkCatFEntries.
