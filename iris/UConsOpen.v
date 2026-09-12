(* ===================================================================== *)
(* UConsOpen.v -- THE CONSOLE OPEN, FACTORED (lane SH-OPEN, ruling (C)).  *)
(*                                                                        *)
(* /init and /sh both open "console" at the ROOT with O_RDWR, and both do  *)
(* it through a PINNED bundle: the PRESENT pin when the node is there and  *)
(* the DEAD walk when it is not.  Everything about those two bundles that  *)
(* is not the CALLER's -- the path literal, the working directory, the     *)
(* claim laws, the families, the two key-level rows, the receipt readings  *)
(* -- is the same for both, so it lives here and the two programs are TWO  *)
(* INSTANTIATIONS (the PINNING ruling's (3): factor before the second      *)
(* hand-rolled instance).  This file was cut out of UInitConsK.v verbatim; *)
(* what stayed there is exactly what names /init's own image: its rodata   *)
(* base 0x970, its stub addresses, and the MKNOD, which only /init calls.  *)
(*                                                                        *)
(* WHAT A CALLER SUPPLIES, and all it supplies:                           *)
(*   its READ-ONLY IMAGE [Img] (a persistent [UserHeap.utext_img]) and the *)
(*     base [pv] of its own "console" literal, with the one reading        *)
(*     [forall M, uimg_sub Img M -> arg_path_of M pv init_cons_pl];        *)
(*   the two argument words in its register file (a0 = pv, a1 = O_RDWR);   *)
(*   the era's laws ([UInitCons.init_cons_laws]) and [AppInv.app_inv];     *)
(*   at the PRESENT arm the persistent flag [AppEcho.cons_made r i], at    *)
(*     the ABSENT arm the credential [K].                                  *)
(* ===================================================================== *)

From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.base_logic.lib Require Import mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
(* THE GHOST BINDER LIST, each module IMPORTED and not merely required --
   naming a class without its defining module in scope introduces a FRESH
   Type variable and the kernel's [uexecSG] instance becomes invisible to
   resolution ([UInitSh.v]'s header). *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserPerm.        (* [uperm] *)
Require Import UserCwd.
Require Import UmodeAbi.           (* [uimg_sub] *)
Require Import ProcGeom.           (* [NOFILE], [tf_arg_idx] *)
Require Import UInitFd.            (* [ufd_l0] / [ufd_l1] / [ufd_alloc0] *)
Require Import PieceFam.
Require Import FsTree.             (* [fname] *)
Require Import PathElems.
Require Import ArgPath.
Require Import ChildTok.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunLeaf UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsBlocks.           (* [fs_names] *)
Require Import FsBytesGamma.
Require Import FsAbsDefs.
Require Import FsAbs.              (* [ax_hop] / [ax_hops_from] *)
Require Import FsAbsEra.           (* [ex_start] / [ex_hop] / [elend] *)
Require Import SysOpenDefs SpecSysOpen.
Require Import SysMknodDefs SpecSysMknod.
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import FsConsPin.
Require Import PinnedObs.
Require Import PinnedOpen.
Require Import AppEcho.
Require Import UInitCons.
Require Import TsoCtx.
Require FsImg.
Require User.InitSyms.
Import Defs.

(* /init's omode word and its two device words, read the way the rows read
   them.  All four are closed. *)
Lemma init_cons_om2_arg : om_arg (mword_of_int 2 : mword 64) = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma init_cons_om2_create : om_create (mword_of_int 2 : mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma init_cons_om2_trunc : om_trunc (mword_of_int 2 : mword 64) = false.
Proof. vm_compute. reflexivity. Qed.

(* the path has ONE element, which is what makes the walk's TERMINAL cursor
   a later hop than hop 0 -- and hence, at the dead pin, the taint *)
Lemma init_cons_elems_len : length (path_elems init_cons_pl) = 1%nat.
Proof. rewrite init_cons_path_elems. reflexivity. Qed.

Lemma init_cons_elems_hd : path_elems init_cons_pl !! 0%nat = Some fname_console.
Proof. rewrite init_cons_path_elems. reflexivity. Qed.

(* a small-nat word is not [-1], and two small-nat words are equal only at
   equal numbers.  Both are the standard [bv_wrap] recipe. *)
Lemma init_cons_moi_nat_m1 (a : nat) :
  (a < NOFILE)%nat ->
  (mword_of_int (Z.of_nat a) : mword 64) <> (mword_of_int (-1) : mword 64).
Proof.
  unfold NOFILE. intros Ha Heq. apply (f_equal bv_unsigned) in Heq.
  rewrite !moi64_unsigned in Heq.
  rewrite (bvw64_small (Z.of_nat a)) in Heq;
    [| change (2 ^ 64)%Z with 18446744073709551616%Z; lia ].
  assert (Hm1 : bv_wrap 64 (-1) = 18446744073709551615%Z)
    by (vm_compute; reflexivity).
  rewrite Hm1 in Heq. lia.
Qed.

Lemma init_cons_moi_nat_inj (a b : nat) :
  (a < NOFILE)%nat -> (b < NOFILE)%nat ->
  (mword_of_int (Z.of_nat a) : mword 64) = mword_of_int (Z.of_nat b) ->
  a = b.
Proof.
  unfold NOFILE. intros Ha Hb Heq. apply (f_equal bv_unsigned) in Heq.
  rewrite !moi64_unsigned in Heq.
  rewrite (bvw64_small (Z.of_nat a)) in Heq;
    [| change (2 ^ 64)%Z with 18446744073709551616%Z; lia ].
  rewrite (bvw64_small (Z.of_nat b)) in Heq;
    [| change (2 ^ 64)%Z with 18446744073709551616%Z; lia ].
  lia.
Qed.

Section UConsOpen.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UInitSh.v]'s note): no local
     [Context {SG}] / [Context {PS}], or two [sbundle]s print identically
     and [UexecSG.psok] resolves to the generic [fun _ => True]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* the console KEY's camera.  NOT [mono_natG]: [Xv6Cameras]'s note --
     the flag's camera is [riscvFixedGS]'s own, and a second binder here
     would be a second instance that prints alike, which is exactly what
     makes [UInitCons.init_cons_laws_echo]'s record equation unusable. *)
  Context `{!inG Σ (mono_listR (leibnizO Z))}.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* A FANCY UPDATE IN FRONT OF THE TRIVIAL-POST WP.  [RiscvPtsto.wp_triv]
     is a DEFINITION, so the proofmode's [ElimModal] instance for [wp] does
     not see through it and [iMod] fails against a bare [WP e] goal; this
     is [fupd_wp] with the definition peeled. *)
  Lemma fupd_wp_triv (e : expr riscv_lang) : (|={⊤}=> WP e) ⊢ WP e.
  Proof. rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  (* =================================================================== *)
  (*  S2.  THE DEPOSIT'S FAMILIES                                         *)
  (*                                                                      *)
  (*  One [UexecExecInst.xfam] per call, with the pinned families in the   *)
  (*  branch the ecall reads and the trivial ones in every other: a        *)
  (*  deposit is read at ONE number ([UexecExecInst.xv6_sbundle] is a      *)
  (*  match on it), so the rest of the record is inert.  [kf_xpay] is the  *)
  (*  PROGRAM'S OWN EXIT PAYLOAD, which is what [UkRun.udepwf_at]'s pure   *)
  (*  row demands.                                                        *)
  (* =================================================================== *)
  Definition xfam_open (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Q : Z -> iProp Σ) : xfam :=
    {| xf_P     := fun _ _ => True%I;
       xf_Pmiss := fun _ _ => True%I;
       xf_Fo    := pfam_triv (fun _ _ _ => True%I);
       xf_Rs    := True%I;
       rf_F     := pfam_triv (fun _ _ _ _ => True%I);
       cf_P     := fun _ _ => True%I;
       cf_Pmiss := fun _ _ => True%I;
       cf_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_P     := P;
       of_Pmiss := Pmiss;
       of_Farm  := pfam_triv (fun _ _ => True%I);
       of_Fun   := pfam_triv (fun _ _ => True%I);
       of_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fo    := Fo;
       of_Ft    := pfam_triv (fun _ _ _ => True%I);
       wf_Q     := fun _ => True%I;
       wf_tr0   := [];
       nf_P     := fun _ _ => True%I;
       nf_Pmiss := fun _ _ => True%I;
       nf_Farm  := pfam_triv (fun _ _ => True%I);
       nf_Fun   := pfam_triv (fun _ _ => True%I);
       nf_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       nf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_P     := fun _ _ => True%I;
       uf_Pmiss := fun _ _ => True%I;
       uf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       uf_Ftgt  := pfam_triv (fun _ _ => True%I);
       uf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_Fmiss := pfam_triv (fun _ _ _ => True%I);
       lf_Ftgt  := pfam_triv (fun _ _ _ => True%I);
       lf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       lf_Funt  := pfam_triv (fun _ _ => True%I);
       df_P     := fun _ _ => True%I;
       df_Pmiss := fun _ _ => True%I;
       df_Farm  := pfam_triv (fun _ _ => True%I);
       df_Fdots := pfam_triv (fun _ _ _ _ => True%I);
       df_Fun   := pfam_triv (fun _ _ => True%I);
       df_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       df_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       kf_pay   := fun _ => True%I;
       kf_xpay  := Q;
       rf_ret   := fun _ _ => True%I |}.

  (* =================================================================== *)
  (*  S3.  THE TWO ROWS, IN THE PROCESS'S DIRECTION                       *)
  (*                                                                      *)
  (*  [UexecExecInst] states the deposit's ELIM and the post's INTRO --    *)
  (*  the DISPATCHER's two directions.  A process needs the other two, and *)
  (*  it needs them at readings it can name, so each takes the key's own   *)
  (*  projections as pure premises.  The proofs are the same three lines:  *)
  (*  the match at one literal.                                           *)
  (* =================================================================== *)
  Local Ltac xv6_skip :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [Hc | _]; [ exfalso; by vm_compute in Hc | ]
    end.
  Local Ltac xv6_take :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [_ | Hc]; [ | exfalso; by apply Hc ]
    end.

  Lemma sbundle_at_open_intro_at (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64) :
    uvis_cwd W = cw -> uvis_M W = M ->
    tf_w (uvis_tf W) (tf_arg_idx 0) = pv ->
    tf_w (uvis_tf W) (tf_arg_idx 1) = vom ->
    open_in (fs_gamma_L fsc_fs) fsc_fs cw M pv vom
      (of_P f) (of_Pmiss f) (of_Farm f) (of_Fun f) (of_Fok f) (of_Fex f)
      (of_Fo f) (of_Ft f) -∗
    sbundle_at X 15 f W.
  Proof.
    intros Hc HM H0 H1. iIntros "H".
    (* the REWRITE GOES FIRST, against the lemma's own variables: after the
       unfold both sides are whatever [simpl] made of the key's
       projections, and a rewrite aimed at one of those would not find its
       pattern. *)
    rewrite -Hc -HM -H0 -H1.
    rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_open_elim_at (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (cw : Z) (M : gmap Z (bv 8)) (pv vom : mword 64)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate)
      (cw' : Z) (cs' : gset gname) :
    uvis_cwd W = cw -> uvis_M W = M ->
    tf_w (uvis_tf W) (tf_arg_idx 0) = pv ->
    tf_w (uvis_tf W) (tf_arg_idx 1) = vom ->
    spost_at X 15 f W r M' fdv' cw' cs' -∗
    open_receipt (fs_gamma_L fsc_fs) fsc_fs cw M pv vom
      (of_P f) (of_Pmiss f) (of_Farm f) (of_Fun f) (of_Fok f) (of_Fex f)
      (of_Fo f) (of_Ft f) (uvis_fd W) r fdv'.
  Proof.
    intros Hc HM H0 H1. iIntros "H".
    rewrite -Hc -HM -H0 -H1.
    rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  (* =================================================================== *)
  (*  S4.  THE SUPPLIERS, at the CALLER's own literal                     *)
  (*                                                                      *)
  (*  [UkRun.udepwf_at]: the deposit at a NAMED family (the program reads  *)
  (*  its receipt at the family it deposited) and at ONE working directory *)
  (*  (a pin is about a PATH, and "console" names a file only relative to  *)
  (*  the directory it is resolved from).  The heap is LENT, which is what *)
  (*  makes the path reading possible at all: [M] is bound by [urun]'s own *)
  (*  existential.                                                        *)

  (* ...AT AN ARBITRARY READ-ONLY IMAGE (lane SH-OPEN): the caller's own
     persistent view of its own literal's page.  [init_cons_ro_sub] is
     this at /init's. *)
  Lemma cons_ro_sub (N : uk_names Σ) (Img M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) :
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
    utext_img (ukn_t N) Img -∗ ⌜uimg_sub Img M⌝.
  Proof.
    iIntros "Hheap #Hro". iIntros (a b Hb).
    rewrite /utext_img.
    iDestruct (big_sepM_lookup _ _ a b Hb with "Hro") as "Hb".
    iDestruct (uheap_text with "Hheap Hb") as %(HM & _ & _).
    iPureIntro. exact HM.
  Qed.

  (* =================================================================== *)
  (*  S4a.  THE DEAD WALK THAT GIVES THE CREDENTIAL BACK                  *)
  (*                                                                      *)
  (*  [PinnedObs.pobs_walk_dead] SPENDS the absence credential: the hop    *)
  (*  takes it, reads the claim with it, and drops it, so nothing comes    *)
  (*  home.  /init needs it back -- the miss leaf runs twice and the mknod *)
  (*  runs between ([UkInit.uki_open_absent_leaf]'s failure arm hands [K]  *)
  (*  over) -- so the credential RIDES IN THE WALK'S OWN FAMILIES here:    *)
  (*                                                                      *)
  (*    in the CURSOR [cons_P_dead], which is what hop 0 consumes and what *)
  (*      the failure fold hands back when the walk never fired (argstr    *)
  (*      failed, or the kernel stopped at the cursor);                    *)
  (*    in the MISS family [cons_Pmiss], which is what hop 0 pays when the *)
  (*      entry is not there and what [SysOpenDefs.namei_walk_dead_era]    *)
  (*      hands back on the path the console actually takes.               *)
  (*                                                                      *)
  (*  Every arm of [SpecSysOpen.open_post_fail_plain] therefore yields     *)
  (*  [K ∨ T], and every SUCCESS arm still collapses to the taint: the     *)
  (*  cursor at the terminal hop is at [k = 1] and the credential arm      *)
  (*  demands [k = 0].                                                     *)
  (* =================================================================== *)
  Definition cons_P_dead (T K : iProp Σ) (d0 : Z) (k : nat) (d : Z)
    : iProp Σ := ((⌜k = 0%nat /\ d = d0⌝ ∗ K) ∨ T)%I.

  Definition cons_Pmiss (T K : iProp Σ) (k : nat) (d : Z) : iProp Σ :=
    (K ∨ T)%I.

  (* HOP 0: the claim says `console` is not an entry of the root, the lent
     entry map IS the root's, so the hop takes the MISS branch -- and pays
     it with the very credential the cursor handed it. *)
  Lemma cons_hop_dead (γfs : fs_names) (T K : iProp Σ) :
    Persistent T -> Timeless T -> Timeless K ->
    init_cons_abs_law T K -∗ app_inv γfs -∗
    ex_hop γfs (cons_P_dead T K FsImg.ROOTINO) (cons_Pmiss T K)
      0%nat fname_console.
  Proof.
    intros HPT HTT HTK. iIntros "#Hcl #Hinv".
    pose proof cons_pin_misses_at as [_ Hmiss].
    rewrite /ex_hop /ax_hop /cons_P_dead /cons_Pmiss.
    iIntros (d ents dqv) "HP HF".
    iDestruct "HP" as "[[%Hpd HK] | #HT]"; last first.
    { iModIntro. iFrame "HF".
      destruct (ents !! fname_console) as [c |]; by iRight. }
    destruct Hpd as [_ Hd]. subst d.
    iMod (inv_acc ⊤ appN with "Hinv") as "[Hbody Hclose]"; [ set_solver | ].
    iEval (rewrite /app_body) in "Hbody".
    iDestruct "Hbody" as (I) "(>Hh & Hp & >%Hdom & #Hx)".
    iAssert (▷ (app_pred app_run (abs_view I) ∗ K
                ∗ (⌜cons_absent (abs_view I)⌝ ∨ T)))%I
      with "[Hp HK]" as "Hpc".
    { iNext. iApply ("Hcl" with "HK Hp"). }
    iDestruct "Hpc" as "[Hp [HK Hc]]".
    iMod "Hc". iMod "HK".
    iDestruct (pobs_elend_astep γfs (1/2)%Qp I FsImg.ROOTINO dqv ents
                 fname_console with "Hh HF") as %Hae.
    iMod ("Hclose" with "[Hh Hp]") as "_".
    { iNext. rewrite /app_body. iExists I. iFrame "Hh Hp Hx".
      iPureIntro. exact Hdom. }
    iModIntro. iFrame "HF".
    iDestruct "Hc" as "[%HP | #HT]"; last first.
    { destruct (ents !! fname_console) as [c |]; by iRight. }
    assert (Hn : ents !! fname_console = None)
      by (rewrite -Hae;
          exact (Hmiss (abs_view I) fname_console HP init_cons_elems_hd)).
    rewrite Hn. iLeft. iExact "HK".
  Qed.

  (* ...AND EVERY LATER HOP, reached only under the taint: the cursor at
     [k <> 0] IS the taint, and the hop opens nothing. *)
  Lemma cons_hop_dead_hi (γfs : fs_names) (T K : iProp Σ) (k : nat)
      (s : fname) :
    (k <> 0)%nat ->
    ⊢ ex_hop γfs (cons_P_dead T K FsImg.ROOTINO) (cons_Pmiss T K) k s.
  Proof.
    intros Hk. rewrite /ex_hop /ax_hop /cons_P_dead /cons_Pmiss.
    iIntros (d ents dqv) "HP HF".
    iDestruct "HP" as "[[%Hpd _] | HT]";
      [ destruct Hpd as [Hz _]; destruct (Hk Hz) | ].
    iModIntro. iFrame "HF".
    destruct (ents !! s) as [c |]; by iRight.
  Qed.

  Lemma cons_walk_dead (γfs : fs_names) (T K : iProp Σ) :
    Persistent T -> Timeless T -> Timeless K ->
    init_cons_abs_law T K -∗ app_inv γfs -∗ K -∗
    ex_start γfs FsImg.ROOTINO (cons_P_dead T K FsImg.ROOTINO)
      (cons_Pmiss T K) init_cons_pl.
  Proof.
    intros HPT HTT HTK. iIntros "#Hcl #Hinv HK".
    rewrite /ex_start. iIntros (r Hr). iModIntro. iSplitL "HK".
    { rewrite /cons_P_dead. iLeft. iFrame "HK". iPureIntro.
      split; [ reflexivity | rewrite Hr; exact init_cons_start ]. }
    rewrite /ex_hops_from /ax_hops_from drop_0 init_cons_path_elems
            /cons_path big_sepL_cons.
    iSplitR.
    - iApply (cons_hop_dead γfs T K HPT HTT HTK with "Hcl Hinv").
    - iApply big_sepL_intro. iIntros "!>" (j s Hj).
      iApply (cons_hop_dead_hi γfs T K (0 + S j)%nat s ltac:(lia)).
  Qed.

  (* /init's own bundle for an open it expects to fail, with the credential
     inside the walk's families. *)
  Lemma cons_open_bundle_dead (γfs : fs_names) (T K : iProp Σ)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ)) :
    Persistent T -> Timeless T -> Timeless K ->
    om_arg vom = 2 ->
    arg_path_of M pv init_cons_pl ->
    init_cons_abs_law T K -∗ app_inv γfs -∗ K -∗
    open_in (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv vom
      (cons_P_dead T K FsImg.ROOTINO) (cons_Pmiss T K) Farm Fun Fok Fex
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I)) Ft.
  Proof.
    intros HPT HTT HTK Hom Hpath. iIntros "#Hcl #Hinv HK".
    destruct (om_rdwr_plain vom Hom) as [Hcr Htr].
    rewrite /open_in Hcr /open_au_plain_at.
    iSplitL "HK".
    { iIntros (pl') "%Hpath'".
      rewrite (arg_path_of_uniq M pv pl' init_cons_pl Hpath' Hpath).
      iApply (cons_walk_dead γfs T K HPT HTT HTK with "Hcl Hinv HK"). }
    iSplitR; [ iApply pobs_aopen_triv | ].
    iApply (open_trunc_piece_none _ vom Ft Htr).
  Qed.

  (* ...AND THE RECEIPT: the call failed, the table did not move, AND THE
     CREDENTIAL IS BACK -- or the application is tainted.  There is no
     third arm: at a view the credential holds of the walk dies at hop 0,
     so the success fold's terminal cursor is the taint.

     THE FUPD IS THE ARGSTR ARM's: when the path was never fetched the
     whole bundle comes home and the credential is inside the walk's own
     one-shot, so it is fired here -- at the caller's own path, which it
     knows.  Every call site is inside its leaf's WP, which absorbs it. *)
  Lemma cons_open_dead_recv (γfs : fs_names) (T K : iProp Σ)
      (M : gmap Z (bv 8)) (pv vom : mword 64)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (Ft : pfam Σ (aview -> Z -> list (bv 8) -> iProp Σ))
      (sts : list fdstate) (r : mword 64) (fdv' : list fdstate) :
    Persistent T ->
    arg_path_of M pv init_cons_pl ->
    open_receipt_plain (fs_gamma_L γfs) γfs FsImg.ROOTINO M pv vom
      (cons_P_dead T K FsImg.ROOTINO) (cons_Pmiss T K) Fo Ft sts r fdv' -∗
    |={⊤}=> ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ ⌜fdv' = sts⌝
              ∗ (K ∨ T)) ∨ T).
  Proof.
    intros HPT Hpath. iIntros "Hrc". rewrite /open_receipt_plain.
    iDestruct "Hrc" as "[(%Hr & %Hfd & Hfail) | Hok]"; last first.
    { (* THE SUCCESS FOLD: the terminal cursor is at hop 1, and the
         credential arm demands hop 0 *)
      iDestruct "Hok" as (pl' av i) "(%Hpath' & HP & _)".
      rewrite (arg_path_of_uniq M pv pl' init_cons_pl Hpath' Hpath).
      rewrite /cons_P_dead.
      iDestruct "HP" as "[[%Hz _] | #HT]".
      - exfalso. destruct Hz as [Hz _]. rewrite init_cons_elems_len in Hz.
        discriminate Hz.
      - iModIntro. by iRight. }
    rewrite /open_post_fail_plain.
    iDestruct "Hfail" as "[Hau | Hd]".
    - (* ARGSTR FAILED: the whole bundle is home, so fire its walk here *)
      rewrite /open_au_plain_at.
      iDestruct "Hau" as "(Hwalk & _ & _)".
      iDestruct ("Hwalk" $! init_cons_pl with "[%]") as "Hst";
        [ exact Hpath | ].
      rewrite /ex_start.
      iMod ("Hst" $! (um_start_of FsImg.ROOTINO init_cons_pl) with "[%]")
        as "[HP _]"; [ reflexivity | ].
      iModIntro. iLeft. iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ].
      rewrite /cons_P_dead.
      iDestruct "HP" as "[[_ HK] | #HT]"; [ by iLeft | by iRight ].
    - iDestruct "Hd" as (pl') "(%Hpath' & Harm)".
      rewrite (arg_path_of_uniq M pv pl' init_cons_pl Hpath' Hpath).
      iDestruct "Harm" as "[(Hdead & _ & _) | Hterm]".
      + (* THE WALK DIED: the cursor or the miss family, and the
           credential is in whichever one came home *)
        rewrite /namei_walk_dead_era.
        iDestruct "Hdead" as (k d) "(_ & [[HP _] | [HPm _]])".
        * iModIntro. iLeft. iSplitR; [ by iPureIntro | ].
          iSplitR; [ by iPureIntro | ].
          rewrite /cons_P_dead.
          iDestruct "HP" as "[[_ HK] | #HT]"; [ by iLeft | by iRight ].
        * iModIntro. iLeft. iSplitR; [ by iPureIntro | ].
          iSplitR; [ by iPureIntro | ]. rewrite /cons_Pmiss. iExact "HPm".
      + (* THE CALL FAILED AFTER THE WALK: the terminal cursor again *)
        iDestruct "Hterm" as (i) "(HP & _ & _)".
        rewrite /cons_P_dead.
        iDestruct "HP" as "[[%Hz _] | #HT]".
        * exfalso. destruct Hz as [Hz _]. rewrite init_cons_elems_len in Hz.
          discriminate Hz.
        * iModIntro. by iRight.
  Qed.

  (* ---- the FIRST open, at the pin that MISSES ---- *)
  (* AT THE CLASS'S OWN FAMILY TYPE, not at [xfam]: the ecall leaves take
     [sfam], and an [xfam]-typed argument is checked before the instance
     evar is resolved and so does not convert. *)
  Definition init_cons_absent_fam (T K : iProp Σ) (Q : Z -> iProp Σ) : sfam :=
    xfam_open (cons_P_dead T K FsImg.ROOTINO) (cons_Pmiss T K)
      (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I)) Q.

  (* THE SUPPLIER AT THE MISSING PIN, at the CALLER's own literal.  The
     path reading is a premise because it is the one thing that is the
     caller's: /init's literal is at 0x970 in [UCodeInit.init_ro] and sh's
     at [UkSh.sh_cons_pv] in [UCodeShK.shk_ro], and both are one
     [vm_compute] over the caller's own dump. *)
  Lemma cons_sup_absent (N : uk_names Σ) (T K : iProp Σ)
      (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile) (pc : mword 64) :
    Persistent T -> Timeless T -> Timeless K ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv init_cons_pl) ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ->
    (* ...AND ONLY THE ABSENCE LAW, not the whole bundle: /init runs this at
       [K := AppEcho.cons_key r] and sh at a PERSISTENT credential (ruling
       (A)), and at sh's the bundle's mknod conjuncts are false. *)
    init_cons_abs_law T K -∗ app_inv fsc_fs -∗ utext_img (ukn_t N) Img -∗ K -∗
    udepwf_at N m pc USYS_open (init_cons_absent_fam T K (ukn_pay N))
      FsImg.ROOTINO.
  Proof.
    intros HPT HTT HTK Hpath Ha0 Ha1. iIntros "#Habs #Hinv #Hro HK".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (cons_ro_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot (init_cons_absent_fam T K (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false)
              FsImg.ROOTINO M pv (mword_of_int 2)
              eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (eq_trans (tf_of_arg1 m pc) Ha1)).
    cbn [init_cons_absent_fam xfam_open of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    iApply (cons_open_bundle_dead fsc_fs T K M pv (mword_of_int 2)
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : fname) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : fname) (_ : Z) => True%I))
              HPT HTT HTK init_cons_om2_arg (Hpath M Hsro)
              with "Habs Hinv HK").
  Qed.

  (* ---- the SECOND open, at the pin that RESOLVES ---- *)
  Definition init_cons_console_fam (T : iProp Σ) (i : Z) (Q : Z -> iProp Σ)
      : sfam :=
    xfam_open (pobs_P T [FsImg.ROOTINO; i]) (pobs_Pmiss T)
      (pobs_Fo (cons_present_at i) T) Q.

  (* ...AND AT THE RESOLVING PIN.  The credential does NOT appear: the
     flag [AppEcho.cons_made r i] is persistent, which is what lets sh have
     this arm while /init keeps the key. *)
  (* GENERALISED OVER THE FACT THE CREDENTIAL PINS (lane E2): only conjunct
     (i) of the bundle is read here, and it does not mention [Pv]. *)
  Lemma cons_sup_console (N : uk_names Σ) (Pv : aview -> Prop)
      (T K : iProp Σ) (r : echo_names)
      (i : Z) (Img : gmap Z (bv 8)) (pv : mword 64)
      (m : regfile) (pc : mword 64) :
    Persistent T -> Timeless T ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv init_cons_pl) ->
    m !!! Regidx a0_idx = pv ->
    m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ->
    init_cons_laws_at Pv T K r -∗ cons_made r i -∗ app_inv fsc_fs -∗
    utext_img (ukn_t N) Img -∗
    udepwf_at N m pc USYS_open (init_cons_console_fam T i (ukn_pay N))
      FsImg.ROOTINO.
  Proof.
    intros HPT HTT Hpath Ha0 Ha1. iIntros "#Hlaws #Hmade #Hinv #Hro".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (cons_ro_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (init_cons_console_fam T i (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false)
              FsImg.ROOTINO M pv (mword_of_int 2)
              eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (eq_trans (tf_of_arg1 m pc) Ha1)).
    cbn [init_cons_console_fam xfam_open of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    iApply (init_cons_laws_open_console fsc_fs r Pv T K i
              M pv (mword_of_int 2)
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : fname) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : fname) (_ : Z) => True%I))
              init_cons_om2_arg (Hpath M Hsro)
              with "Hlaws Hmade Hinv").
  Qed.

  (* THE LEDGER ARM, READ.  A receipt that says [-1] refutes the           *)
  (* allocation arm (a descriptor is a small nat), and either arm carries  *)
  (* a ledger.                                                            *)
  Definition uk_open_fd_arm (γfd : gname) (l sts fdv' : list fdstate)
      (r : mword 64) : iProp Σ :=
    ((∃ (fd : nat) (rd wr : bool) (t : fdtype),
        ⌜r = (mword_of_int (Z.of_nat fd) : mword 64)
         /\ (fd < NOFILE)%nat
         /\ fdv' = <[fd := FdOpen rd wr t]> sts⌝ ∗
        ualloc γfd l fd (FdOpen rd wr t))
     ∨ (⌜r = (mword_of_int (-1) : mword 64) /\ fdv' = sts⌝ ∗ ustd γfd l))%I.

  Lemma init_cons_fail_std (γfd : gname) (l sts fdv' : list fdstate)
      (r : mword 64) :
    r = (mword_of_int (-1) : mword 64) ->
    uk_open_fd_arm γfd l sts fdv' r -∗ ustd γfd l.
  Proof.
    intros Hr. rewrite /uk_open_fd_arm. iIntros "[Hal | [_ $]]".
    iDestruct "Hal" as (fd rd wr t) "[%Hb _]".
    destruct Hb as (Hfd & Hlt & _). exfalso.
    rewrite Hr in Hfd.
    exact (init_cons_moi_nat_m1 fd Hlt (eq_sym Hfd)).
  Qed.

  Lemma init_cons_any_std (γfd : gname) (l sts fdv' : list fdstate)
      (r : mword 64) :
    uk_open_fd_arm γfd l sts fdv' r -∗ ustd_any γfd.
  Proof.
    rewrite /uk_open_fd_arm. iIntros "[Hal | [_ Hstd]]"; [| by iExists l ].
    iDestruct "Hal" as (fd rd wr t) "[_ Hal]".
    iDestruct (ualloc_ledger with "Hal") as "Hstd". by iExists _.
  Qed.

End UConsOpen.
