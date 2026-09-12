(* ===================================================================== *)
(* UInitConsK.v -- OPEN-PIN's LAST STEP: /init's three console leaves,     *)
(* DISCHARGED at echo's era.                                              *)
(*                                                                        *)
(* [UkInit.v] states /init's console prologue as three LEAF BODIES over    *)
(* three abstract pieces -- the taint [T], the absence credential [K] and  *)
(* the descriptor [stc] -- because the program tier names no application   *)
(* ([UConsLine.v:202]).  This file pays them.  It is [UInitSh.v]'s sibling *)
(* one syscall over: there /init's EXEC deposit is paid out of the claim   *)
(* that /sh is the image's file; here its two OPEN deposits and its MKNOD  *)
(* deposit are paid out of [UInitCons.init_cons_laws] -- the nine          *)
(* application laws -- beside [AppInv.app_inv].                            *)
(*                                                                        *)
(*   S1  the path, READ OFF THE LOANED HEAP: "console" is seven bytes of   *)
(*       /init's own .rodata at 0x970 ([UCodeInit.init_ro]), and           *)
(*       [ArgPath.arg_path_of] is what rows 15 and 17 name.                *)
(*   S2  the deposit's FAMILIES, as [UexecExecInst.xfam] records: the      *)
(*       pinned families in the branch the ecall reads and the trivial     *)
(*       ones in every other.                                              *)
(*   S3  the two key-level rows in the PROCESS's direction.                *)
(*   S4  the three suppliers ([UkRun.udepwf_at], family-named AND          *)
(*       cwd-fixed: a pinned bundle answers at ONE working directory).     *)
(*   S5  the three leaf discharges, each walking usys.S's three-           *)
(*       instruction stub through [UkRunSys.wp_uk_ecall_open_recv_img] /   *)
(*       [wp_uk_ecall_quiet_recv_img] and reading the receipt.             *)
(*   S6  [init_cons_leaves_echo]: the pair /init carries from its entry,   *)
(*       out of the era's record equation.                                *)
(*                                                                        *)
(* WHY THE LEAF BODIES CARRY THE RODATA AND THE ARGUMENT WORDS.  A pinned  *)
(* open is about a PATH, and the path is a string in the caller's own      *)
(* image: the supplier reads [arg_path_of M 0x970 init_cons_pl] off the    *)
(* LOANED heap ([UkRun.udepwf_at] lends it), which needs the persistent    *)
(* view of those bytes ([UCodeInit.init_rodata]) and the knowledge that    *)
(* argument 0 IS 0x970 and the omode is O_RDWR.  Every call site holds all *)
(* three ([UkInitMain] at 0x0e-0x16, 0x64-0x70 and 0x74-0x7e), so the rows *)
(* are premises of the bodies and the leaves lose no force.                *)
(*                                                                        *)
(* WHY THE TWO recv LEAVES GREW AN IMAGE ROW.  The receipt names the path  *)
(* through [arg_path_of (uvis_M W) (xk_a W 0) pl] -- a fact about the      *)
(* TRAPPING KEY's image -- and [urun] hides that image from the caller, so *)
(* the inclusion is readable only inside the leaf, where the persistent    *)
(* view and the heap are in one hand.  [wp_uk_ecall_open_recv_img] /       *)
(* [wp_uk_ecall_quiet_recv_img] are their leaves' walks with that one      *)
(* extra reading (and, at open, the table's length and the row the         *)
(* allocation left, which is what ties the receipt's TYPE to the slot the  *)
(* caller's own ledger decided).                                           *)
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
Require Import UCodeInit UkInit.
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

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  S1.  THE PATH, OFF /init's READ-ONLY IMAGE                             *)
(*                                                                        *)
(*  [UInitSh.init_sh_path_of]'s twin at "console".  The literal is at      *)
(*  0x970 ([UCodeInit.uis_init_12] / [uis_init_7a] compute the pointer and *)
(*  [UkInitMain]'s walk carries it into a0), seven bytes and a NUL.  Both  *)
(*  facts are one [vm_compute] on the dump.                                *)
(* ===================================================================== *)
Lemma init_cons_ro_bytes_bool :
  forallb (fun k : nat =>
      bool_decide (
          UCodeInit.init_ro
            !! uint (add_vec_int (mword_of_int 0x970 : mword 64) (Z.of_nat k))
          = init_cons_pl !! k))
    (seq 0 7) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma init_cons_ro_byte (k : nat) :
  (k < 7)%nat ->
  UCodeInit.init_ro
    !! uint (add_vec_int (mword_of_int 0x970 : mword 64) (Z.of_nat k))
  = init_cons_pl !! k.
Proof.
  intro Hk.
  pose proof (proj1 (forallb_forall _ (seq 0 7)) init_cons_ro_bytes_bool k
                ltac:(apply in_seq; lia)) as H.
  exact (bool_decide_eq_true_1 _ H).
Qed.

Lemma init_cons_ro_nul_bool :
  bool_decide (
      UCodeInit.init_ro
        !! uint (add_vec_int (mword_of_int 0x970 : mword 64) (Z.of_nat 7%nat))
      = Some (bv_0 8)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma init_cons_path_of (M : gmap Z (bv 8)) :
  uimg_sub UCodeInit.init_ro M ->
  arg_path_of M (mword_of_int 0x970 : mword 64) init_cons_pl.
Proof.
  intro Hro.
  split_and!.
  - split.
    + rewrite init_cons_pl_len. clear; lia.
    + intros j b Hj.
      destruct j as [| [| [| [| [| [| [| j]]]]]]]; cbn in Hj;
        try discriminate Hj; injection Hj as <-;
        (intro Hc; apply (f_equal bv_unsigned) in Hc;
         vm_compute in Hc; discriminate Hc).
  - intros j b Hj.
    pose proof (lookup_lt_Some _ _ _ Hj) as Hlt.
    rewrite init_cons_pl_len in Hlt.
    apply Hro. rewrite (init_cons_ro_byte j Hlt). exact Hj.
  - rewrite init_cons_pl_len. apply Hro.
    exact (bool_decide_eq_true_1 _ init_cons_ro_nul_bool).
Qed.

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

Lemma init_cons_dev_major : dev_arg (mword_of_int 1 : mword 64) = CONSOLE.
Proof. vm_compute. reflexivity. Qed.

Lemma init_cons_dev_minor : dev_arg (mword_of_int 0 : mword 64) = 0.
Proof. vm_compute. reflexivity. Qed.

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

Section UInitConsK.
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

  (* the rodata, at the shape the two [_img] leaves take it *)
  Lemma init_rodata_img (g : gname) :
    init_rodata g -∗ utext_img g UCodeInit.init_ro.
  Proof. rewrite /init_rodata. iIntros "#H". iExact "H". Qed.

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

  Definition xfam_mknod (P : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (Q : Z -> iProp Σ) : xfam :=
    {| xf_P     := fun _ _ => True%I;
       xf_Pmiss := fun _ _ => True%I;
       xf_Fo    := pfam_triv (fun _ _ _ => True%I);
       xf_Rs    := True%I;
       rf_F     := pfam_triv (fun _ _ _ _ => True%I);
       cf_P     := fun _ _ => True%I;
       cf_Pmiss := fun _ _ => True%I;
       cf_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_P     := fun _ _ => True%I;
       of_Pmiss := fun _ _ => True%I;
       of_Farm  := pfam_triv (fun _ _ => True%I);
       of_Fun   := pfam_triv (fun _ _ => True%I);
       of_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_Ft    := pfam_triv (fun _ _ _ => True%I);
       wf_Q     := fun _ => True%I;
       wf_tr0   := [];
       nf_P     := P;
       nf_Pmiss := fun _ _ => True%I;
       nf_Farm  := Farm;
       nf_Fun   := Fun;
       nf_Fok   := Fok;
       nf_Fex   := init_mk_Fex;
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

  Lemma sbundle_at_mknod_intro_at (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (cw : Z) (M : gmap Z (bv 8)) (pv : mword 64) (ma mi : Z) :
    uvis_cwd W = cw -> uvis_M W = M ->
    tf_w (uvis_tf W) (tf_arg_idx 0) = pv ->
    dev_arg (tf_w (uvis_tf W) (tf_arg_idx 1)) = ma ->
    dev_arg (tf_w (uvis_tf W) (tf_arg_idx 2)) = mi ->
    mknod_au_at (fs_gamma_L fsc_fs) fsc_fs cw M pv ma mi
      (nf_P f) (nf_Pmiss f) (nf_Farm f) (nf_Fun f) (nf_Fok f) (nf_Fex f) -∗
    sbundle_at X 17 f W.
  Proof.
    intros Hc HM H0 H1 H2. iIntros "H".
    rewrite -Hc -HM -H0 -H1 -H2.
    rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_mknod_elim_at (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (cw : Z) (M : gmap Z (bv 8)) (pv : mword 64) (ma mi : Z)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate)
      (cw' : Z) (cs' : gset gname) :
    uvis_cwd W = cw -> uvis_M W = M ->
    tf_w (uvis_tf W) (tf_arg_idx 0) = pv ->
    dev_arg (tf_w (uvis_tf W) (tf_arg_idx 1)) = ma ->
    dev_arg (tf_w (uvis_tf W) (tf_arg_idx 2)) = mi ->
    spost_at X 17 f W r M' fdv' cw' cs' -∗
    mknod_arms (fs_gamma_L fsc_fs) fsc_fs cw M pv ma mi
      (nf_P f) (nf_Pmiss f) (nf_Farm f) (nf_Fun f) (nf_Fok f) (nf_Fex f) r.
  Proof.
    intros Hc HM H0 H1 H2. iIntros "H".
    rewrite -Hc -HM -H0 -H1 -H2.
    rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  (* =================================================================== *)
  (*  S4.  THE THREE SUPPLIERS                                            *)
  (*                                                                      *)
  (*  [UkRun.udepwf_at]: the deposit at a NAMED family (the program reads  *)
  (*  its receipt at the family it deposited) and at ONE working directory *)
  (*  (a pin is about a PATH, and "console" names a file only relative to  *)
  (*  the directory it is resolved from).  The heap is LENT, which is what *)
  (*  makes the path reading possible at all: [M] is bound by [urun]'s own *)
  (*  existential.                                                        *)
  (* =================================================================== *)
  Lemma init_cons_ro_sub (N : uk_names Σ) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) :
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
    init_rodata (ukn_t N) -∗ ⌜uimg_sub UCodeInit.init_ro M⌝.
  Proof.
    iIntros "Hheap #Hro". iIntros (a b Hb).
    rewrite /init_rodata /utext_img.
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

  Lemma init_cons_sup_absent (N : uk_names Σ) (T K : iProp Σ) (r : echo_names)
      (m : regfile) (pc : mword 64) :
    Persistent T -> Timeless T -> Timeless K ->
    m !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64) ->
    m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ->
    init_cons_laws T K r -∗ app_inv fsc_fs -∗ init_rodata (ukn_t N) -∗ K -∗
    udepwf_at N m pc USYS_open (init_cons_absent_fam T K (ukn_pay N))
      FsImg.ROOTINO.
  Proof.
    intros HPT HTT HTK Ha0 Ha1. iIntros "#Hlaws #Hinv #Hro HK".
    iDestruct "Hlaws" as "(_ & _ & #Habs & _)".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (init_cons_ro_sub N M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot (init_cons_absent_fam T K (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false)
              FsImg.ROOTINO M (mword_of_int 0x970) (mword_of_int 2)
              eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (eq_trans (tf_of_arg1 m pc) Ha1)).
    cbn [init_cons_absent_fam xfam_open of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    iApply (cons_open_bundle_dead fsc_fs T K M (mword_of_int 0x970)
              (mword_of_int 2)
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : fname) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : fname) (_ : Z) => True%I))
              HPT HTT HTK init_cons_om2_arg (init_cons_path_of M Hsro)
              with "Habs Hinv HK").
  Qed.

  (* ---- the SECOND open, at the pin that RESOLVES ---- *)
  Definition init_cons_console_fam (T : iProp Σ) (i : Z) (Q : Z -> iProp Σ)
      : sfam :=
    xfam_open (pobs_P T [FsImg.ROOTINO; i]) (pobs_Pmiss T)
      (pobs_Fo (cons_present_at i) T) Q.

  Lemma init_cons_sup_console (N : uk_names Σ) (T K : iProp Σ) (r : echo_names)
      (i : Z) (m : regfile) (pc : mword 64) :
    Persistent T -> Timeless T ->
    m !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64) ->
    m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ->
    init_cons_laws T K r -∗ cons_made r i -∗ app_inv fsc_fs -∗
    init_rodata (ukn_t N) -∗
    udepwf_at N m pc USYS_open (init_cons_console_fam T i (ukn_pay N))
      FsImg.ROOTINO.
  Proof.
    intros HPT HTT Ha0 Ha1. iIntros "#Hlaws #Hmade #Hinv #Hro".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (init_cons_ro_sub N M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (init_cons_console_fam T i (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false)
              FsImg.ROOTINO M (mword_of_int 0x970) (mword_of_int 2)
              eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (eq_trans (tf_of_arg1 m pc) Ha1)).
    cbn [init_cons_console_fam xfam_open of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    iApply (init_cons_laws_open_console fsc_fs r T K i
              M (mword_of_int 0x970) (mword_of_int 2)
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : fname) (_ : Z) => True%I))
              (pfam_triv (fun (_ : aview) (_ : Z) (_ : fname) (_ : Z) => True%I))
              init_cons_om2_arg (init_cons_path_of M Hsro)
              with "Hlaws Hmade Hinv").
  Qed.

  (* ---- the MKNOD ---- *)
  Definition init_cons_mknod_fam (T K : iProp Σ) (r : echo_names)
      (Q : Z -> iProp Σ) : sfam :=
    xfam_mknod (init_mk_P T) (init_mk_Farm T K) (init_mk_Fun T K)
      (init_mk_Fok r T K) Q.

  Lemma init_cons_sup_mknod (N : uk_names Σ) (T K : iProp Σ) (r : echo_names)
      (m : regfile) (pc : mword 64) :
    Persistent T -> Timeless T -> Timeless K ->
    (forall v : aview, Timeless (app_pred app_run v)) ->
    m !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64) ->
    m !!! Regidx a1_idx = (mword_of_int 1 : mword 64) ->
    m !!! Regidx a2_idx = (mword_of_int 0 : mword 64) ->
    init_cons_laws T K r -∗ app_inv fsc_fs -∗ init_rodata (ukn_t N) -∗ K -∗
    udepwf_at N m pc 17 (init_cons_mknod_fam T K r (ukn_pay N)) FsImg.ROOTINO.
  Proof.
    intros HPT HTT HTK HTL Ha0 Ha1 Ha2.
    iIntros "#Hlaws #Hinv #Hro HK".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (init_cons_ro_sub N M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_mknod_intro_at uslot
              (init_cons_mknod_fam T K r (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false)
              FsImg.ROOTINO M (mword_of_int 0x970) CONSOLE 0
              eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              ltac:(unfold tf_w; cbn [uvis_tf uvis_of_run];
                    rewrite (tf_of_arg1 m pc) Ha1;
                    exact init_cons_dev_major)
              ltac:(unfold tf_w; cbn [uvis_tf uvis_of_run];
                    rewrite (tf_of_arg2 m pc) Ha2;
                    exact init_cons_dev_minor)).
    cbn [init_cons_mknod_fam xfam_mknod nf_P nf_Pmiss nf_Farm nf_Fun
         nf_Fok nf_Fex].
    iApply (init_cons_laws_mknod_bundle fsc_fs r T K M (mword_of_int 0x970)
              (init_cons_path_of M Hsro) with "Hlaws Hinv HK").
  Qed.

  (* =================================================================== *)
  (*  S5.  THE THREE LEAF DISCHARGES                                      *)
  (*                                                                      *)
  (*  usys.S's stub is three instructions -- [c.li a7,n], [ecall],         *)
  (*  [c.jr ra] -- and each walk is [UkInit.wp_kinit_open]'s (resp.        *)
  (*  [wp_kinit_mknod]'s) with the RECEIPT-KEEPING leaf in the middle.     *)
  (* =================================================================== *)

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

  (* ------------------------------------------------------------------- *)
  (* THE FIRST open, AND THE REPAIR ARM'S SECOND ONE WHEN THE MKNOD FAILED *)
  (* ------------------------------------------------------------------- *)
  Lemma init_open_absent_leaf_holds (N : uk_names Σ) (T K : iProp Σ)
      (r : echo_names) :
    Persistent T -> Timeless T -> Timeless K ->
    init_cons_laws T K r -∗ app_inv fsc_fs -∗
    □ UkInit.uki_open_absent_leaf N T K.
  Proof.
    intros HPT HTT HTK. iIntros "#Hlaws #Hinv !>".
    iIntros (h m l avail) "#Hcode #Hro %Hargs Hrun Hcwd Hstd HK Hcont".
    destruct Hargs as [Ha0 Ha1].
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & Hopen & _ & _ & _ & _ & _ & _ & _).
    rewrite Hopen.
    (* ---- 0x3b2  c.li a7,15 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3b2)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3b2 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3b2 : mword 64) 2
                 = mword_of_int 0x3b4)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 15 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    assert (Ha0' : m1 !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Ha1' : m1 !!! Regidx a1_idx = (mword_of_int 2 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha1. }
    (* ---- 0x3b4  ecall -- the RECEIPT-KEEPING open leaf ---- *)
    iApply (wp_uk_ecall_open_recv_img N h1 m1 (mword_of_int 0x3b4) l avail
              (init_cons_absent_fam T K (ukn_pay N)) FsImg.ROOTINO
              UCodeInit.init_ro
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [] Hrun Hcwd [HK] Hstd").
    { iApply (uis_init_3b4 with "Hcode"). }
    { iApply (init_rodata_img with "Hro"). }
    { iApply (init_cons_sup_absent N T K r m1 (mword_of_int 0x3b4)
                HPT HTT HTK Ha0' Ha1' with "Hlaws Hinv Hro HK"). }
    assert (E1 : add_vec_int (mword_of_int 0x3b4 : mword 64) 4
                 = mword_of_int 0x3b8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    assert (Hpath : arg_path_of (uvis_M W) (mword_of_int 0x970 : mword 64)
                      init_cons_pl)
      by exact (init_cons_path_of (uvis_M W) Himg).
    (* ---- the receipt: the walk died at hop 0, so the call returned -1
       and the table did not move -- or the application is tainted ---- *)
    iDestruct (spost_at_open_elim_at uslot
                 (init_cons_absent_fam T K (ukn_pay N)) W
                 FsImg.ROOTINO (uvis_M W) (mword_of_int 0x970)
                 (mword_of_int 2) ret M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0')
                 ltac:(rewrite Hk1; exact Ha1')
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt init_cons_om2_create;
           cbn [init_cons_absent_fam xfam_open of_P of_Pmiss of_Fo of_Ft])
      in "Hrc".
    iApply fupd_wp_triv.
    iMod (cons_open_dead_recv fsc_fs T K
            (uvis_M W) (mword_of_int 0x970) (mword_of_int 2)
            (pfam_triv (fun (_ : aview) (_ : Z) (_ : anode) => True%I))
            (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => True%I))
            (uvis_fd W) ret fdv' HPT Hpath with "Hrc") as "Hans".
    iModIntro.
    (* ---- 0x3b8  c.jr ra ---- *)
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3b8) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3b8 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[(%Hr & _ & [HK | #HT]) | #HT]".
    - iLeft. iSplitR; [ by iPureIntro | ]. iFrame "HK".
      iApply (init_cons_fail_std (ukn_fd N) l (uvis_fd W) fdv' ret Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
    - iRight. iFrame "HT".
      iApply (init_cons_any_std (ukn_fd N) l (uvis_fd W) fdv' ret with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
    - iRight. iFrame "HT".
      iApply (init_cons_any_std (ukn_fd N) l (uvis_fd W) fdv' ret with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE SECOND open, AT THE RESOLVING PIN                                 *)
  (* ------------------------------------------------------------------- *)
  Lemma init_open_console_leaf_holds (N : uk_names Σ) (T K : iProp Σ)
      (r : echo_names) (i : Z) :
    Persistent T -> Timeless T ->
    init_cons_laws T K r -∗ cons_made r i -∗ app_inv fsc_fs -∗
    □ UkInit.uki_open_console_leaf N T init_cons_fd.
  Proof.
    intros HPT HTT. iIntros "#Hlaws #Hmade #Hinv !>".
    iIntros (h m avail) "#Hcode #Hro %Hargs Hrun Hcwd Hstd Hcont".
    destruct Hargs as [Ha0 Ha1].
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & Hopen & _ & _ & _ & _ & _ & _ & _).
    rewrite Hopen.
    (* ---- 0x3b2  c.li a7,15 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3b2)
              (mword_of_int 15 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3b2 with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3b2 : mword 64) 2
                 = mword_of_int 0x3b4)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 15 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 15 : mword 64)]> m).
    assert (Ha0' : m1 !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Ha1' : m1 !!! Regidx a1_idx = (mword_of_int 2 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                 (mword_of_int 15 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha1. }
    (* ---- 0x3b4  ecall ---- *)
    iApply (wp_uk_ecall_open_recv_img N h1 m1 (mword_of_int 0x3b4) ufd_l0 avail
              (init_cons_console_fam T i (ukn_pay N)) FsImg.ROOTINO
              UCodeInit.init_ro
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 15 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] [] Hrun Hcwd [] Hstd").
    { iApply (uis_init_3b4 with "Hcode"). }
    { iApply (init_rodata_img with "Hro"). }
    { iApply (init_cons_sup_console N T K r i m1 (mword_of_int 0x3b4)
                HPT HTT Ha0' Ha1' with "Hlaws Hmade Hinv Hro"). }
    assert (E1 : add_vec_int (mword_of_int 0x3b4 : mword 64) 4
                 = mword_of_int 0x3b8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    assert (Hpath : arg_path_of (uvis_M W) (mword_of_int 0x970 : mword 64)
                      init_cons_pl)
      by exact (init_cons_path_of (uvis_M W) Himg).
    iDestruct (spost_at_open_elim_at uslot
                 (init_cons_console_fam T i (ukn_pay N)) W
                 FsImg.ROOTINO (uvis_M W) (mword_of_int 0x970)
                 (mword_of_int 2) ret M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0')
                 ltac:(rewrite Hk1; exact Ha1')
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt init_cons_om2_create) in "Hrc".
    iDestruct (init_cons_recv fsc_fs T i
                 (uvis_M W) (mword_of_int 0x970) (mword_of_int 2)
                 (pfam_triv (fun (_ : aview) (_ : Z) (_ : list (bv 8)) => True%I))
                 (uvis_fd W) ret fdv' Hpath with "Hrc") as "Hans".
    (* ---- 0x3b8  c.jr ra ---- *)
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 15 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3b8) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3b8 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[Hfd Hans] Hcwd Hrun").
    iDestruct "Hans" as "[[%Hr _] | [[%Hrcpt _] | #HT]]".
    - (* the call failed after the walk: nothing moved *)
      iRight. iLeft. iSplitR; [ by iPureIntro | ].
      iApply (init_cons_fail_std (ukn_fd N) ufd_l0 (uvis_fd W) fdv' ret Hr
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
    - (* THE CONSOLE: the receipt names the TYPE, the ledger the NUMBER *)
      destruct (init_cons_open_fd (mword_of_int 2) (uvis_fd W) ret fdv'
                  init_cons_om2_arg Hrcpt) as (fd0 & Hr0 & Hcl0 & Hfdv0).
      assert (Hlt0 : (fd0 < NOFILE)%nat).
      { rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hcl0). }
      iDestruct "Hfd" as "[Hal | [%Hb _]]"; last first.
      { exfalso. destruct Hb as [Hrm _].
        exact (init_cons_moi_nat_m1 fd0 Hlt0 (eq_trans (eq_sym Hr0) Hrm)). }
      iDestruct "Hal" as (fd rd wr t) "[%Hb Hal]".
      destruct Hb as (Hr1 & Hlt1 & Hfdv1).
      assert (Hfdeq : fd = fd0)
        by exact (init_cons_moi_nat_inj fd fd0 Hlt1 Hlt0
                    (eq_trans (eq_sym Hr1) Hr0)).
      subst fd0.
      (* the two spellings of the resume view agree at the slot the call
         wrote, so the receipt's TYPE is the ledger's *)
      assert (Hfdlt : (fd < length (uvis_fd W))%nat)
        by (rewrite Hlen; exact Hlt1).
      assert (Hins : <[fd := FdOpen rd wr t]> (uvis_fd W)
                     = <[fd := init_cons_fd]> (uvis_fd W))
        by exact (eq_trans (eq_sym Hfdv1) Hfdv0).
      assert (Hst : FdOpen rd wr t = init_cons_fd).
      { pose proof (list_lookup_insert (uvis_fd W) fd (FdOpen rd wr t) Hfdlt)
          as Hl1.
        pose proof (list_lookup_insert (uvis_fd W) fd init_cons_fd Hfdlt)
          as Hl2.
        rewrite Hins in Hl1. rewrite Hl2 in Hl1.
        injection Hl1 as Hrd Hwr Ht.
        rewrite <- Hrd. rewrite <- Hwr. rewrite <- Ht. reflexivity. }
      rewrite Hst.
      iDestruct (ufd_alloc0 (ukn_fd N) init_cons_fd fd with "Hal")
        as "[%Hfd0 Hstd]".
      subst fd.
      iLeft. iFrame "Hstd". iPureIntro. rewrite Hr1. reflexivity.
    - iRight. iRight. iFrame "HT".
      iApply (init_cons_any_std (ukn_fd N) ufd_l0 (uvis_fd W) fdv' ret
                with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE MKNOD: where the console node comes into existence                *)
  (* ------------------------------------------------------------------- *)
  Lemma init_mknod_leaf_holds (N : uk_names Σ) (T K : iProp Σ)
      (r : echo_names) :
    Persistent T -> Timeless T -> Timeless K ->
    (forall v : aview, Timeless (app_pred app_run v)) ->
    init_cons_laws T K r -∗ app_inv fsc_fs -∗
    □ UkInit.uki_mknod_leaf N T K init_cons_fd.
  Proof.
    intros HPT HTT HTK HTL. iIntros "#Hlaws #Hinv !>".
    iIntros (h m avail) "#Hcode #Hro %Hargs Hrun Hcwd HK Hcont".
    destruct Hargs as (Ha0 & Ha1 & Ha2).
    destruct init_syms_pins
      as (_ & _ & _ & _ & _ & _ & Hmknod & _ & _ & _ & _ & _ & _).
    rewrite Hmknod.
    (* ---- 0x3ba  c.li a7,17 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0x3ba)
              (mword_of_int 17 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_init_3ba with "Hcode"). }
    assert (E0 : add_vec_int (mword_of_int 0x3ba : mword 64) 2
                 = mword_of_int 0x3bc)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 17 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 17 : mword 64)]> m).
    assert (Ha0' : m1 !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a0_idx)
                 (mword_of_int 17 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha0. }
    assert (Ha1' : m1 !!! Regidx a1_idx = (mword_of_int 1 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a1_idx)
                 (mword_of_int 17 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha1. }
    assert (Ha2' : m1 !!! Regidx a2_idx = (mword_of_int 0 : mword 64)).
    { unfold m1.
      rewrite (upd_ne m (Regidx a7_idx) (Regidx a2_idx)
                 (mword_of_int 17 : mword 64)
                 ltac:(vm_compute; discriminate)).
      exact Ha2. }
    (* ---- 0x3bc  ecall -- the RECEIPT-KEEPING quiet leaf ---- *)
    iApply (wp_uk_ecall_quiet_recv_img N h1 m1 (mword_of_int 0x3bc) 17 avail
              (init_cons_mknod_fam T K r (ukn_pay N)) FsImg.ROOTINO
              UCodeInit.init_ro
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 17 : mword 64));
                    vm_compute; reflexivity)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(vm_compute; reflexivity)
              with "[] [] Hrun Hcwd [HK]").
    { iApply (uis_init_3bc with "Hcode"). }
    { iApply (init_rodata_img with "Hro"). }
    { iApply (init_cons_sup_mknod N T K r m1 (mword_of_int 0x3bc)
                HPT HTT HTK HTL Ha0' Ha1' Ha2'
                with "Hlaws Hinv Hro HK"). }
    assert (E1 : add_vec_int (mword_of_int 0x3bc : mword 64) 4
                 = mword_of_int 0x3c0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E1.
    iIntros (h2 ret W cs') "%Himg %Hk0 %Hk1 %Hk2 %Hcw Hpost Hcwd Hrun".
    assert (Hpath : arg_path_of (uvis_M W) (mword_of_int 0x970 : mword 64)
                      init_cons_pl)
      by exact (init_cons_path_of (uvis_M W) Himg).
    iDestruct (spost_at_mknod_elim_at uslot
                 (init_cons_mknod_fam T K r (ukn_pay N)) W
                 FsImg.ROOTINO (uvis_M W) (mword_of_int 0x970) CONSOLE 0
                 ret (uvis_M W) (uvis_fd W) FsImg.ROOTINO cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0')
                 ltac:(rewrite Hk1 Ha1'; exact init_cons_dev_major)
                 ltac:(rewrite Hk2 Ha2'; exact init_cons_dev_minor)
                 with "Hpost") as "Harms".
    (* ---- 0x3c0  c.jr ra ---- *)
    set (m2 := <[Regidx a0_idx := ret]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 17 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0x3c0) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_init_3c0 with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "[Harms] Hcwd Hrun").
    rewrite /mknod_arms.
    iDestruct "Harms" as "[[_ Hok] | [_ Hfail]]".
    - (* THE NODE EXISTS: the flag, and hence the SECOND open's leaf *)
      iDestruct (init_cons_mknod_recv fsc_fs r T K
                   (uvis_M W) (mword_of_int 0x970) Hpath with "Hok") as "Hm".
      iDestruct "Hm" as "[Hm | #HT]"; last first.
      { iRight. iRight. iExact "HT". }
      iDestruct "Hm" as (i) "#Hmade".
      iDestruct (init_open_console_leaf_holds N T K r i HPT HTT
                   with "Hlaws Hmade Hinv") as "#Hlf".
      iLeft. iExact "Hlf".
    - (* THE MKNOD FAILED: the credential comes back *)
      iDestruct (init_cons_mknod_fail_recv fsc_fs r T K (fun _ _ => True%I)
                   (uvis_M W) (mword_of_int 0x970) with "Hfail") as "Hk".
      iDestruct "Hk" as "[HK | #HT]"; [ iRight; iLeft; iExact "HK" |].
      iRight. iRight. iExact "HT".
  Qed.

  (* =================================================================== *)
  (*  S6.  THE PAIR /init CARRIES FROM ITS ENTRY, at echo's era            *)
  (*                                                                      *)
  (*  The premise is the era's record equation -- the one                  *)
  (*  [App.xv6_app_adequacy]'s [Hinit_boot] already carries and E2's boot  *)
  (*  arm supplies -- and the rewrite goes FIRST, before anything typed at *)
  (*  [app_names file_app] is introduced ([UInitCons.init_cons_laws_echo]  *)
  (*  is the precedent and its note says why).                             *)
  (* =================================================================== *)
  Lemma init_cons_leaves_echo (γ : echo_fixed) (r : echo_names) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ,
         UkInit.init_cons_leaves N (echo_taint γ) (cons_key r) init_cons_fd).
  Proof.
    intros Heq.
    assert (HTL : forall v : aview, Timeless (app_pred app_run v)).
    { rewrite Heq. cbn [app_pred app_run]. intro v. apply _. }
    iIntros "#Hinv".
    iDestruct (init_cons_laws_echo γ r Heq) as "#Hlaws".
    iModIntro. iIntros (N). rewrite /UkInit.init_cons_leaves. iSplit.
    - iApply (init_open_absent_leaf_holds N (echo_taint γ) (cons_key r) r
                ltac:(apply _) ltac:(apply _) ltac:(apply _)
                with "Hlaws Hinv").
    - iApply (init_mknod_leaf_holds N (echo_taint γ) (cons_key r) r
                ltac:(apply _) ltac:(apply _) ltac:(apply _) HTL
                with "Hlaws Hinv").
  Qed.

End UInitConsK.
