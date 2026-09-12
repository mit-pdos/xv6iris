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
Require Import UConsOpen.   (* the shared console open: the dead walk, the
                               two suppliers, the two key-level rows *)
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

Lemma init_cons_dev_major : dev_arg (mword_of_int 1 : mword 64) = CONSOLE.
Proof. vm_compute. reflexivity. Qed.

Lemma init_cons_dev_minor : dev_arg (mword_of_int 0 : mword 64) = 0.
Proof. vm_compute. reflexivity. Qed.


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
  (*  S4.  THE SUPPLIERS.  The two OPEN ones are [UConsOpen]'s, at /init's *)
  (*  own literal; the MKNOD one stays here, because only /init calls it.  *)
  (* =================================================================== *)
  Lemma init_cons_ro_sub (N : uk_names Σ) (M : gmap Z (bv 8))
      (pm : gmap (mword 27) uperm) (sz : Z) :
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
    init_rodata (ukn_t N) -∗ ⌜uimg_sub UCodeInit.init_ro M⌝.
  Proof.
    iIntros "Hheap #Hro".
    iApply (cons_ro_sub N UCodeInit.init_ro M pm sz with "Hheap [Hro]").
    iApply (init_rodata_img with "Hro").
  Qed.



  (* /INIT'S INSTANCE of [UConsOpen.cons_sup_absent].  AND ONLY THE
     ABSENCE LAW, not the whole bundle: /init runs it at the KEY and, once
     its mknod has failed, at the SEAL ([AppEcho.cons_never]). *)
  Lemma init_cons_sup_absent (N : uk_names Σ) (T K : iProp Σ)
      (m : regfile) (pc : mword 64) :
    Persistent T -> Timeless T -> Timeless K ->
    m !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64) ->
    m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ->
    init_cons_abs_law T K -∗ app_inv fsc_fs -∗ init_rodata (ukn_t N) -∗ K -∗
    udepwf_at N m pc USYS_open (init_cons_absent_fam T K (ukn_pay N))
      FsImg.ROOTINO.
  Proof.
    intros HPT HTT HTK Ha0 Ha1. iIntros "#Habs #Hinv #Hro HK".
    iApply (cons_sup_absent N T K UCodeInit.init_ro
              (mword_of_int 0x970) m pc HPT HTT HTK
              (fun M H => init_cons_path_of M H) Ha0 Ha1
              with "Habs Hinv [Hro] HK").
    iApply (init_rodata_img with "Hro").
  Qed.


  (* /INIT'S INSTANCE of [UConsOpen.cons_sup_console]: its own literal, at
     0x970 in its own .rodata. *)
  Lemma init_cons_sup_console (N : uk_names Σ) (Pv : aview -> Prop)
      (T K : iProp Σ) (r : echo_names)
      (i : Z) (m : regfile) (pc : mword 64) :
    Persistent T -> Timeless T ->
    m !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64) ->
    m !!! Regidx a1_idx = (mword_of_int 2 : mword 64) ->
    init_cons_laws_at Pv T K r -∗ cons_made r i -∗ app_inv fsc_fs -∗
    init_rodata (ukn_t N) -∗
    udepwf_at N m pc USYS_open (init_cons_console_fam T i (ukn_pay N))
      FsImg.ROOTINO.
  Proof.
    intros HPT HTT Ha0 Ha1. iIntros "#Hlaws #Hmade #Hinv #Hro".
    iApply (cons_sup_console N Pv T K r i UCodeInit.init_ro
              (mword_of_int 0x970) m pc HPT HTT
              (fun M H => init_cons_path_of M H) Ha0 Ha1
              with "Hlaws Hmade Hinv [Hro]").
    iApply (init_rodata_img with "Hro").
  Qed.

  (* ---- the MKNOD ---- *)
  Definition init_cons_mknod_fam (Pv : aview -> Prop) (T K : iProp Σ)
      (r : echo_names) (Q : Z -> iProp Σ) : sfam :=
    xfam_mknod (init_mk_P T) (init_mk_Farm Pv T K) (init_mk_Fun T K)
      (init_mk_Fok r T K) Q.

  Lemma init_cons_sup_mknod (N : uk_names Σ) (Pv : aview -> Prop)
      (T K : iProp Σ) (r : echo_names)
      (m : regfile) (pc : mword 64) :
    Persistent T -> Timeless T -> Timeless K ->
    (forall v : aview, Timeless (app_pred app_run v)) ->
    m !!! Regidx a0_idx = (mword_of_int 0x970 : mword 64) ->
    m !!! Regidx a1_idx = (mword_of_int 1 : mword 64) ->
    m !!! Regidx a2_idx = (mword_of_int 0 : mword 64) ->
    init_cons_laws_at Pv T K r -∗ app_inv fsc_fs -∗
    init_rodata (ukn_t N) -∗ K -∗
    udepwf_at N m pc 17 (init_cons_mknod_fam Pv T K r (ukn_pay N)) FsImg.ROOTINO.
  Proof.
    intros HPT HTT HTK HTL Ha0 Ha1 Ha2.
    iIntros "#Hlaws #Hinv #Hro HK".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (init_cons_ro_sub N M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_mknod_intro_at uslot
              (init_cons_mknod_fam Pv T K r (ukn_pay N))
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
    iApply (init_cons_laws_mknod_bundle fsc_fs r Pv T K M (mword_of_int 0x970)
              (init_cons_path_of M Hsro) with "Hlaws Hinv HK").
  Qed.

  (* =================================================================== *)
  (*  S5.  THE THREE LEAF DISCHARGES                                      *)
  (*                                                                      *)
  (*  usys.S's stub is three instructions -- [c.li a7,n], [ecall],         *)
  (*  [c.jr ra] -- and each walk is [UkInit.wp_kinit_open]'s (resp.        *)
  (*  [wp_kinit_mknod]'s) with the RECEIPT-KEEPING leaf in the middle.     *)
  (* =================================================================== *)


  (* ------------------------------------------------------------------- *)
  (* THE FIRST open, AND THE REPAIR ARM'S SECOND ONE WHEN THE MKNOD FAILED *)
  (* ------------------------------------------------------------------- *)
  Lemma init_open_absent_leaf_holds (N : uk_names Σ) (T K : iProp Σ) :
    Persistent T -> Timeless T -> Timeless K ->
    init_cons_abs_law T K -∗ app_inv fsc_fs -∗
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
    { iApply (init_cons_sup_absent N T K m1 (mword_of_int 0x3b4)
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
  Lemma init_open_console_leaf_holds (N : uk_names Σ) (Pv : aview -> Prop)
      (T K : iProp Σ) (r : echo_names) (i : Z) :
    Persistent T -> Timeless T ->
    init_cons_laws_at Pv T K r -∗ cons_made r i -∗ app_inv fsc_fs -∗
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
    { iApply (init_cons_sup_console N Pv T K r i m1 (mword_of_int 0x3b4)
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
  Lemma init_mknod_leaf_holds (N : uk_names Σ) (Pv : aview -> Prop)
      (T K : iProp Σ) (r : echo_names) :
    Persistent T -> Timeless T -> Timeless K ->
    (forall v : aview, Timeless (app_pred app_run v)) ->
    init_cons_laws_at Pv T K r -∗
    (* WHAT A FAILED MKNOD LEAVES, in the caller's own vocabulary.  The
       call can fail at either arm of the dance, and what its credential
       becomes differs: at the KEY arm the key is SPENT into the claim and
       what comes back is the persistent SEAL beside the dead walk's leaf
       again ([AppEcho.echo_cons_seal_step], lane SH-OPEN); at the FLAG arm
       the credential IS the flag, the node is still there, and the second
       open is the pinned one.  A [□] and a fupd, because the seal is an
       update of the claim under [AppInv.app_inv]
       ([AppInv.app_claim_update]). *)
    □ (K ={⊤}=∗ UkInit.uki_mknod_out N T (init_cons_cred T r) init_cons_fd) -∗
    app_inv fsc_fs -∗
    □ UkInit.uki_mknod_leaf N T K (init_cons_cred T r) init_cons_fd.
  Proof.
    intros HPT HTT HTK HTL. iIntros "#Hlaws #Hfl #Hinv !>".
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
              (init_cons_mknod_fam Pv T K r (ukn_pay N)) FsImg.ROOTINO
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
    { iApply (init_cons_sup_mknod N Pv T K r m1 (mword_of_int 0x3bc)
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
                 (init_cons_mknod_fam Pv T K r (ukn_pay N)) W
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
    iApply fupd_wp_triv.
    iAssert (|={⊤}=> UkInit.uki_mknod_out N T (init_cons_cred T r) init_cons_fd)%I
      with "[Harms]" as ">Hout".
    { rewrite /mknod_arms.
      iDestruct "Harms" as "[[_ Hok] | [_ Hfail]]".
      - (* THE NODE EXISTS: the flag, and hence the SECOND open's leaf *)
        iDestruct (init_cons_mknod_recv fsc_fs r Pv T K
                     (uvis_M W) (mword_of_int 0x970) Hpath with "Hok") as "Hm".
        iDestruct "Hm" as "[Hm | #HT]"; last first.
        { iModIntro. rewrite /UkInit.uki_mknod_out.
          iRight. iRight. iExact "HT". }
        iDestruct "Hm" as (i) "#Hmade".
        iDestruct (init_open_console_leaf_holds N Pv T K r i HPT HTT
                     with "Hlaws Hmade Hinv") as "#Hlf".
        iModIntro. rewrite /UkInit.uki_mknod_out. iLeft. iFrame "Hlf".
        iApply (init_cons_cred_of_made T r i with "Hmade").
      - (* THE MKNOD FAILED: what the credential becomes is the caller's *)
        iDestruct (init_cons_mknod_fail_recv fsc_fs r Pv T K
                     (fun _ _ => True%I)
                     (uvis_M W) (mword_of_int 0x970) with "Hfail") as "Hk".
        iDestruct "Hk" as "[HK | #HT]"; last first.
        { iModIntro. rewrite /UkInit.uki_mknod_out.
          iRight. iRight. iExact "HT". }
        iApply ("Hfl" with "HK"). }
    iModIntro.
    iApply ("Hcont" $! h3 ret with "Hout Hcwd Hrun").
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
  (* THE SEAL'S ABSENCE LAW at echo's era: the credential /init keeps when
     its mknod FAILED, and the one sh's own first open then runs on (lane
     SH-OPEN).  [AppEcho.cons_never] is the ghost FRAGMENT, so it is
     persistent and timeless and the linear form is free. *)
  Lemma init_cons_never_abs_law (γ : echo_fixed) (r : echo_names) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    ⊢ init_cons_abs_law (echo_taint γ) (cons_never r).
  Proof.
    intros Heq. rewrite /init_cons_abs_law /init_cons_pin_law.
    rewrite Heq. cbn [app_pred app_run app_names].
    iIntros "!>" (v) "#Hn Hp".
    iDestruct (echo_cons_never_law γ r) as "#Hl".
    iDestruct ("Hl" with "Hn") as "#Hl'".
    iDestruct ("Hl'" $! v with "Hp") as "[Hp Hc]". iFrame "Hp Hn Hc".
  Qed.

  (* ...and the STEP that mints it, at the era's record: the key goes into
     the claim and the credential comes out ([AppEcho.echo_cons_seal_step]).
     Stated at the ambient record's [app_pred] so that
     [AppInv.app_claim_update] applies without rewriting its caller's
     goal. *)
  Lemma init_cons_seal_law_echo (γ : echo_fixed) (r : echo_names) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    ⊢ □ (∀ av : aview, cons_key r -∗ ▷ app_pred app_run av
           ={⊤ ∖ ↑appN}=∗
           ▷ app_pred app_run av ∗ (cons_never r ∨ echo_taint γ)).
  Proof.
    intros Heq. rewrite Heq. cbn [app_pred app_run app_names].
    iIntros "!>" (av) "HK >Hp".
    iMod (echo_cons_seal_step γ r av with "HK Hp") as "[Hp Hn]".
    iModIntro. iFrame "Hp Hn".
  Qed.

  (* WHAT A FAILED MKNOD LEAVES AT THE KEY ARM: the key is SPENT and what
     comes back is the seal, its own dead-walk leaf, and the credential the
     shell is handed. *)
  Lemma init_cons_seal_out_echo (N : uk_names Σ) (γ : echo_fixed)
      (r : echo_names) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    app_inv fsc_fs -∗
    □ (cons_key r ={⊤}=∗
         UkInit.uki_mknod_out N (echo_taint γ)
           (init_cons_cred (echo_taint γ) r) init_cons_fd).
  Proof.
    intros Heq. iIntros "#Hinv !> HK".
    iDestruct (init_cons_never_abs_law γ r Heq) as "#Habs".
    iMod (app_claim_update ⊤ fsc_fs (cons_key r)
            (cons_never r ∨ echo_taint γ)%I ltac:(set_solver)
            with "Hinv [] HK") as "Hn".
    { iApply (init_cons_seal_law_echo γ r Heq). }
    iModIntro. rewrite /UkInit.uki_mknod_out.
    iDestruct "Hn" as "[#Hn | #HT]"; last first.
    { iRight. iRight. iExact "HT". }
    iRight. iLeft. iExists (cons_never r).
    iDestruct (init_open_absent_leaf_holds N (echo_taint γ) (cons_never r)
                 ltac:(apply _) ltac:(apply _) ltac:(apply _)
                 with "Habs Hinv") as "#Hlf".
    iSplitR; [ iExact "Hlf" | ]. iSplitR; [ iExact "Hn" | ].
    iApply (init_cons_cred_of_never (echo_taint γ) r with "Hn").
  Qed.

  (* ---- THE MISS ARM'S PAIR, at echo's era ---- *)
  Lemma init_cons_leaves_echo (γ : echo_fixed) (r : echo_names) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ,
         UkInit.init_cons_leaves N (echo_taint γ) (cons_key r)
           (init_cons_cred (echo_taint γ) r) init_cons_fd).
  Proof.
    intros Heq.
    assert (HTL : forall v : aview, Timeless (app_pred app_run v)).
    { rewrite Heq. cbn [app_pred app_run]. intro v. apply _. }
    iIntros "#Hinv".
    iDestruct (init_cons_laws_echo γ r Heq) as "#Hlaws".
    iModIntro. iIntros (N). rewrite /UkInit.init_cons_leaves. iSplit.
    - iApply (init_open_absent_leaf_holds N (echo_taint γ) (cons_key r)
                ltac:(apply _) ltac:(apply _) ltac:(apply _)
                with "[] Hinv").
      rewrite /init_cons_laws /init_cons_laws_at.
      iDestruct "Hlaws" as "(_ & _ & #Hc & _)". iExact "Hc".
    - iApply (init_mknod_leaf_holds N cons_absent (echo_taint γ) (cons_key r) r
                ltac:(apply _) ltac:(apply _) ltac:(apply _) HTL
                with "Hlaws [] Hinv").
      iApply (init_cons_seal_out_echo N γ r Heq with "Hinv").
  Qed.

  (* the credential the FLAG arm hands the shell *)
  Lemma init_cons_cred_made_echo (γ : echo_fixed) (r : echo_names) (i0 : Z) :
    cons_made r i0 -∗ init_cons_cred (echo_taint γ) r.
  Proof. iApply (init_cons_cred_of_made (echo_taint γ) r i0). Qed.

  (* ---- THE FLAG ARM'S PAIR (lane E2): the node is already there ---- *)
  Lemma init_cons_hit_echo (γ : echo_fixed) (r : echo_names) (i0 : Z) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    cons_made r i0 -∗ app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ,
         □ UkInit.uki_open_console_leaf N (echo_taint γ) init_cons_fd
         ∗ □ UkInit.uki_mknod_hit_leaf N (echo_taint γ)
               (init_cons_cred (echo_taint γ) r) init_cons_fd).
  Proof.
    intros Heq.
    assert (HTL : forall v : aview, Timeless (app_pred app_run v)).
    { rewrite Heq. cbn [app_pred app_run]. intro v. apply _. }
    iIntros "#Hm #Hinv".
    iDestruct (init_cons_laws_made_echo γ r i0 Heq with "Hm") as "#Hlaws".
    (* the credential the shell is handed at this arm: the flag's own law *)
    iAssert (init_cons_cred (echo_taint γ) r) as "#Hcred".
    { iApply (init_cons_cred_of_made (echo_taint γ) r i0 with "Hm"). }
    iModIntro. iIntros (N). iSplit.
    - iApply (init_open_console_leaf_holds N (cons_present_at i0)
                (echo_taint γ) (cons_made r i0) r i0
                ltac:(apply _) ltac:(apply _) with "Hlaws Hm Hinv").
    - (* the mknod at a view that ALREADY HAS the node: it cannot commit,
         and the credential it hands on is the flag it went in with *)
      iModIntro.
      iApply (UkInit.uki_mknod_hit_of_leaf N (echo_taint γ)
                (cons_made r i0) (init_cons_cred (echo_taint γ) r)
                init_cons_fd with "[] Hm").
      iApply (init_mknod_leaf_holds N (cons_present_at i0) (echo_taint γ)
                (cons_made r i0) r
                ltac:(apply _) ltac:(apply _) ltac:(apply _) HTL
                with "Hlaws [] Hinv").
      iIntros "!> #Hm'". iModIntro. rewrite /UkInit.uki_mknod_out. iLeft.
      iSplitR; [ | iExact "Hcred" ].
      iApply (init_open_console_leaf_holds N (cons_present_at i0)
                (echo_taint γ) (cons_made r i0) r i0
                ltac:(apply _) ltac:(apply _) with "Hlaws Hm Hinv").
  Qed.

End UInitConsK.
