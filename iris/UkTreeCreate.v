(* ===================================================================== *)
(* UkTreeCreate.v -- THE CREATE FAMILY OF AN OWNED SUBTREE, AT THE U TIER. *)
(*                                                                       *)
(* design/user-tree.md section 7.9, lane TL-3U.  [TreeMove] supplies the  *)
(* three create-family BUNDLES from one live deed at a parent prefix of   *)
(* length zero ([tree_mknod_au] / [tree_mkdir_au] / [tree_open_create_au]) *)
(* and what is left is U-TIER ASSEMBLY ONLY: turn each bundle into the    *)
(* deposit its leaf consumes, read the arm's receipt out of [spost_at],   *)
(* and fold the success and failure arms.  The landed model is            *)
(* [UInitCons]'s [mknod("console")] step, and this file is that shape at  *)
(* the TREE claim's families:                                            *)
(*                                                                       *)
(*   [wp_uk_ecall_mknod_own]   mknod("/x") at an owner of "/" (row 17)    *)
(*   [wp_uk_ecall_mkdir_own]   mkdir("/d")                  (row 20)      *)
(*   [wp_uk_ecall_open_create_own]                                        *)
(*                             open("/f", O_CREATE)         (row 15)      *)
(*   [wp_uk_tree_app_core]     THE TEST: own "/" -> mkdir -> open-create  *)
(*                             -> write -> freeze -> read-learns          *)
(*                                                                       *)
(* WHAT IS NOT HERE: unlink.  Its ENTRY leg is supplied ([TreeMove]       *)
(* section 3c) and its TARGET leg's tree-side move is too                 *)
(* ([tree_utgt_phases_rooted]), but [SysUnlinkDefs.utgt_commit_at] binds  *)
(* its target INSIDE with no cursor and the two legs share no receipt     *)
(* channel -- design/user-tree.md section 7.9 item 8, with what each      *)
(* restatement costs priced at section 7.10 item 8.                       *)
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
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserCwd.
Require Import UmodeAbi.           (* [uimg_sub] *)
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import PieceFam.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UConsOpen.          (* [xfam_open]'s two key-level rows *)
Require Import UkTreeRead.         (* the read side: open, read, and the tie *)
Require Import UkTreeWrite.        (* the write side: the deed moves *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import SysReadDefs.        (* [ard_count] *)
Require Import SysOpenDefs.
Require Import SpecSysOpen.
Require Import SysMknodDefs.       (* [npar_elems] / [npar_cur] / [dev_arg] *)
Require Import SpecSysMknod.
Require Import SpecSysMkdir.
Require Import SpecCreate.
Require Import SpecDirlookup.      (* [T_DIR] *)
Require Import ArgPath.
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsBytesGamma.
Require Import FsImg.
Require Import PathElems.
Require Import FsTree.
Require Import FsAbsEra.
Require Import FsAbsDelta.
Require Import DirView.           (* [T_DIR_z] *)
Require Import FsAbsCreateFire.
Require Import TreeView.
Require Import AppTree.
Require Import TreeMove.           (* the owner's move at the create fires *)
Require Import FsAbsDefs.
Require Import CtxIdDefs.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE PURE TREE FACTS THE CHAIN SPENDS                              *)
(*                                                                       *)
(*  A create moves the owner's tree by [top_ins], and the NEXT call in    *)
(*  the chain reads that tree: the second create needs the root to still  *)
(*  be a directory of it, and the write and the read need the new file    *)
(*  to be AT THE PATH the program passed.  Both are one computation on    *)
(*  [tedge_ins], and neither needs anything from the logic.               *)
(* ===================================================================== *)

Lemma top_ins_root_dom (d : Z) (nm : fname) (i : Z) (c : absnode) (t : ttree)
    (j : Z) :
  j ∈ dom (tv_nodes t) -> j ∈ dom (tv_nodes (top_ins d nm i c t)).
Proof.
  intros Hj. rewrite /top_ins /=.
  rewrite /tedge_ins. destruct (<[i := c]> (tv_nodes t) !! d) as [n |] eqn:Hd.
  - destruct n as [bs | e | ma mi];
      [ rewrite dom_insert_L; set_solver
      | rewrite dom_insert_L dom_insert_L; set_solver
      | rewrite dom_insert_L; set_solver ].
  - rewrite dom_insert_L. set_solver.
Qed.

(* the root is still a DIRECTORY of the moved tree: [tedge_ins] preserves
   the kind at every row, and the inserted child is one the caller knows
   the kind of (a directory at mkdir, a row other than [d] elsewhere). *)
Lemma top_ins_dir_at (d : Z) (nm : fname) (i : Z) (c : absnode) (t : ttree)
    (e : gmap fname Z) :
  tv_nodes t !! d = Some (ADir e) ->
  (i <> d \/ exists e0 : gmap fname Z, c = ADir e0) ->
  exists e' : gmap fname Z, tv_nodes (top_ins d nm i c t) !! d = Some (ADir e').
Proof.
  intros Hd Hc. rewrite /top_ins /=.
  assert (Hrow : exists e1 : gmap fname Z,
                   <[i := c]> (tv_nodes t) !! d = Some (ADir e1)).
  { destruct (decide (i = d)) as [-> | Hne].
    - destruct Hc as [Hc | [e0 ->]]; [ exfalso; exact (Hc eq_refl) | ].
      rewrite lookup_insert. by exists e0.
    - rewrite lookup_insert_ne; [| exact Hne]. rewrite Hd. by exists e. }
  destruct Hrow as [e1 He1].
  rewrite (tedge_ins_lookup_at _ d nm i e1 He1). by exists (<[nm := i]> e1).
Qed.

(* ...AND THE NEW CHILD IS AT THE PATH THE PROGRAM PASSED, which is the
   fact the write and the read corollaries take: at a ONE-ELEMENT path
   ("/f" from the root) the walk is one [tedge_ins] lookup. *)
Lemma resolves_from_top_ins (d : Z) (nm : fname) (i : Z) (c : absnode)
    (t : ttree) (e : gmap fname Z) (pl : list (bv 8)) :
  tv_nodes t !! d = Some (ADir e) ->
  i <> d ->
  path_elems pl = [nm] ->
  resolves_from (top_ins d nm i c t) d pl = Some (i, c).
Proof.
  intros Hd Hne Hpl.
  assert (Hrow : <[i := c]> (tv_nodes t) !! d = Some (ADir e))
    by (rewrite lookup_insert_ne; [ exact Hd | exact Hne ]).
  assert (Hnodes : tv_nodes (top_ins d nm i c t)
                   = tedge_ins d nm i (<[i := c]> (tv_nodes t)))
    by reflexivity.
  rewrite /resolves_from Hpl Hnodes npath_cons.
  rewrite (nstep_tedge_ins_at _ d nm i e nm Hrow) decide_True; [| reflexivity].
  rewrite npath_nil.
  rewrite (tedge_ins_lookup_ne _ d nm i i Hne) lookup_insert //.
Qed.


Section UkTreeCreate.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UInitSh.v]'s note): no local
     [Context {SG}] / [Context {PS}], or two [sbundle]s print identically
     and [UexecSG.psok] resolves to the generic [fun _ => True]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* NO local [ghost_varG Σ (gset gname)] -- and that is not a matter of
     taste (durable-notes, the instance-shadowing wedge).  [UkRun.urun]
     takes one, and with a local Context variable in scope it resolves to
     THAT rather than to the canonical [Xv6G.xv6_uch], so the [urun] in
     this file's goals stops matching the [urun] of every lemma stated
     without the variable -- [UkTreeRead.wp_uk_tree_read_learns] is one.
     What follows is not an error but a HANG: [iFrame] refuses the
     hypothesis outright, and the [with "H"] path drops into a conversion
     between two ghost-map instances that does not come back.  A lemma
     from a file that DOES carry the variable ([UkTreeWrite]) is
     generalised over it at section close, so it applies here either way. *)
  Context `{!treeG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  THE DEPOSIT'S FAMILY                                            *)
  (*                                                                      *)
  (*  ONE [UexecExecInst.xfam] for all three calls, because a deposit is   *)
  (*  read at ONE number ([UexecExecInst.xv6_sbundle] is a match on it):   *)
  (*  the create family's three rows -- 17 (mknod), 20 (mkdir) and 15      *)
  (*  (open at O_CREATE) -- take the SAME four pieces, so filling the      *)
  (*  three groups from one argument list costs nothing and every other    *)
  (*  row stays inert.  What differs per call is the CHILD KIND inside     *)
  (*  [Fok] ([TreeMove.tree_acre_fam]'s [cf]), which is the caller's       *)
  (*  argument here.  [kf_xpay] is the PROGRAM'S OWN EXIT PAYLOAD, which   *)
  (*  is what [UkRun.udepwf_at]'s pure row demands.                        *)
  (* =================================================================== *)
  Definition xfam_tree (P : nat -> Z -> iProp Σ)
      (Farm Fun : pfam Σ (aview -> Z -> iProp Σ))
      (Fdots : pfam Σ (aview -> Z -> Z -> bool -> iProp Σ))
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
       (* row 15, at O_CREATE: the walk cursor, create's four legs, and
          the two read-only observations at their units *)
       of_P     := P;
       of_Pmiss := fun _ _ => True%I;
       of_Farm  := Farm;
       of_Fun   := Fun;
       of_Fok   := Fok;
       of_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_Ft    := pfam_triv (fun _ _ _ => True%I);
       of_om    := OffParked;
       wf_Q     := fun _ => True%I;
       (* row 17 *)
       nf_P     := P;
       nf_Pmiss := fun _ _ => True%I;
       nf_Farm  := Farm;
       nf_Fun   := Fun;
       nf_Fok   := Fok;
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
       (* row 20 -- the dots leg beside the same four *)
       df_P     := P;
       df_Pmiss := fun _ _ => True%I;
       df_Farm  := Farm;
       df_Fdots := Fdots;
       df_Fun   := Fun;
       df_Fok   := Fok;
       df_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       kf_pay   := fun _ => True%I;
       (* a program that forks lends nothing at this record (lane
          FORK-REFUND): [UexecSG.sfork_lend] is [emp]. *)
       kf_lend  := emp%I;
       kf_xpay  := Q;
       rf_ret   := fun _ _ => True%I;
       rf_in    := fun _ => True%I;
       (* ...and nothing about any pipe or close (upstream's pipe-queue
          fields, at their generic defaults): a tree application claims
          nothing there *)
       rf_pq    := fun _ => True%I;
       rf_pqe   := fun _ _ => True%I;
       wf_Qe    := fun _ _ => True%I;
       cl_P     := True%I |}.

  (* THE OWNER'S CURSOR, and it is PURE at a parent prefix of length zero:
     the walk reads no claim law at all ([FsAbsEra.ep_hops_from] is the
     empty big-op), so the cursor is duplicable and returns itself --
     design/user-tree.md section 7.7's (R), and the reason the SPLIT
     CURSOR seam is not a prerequisite here. *)
  Definition tree_root_cur : nat -> Z -> iProp Σ :=
    fun (_ : nat) (d : Z) => ⌜d = FsImg.ROOTINO⌝%I.

  (* =================================================================== *)
  (*  2.  THE THREE ROWS, IN THE PROCESS'S DIRECTION                      *)
  (*                                                                      *)
  (*  [UexecExecInst] states the deposit's ELIM and the post's INTRO --    *)
  (*  the DISPATCHER's two directions.  A process needs the other two, at  *)
  (*  readings it can name, so each takes the key's own projections as     *)
  (*  pure premises.  [UConsOpen] has row 15's pair already; these are     *)
  (*  rows 17 and 20's, and the proofs are the same three lines.           *)
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

  Lemma sbundle_at_mknod_intro_tr (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (cw : Z) (M : gmap Z (bv 8)) (pv : mword 64) (ma mi : Z) :
    uvis_cwd W = cw -> uvis_M W = M ->
    tf_w (uvis_tf W) (tf_arg_idx 0) = pv ->
    dev_arg (tf_w (uvis_tf W) (tf_arg_idx 1)) = ma ->
    dev_arg (tf_w (uvis_tf W) (tf_arg_idx 2)) = mi ->
    mknod_au_at (fs_gamma_L fsc_fs) fsc_fs cw M pv ma mi
      (nf_P f) (nf_Pmiss f) (nf_Farm f) (nf_Fun f) (nf_Fok f) (nf_Fex f) -∗
    sbundle_at X 17 f W.
  Proof using .
    intros Hc HM H0 H1 H2. iIntros "H".
    rewrite -Hc -HM -H0 -H1 -H2.
    rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_mknod_elim_tr (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
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
  Proof using .
    intros Hc HM H0 H1 H2. iIntros "H".
    rewrite -Hc -HM -H0 -H1 -H2.
    rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_skip. xv6_skip. xv6_skip. xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma sbundle_at_mkdir_intro_tr (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (cw : Z) (M : gmap Z (bv 8)) (pv : mword 64) :
    uvis_cwd W = cw -> uvis_M W = M ->
    tf_w (uvis_tf W) (tf_arg_idx 0) = pv ->
    mkdir_au_at (fs_gamma_L fsc_fs) fsc_fs cw M pv
      (df_P f) (df_Pmiss f) (df_Farm f) (df_Fdots f) (df_Fun f)
      (df_Fok f) (df_Fex f) -∗
    sbundle_at X 20 f W.
  Proof using .
    intros Hc HM H0. iIntros "H".
    rewrite -Hc -HM -H0.
    rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    repeat xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_mkdir_elim_tr (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (cw : Z) (M : gmap Z (bv 8)) (pv : mword 64)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate)
      (cw' : Z) (cs' : gset gname) :
    uvis_cwd W = cw -> uvis_M W = M ->
    tf_w (uvis_tf W) (tf_arg_idx 0) = pv ->
    spost_at X 20 f W r M' fdv' cw' cs' -∗
    mkdir_arms (fs_gamma_L fsc_fs) fsc_fs cw
      (df_P f) (df_Pmiss f) (df_Farm f) (df_Fdots f) (df_Fun f)
      (df_Fok f) (df_Fex f) M pv r.
  Proof using .
    intros Hc HM H0. iIntros "H".
    rewrite -Hc -HM -H0.
    rewrite /spost_at /= /xv6_spost /xk_a.
    repeat xv6_skip. xv6_take. iExact "H".
  Qed.

  (* =================================================================== *)
  (*  3.  mknod AT AN OWNER OF "/"  (row 17)                              *)
  (* =================================================================== *)

  Definition tree_mknod_fam (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) (ma mi : Z) (Q : Z -> iProp Σ) : sfam :=
    xfam_tree tree_root_cur (tree_arm_fam c r g t) (tree_unarm_fam c r g t)
      (pfam_triv (fun _ _ _ _ => True%I))
      (tree_acre_fam c r g t (fun _ _ => ADev ma mi)) Q.

  (* THE DEPOSIT, OUT OF THE DEED: [UkTreeRead.tree_open_sup]'s shape at
     row 17.  The heap is LENT, which is what lets the path reading
     ([ArgPath.arg_path_of] at the trapping key's own image) be discharged
     from the caller's persistent view of its own rodata. *)
  Lemma tree_mknod_sup (N : uk_names Σ) (c : tree_fixed) (r : tree_names)
      (g : gname) (t : ttree) (ma mi cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile) (pc : mword 64)
      (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    dev_arg (m !!! Regidx a1_idx) = ma ->
    dev_arg (m !!! Regidx a2_idx) = mi ->
    np_elems pl = [] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    app_inv fsc_fs -∗ utext_img (ukn_t N) Img -∗ tree_own r g FsImg.ROOTINO t -∗
    udepwf_at N m pc 17 (tree_mknod_fam c r g t ma mi (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Ha1 Ha2 Hnp Hstart Hdd.
    iIntros "#Hinv #Hro Hown".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (cons_ro_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_mknod_intro_tr uslot
              (tree_mknod_fam c r g t ma mi (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              cw M pv ma mi eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              ltac:(unfold tf_w; cbn [uvis_tf uvis_of_run];
                    rewrite (tf_of_arg1 m pc); exact Ha1)
              ltac:(unfold tf_w; cbn [uvis_tf uvis_of_run];
                    rewrite (tf_of_arg2 m pc); exact Ha2)).
    cbn [tree_mknod_fam xfam_tree nf_P nf_Pmiss nf_Farm nf_Fun nf_Fok nf_Fex].
    iApply (tree_mknod_au fsc_fs c r g t cw ma mi M pv pl Heq
              (Hpath M Hsro) Hnp Hstart Hdd with "Hinv Hown").
  Qed.

  (* WHAT A SUCCEEDING mknod HANDS BACK: the deed at the tree with the
     device filed under the path's own last element.  The cursor says the
     parent was the root and the path reading says which name it is, so
     the receipt collapses -- [UInitCons.init_cons_mknod_recv]'s shape at
     the tree family. *)
  Lemma tree_mknod_ok_recv (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) (ma mi : Z) (M : gmap Z (bv 8)) (pv : mword 64)
      (pl : list (bv 8)) (nm : fname) :
    arg_path_of M pv pl ->
    list_basics.last (path_elems pl) = Some nm ->
    mknod_post_ok (fs_gamma_L fsc_fs) M pv ma mi tree_root_cur
      (tree_arm_fam c r g t) (tree_unarm_fam c r g t)
      (tree_acre_fam c r g t (fun _ _ => ADev ma mi))
      (pfam_triv (fun _ _ _ _ => True%I)) -∗
    ((∃ i : Z,
        ⌜i <> FsImg.ROOTINO⌝ ∗
        tree_own r g FsImg.ROOTINO
          (top_ins FsImg.ROOTINO nm i (ADev ma mi) t))
     ∨ tree_taint c).
  Proof using .
    intros Hpath Hlast. rewrite /mknod_post_ok. iIntros "H".
    iDestruct "H" as (pl0 i) "(%Hpath0 & _ & H)".
    rewrite (arg_path_of_uniq M pv pl0 pl Hpath0 Hpath).
    iDestruct "H" as (av d nm0 ents nl) "(%Hlast0 & %Hcre & %Hd & _ & Hok & _)".
    rewrite Hlast in Hlast0. injection Hlast0 as <-.
    rewrite /tree_root_cur in Hd.
    (* THE CHILD IS NOT THE PARENT, and the reason is the child's KIND:
       [cre_pre] observes both rows at the same view and a device is not a
       directory ([FsAbsDelta.cre_pre_ne]).  It is what the tree's own
       [top_ins] needs to be the insert the caller means. *)
    assert (Hne : i <> FsImg.ROOTINO).
    { intros ->. subst d.
      exact (cre_pre_ne av FsImg.ROOTINO nm ents nl FsImg.ROOTINO
               (ADev ma mi) Hcre (fun e He => ltac:(discriminate He))
               eq_refl). }
    rewrite Hd.
    cbn [tree_acre_fam pf_recv].
    iDestruct "Hok" as "[Hown | HT]";
      [ iLeft; iExists i; iSplitR; [ by iPureIntro | iExact "Hown" ]
      | iRight; iExact "HT" ].
  Qed.

  (* ...AND WHAT A FAILING ONE DOES: the deed comes straight back.  Every
     arm of the fold either hands the ARM's piece home unfired -- and its
     refund IS the deed (design/user-tree.md section 7.9(5)) -- or fired
     the do-then-undo pair, whose unarm receipt is the deed again.
     [UInitCons.init_cons_mknod_fail_recv] is this at the console's key. *)
  Lemma tree_mknod_fail_recv (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) (ma mi cw : Z) (M : gmap Z (bv 8)) (pv : mword 64) :
    mknod_post_fail (fs_gamma_L fsc_fs) fsc_fs cw M pv ma mi tree_root_cur
      (fun _ _ => True%I) (tree_arm_fam c r g t) (tree_unarm_fam c r g t)
      (tree_acre_fam c r g t (fun _ _ => ADev ma mi))
      (pfam_triv (fun _ _ _ _ => True%I)) -∗
    (tree_own r g FsImg.ROOTINO t ∨ tree_taint c).
  Proof using .
    rewrite /mknod_post_fail /cre_child_unfired /cre_child_pair. iIntros "H".
    iDestruct "H" as "[Hau | Hf]".
    { rewrite /mknod_au_at. iDestruct "Hau" as "(_ & _ & _ & Harm & _)".
      iLeft. iApply (pf_at_refund with "Harm"). }
    iDestruct "Hf" as (pl) "(_ & [Hd | Hc])".
    - iDestruct "Hd" as "(_ & _ & _ & Harm & _)".
      iLeft. iApply (pf_at_refund with "Harm").
    - iDestruct "Hc" as (d) "(_ & _ & _ & [Hun | Hpair])".
      + iDestruct "Hun" as "(Harm & _)".
        iLeft. iApply (pf_at_refund with "Harm").
      + iDestruct "Hpair" as (i) "Hu". rewrite /cre_unarm_fired.
        iDestruct "Hu" as (av cc) "(_ & Hk)".
        cbn [tree_unarm_fam pf_recv]. iExact "Hk".
  Qed.

  (* ---- THE COROLLARY: "mknod a name of MY OWN root, and my tree records
     the device under that name".  Three arms and no fourth: ret 0 and the
     deed at the moved tree, ret -1 and the deed back where it was, or the
     application is tainted.  The leaf is the RECEIPT-KEEPING quiet one
     ([UkRunSys.wp_uk_ecall_quiet_recv_img] -- 17 pays a post and is not
     one of the numbers that leaf excludes). *)
  Lemma wp_uk_ecall_mknod_own (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat)
      (c : tree_fixed) (r : tree_names) (g : gname) (t : ttree)
      (ma mi cw : Z) (Img : gmap Z (bv 8)) (pv : mword 64)
      (pl : list (bv 8)) (nm : fname) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    usysno m = 17 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    dev_arg (m !!! Regidx a1_idx) = ma ->
    dev_arg (m !!! Regidx a2_idx) = mi ->
    (* THE PATH'S PARENT PREFIX IS EMPTY -- "/x", not "/a/x" *)
    np_elems pl = [] ->
    list_basics.last (path_elems pl) = Some nm ->
    um_start_of cw pl = FsImg.ROOTINO ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    (* THE DEED, LIVE (not frozen: this call moves it) *)
    tree_own r g FsImg.ROOTINO t -∗
    app_inv fsc_fs -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((⌜rv = (zero_reg : mword 64)⌝ ∗
         ∃ i : Z, ⌜i <> FsImg.ROOTINO⌝ ∗
                  tree_own r g FsImg.ROOTINO
                    (top_ins FsImg.ROOTINO nm i (ADev ma mi) t))
        ∨ (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗
           tree_own r g FsImg.ROOTINO t)
        ∨ tree_taint c) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Ha1 Ha2 Hnp Hlast Hstart Hdd.
    iIntros "#Hi #Hro Hrun Hcwd Hown #Hinv Hcont".
    iDestruct (tree_mknod_sup N c r g t ma mi cw Img pv m pc pl Heq Hpath
                 Ha0 Ha1 Ha2 Hnp Hstart Hdd with "Hinv Hro Hown") as "Hsb".
    iApply (wp_uk_ecall_quiet_recv_img N h m pc 17 avail
              (tree_mknod_fam c r g t ma mi (ukn_pay N)) cw Img
              Hn ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              Hal4 with "Hi Hro Hrun Hcwd Hsb").
    iIntros (h' rv W cs') "%Himg %Hk0 %Hk1 %Hk2 %Hcw Hpost Hcwd Hrun".
    iDestruct (spost_at_mknod_elim_tr uslot
                 (tree_mknod_fam c r g t ma mi (ukn_pay N)) W
                 cw (uvis_M W) pv ma mi rv (uvis_M W) (uvis_fd W) cw cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 ltac:(rewrite Hk1; exact Ha1)
                 ltac:(rewrite Hk2; exact Ha2)
                 with "Hpost") as "Harms".
    iApply ("Hcont" $! h' rv with "[Harms] Hcwd Hrun").
    rewrite /mknod_arms.
    cbn [tree_mknod_fam xfam_tree nf_P nf_Pmiss nf_Farm nf_Fun nf_Fok nf_Fex].
    iDestruct "Harms" as "[[%Hr Hok] | [%Hr Hfail]]".
    - iDestruct (tree_mknod_ok_recv c r g t ma mi (uvis_M W) pv pl nm
                   (Hpath (uvis_M W) Himg) Hlast with "Hok") as "[Ht | HT]";
        [| iRight; iRight; iExact "HT" ].
      iLeft. iSplitR; [ by iPureIntro | ]. iExact "Ht".
    - iDestruct (tree_mknod_fail_recv c r g t ma mi cw (uvis_M W) pv
                   with "Hfail") as "[Ht | HT]";
        [| iRight; iRight; iExact "HT" ].
      iRight. iLeft. iSplitR; [ by iPureIntro | ]. iExact "Ht".
  Qed.

  (* =================================================================== *)
  (*  4.  mkdir AT AN OWNER OF "/"  (row 20)                              *)
  (*                                                                      *)
  (*  mknod's corollary at the DIRECTORY child -- the case                *)
  (*  [own_wf_ent_leaf] could never reach, and which the rooted view       *)
  (*  closes (design/user-tree.md section 7.9(4)): the credential that     *)
  (*  the armed inum is nobody's root comes off [own_rooted], not off the  *)
  (*  child's kind, so [TreeMove.tree_mkdir_au] needs no leaf premise and  *)
  (*  the assembly here is mknod's, line for line.                        *)
  (* =================================================================== *)

  (* what the owner's tree records for the new directory: the tree HIDES
     the dots, so a fresh directory is the EMPTY node map. *)
  Lemma tabs_of_cre_child_dir (ma mi d i : Z) :
    tabs_of (cre_child T_DIR_z ma mi d i) = ADir ∅.
  Proof using .
    rewrite cre_child_dir /tabs_of /dots_ents /hide_dots.
    rewrite (delete_insert_ne _ DOTDOT DOT);
      [| intros Hc; exact (dot_ne_dotdot (eq_sym Hc))].
    rewrite !delete_insert_delete !delete_empty //.
  Qed.

  Definition tree_mkdir_fam (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) (Q : Z -> iProp Σ) : sfam :=
    xfam_tree tree_root_cur (tree_arm_fam c r g t) (tree_unarm_fam c r g t)
      (pfam_triv (fun _ _ _ _ => True%I))
      (tree_acre_fam c r g t
         (cre_child (bv_unsigned (SpecDirlookup.T_DIR : mword 16))
            (bv_unsigned (mword_of_int 0 : mword 16))
            (bv_unsigned (mword_of_int 0 : mword 16)))) Q.

  Lemma tree_mkdir_sup (N : uk_names Σ) (c : tree_fixed) (r : tree_names)
      (g : gname) (t : ttree) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile) (pc : mword 64)
      (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    np_elems pl = [] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    app_inv fsc_fs -∗ utext_img (ukn_t N) Img -∗ tree_own r g FsImg.ROOTINO t -∗
    udepwf_at N m pc 20 (tree_mkdir_fam c r g t (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Hnp Hstart Hdd.
    iIntros "#Hinv #Hro Hown".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (cons_ro_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_mkdir_intro_tr uslot
              (tree_mkdir_fam c r g t (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              cw M pv eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)).
    cbn [tree_mkdir_fam xfam_tree df_P df_Pmiss df_Farm df_Fdots df_Fun
         df_Fok df_Fex].
    iApply (tree_mkdir_au fsc_fs c r g t cw M pv pl Heq
              (Hpath M Hsro) Hnp Hstart Hdd with "Hinv Hown").
  Qed.

  (* THE SUCCESS READING, and it is WEAKER THAN mknod's IN ONE PLACE --
     the lane's first finding, and it is a fact about [SpecSysMkdir.
     mkdir_arms] rather than about the claim.  mknod's success arm carries
     [⌜arg_path_of M pv pl⌝] beside its walk cursor
     ([SpecSysMknod.mknod_post_ok]) and so names the entry the call filed;
     mkdir's carries none -- its [pl] is existentially quantified with
     nothing tying it to the caller's argument -- so the strongest honest
     post here names the directory's NAME existentially too.  The fix is
     one conjunct in [mkdir_arms]'s ok arm, i.e. a kernel-tier
     restatement of [ProofSysMkdir]'s own [arg_path_of], and it is not
     taken here. *)
  Lemma tree_mkdir_ok_recv (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) (pl : list (bv 8)) (i : Z) :
    cre_ok_arms (fs_gamma_L fsc_fs)
      (bv_unsigned (SpecDirlookup.T_DIR : mword 16))
      (bv_unsigned (mword_of_int 0 : mword 16))
      (bv_unsigned (mword_of_int 0 : mword 16))
      (fun _ : fname => True%type) (fun _ : absnode => True%type)
      tree_root_cur (tree_arm_fam c r g t)
      (pfam_triv (fun _ _ _ _ => True%I)) (tree_unarm_fam c r g t)
      (tree_acre_fam c r g t
         (cre_child (bv_unsigned (SpecDirlookup.T_DIR : mword 16))
            (bv_unsigned (mword_of_int 0 : mword 16))
            (bv_unsigned (mword_of_int 0 : mword 16))))
      (pfam_triv (fun _ _ _ _ => True%I)) pl true i -∗
    ((∃ nm : fname,
        ⌜list_basics.last (path_elems pl) = Some nm⌝ ∗
        tree_own r g FsImg.ROOTINO
          (top_ins FsImg.ROOTINO nm i (ADir ∅) t))
     ∨ tree_taint c).
  Proof using .
    rewrite /cre_ok_arms. iIntros "H".
    iDestruct "H" as (d nm) "(%Hlast & %Hd & _ & Hok & _ & _)".
    rewrite /tree_root_cur in Hd. subst d.
    rewrite /cre_acre_fired. iDestruct "Hok" as (av ents nl) "(_ & Hok)".
    cbn [tree_acre_fam pf_recv].
    rewrite (tabs_of_cre_child_dir
               (bv_unsigned (mword_of_int 0 : mword 16))
               (bv_unsigned (mword_of_int 0 : mword 16)) FsImg.ROOTINO i).
    iDestruct "Hok" as "[Hown | HT]"; [| iRight; iExact "HT" ].
    iLeft. iExists nm. iSplitR; [ by iPureIntro | ]. iExact "Hown".
  Qed.

  Lemma tree_mkdir_fail_recv (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) (cw : Z) (M : gmap Z (bv 8)) (pv : mword 64) :
    (mkdir_au_at (fs_gamma_L fsc_fs) fsc_fs cw M pv tree_root_cur
       (fun _ _ => True%I) (tree_arm_fam c r g t)
       (pfam_triv (fun _ _ _ _ => True%I)) (tree_unarm_fam c r g t)
       (tree_acre_fam c r g t
          (cre_child (bv_unsigned (SpecDirlookup.T_DIR : mword 16))
             (bv_unsigned (mword_of_int 0 : mword 16))
             (bv_unsigned (mword_of_int 0 : mword 16))))
       (pfam_triv (fun _ _ _ _ => True%I))
     ∨ ∃ pl : list (bv 8),
         cre_fail_arms (fs_gamma_L fsc_fs) fsc_fs
           (bv_unsigned (SpecDirlookup.T_DIR : mword 16))
           (bv_unsigned (mword_of_int 0 : mword 16))
           (bv_unsigned (mword_of_int 0 : mword 16))
           (fun _ : fname => True%type) (fun _ : absnode => True%type)
           tree_root_cur (fun _ _ => True%I) (tree_arm_fam c r g t)
           (pfam_triv (fun _ _ _ _ => True%I)) (tree_unarm_fam c r g t)
           (tree_acre_fam c r g t
              (cre_child (bv_unsigned (SpecDirlookup.T_DIR : mword 16))
                 (bv_unsigned (mword_of_int 0 : mword 16))
                 (bv_unsigned (mword_of_int 0 : mword 16))))
           (pfam_triv (fun _ _ _ _ => True%I)) pl) -∗
    (tree_own r g FsImg.ROOTINO t ∨ tree_taint c).
  Proof using .
    rewrite /mkdir_au_at /cre_fail_arms /cre_commits. iIntros "H".
    iDestruct "H" as "[Hau | Hf]".
    { iDestruct "Hau" as "(_ & _ & Harm & _)".
      iLeft. iApply (pf_at_refund with "Harm"). }
    iDestruct "Hf" as (pl) "[Hd | Hc]".
    - iDestruct "Hd" as "(_ & _ & Harm & _)".
      iLeft. iApply (pf_at_refund with "Harm").
    - iDestruct "Hc" as (d) "(_ & _ & _ & [Hun | Hpair])".
      + iDestruct "Hun" as "(Harm & _)".
        iLeft. iApply (pf_at_refund with "Harm").
      + iDestruct "Hpair" as (i) "(_ & Hu)". rewrite /cre_unarm_fired.
        iDestruct "Hu" as (av cc) "(_ & Hk)".
        cbn [tree_unarm_fam pf_recv]. iExact "Hk".
  Qed.

  Lemma wp_uk_ecall_mkdir_own (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat)
      (c : tree_fixed) (r : tree_names) (g : gname) (t : ttree)
      (cw : Z) (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    usysno m = 20 ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    np_elems pl = [] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    tree_own r g FsImg.ROOTINO t -∗
    app_inv fsc_fs -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((⌜rv = (zero_reg : mword 64)⌝ ∗
         ∃ (i : Z) (nm : fname),
           tree_own r g FsImg.ROOTINO
             (top_ins FsImg.ROOTINO nm i (ADir ∅) t))
        ∨ (⌜rv = (mword_of_int (-1) : mword 64)⌝ ∗
           tree_own r g FsImg.ROOTINO t)
        ∨ tree_taint c) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hnp Hstart Hdd.
    iIntros "#Hi #Hro Hrun Hcwd Hown #Hinv Hcont".
    iDestruct (tree_mkdir_sup N c r g t cw Img pv m pc pl Heq Hpath
                 Ha0 Hnp Hstart Hdd with "Hinv Hro Hown") as "Hsb".
    iApply (wp_uk_ecall_quiet_recv_img N h m pc 20 avail
              (tree_mkdir_fam c r g t (ukn_pay N)) cw Img
              Hn ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
              Hal4 with "Hi Hro Hrun Hcwd Hsb").
    iIntros (h' rv W cs') "%Himg %Hk0 %Hk1 %Hk2 %Hcw Hpost Hcwd Hrun".
    iDestruct (spost_at_mkdir_elim_tr uslot
                 (tree_mkdir_fam c r g t (ukn_pay N)) W
                 cw (uvis_M W) pv rv (uvis_M W) (uvis_fd W) cw cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 with "Hpost") as "Harms".
    iApply ("Hcont" $! h' rv with "[Harms] Hcwd Hrun").
    rewrite /mkdir_arms.
    cbn [tree_mkdir_fam xfam_tree df_P df_Pmiss df_Farm df_Fdots df_Fun
         df_Fok df_Fex].
    iDestruct "Harms" as "[[%Hr Hok] | [%Hr Hfail]]".
    - iDestruct "Hok" as (pl0 i) "Hok".
      iDestruct (tree_mkdir_ok_recv c r g t pl0 i with "Hok")
        as "[Ht | HT]"; [| iRight; iRight; iExact "HT" ].
      iDestruct "Ht" as (nm) "(_ & Ht)".
      iLeft. iSplitR; [ by iPureIntro | ]. iExists i, nm. iExact "Ht".
    - iDestruct (tree_mkdir_fail_recv c r g t cw (uvis_M W) pv
                   with "Hfail") as "[Ht | HT]";
        [| iRight; iRight; iExact "HT" ].
      iRight. iLeft. iSplitR; [ by iPureIntro | ]. iExact "Ht".
  Qed.

  (* =================================================================== *)
  (*  5.  open("/f", O_CREATE) AT AN OWNER OF "/"  (row 15)               *)
  (*                                                                      *)
  (*  The one create-family call that hands the caller a DESCRIPTOR, so    *)
  (*  its corollary carries both halves: the moved deed AND the handle on  *)
  (*  the file the call just made.  The leaf is the read side's own        *)
  (*  ([UkRunSys.wp_uk_ecall_open_recv_img]) and the ledger tie is         *)
  (*  [UkTreeRead.tree_open_fd_tie].                                      *)
  (* =================================================================== *)

  Definition tree_opencreate_fam (c : tree_fixed) (r : tree_names) (g : gname)
      (t : ttree) (Q : Z -> iProp Σ) : sfam :=
    xfam_tree tree_root_cur (tree_arm_fam c r g t) (tree_unarm_fam c r g t)
      (pfam_triv (fun _ _ _ _ => True%I))
      (tree_acre_fam c r g t (fun _ _ => AFile [])) Q.

  Lemma tree_open_create_sup (N : uk_names Σ) (c : tree_fixed) (r : tree_names)
      (g : gname) (t : ttree) (cw : Z)
      (Img : gmap Z (bv 8)) (pv : mword 64) (m : regfile) (pc : mword 64)
      (pl : list (bv 8)) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = true ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    np_elems pl = [] ->
    um_start_of cw pl = FsImg.ROOTINO ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    app_inv fsc_fs -∗ utext_img (ukn_t N) Img -∗ tree_own r g FsImg.ROOTINO t -∗
    udepwf_at N m pc USYS_open (tree_opencreate_fam c r g t (ukn_pay N)) cw.
  Proof using .
    intros Heq Hpath Ha0 Hcr Htr Hnp Hstart Hdd.
    iIntros "#Hinv #Hro Hown".
    rewrite /udepwf_at. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    iDestruct (cons_ro_sub N Img M pm sz with "Hheap Hro") as %Hsro.
    iFrame "Hheap Hufd".
    iApply (sbundle_at_open_intro_at uslot
              (tree_opencreate_fam c r g t (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false secc_all)
              cw M pv (m !!! Regidx a1_idx) eq_refl eq_refl
              (eq_trans (tf_of_arg0 m pc) Ha0)
              (tf_of_arg1 m pc)).
    cbn [tree_opencreate_fam xfam_tree of_P of_Pmiss of_Farm of_Fun
         of_Fok of_Fex of_Fo of_Ft].
    rewrite /open_in Hcr.
    iApply (tree_open_create_au fsc_fs c r g t cw M pv (m !!! Regidx a1_idx) pl
              Heq (Hpath M Hsro) Hnp Hstart Htr Hdd with "Hinv Hown").
  Qed.

  (* THE FAILURE FOLD.  Every arm hands the deed back, and TWO of them hand
     it back MOVED: an open whose create succeeded and which then failed
     past it left the entry standing (design section 2g's note -- "the fs
     mutation of a failed open is real"), so the honest post is the
     disjunction and not the deed at [t]. *)
  Lemma tree_open_create_fail_recv (c : tree_fixed) (r : tree_names)
      (g : gname) (t : ttree) (cw : Z) (M : gmap Z (bv 8))
      (pv vom : mword 64) (pl : list (bv 8)) (nm : fname) :
    (* THE MODE IS THE TREE APPLICATION'S OWN (lane F-OPEN-3): with the
       O_TRUNC bit clear the arms report exactly what they always did
       ([SpecSysOpen]'s [cre_*_kept] family), and this application's open
       is [0x201]. *)
    om_trunc vom = false ->
    arg_path_of M pv pl ->
    list_basics.last (path_elems pl) = Some nm ->
    open_post_fail_create (fs_gamma_L fsc_fs) fsc_fs cw M pv vom
      tree_root_cur (fun _ _ => True%I)
      (tree_arm_fam c r g t) (tree_unarm_fam c r g t)
      (tree_acre_fam c r g t (fun _ _ => AFile []))
      (pfam_triv (fun _ _ _ _ => True%I))
      (pfam_triv (fun _ _ _ => True%I))
      (pfam_triv (fun _ _ _ => True%I)) -∗
    (tree_own r g FsImg.ROOTINO t
     ∨ (∃ i : Z, tree_own r g FsImg.ROOTINO
                   (top_ins FsImg.ROOTINO nm i (AFile []) t))
     ∨ tree_taint c).
  Proof using .
    intros Htr Hpath Hlast.
    rewrite /open_post_fail_create /open_au_create_at /cre_child_unfired
            /cre_child_pair /cur_kept /cre_rcpt_kept /cre_fail_kept Htr.
    iIntros "H". iDestruct "H" as "[Hau | Hf]".
    { iDestruct "Hau" as "(_ & _ & _ & _ & _ & Harm & _)".
      iLeft. iApply (pf_at_refund with "Harm"). }
    iDestruct "Hf" as (pl0) "(%Hpath0 & [Hd | Hc])".
    - iDestruct "Hd" as "(_ & _ & _ & _ & _ & Harm & _)".
      iLeft. iApply (pf_at_refund with "Harm").
    - iDestruct "Hc" as (d) "(%Hd & [Ha | [Hb | Hc]])".
      + (* (a) the create FIRED and the open failed past it *)
        rewrite /tree_root_cur in Hd. subst d.
        iDestruct "Ha" as (av i nm0 ents nl) "(%Hlast0 & _ & _ & Hok & _)".
        rewrite (arg_path_of_uniq M pv pl0 pl Hpath0 Hpath) in Hlast0.
        rewrite Hlast in Hlast0. injection Hlast0 as <-.
        cbn [tree_acre_fam pf_recv].
        iDestruct "Hok" as "[Hown | HT]";
          [ iRight; iLeft; iExists i; iExact "Hown"
          | iRight; iRight; iExact "HT" ].
      + (* (b) the name was already there *)
        iDestruct "Hb" as (av i nm0 ents nl) "(_ & _ & _ & _ & _ & [Hun | Hpair] & _)".
        * iDestruct "Hun" as "(Harm & _)".
          iLeft. iApply (pf_at_refund with "Harm").
        * iDestruct "Hpair" as (ic) "Hu". rewrite /cre_unarm_fired.
          iDestruct "Hu" as (av0 cc) "(_ & Hk)".
          cbn [tree_unarm_fam pf_recv].
          iDestruct "Hk" as "[Hown | HT]";
            [ iLeft; iExact "Hown" | iRight; iRight; iExact "HT" ].
      + (* (c) nothing was observed at all.  The trunc piece rides HERE
             now (lane F-OPEN-3): create never returned a node, so its
             permit was never paid and the caller's own piece comes home
             inside the arm. *)
        iDestruct "Hc" as "(_ & _ & _ & _ & [Hun | Hpair])".
        * iDestruct "Hun" as "(Harm & _)".
          iLeft. iApply (pf_at_refund with "Harm").
        * iDestruct "Hpair" as (ic) "Hu". rewrite /cre_unarm_fired.
          iDestruct "Hu" as (av0 cc) "(_ & Hk)".
          cbn [tree_unarm_fam pf_recv].
          iDestruct "Hk" as "[Hown | HT]";
            [ iLeft; iExact "Hown" | iRight; iRight; iExact "HT" ].
  Qed.

  (* ---- THE COROLLARY: "create a name of my own root and open it, and
     the descriptor that comes back is ON THE FILE MY TREE NOW RECORDS
     THERE".  Two arms: the FRESH one, which is both halves at once; and
     everything else -- the name was already there, or the call failed --
     where some ledger comes back and so does the deed, moved exactly if
     the create fired. *)
  Lemma wp_uk_ecall_open_create_own (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (avail : nat)
      (c : tree_fixed) (r : tree_names) (g : gname) (t : ttree)
      (cw : Z) (Img : gmap Z (bv 8)) (pv : mword 64) (pl : list (bv 8))
      (nm : fname) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    usysno m = USYS_open ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pv pl) ->
    m !!! Regidx a0_idx = pv ->
    om_create (m !!! Regidx a1_idx) = true ->
    om_trunc (m !!! Regidx a1_idx) = false ->
    np_elems pl = [] ->
    list_basics.last (path_elems pl) = Some nm ->
    um_start_of cw pl = FsImg.ROOTINO ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    tree_own r g FsImg.ROOTINO t -∗
    app_inv fsc_fs -∗
    (∀ (h' : CpuId) (rv : mword 64),
       ((* THE FILE WAS MADE AND THE HANDLE IS ON IT *)
        (∃ (fd : nat) (γo : gname) (i : Z),
           ⌜rv = (mword_of_int (Z.of_nat fd) : mword 64)
            /\ (fd < NOFILE)%nat⌝ ∗
           ualloc (ukn_fd N) l fd
             (FdOpen (om_readable (m !!! Regidx a1_idx))
                     (om_writable (m !!! Regidx a1_idx))
                     (FdInode i γo OffParked)) ∗
           tree_own r g FsImg.ROOTINO
             (top_ins FsImg.ROOTINO nm i (AFile []) t) ∗
           ⌜i <> FsImg.ROOTINO⌝)
        ∨ (* ...or the name was already there, or the call failed: SOME
             ledger comes back, and so does the deed -- moved exactly if
             the create fired *)
        (ustd_any (ukn_fd N) ∗
         (tree_own r g FsImg.ROOTINO t
          ∨ (∃ i : Z, tree_own r g FsImg.ROOTINO
                        (top_ins FsImg.ROOTINO nm i (AFile []) t))
          ∨ tree_taint c))) -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn Hal4 Hpath Ha0 Hcr Htr Hnp Hlast Hstart Hdd.
    iIntros "#Hi #Hro Hrun Hcwd Hstd Hown #Hinv Hcont".
    iDestruct (tree_open_create_sup N c r g t cw Img pv m pc pl Heq Hpath
                 Ha0 Hcr Htr Hnp Hstart Hdd with "Hinv Hro Hown") as "Hsb".
    iApply (wp_uk_ecall_open_recv_img N h m pc l avail
              (tree_opencreate_fam c r g t (ukn_pay N)) cw Img Hn Hal4
              with "Hi Hro Hrun Hcwd Hsb Hstd").
    iIntros (h' rv W M' fdv' cw' cs')
      "%Himg %Hlen %Hk0 %Hk1 %Hcw %Htk Hfd Hpost Hcwd Hrun".
    iDestruct (spost_at_open_elim_at uslot
                 (tree_opencreate_fam c r g t (ukn_pay N)) W
                 cw (uvis_M W) pv (m !!! Regidx a1_idx) rv M' fdv' cw' cs'
                 Hcw eq_refl
                 ltac:(rewrite Hk0; exact Ha0)
                 ltac:(exact Hk1)
                 with "Hpost") as "Hrc".
    iEval (rewrite /open_receipt Hcr) in "Hrc".
    iEval (cbn [tree_opencreate_fam xfam_tree of_P of_Pmiss of_Farm of_Fun
                of_Fok of_Fex of_Fo of_Ft]) in "Hrc".
    rewrite /open_receipt_create /cur_kept /cre_rcpt_kept /cre_child_kept
            Htr.
    iDestruct "Hrc" as "[(%Hr & %Hfdv & Hfail) | Hok]".
    - (* THE CALL FAILED: the ledger is back untouched and the deed comes
         home, moved exactly if the create fired before the failure *)
      iDestruct (tree_open_create_fail_recv c r g t cw (uvis_M W) pv
                   (m !!! Regidx a1_idx) pl nm Htr (Hpath (uvis_M W) Himg)
                   Hlast with "Hfail") as "Hd".
      iApply ("Hcont" $! h' rv with "[Hfd Hd] Hcwd Hrun").
      iRight. iSplitL "Hfd"; [| iExact "Hd" ].
      iApply (init_cons_any_std (ukn_fd N) l (uvis_fd W) fdv' rv with "[Hfd]").
      rewrite /uk_open_fd_arm. iExact "Hfd".
    - iDestruct "Hok" as (pl0 d i nm0) "(%Hpath0 & %Hlast0 & %Hd & Harm)".
      rewrite (arg_path_of_uniq (uvis_M W) pv pl0 pl Hpath0
                 (Hpath (uvis_M W) Himg)) in Hlast0.
      rewrite Hlast in Hlast0. injection Hlast0 as <-.
      rewrite /tree_root_cur in Hd. subst d.
      iDestruct "Harm" as "[Hfresh | Hex]".
      + (* FRESH: the receipt's inum is the descriptor's, and the deed is
           at the tree with the new file filed under the caller's name *)
        iDestruct "Hfresh" as (av ents nl)
          "(%Hcre & _ & Hok & _ & _ & _ & _ & Hrc)".
        assert (Hne : i <> FsImg.ROOTINO).
        { intros ->.
          exact (cre_pre_ne av FsImg.ROOTINO nm ents nl FsImg.ROOTINO
                   (AFile []) Hcre (fun e He => ltac:(discriminate He))
                   eq_refl). }
        iDestruct "Hrc" as (γo) "[%Hrcpt _]".
        cbn [tree_acre_fam pf_recv].
        iDestruct "Hok" as "[Hown | #HT]"; last first.
        { iApply ("Hcont" $! h' rv with "[Hfd] Hcwd Hrun").
          iRight. iSplitL "Hfd"; [| iRight; iRight; iExact "HT" ].
          iApply (init_cons_any_std (ukn_fd N) l (uvis_fd W) fdv' rv
                    with "[Hfd]").
          rewrite /uk_open_fd_arm. iExact "Hfd". }
        iDestruct "Hfd" as "[Hal | [%Hb _]]"; last first.
        { exfalso. destruct Hb as [Hrm _].
          destruct Hrcpt as (fd0 & Hr0 & Hcl0 & _).
          assert (Hlt0 : (fd0 < NOFILE)%nat).
          { rewrite <- Hlen. exact (lookup_lt_Some _ _ _ Hcl0). }
          exact (init_cons_moi_nat_m1 fd0 Hlt0 (eq_trans (eq_sym Hr0) Hrm)). }
        iDestruct "Hal" as (fd rd wr ty) "[%Hb Hal]".
        destruct Hb as (Hr1 & Hlt1 & Hfdv1 & _).
        rewrite (tree_open_fd_tie l (uvis_fd W) fdv' rv
                   (om_readable (m !!! Regidx a1_idx))
                   (om_writable (m !!! Regidx a1_idx)) i γo OffParked fd rd wr ty
                   Hlen Hr1 Hlt1 Hfdv1 Hrcpt).
        iApply ("Hcont" $! h' rv with "[Hal Hown] Hcwd Hrun").
        iLeft. iExists fd, γo, i. iFrame "Hal Hown". iSplitR.
        { iPureIntro. exact (conj Hr1 Hlt1). }
        by iPureIntro.
      + (* THE NAME WAS ALREADY THERE: nothing moved, and the deed is the
           ARM piece's refund *)
        iDestruct "Hex" as (avx entsx nlx) "(_ & _ & _ & _ & Harm & _)".
        rewrite /cre_child_unfired.
        iDestruct "Harm" as "(Harm & _)".
        iDestruct (pf_at_refund with "Harm") as "Hown".
        cbn [tree_arm_fam pf_refund].
        iApply ("Hcont" $! h' rv with "[Hfd Hown] Hcwd Hrun").
        iRight. iSplitL "Hfd"; [| iLeft; iExact "Hown" ].
        iApply (init_cons_any_std (ukn_fd N) l (uvis_fd W) fdv' rv with "[Hfd]").
        rewrite /uk_open_fd_arm. iExact "Hfd".
  Qed.

  (* =================================================================== *)
  (*  6.  THE TEST: THE SECOND APPLICATION'S CORE                         *)
  (*                                                                      *)
  (*  own "/" -> mkdir("/d") -> open("/f", O_CREATE) -> write -> freeze    *)
  (*  -> read-learns, in ONE run, with no whole-fs pin anywhere and no     *)
  (*  claim about a row outside the owner's own subtree.                   *)
  (*                                                                      *)
  (*  THE ONE THING THIS FILE CANNOT STATE FROM THE LEAVES, and it is the  *)
  (*  program's own code rather than the kernel's: between two ecalls a    *)
  (*  program executes ITS OWN instructions -- it loads the next syscall   *)
  (*  number, the next path pointer, the descriptor it was just handed.    *)
  (*  A corollary about ONE ecall takes the machine state as a parameter,  *)
  (*  so a corollary about FOUR has to say how the state gets from one to  *)
  (*  the next, and that is [ucode_between]: the straight-line block runs  *)
  (*  and arrives at the next ecall with the registers the block promised  *)
  (*  ([UInitConsK]'s [wp_uk_cli] chains are what discharges one).  The    *)
  (*  promise is a RELATION between the resumed state, the answer and the  *)
  (*  next state, which is what lets the write and the read name the       *)
  (*  descriptor the open just returned without this statement having to   *)
  (*  guess its number.                                                    *)
  (*                                                                      *)
  (*  WHERE THE TEST STOPS: at the read.  unlink("/f") joins it the moment *)
  (*  section 7 below's two restatements land -- the target leg's cursor   *)
  (*  and the entry-to-target receipt channel -- and nothing else in the   *)
  (*  chain moves when it does: the deed the read froze would be kept      *)
  (*  LIVE instead and handed to [TreeMove.tree_uent_piece]'s twin at the  *)
  (*  target leg.                                                          *)
  (* =================================================================== *)

  (* THE PROGRAM'S OWN CODE BETWEEN TWO ECALLS.  [Ψ] is what the block
     promises about the registers it leaves: a real program proves it
     against its own image, and every instance below is "keep the answer,
     load the next call's arguments". *)
  Definition ucode_between (N : uk_names Σ) (avail : nat) (pc pc' : mword 64)
      (Ψ : regfile -> mword 64 -> regfile -> Prop) : iProp Σ :=
    (□ ∀ (h : CpuId) (m : regfile) (rv : mword 64),
        urun N h (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
        (∀ (h' : CpuId) (m' : regfile), ⌜Ψ m rv m'⌝ -∗
           urun N h' m' pc' avail -∗ mWP (Loop : expr riscv_lang)) -∗
        mWP (Loop : expr riscv_lang))%I.

  (* ...AND ITS BAIL-OUT PATH.  The chain below continues through a FAILED
     mkdir and through a failed write -- neither costs the program its
     deed -- but an open that did not create the file has no descriptor to
     write on, so the program stops there.  This is the resource that says
     it can: a program with an [exit] to jump to. *)
  Definition ubail (N : uk_names Σ) (avail : nat) : iProp Σ :=
    (□ ∀ (h : CpuId) (m : regfile) (pc : mword 64),
        urun N h m pc avail -∗ mWP (Loop : expr riscv_lang))%I.

  (* ---- 6a.  THE FIRST HALF: the file is made and opened --------------
     Split from the second half for readability only -- the two halves
     meet at the write's ecall, where everything the second half asks of
     the tree is a fact the first half established about the tree IT
     built, so the seam is where the statement is smallest. *)
  Lemma wp_uk_tree_mkdir_then_create (N : uk_names Σ) (h : CpuId)
      (avail : nat) (c : tree_fixed) (r : tree_names) (g : gname) (t : ttree)
      (cw : Z) (Img : gmap Z (bv 8)) (l : list fdstate)
      (m1 : regfile) (pc1 pc2 pc3 : mword 64)
      (pvd pvf vom wbuf : mword 64)
      (pld plf : list (bv 8)) (nmf : fname) (e0 : gmap fname Z) (nb : nat) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tv_nodes t !! FsImg.ROOTINO = Some (ADir e0) ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pvd pld) ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pvf plf) ->
    np_elems pld = [] ->
    np_elems plf = [] ->
    um_start_of cw pld = FsImg.ROOTINO ->
    um_start_of cw plf = FsImg.ROOTINO ->
    path_elems plf = [nmf] ->
    om_create vom = true ->
    om_trunc vom = false ->
    om_readable vom = true ->
    om_writable vom = true ->
    fd_lowest_closed l = None ->
    usysno m1 = 20 ->
    m1 !!! Regidx a0_idx = pvd ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc1 4)) 2 = true ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc2 4)) 2 = true ->
    uinstr_is (ukn_t N) pc1 false (ECALL tt) -∗
    uinstr_is (ukn_t N) pc2 false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun N h m1 pc1 avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    tree_own r g FsImg.ROOTINO t -∗
    app_inv fsc_fs -∗
    ucode_between N avail pc1 pc2
      (fun _ _ m' => usysno m' = USYS_open
                     /\ m' !!! Regidx a0_idx = pvf
                     /\ m' !!! Regidx a1_idx = vom) -∗
    ucode_between N avail pc2 pc3
      (fun _ rv m' =>
         usysno m' = 16
         /\ (forall fd : nat, rv = (mword_of_int (Z.of_nat fd) : mword 64) ->
               bv_signed (trunc32 (m' !!! Regidx a0_idx)) = Z.of_nat fd)
         /\ m' !!! Regidx a1_idx = wbuf
         /\ sys_rw_count (m' !!! Regidx a2_idx) = Z.of_nat nb) -∗
    ubail N avail -∗
    (∀ (h' : CpuId) (m' : regfile) (fd : nat) (γo : gname) (i : Z)
       (t2 : ttree),
       ⌜usysno m' = 16
        /\ bv_signed (trunc32 (m' !!! Regidx a0_idx)) = Z.of_nat fd
        /\ (fd < NOFILE)%nat
        /\ m' !!! Regidx a1_idx = wbuf
        /\ sys_rw_count (m' !!! Regidx a2_idx) = Z.of_nat nb
        /\ tv_nodes t2 !! i = Some (AFile [])
        /\ resolves_from t2 FsImg.ROOTINO plf = Some (i, AFile [])
        /\ FsImg.ROOTINO ∈ dom (tv_nodes t2)⌝ -∗
       UserFd.ufd (ukn_fd N) fd (FdOpen true true (FdInode i γo OffParked)) -∗
       ustd (ukn_fd N) l -∗
       tree_own r g FsImg.ROOTINO t2 -∗
       UserCwd.ucwd (ukn_cwd N) cw -∗
       urun N h' m' pc3 avail -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hroot Hdd Hpathd Hpathf Hnpd Hnpf Hstd Hstf Hplf
      Hcr Htr Hrd Hwr Hlow Hn1 Ha01 Hal1 Hal2.
    iIntros "#Hi1 #Hi2 #Hro Hrun Hcwd Hstd Hown #Hinv #Hg1 #Hg2 #Hbail Hcont".
    (* ---- mkdir("/d"): the deed moves, or it does not, and EITHER WAY the
       chain goes on -- what the next call needs of the tree is that the
       root is still a directory of it. ---- *)
    iApply (wp_uk_ecall_mkdir_own N h m1 pc1 avail c r g t cw Img pvd pld
              Heq Hn1 Hal1 Hpathd Ha01 Hnpd Hstd Hdd
              with "Hi1 Hro Hrun Hcwd Hown Hinv").
    iIntros (h1 rv1) "Hout Hcwd Hrun".
    iAssert ((∃ (t1 : ttree) (e1 : gmap fname Z),
                tree_own r g FsImg.ROOTINO t1
                ∗ ⌜tv_nodes t1 !! FsImg.ROOTINO = Some (ADir e1)⌝
                ∗ ⌜FsImg.ROOTINO ∈ dom (tv_nodes t1)⌝)
             ∨ tree_taint c)%I with "[Hout]" as "Hout".
    { iDestruct "Hout" as "[[_ Hok] | [[_ Ht] | HT]]"; last first.
      - iRight. iExact "HT".
      - iLeft. iExists t, e0. iFrame "Ht". iPureIntro.
        exact (conj Hroot Hdd).
      - iDestruct "Hok" as (i nm) "Ht". iLeft.
        destruct (top_ins_dir_at FsImg.ROOTINO nm i (ADir ∅) t e0 Hroot
                    (or_intror (ex_intro _ ∅ eq_refl))) as [e1 He1].
        iExists (top_ins FsImg.ROOTINO nm i (ADir ∅) t), e1. iFrame "Ht".
        iPureIntro. split; [ exact He1 |].
        exact (top_ins_root_dom FsImg.ROOTINO nm i (ADir ∅) t
                 FsImg.ROOTINO Hdd). }
    iDestruct "Hout" as "[Hout | #HT]"; last first.
    { iApply ("Hbail" with "Hrun"). }
    iDestruct "Hout" as (t1 e1) "(Hown & %Hroot1 & %Hdd1)".
    iApply ("Hg1" $! h1 m1 rv1 with "Hrun").
    iIntros (h2 m2) "%HPs1 Hrun". destruct HPs1 as (Hn2 & Ha02 & Ha12).
    (* ---- open("/f", O_CREATE): the file is made, the deed moves, and the
       descriptor comes back ON IT ---- *)
    iApply (wp_uk_ecall_open_create_own N h2 m2 pc2 l avail c r g t1 cw Img
              pvf plf nmf Heq Hn2 Hal2 Hpathf Ha02
              ltac:(rewrite Ha12; exact Hcr) ltac:(rewrite Ha12; exact Htr)
              Hnpf ltac:(rewrite Hplf; reflexivity) Hstf Hdd1
              with "Hi2 Hro Hrun Hcwd Hstd Hown Hinv").
    iIntros (h3 rv2) "Hout Hcwd Hrun".
    iDestruct "Hout" as "[Hfresh | [_ _]]"; last first.
    { (* the name was already there, or the call failed: the program has no
         descriptor to write on, so it stops *)
      iApply ("Hbail" with "Hrun"). }
    iDestruct "Hfresh" as (fd γo i) "((%Hrv2 & %Hfdlt) & Hal & Hown & %Hne)".
    rewrite Ha12 Hrd Hwr.
    iDestruct (ualloc_hi (ukn_fd N) l fd
                 (FdOpen true true (FdInode i γo OffParked)) Hlow
                 with "Hal") as "(_ & Hstd & Hufd)".
    assert (Hfile : tv_nodes (top_ins FsImg.ROOTINO nmf i (AFile []) t1) !! i
                    = Some (AFile [])).
    { rewrite /top_ins /=.
      rewrite (tedge_ins_lookup_ne _ FsImg.ROOTINO nmf i i ltac:(exact Hne)).
      rewrite lookup_insert //. }
    assert (Hres : resolves_from (top_ins FsImg.ROOTINO nmf i (AFile []) t1)
                     FsImg.ROOTINO plf = Some (i, AFile [])).
    { exact (resolves_from_top_ins FsImg.ROOTINO nmf i (AFile []) t1 e1 plf
               Hroot1 Hne Hplf). }
    assert (Hdd2 : FsImg.ROOTINO
                   ∈ dom (tv_nodes (top_ins FsImg.ROOTINO nmf i (AFile []) t1)))
      by exact (top_ins_root_dom FsImg.ROOTINO nmf i (AFile []) t1
                  FsImg.ROOTINO Hdd1).
    iApply ("Hg2" $! h3 m2 rv2 with "Hrun").
    iIntros (h4 m3) "%HPs2 Hrun". destruct HPs2 as (Hn3 & Hfd3 & Ha13 & Ha23).
    iApply ("Hcont" $! h4 m3 fd γo i
              (top_ins FsImg.ROOTINO nmf i (AFile []) t1)
              with "[%] Hufd Hstd Hown Hcwd Hrun").
    split_and!; [ exact Hn3 | exact (Hfd3 fd Hrv2) | exact Hfdlt
                | exact Ha13 | exact Ha23 | exact Hfile | exact Hres
                | exact Hdd2 ].
  Qed.

  (* ---- 6b.  THE SECOND HALF: the bytes land, the deed is frozen, and
     the read delivers what the tree records ---- *)
  Lemma wp_uk_tree_write_then_read (N : uk_names Σ) (h : CpuId) (avail : nat)
      (c : tree_fixed) (r : tree_names) (g : gname) (t2 : ttree)
      (i : Z) (fd : nat) (γo : gname) (cw : Z)
      (m3 : regfile) (pc3 pc4 : mword 64) (wbuf rbuf : mword 64)
      (plf : list (bv 8)) (bs0 : list (bv 8))
      (dq : dfrac) (nb k : nat) (cnt : Z) (fw fr : nat -> bv 8) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    usysno m3 = 16 ->
    bv_signed (trunc32 (m3 !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    m3 !!! Regidx a1_idx = wbuf ->
    sys_rw_count (m3 !!! Regidx a2_idx) = Z.of_nat nb ->
    tv_nodes t2 !! i = Some (AFile bs0) ->
    resolves_from t2 FsImg.ROOTINO plf = Some (i, AFile bs0) ->
    FsImg.ROOTINO ∈ dom (tv_nodes t2) ->
    fs_proper (path_elems plf) ->
    um_start_of cw plf = FsImg.ROOTINO ->
    (Z.to_nat cnt <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc3 4)) 2 = true ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc4 4)) 2 = true ->
    uinstr_is (ukn_t N) pc3 false (ECALL tt) -∗
    uinstr_is (ukn_t N) pc4 false (ECALL tt) -∗
    urun N h m3 pc3 avail -∗
    UserFd.ufd (ukn_fd N) fd (FdOpen true true (FdInode i γo OffParked)) -∗
    ubytesq (ukn_d N) dq (uint wbuf) nb fw -∗
    ubytes (ukn_d N) (uint rbuf) k fr -∗
    tree_own r g FsImg.ROOTINO t2 -∗
    app_inv fsc_fs -∗
    ucode_between N avail pc3 pc4
      (fun m _ m' =>
         usysno m' = USYS_read
         /\ bv_signed (trunc32 (m' !!! Regidx a0_idx))
            = bv_signed (trunc32 (m !!! Regidx a0_idx))
         /\ m' !!! Regidx a1_idx = rbuf
         /\ bv_signed (subrange_vec_dec (m' !!! Regidx a2_idx) 31 0 : mword 32)
            = cnt) -∗
    ubail N avail -∗
    (∀ (h' : CpuId) (m' : regfile) (rv : mword 64) (gb : nat -> bv 8),
       ((∃ (t3 : ttree) (bs' : list (bv 8)),
           tree_pin r g FsImg.ROOTINO t3 ∗
           ⌜resolves_from t3 FsImg.ROOTINO plf = Some (i, AFile bs')⌝ ∗
           (⌜rv = (mword_of_int (-1) : mword 64)⌝
            ∨ (∃ off : nat,
                 ⌜Z.to_nat (bv_unsigned rv)
                  = ard_count (Z.to_nat cnt) off (length bs')⌝ ∗
                 ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                    gb j = bs' !!! (off + j)%nat⌝)))
        ∨ tree_taint c) -∗
       urun N h' (<[Regidx a0_idx := rv]> m') (add_vec_int pc4 4) avail -∗
       ubytes (ukn_d N) (uint rbuf) k gb -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hn3 Hfd3 Hfdlt Ha13 Ha23 Hfile Hres Hdd2 Hprop Hstf Hck
      Hal3 Hal4.
    iIntros "#Hi3 #Hi4 Hrun Hufd Hwbuf Hrbuf Hown #Hinv #Hg3 #Hbail Hcont".
    (* ---- write: the bytes land and the deed moves again ---- *)
    iApply (wp_uk_tree_write_moves N h m3 pc3 avail fd true i γo dq nb fw
              c r g FsImg.ROOTINO t2 bs0 Heq Hn3 Hfd3 Hfdlt Ha23 Hal3 Hfile
              with "Hi3 Hrun Hufd [Hwbuf] Hown Hinv").
    { rewrite Ha13. iExact "Hwbuf". }
    iIntros (h5 rv3) "Hufd Hwbuf _ Hmv Hrun".
    iDestruct "Hmv" as "[Hmv | #HT]"; last first.
    { iApply ("Hbail" with "Hrun"). }
    iDestruct "Hmv" as (t3) "(Hown & %Hw)".
    destruct (twrote_read_back i t2 t3 FsImg.ROOTINO bs0 plf Hw Hdd2 Hres)
      as (bs' & Hdd3 & Hres3 & _).
    (* ---- FREEZE, and read back what was written ---- *)
    iApply fupd_wp_triv.
    iMod (tree_freeze r g FsImg.ROOTINO t3 with "Hown") as "#Hpin".
    iModIntro.
    iApply ("Hg3" $! h5 m3 rv3 with "Hrun").
    iIntros (h6 m4) "%HPs3 Hrun". destruct HPs3 as (Hn4 & Hfd4 & Ha14 & Ha24).
    assert (Hfdr : bv_signed (trunc32 (m4 !!! Regidx a0_idx))
                        = Z.of_nat fd) by (rewrite Hfd4; exact Hfd3).
    iEval (rewrite -Ha14) in "Hrbuf".
    iApply (wp_uk_tree_read_learns N h6 m4 pc4 cnt k fr avail fd true i γo
              c r g FsImg.ROOTINO FsImg.ROOTINO t3 bs' plf cw
              Heq Hn4 Ha24 Hck Hfdr Hfdlt Hal4 Hprop Hstf Hdd3 Hres3
              with "Hi4 Hrun Hufd Hpin Hinv Hrbuf").
    iIntros (h7 rv4 gb) "Hufd Hlearn Hrun Hrbuf".
    iEval (rewrite Ha14) in "Hrbuf".
    iApply ("Hcont" $! h7 m4 rv4 gb with "[Hlearn] Hrun Hrbuf").
    iDestruct "Hlearn" as "[Hl | #HT]"; last first.
    { iRight. iExact "HT". }
    iLeft. iExists t3, bs'. iFrame "Hpin". iSplitR.
    { iPureIntro. exact Hres3. }
    iExact "Hl".
  Qed.

  (* ---- 6c.  THE CHAIN.  No leaf of its own: the two halves meet at the
     write's ecall, and every fact the second half asks of the tree is one
     the first half established about the tree IT built. ---- *)
  Lemma wp_uk_tree_app_core (N : uk_names Σ) (h : CpuId) (avail : nat)
      (c : tree_fixed) (r : tree_names) (g : gname) (t : ttree)
      (cw : Z) (Img : gmap Z (bv 8)) (l : list fdstate)
      (m1 : regfile) (pc1 pc2 pc3 pc4 : mword 64)
      (pvd pvf vom wbuf rbuf : mword 64)
      (pld plf : list (bv 8)) (nmf : fname) (e0 : gmap fname Z)
      (dq : dfrac) (nb k : nat) (cnt : Z) (fw fr : nat -> bv 8) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    tv_nodes t !! FsImg.ROOTINO = Some (ADir e0) ->
    FsImg.ROOTINO ∈ dom (tv_nodes t) ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pvd pld) ->
    (forall M : gmap Z (bv 8), uimg_sub Img M -> arg_path_of M pvf plf) ->
    np_elems pld = [] ->
    np_elems plf = [] ->
    um_start_of cw pld = FsImg.ROOTINO ->
    um_start_of cw plf = FsImg.ROOTINO ->
    path_elems plf = [nmf] ->
    fs_proper (path_elems plf) ->
    om_create vom = true ->
    om_trunc vom = false ->
    om_readable vom = true ->
    om_writable vom = true ->
    fd_lowest_closed l = None ->
    usysno m1 = 20 ->
    m1 !!! Regidx a0_idx = pvd ->
    (Z.to_nat cnt <= k)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc1 4)) 2 = true ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc2 4)) 2 = true ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc3 4)) 2 = true ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc4 4)) 2 = true ->
    uinstr_is (ukn_t N) pc1 false (ECALL tt) -∗
    uinstr_is (ukn_t N) pc2 false (ECALL tt) -∗
    uinstr_is (ukn_t N) pc3 false (ECALL tt) -∗
    uinstr_is (ukn_t N) pc4 false (ECALL tt) -∗
    utext_img (ukn_t N) Img -∗
    urun N h m1 pc1 avail -∗
    UserCwd.ucwd (ukn_cwd N) cw -∗
    ustd (ukn_fd N) l -∗
    (* THE DEED, LIVE: this run moves it three times *)
    tree_own r g FsImg.ROOTINO t -∗
    app_inv fsc_fs -∗
    (* the bytes the program sends, and the buffer it reads back into *)
    ubytesq (ukn_d N) dq (uint wbuf) nb fw -∗
    ubytes (ukn_d N) (uint rbuf) k fr -∗
    ucode_between N avail pc1 pc2
      (fun _ _ m' => usysno m' = USYS_open
                     /\ m' !!! Regidx a0_idx = pvf
                     /\ m' !!! Regidx a1_idx = vom) -∗
    ucode_between N avail pc2 pc3
      (fun _ rv m' =>
         usysno m' = 16
         /\ (forall fd : nat, rv = (mword_of_int (Z.of_nat fd) : mword 64) ->
               bv_signed (trunc32 (m' !!! Regidx a0_idx)) = Z.of_nat fd)
         /\ m' !!! Regidx a1_idx = wbuf
         /\ sys_rw_count (m' !!! Regidx a2_idx) = Z.of_nat nb) -∗
    ucode_between N avail pc3 pc4
      (fun m _ m' =>
         usysno m' = USYS_read
         /\ bv_signed (trunc32 (m' !!! Regidx a0_idx))
            = bv_signed (trunc32 (m !!! Regidx a0_idx))
         /\ m' !!! Regidx a1_idx = rbuf
         /\ bv_signed (subrange_vec_dec (m' !!! Regidx a2_idx) 31 0 : mword 32)
            = cnt) -∗
    ubail N avail -∗
    (∀ (h' : CpuId) (m' : regfile) (rv : mword 64) (gb : nat -> bv 8),
       (* WHAT THE PROGRAM LEARNED: the bytes the read delivered are the
          bytes ITS OWN TREE records at the path it created -- and it holds
          that tree, frozen, to say so. *)
       ((∃ (i : Z) (t3 : ttree) (bs' : list (bv 8)),
           tree_pin r g FsImg.ROOTINO t3 ∗
           ⌜resolves_from t3 FsImg.ROOTINO plf = Some (i, AFile bs')⌝ ∗
           (⌜rv = (mword_of_int (-1) : mword 64)⌝
            ∨ (∃ off : nat,
                 ⌜Z.to_nat (bv_unsigned rv)
                  = ard_count (Z.to_nat cnt) off (length bs')⌝ ∗
                 ⌜forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                    gb j = bs' !!! (off + j)%nat⌝)))
        ∨ tree_taint c) -∗
       urun N h' (<[Regidx a0_idx := rv]> m') (add_vec_int pc4 4) avail -∗
       ubytes (ukn_d N) (uint rbuf) k gb -∗
       mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Heq Hroot Hdd Hpathd Hpathf Hnpd Hnpf Hstd Hstf Hplf Hprop
      Hcr Htr Hrd Hwr Hlow Hn1 Ha01 Hck Hal1 Hal2 Hal3 Hal4.
    iIntros "#Hi1 #Hi2 #Hi3 #Hi4 #Hro Hrun Hcwd Hstd Hown #Hinv Hwbuf Hrbuf".
    iIntros "#Hg1 #Hg2 #Hg3 #Hbail Hcont".
    iApply (wp_uk_tree_mkdir_then_create N h avail c r g t cw Img l m1
              pc1 pc2 pc3 pvd pvf vom wbuf pld plf nmf e0 nb
              Heq Hroot Hdd Hpathd Hpathf Hnpd Hnpf Hstd Hstf Hplf
              Hcr Htr Hrd Hwr Hlow Hn1 Ha01 Hal1 Hal2
              with "Hi1 Hi2 Hro Hrun Hcwd Hstd Hown Hinv Hg1 Hg2 Hbail").
    iIntros (h' m' fd γo i t2) "%Hfacts Hufd Hstd Hown Hcwd Hrun".
    destruct Hfacts as (Hn3 & Hfd3 & Hfdlt & Ha13 & Ha23 & Hfile & Hres & Hdd2).
    iApply (wp_uk_tree_write_then_read N h' avail c r g t2 i fd γo cw m' pc3 pc4
              wbuf rbuf plf [] dq nb k cnt fw fr
              Heq Hn3 Hfd3 Hfdlt Ha13 Ha23 Hfile Hres Hdd2 Hprop Hstf Hck
              Hal3 Hal4
              with "Hi3 Hi4 Hrun Hufd Hwbuf Hrbuf Hown Hinv Hg3 Hbail").
    iIntros (h'' m'' rv gb) "Hlearn Hrun Hrbuf".
    iApply ("Hcont" $! h'' m'' rv gb with "[Hlearn] Hrun Hrbuf").
    iDestruct "Hlearn" as "[Hl | #HT]"; last first.
    { iRight. iExact "HT". }
    iDestruct "Hl" as (t3 bs') "(Hpin & %Hr3 & Hl)".
    iLeft. iExists i, t3, bs'. iFrame "Hpin". iSplitR.
    { iPureIntro. exact Hr3. }
    iExact "Hl".
  Qed.

End UkTreeCreate.

(* ===================================================================== *)
(*  7.  WHAT UNLINK'S TARGET LEG STILL WANTS, AND WHAT IT COSTS           *)
(*                                                                       *)
(*  design/user-tree.md section 7.9(8), priced at section 7.10(8).  The   *)
(*  tree side is DONE on both legs: [TreeMove.tree_uent_commit] is the    *)
(*  entry leg at the shape [SpecSysUnlink.unlink_au_at] asks for, and     *)
(*  [TreeMove.tree_utgt_phases_rooted] is the target leg's move at a      *)
(*  GIVEN target -- including a directory's last link, which TL-2 had     *)
(*  recorded as a wall.  What is missing is two KERNEL-TIER              *)
(*  RESTATEMENTS, both TL-3K-shaped, and neither is a credential:        *)
(*                                                                       *)
(*  (a) THE TARGET CURSOR.  [SysUnlinkDefs.utgt_commit_at Γ E Φ] binds    *)
(*      its target [t] INSIDE with no cursor, so a supplier owes a step   *)
(*      at EVERY row of every view at count >= 1 -- including a row that  *)
(*      IS named, where [delta_unl_tgt] leaves a DANGLING ENTRY and no    *)
(*      application has a step at all.  The fix is TL-3K's verbatim: a    *)
(*      parameter [Pt : Z -> iProp] and a premise [Pt t] beside           *)
(*      [abs_view I !! t = Some a], READ AND HANDED BACK in phase 1.      *)
(*      [uent_commit_at_mono] / [_cur] are the two movers to copy;        *)
(*      [utgt_commit_at_unit] gains a [forall Pt] and its proof is        *)
(*      unchanged but for framing.  [ProofSysUnlinkW5D] / [W5F] hold the  *)
(*      target they just resolved and already pass the ENTRY cursor into  *)
(*      [uf_uent_fire] and take it back, so the fire sites pay nothing.   *)
(*                                                                       *)
(*  (b) THE RECEIPT CHANNEL.  create's two child legs share the arm's     *)
(*      receipt ([FsAbsCreateFire.cre_arm_fired], the exclusive one-shot  *)
(*      per armed inode, and it is what lets section 3's ONE deed answer  *)
(*      four [*]-joined legs); unlink's two legs share NOTHING, so the    *)
(*      MOVED deed the entry leg returns cannot reach the target leg's    *)
(*      AU.  The fix is that same trick at the unlink family:             *)
(*      [utgt_commit_at] takes the entry leg's own receipt at the target  *)
(*      it cut, exactly as [aunarm_of_arm] takes the arm's.  The          *)
(*      exclusion argument is already there -- the kernel cuts the entry  *)
(*      once and only then unlinks the target.                            *)
(*                                                                       *)
(*  With both, [tree_utgt_phases_rooted]'s premise                        *)
(*  [tg not in dom (tv_nodes t)] is what the entry leg's receipt          *)
(*  delivers (the moved tree is [top_unlink d nm t]), the unlink          *)
(*  corollary is row 18's assembly on section 6a's mould, and the test    *)
(*  gains its last step -- keeping the deed LIVE where section 6b freezes *)
(*  it.                                                                   *)
(* ===================================================================== *)
