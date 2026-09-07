(* FsAbsCreateFire.v -- CREATE'S LEGS AS COMMITS AND FIRES (round E2, lane
   E2-C), and the authority-shaped commits of the create family, moved down
   here from FsAbsMknodFire.v so that [SpecCreate]'s bundle can name them.

   Design of record: claude-notes/design/applications.md section 2 (the
   three mover forms), claude-notes/design/fs-syscall-specs.md section 4
   (the legs), claude-notes/projects/app-round-e2.md sections 2(b)/3/5.

   ==== WHAT MOVES HERE ================================================

   The kernel performs [delta_create] as LEGS, one retag each:

     the ARM     ialloc's claim box gets [ip->nlink = 1; iupdate] -- the
                 child's row APPEARS at content [c], count 1 ([delta_arm]);
     the DOTS    mkdir's two interior [dirlink]s -- the child's row moves
                 from [ADir ∅] to a directory holding its dots
                 ([delta_dots], or [delta_dot] when the [".."] fell short);
     the PARENT  [dirlink(dp, name, ip->inum)] and mkdir's [dp->nlink++] --
                 [acre_commit_at]'s fused [delta_create], which at an ARMED
                 child IS the parent's one-row insert
                 ([FsAbsDelta.delta_create_armed]);
     the UNARM   the failure arm's [ip->nlink = 0] -- the row DISAPPEARS
                 ([delta_unarm]).  Ruling Q-h: a failed create is the
                 honest do-then-undo PAIR, arm then unarm, each an instant a
                 concurrent [ilock] can observe.

   Each leg is a two-phase commit in [acre_commit_at]'s mold (phase 1 hands
   the caller's step back beside the kernel's half of the authority; phase 2
   is quantified over the POST map and constrained by its reading), and
   each fires INSIDE the mover's [ftopN] critical section -- for the child
   under the ARMED registry ([InodeRegion.ireg_armed]), which is what
   exempts the half-built directory from [ftop_body]'s [inode_local] row
   between its count landing and its dots.

   ==== THE CHILD'S CONTENT IS TYPE-INDEXED ============================

   [cre_c0 tyz ma mi] is the row content the arm writes (an empty file, an
   empty directory, a device at the two halfwords); [cre_child tyz ma mi d i]
   the content the parent leg reads -- for a directory the dots are in, and
   they NAME THE TWO INUMS, which is why [acre_commit_at_gen] takes the
   content as a function of (parent, child) and [acre_commit_at c] is its
   constant instance.  The AU twins ([SpecCreateAU] at a device,
   [SpecCreateAUF] at a file) stay on the constant form; the general create
   ([SpecCreate], mkdir's only path) takes the function.

   ==== THE DOTS COMMIT IS INDEXED BY WHAT LANDED =======================

   mkdir's [dirlink(ip, "..", dp->inum)] can fall short after the ["."]
   went in whole (ProofCreateMkdir's FAIL ENTRY 2); the child's row then
   moves ONCE, to a directory holding only ["."], and the failure arm
   unarms it.  [adots_commit_at] fires at either reading -- [full = true]
   for both dots, [full = false] for the first alone -- and its receipt
   says which ([FsAbsDelta.dots_delta], [dots_ents]).

   BINDERS: [SpecCreate]'s section list VERBATIM (which is
   [SpecSysMknodAU]'s) -- [fileG] is bound and [icacheG]/[icfg] resolve
   only through its fields. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import DinodeEnc.
Require Import DirView.          (* [T_DIR_z]                               *)
Require Import FsTree.           (* [fname], [DOT], [DOTDOT]                *)
Require Import FsBlocks.         (* [fs_names]                              *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                            *)
Require Import InodeInv.
Require Import IrefSlots.
Require Import Xv6Cameras.
(* the binder classes, IMPORTED rather than inherited (FsAbsMknodFire's
   note: an unbound [fileG] in a [`{! ...}] binder is silently generalised
   into a VARIABLE) *)
Require Import FdSlots.          (* [fdslotG]                               *)
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]   *)
Require Import ProcAvail.        (* [pavG]                                  *)
Require Import FsStateEra.       (* [era_node], [era_node_rec]              *)
Require Import InodeRegion.      (* [ftop_inv]/[ftop_body]/[ireg_armed]     *)
Require Import Xv6G.
Require FsImg.                   (* [FsImg.T_FILE_z], qualified             *)
Require Import FsAbsDelta.       (* the legs, [cre_pre], [dots_delta]       *)
Require Import AppInv.           (* [appN]/[appE], [app_step], [app_inv]    *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)                 *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE CHILD'S CONTENT, BY TYPE (pure)                               *)
(* ===================================================================== *)

(* what the ARM writes: ialloc's claim box is typed [tyz] with size 0, so
   its row at count 1 is an empty file, an empty directory, or the device
   at the two halfwords the stores before the count set *)
Definition cre_c0 (tyz ma mi : Z) : absnode :=
  if decide (tyz = T_DIR_z) then ADir ∅
  else if decide (tyz = FsImg.T_FILE_z) then AFile [] else ADev ma mi.

(* ...and what the PARENT LEG reads: a directory child has its two dots by
   then, and they name the child ([DOT]) and the parent ([DOTDOT]) *)
Definition cre_child (tyz ma mi : Z) (d i : Z) : absnode :=
  if decide (tyz = T_DIR_z) then ADir (dots_ents true i d) else cre_c0 tyz ma mi.

Lemma cre_c0_dir (ma mi : Z) : cre_c0 T_DIR_z ma mi = ADir ∅.
Proof. rewrite /cre_c0. case_decide as Hd; [reflexivity | exfalso; exact (Hd eq_refl)]. Qed.

Lemma cre_child_dir (ma mi d i : Z) :
  cre_child T_DIR_z ma mi d i = ADir (dots_ents true i d).
Proof. rewrite /cre_child. case_decide as Hd; [reflexivity | exfalso; exact (Hd eq_refl)]. Qed.

Lemma cre_child_nondir (tyz ma mi d i : Z) :
  tyz <> T_DIR_z -> cre_child tyz ma mi d i = cre_c0 tyz ma mi.
Proof. intros Hne. rewrite /cre_child. case_decide as Hd; [exfalso; exact (Hne Hd) | reflexivity]. Qed.

(* a non-directory child bumps nothing *)
Lemma acre_bump_cre_c0 (tyz ma mi : Z) :
  tyz <> T_DIR_z -> acre_bump (cre_c0 tyz ma mi) = 0%nat.
Proof.
  intros Hne. rewrite /cre_c0. case_decide as Hd; [exfalso; exact (Hne Hd) |].
  destruct (decide (tyz = FsImg.T_FILE_z)); reflexivity.
Qed.

Lemma acre_bump_cre_child_dir (ma mi d i : Z) :
  acre_bump (cre_child T_DIR_z ma mi d i) = 1%nat.
Proof. rewrite cre_child_dir //. Qed.

(* ===================================================================== *)
(*  0b.  THE ERA NODE'S ROW, AT THE THREE COUNTS A LEG SEES (pure)        *)
(* ===================================================================== *)

Lemma caf_era_type (dn : dinode) (bm : blkmap) (dat : nat -> list (bv 8)) :
  fn_type (era_node dn bm dat) = bv_unsigned (di_type dn).
Proof. by rewrite /fn_type era_node_rec. Qed.

Lemma caf_era_nlink (dn : dinode) (bm : blkmap) (dat : nat -> list (bv 8)) :
  fn_nlink (era_node dn bm dat) = Z.to_nat (bv_unsigned (di_nlink dn)).
Proof. by rewrite /fn_nlink era_node_rec. Qed.

(* count 0: no row (the claim box before the arm, the child after the
   failure arm's [sh zero,74(s3)]) *)
Lemma caf_era_none_nl0 (dn : dinode) (bm : blkmap) (dat : nat -> list (bv 8)) :
  bv_unsigned (di_nlink dn) = 0 -> abs_of (era_node dn bm dat) = None.
Proof.
  intros Hnl. apply abs_of_none. right. rewrite caf_era_nlink Hnl. reflexivity.
Qed.

(* count 1 at a typed record: its typed row *)
Lemma caf_era_row_nl1 (dn : dinode) (bm : blkmap) (dat : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> 0 -> bv_unsigned (di_nlink dn) = 1 ->
  abs_of (era_node dn bm dat)
  = Some (MkAnode (abs_node (era_node dn bm dat)) 1%nat).
Proof.
  intros Hty Hnl.
  assert (Hn1 : fn_nlink (era_node dn bm dat) = 1%nat)
    by (rewrite caf_era_nlink Hnl; reflexivity).
  rewrite (abs_of_live (era_node dn bm dat)
             ltac:(rewrite caf_era_type; exact Hty)
             ltac:(rewrite Hn1; discriminate)).
  rewrite /abs_row Hn1. reflexivity.
Qed.

(* ...and at a directory record, the entries spelled out *)
Lemma caf_era_dir_row (dn : dinode) (bm : blkmap) (dat : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) = T_DIR_z -> bv_unsigned (di_nlink dn) = 1 ->
  abs_of (era_node dn bm dat)
  = Some (MkAnode (ADir (dir_entries (era_node dn bm dat))) 1%nat).
Proof.
  intros Hty Hnl.
  assert (Hn1 : fn_nlink (era_node dn bm dat) = 1%nat)
    by (rewrite caf_era_nlink Hnl; reflexivity).
  rewrite (abs_of_dir (era_node dn bm dat)
             ltac:(rewrite /fn_is_dir caf_era_type; by apply bool_decide_eq_true_2)
             ltac:(rewrite Hn1; discriminate)).
  rewrite Hn1. reflexivity.
Qed.

Section CreateFire.
  (* [SpecCreate]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  THE AUTHORITY-SHAPED COMMITS                                    *)
  (*      ([dlookup_commit_at]/[acre_commit_at] moved from                *)
  (*      FsAbsMknodFire.v, which re-exports them; the legs are new)      *)
  (* =================================================================== *)

  (* the read-only sibling, at the raw map.  Note the receipt is handed
     the READING [abs_view I], so a client never sees a record. *)
  Definition dlookup_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (d i : Z) (nm : fname) (ents : gmap fname Z)
       (nl : nat),
       ⌜abs_view I !! d = Some (MkAnode (ADir ents) nl)⌝ -∗
       ⌜ents !! nm = Some i⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗ Φ (abs_view I) d nm i)%I.

  (* THE PARENT LEG (create's success commit), two-phase, at the raw map,
     with the child's content a FUNCTION of the two inums (a directory's
     dots name them).  Phase 2 is quantified over the POST map and
     constrained by its READING alone -- so the client still witnesses
     exactly "the delta was applied" and nothing about the record the
     mover chose. *)
  Definition acre_commit_at_gen Γ (E : coPset) (cf : Z -> Z -> absnode)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (d i : Z) (nm : fname) (ents : gmap fname Z)
       (nl : nat),
       ⌜cre_pre (abs_view I) d nm ents nl i (cf d i)⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗
         (* THE CALLER'S STEP (app-instances.md section 7): its claim about
            the pre-view survives the delta, at the RAW insert the mover
            performs ([AppInv.app_step]; the delta is its reading) *)
         app_step d I (delta_create d nm i (cf d i) (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_create d nm i (cf d i) (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗ Φ (abs_view I) d nm i))%I.

  (* ...and the CONSTANT-content instance the two pinned AU twins carry
     (a device at mknod, an empty file at open(O_CREATE)) *)
  Definition acre_commit_at Γ (E : coPset) (c : absnode)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) : iProp Σ :=
    acre_commit_at_gen Γ E (fun _ _ => c) Φ.

  (* THE ARM: the row APPEARS.  The view has no row at [i] (the claim box
     is at count 0) but the MAP has one -- the child's inum is a region
     row -- which is what lets the generic discharger pay the step off the
     parked license ([AppInv.app_step_acc] wants [is_Some (I !! i)]). *)
  Definition aarm_commit_at Γ (E : coPset) (c : absnode)
      (Φ : aview -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (i : Z),
       ⌜abs_view I !! i = None⌝ -∗ ⌜is_Some (I !! i)⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗
         app_step i I (delta_arm i c (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_arm i c (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗ Φ (abs_view I) i))%I.

  (* THE DOTS: an empty directory at count 1 gains its dot names -- both
     ([full = true], [delta_dots i d]) or the first alone ([full = false],
     [delta_dot i]; the [".."] write fell short).  [d] is the parent. *)
  Definition adots_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> Z -> bool -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (i d : Z) (full : bool),
       ⌜abs_view I !! i = Some (MkAnode (ADir ∅) 1%nat)⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗
         app_step i I (dots_delta full i d (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = dots_delta full i d (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗ Φ (abs_view I) i d full))%I.

  (* THE UNARM (ruling Q-h): a row at count 1 -- whatever its content --
     DISAPPEARS.  The content is quantified inside: the failure arms reach
     it with an empty file, a device, or a directory holding no, one or
     two dots. *)
  Definition aunarm_commit_at Γ (E : coPset)
      (Φ : aview -> Z -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (i : Z) (c : absnode),
       ⌜abs_view I !! i = Some (MkAnode c 1%nat)⌝ -∗
       ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
       ghost_map_auth (γtop Γ) (1/2) I ∗
         app_step i I (delta_unarm i (abs_view I)) ∗
         (∀ I' : gmap Z fs_node,
            ⌜abs_view I' = delta_unarm i (abs_view I)⌝ -∗
            ghost_map_auth (γtop Γ) (1/2) I' ={E}=∗
            ghost_map_auth (γtop Γ) (1/2) I' ∗ Φ (abs_view I) i))%I.

  (* ------------------------------------------------------------------ *)
  (*  1a.  The receipts, as the contracts hand them out                   *)
  (* ------------------------------------------------------------------ *)

  (* each with its instant's pure facts restated beside the caller's Φ *)
  Definition cre_arm_fired (Φ : aview -> Z -> iProp Σ) (i : Z) : iProp Σ :=
    (∃ av : aview, ⌜av !! i = None⌝ ∗ Φ av i)%I.

  Definition cre_dots_fired (Φ : aview -> Z -> Z -> bool -> iProp Σ)
      (i d : Z) (full : bool) : iProp Σ :=
    (∃ av : aview, ⌜av !! i = Some (MkAnode (ADir ∅) 1%nat)⌝ ∗ Φ av i d full)%I.

  Definition cre_unarm_fired (Φ : aview -> Z -> iProp Σ) (i : Z) : iProp Σ :=
    (∃ (av : aview) (c : absnode), ⌜av !! i = Some (MkAnode c 1%nat)⌝ ∗ Φ av i)%I.

  Definition cre_acre_fired (Φ : aview -> Z -> fname -> Z -> iProp Σ)
      (d : Z) (nm : fname) (i : Z) (c : absnode) : iProp Σ :=
    (∃ (av : aview) (ents : gmap fname Z) (nl : nat),
       ⌜cre_pre av d nm ents nl i c⌝ ∗ Φ av d nm i)%I.

  (* the child's two legs, as the AU twins' arms carry them: both commits
     back UNFIRED, or the do-then-undo PAIR (ruling Q-h) *)
  Definition cre_child_unfired Γ (c : absnode)
      (Φarm Φun : aview -> Z -> iProp Σ) : iProp Σ :=
    (aarm_commit_at Γ appE c Φarm ∗ aunarm_commit_at Γ appE Φun)%I.

  Definition cre_child_pair (Φarm Φun : aview -> Z -> iProp Σ) (i : Z) : iProp Σ :=
    (cre_arm_fired Φarm i ∗ cre_unarm_fired Φun i)%I.

  (* ------------------------------------------------------------------ *)
  (*  1b.  Satisfiability: the [_unit] dischargers                        *)
  (* ------------------------------------------------------------------ *)

  Lemma dlookup_commit_at_unit Γ E :
    ⊢ dlookup_commit_at Γ E (fun _ _ _ _ => True%I).
  Proof.
    rewrite /dlookup_commit_at. iIntros (I d i nm ents nl) "%Hd %Hnm Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  (* the write-kind ones owe the caller's step, paid at the live Γ out of
     the parked license ([AppInv.app_step_acc]) *)
  Lemma acre_commit_at_gen_unit (γfs : fs_names) E (cf : Z -> Z -> absnode) :
    ↑appN ⊆ E ->
    app_inv γfs -∗ acre_commit_at_gen (fs_gamma_L γfs) E cf (fun _ _ _ _ => True%I).
  Proof.
    iIntros (HE) "#Hai". rewrite /acre_commit_at_gen.
    iIntros (I d i nm ents nl) "%Hpre Ha".
    iMod (app_step_acc E γfs d I _ HE
            (abs_view_lookup_is_Some I d _ (proj1 Hpre)) with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma acre_commit_at_unit (γfs : fs_names) E c :
    ↑appN ⊆ E ->
    app_inv γfs -∗ acre_commit_at (fs_gamma_L γfs) E c (fun _ _ _ _ => True%I).
  Proof.
    iIntros (HE) "#Hai". rewrite /acre_commit_at.
    iApply (acre_commit_at_gen_unit γfs E _ HE with "Hai").
  Qed.

  (* the arm's step is paid although the VIEW has no row: the MAP has one *)
  Lemma aarm_commit_at_unit (γfs : fs_names) E c :
    ↑appN ⊆ E ->
    app_inv γfs -∗ aarm_commit_at (fs_gamma_L γfs) E c (fun _ _ => True%I).
  Proof.
    iIntros (HE) "#Hai". rewrite /aarm_commit_at. iIntros (I i) "%Hnone %Hsome Ha".
    iMod (app_step_acc E γfs i I _ HE Hsome with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma adots_commit_at_unit (γfs : fs_names) E :
    ↑appN ⊆ E ->
    app_inv γfs -∗ adots_commit_at (fs_gamma_L γfs) E (fun _ _ _ _ => True%I).
  Proof.
    iIntros (HE) "#Hai". rewrite /adots_commit_at. iIntros (I i d full) "%Hrow Ha".
    iMod (app_step_acc E γfs i I _ HE
            (abs_view_lookup_is_Some I i _ Hrow) with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  Lemma aunarm_commit_at_unit (γfs : fs_names) E :
    ↑appN ⊆ E ->
    app_inv γfs -∗ aunarm_commit_at (fs_gamma_L γfs) E (fun _ _ => True%I).
  Proof.
    iIntros (HE) "#Hai". rewrite /aunarm_commit_at. iIntros (I i c) "%Hrow Ha".
    iMod (app_step_acc E γfs i I _ HE
            (abs_view_lookup_is_Some I i _ Hrow) with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    by iFrame "Ha'".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  1c.  Agreement against the authority, without spending it, and     *)
  (*       the [_pinned] seeds the stable corollaries are assembled from *)
  (* ------------------------------------------------------------------ *)

  (* at ANY fraction of the authority: agreement is all a reading needs *)
  Lemma mkf_auth_frag Γ (q : Qp) (I : gmap Z fs_node) (dq : dfrac) (i : Z)
      (n : fs_node) :
    ghost_map_auth (γtop Γ) q I -∗ top_frag_q Γ dq i n -∗ ⌜I !! i = Some n⌝.
  Proof.
    rewrite /top_frag_q. iIntros "Ha Hf".
    by iDestruct (ghost_map_lookup with "Ha Hf") as %Hl.
  Qed.

  Lemma mkf_auth_nview Γ (q : Qp) (I : gmap Z fs_node) (dq : dfrac) (i : Z)
      (a : anode) :
    ghost_map_auth (γtop Γ) q I -∗ nview_dq Γ dq i a -∗
      ⌜abs_view I !! i = Some a⌝.
  Proof.
    rewrite /nview_dq. iIntros "Ha Hn". iDestruct "Hn" as (n) "[Hf %Han]".
    iDestruct (mkf_auth_frag with "Ha Hf") as %Hl.
    iPureIntro. exact (abs_view_lookup I i n a Hl Han).
  Qed.

  Lemma dlookup_commit_at_pinned Γ E (q : Qp) (dpin : Z) (a : anode)
      (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    nview Γ q dpin a -∗
    (∀ (av : aview) (d : Z) (nm : fname) (i : Z),
       ⌜d = dpin -> av !! dpin = Some a⌝ -∗ nview Γ q dpin a -∗
       Φ av d nm i) -∗
    dlookup_commit_at Γ E Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /dlookup_commit_at.
    iIntros (I d i nm ents nl) "%Hd %Hnm Ha".
    destruct (decide (d = dpin)) as [-> | Hne].
    - iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
      iModIntro. iFrame "Ha".
      iApply ("HΦ" $! (abs_view I) dpin nm i with "[%] Hn"). auto.
    - iModIntro. iFrame "Ha".
      iApply ("HΦ" $! (abs_view I) d nm i with "[%] Hn"). congruence.
  Qed.

  Lemma acre_commit_at_gen_pinned (γfs : fs_names) E (cf : Z -> Z -> absnode)
      (q : Qp) (jpin : Z) (a : anode) (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    nview (fs_gamma_L γfs) q jpin a -∗
    (∀ (av : aview) (d : Z) (nm : fname) (i : Z),
       ⌜av !! jpin = Some a⌝ -∗ nview (fs_gamma_L γfs) q jpin a -∗ Φ av d nm i) -∗
    acre_commit_at_gen (fs_gamma_L γfs) E cf Φ.
  Proof.
    iIntros (HE) "#Hai Hn HΦ". rewrite /acre_commit_at_gen.
    iIntros (I d i nm ents nl) "%Hpre Ha".
    iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
    iMod (app_step_acc E γfs d I _ HE
            (abs_view_lookup_is_Some I d _ (proj1 Hpre)) with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    iFrame "Ha'". iApply ("HΦ" $! (abs_view I) d nm i with "[%] Hn"). done.
  Qed.

  Lemma acre_commit_at_pinned (γfs : fs_names) E (c : absnode) (q : Qp) (jpin : Z)
      (a : anode) (Φ : aview -> Z -> fname -> Z -> iProp Σ) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    nview (fs_gamma_L γfs) q jpin a -∗
    (∀ (av : aview) (d : Z) (nm : fname) (i : Z),
       ⌜av !! jpin = Some a⌝ -∗ nview (fs_gamma_L γfs) q jpin a -∗ Φ av d nm i) -∗
    acre_commit_at (fs_gamma_L γfs) E c Φ.
  Proof.
    iIntros (HE) "#Hai Hn HΦ". rewrite /acre_commit_at.
    iApply (acre_commit_at_gen_pinned γfs E _ q jpin a Φ HE with "Hai Hn HΦ").
  Qed.

  Lemma aarm_commit_at_pinned (γfs : fs_names) E (c : absnode) (q : Qp) (jpin : Z)
      (a : anode) (Φ : aview -> Z -> iProp Σ) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    nview (fs_gamma_L γfs) q jpin a -∗
    (∀ (av : aview) (i : Z),
       ⌜av !! jpin = Some a⌝ -∗ nview (fs_gamma_L γfs) q jpin a -∗ Φ av i) -∗
    aarm_commit_at (fs_gamma_L γfs) E c Φ.
  Proof.
    iIntros (HE) "#Hai Hn HΦ". rewrite /aarm_commit_at.
    iIntros (I i) "%Hnone %Hsome Ha".
    iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
    iMod (app_step_acc E γfs i I _ HE Hsome with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    iFrame "Ha'". iApply ("HΦ" $! (abs_view I) i with "[%] Hn"). done.
  Qed.

  Lemma adots_commit_at_pinned (γfs : fs_names) E (q : Qp) (jpin : Z)
      (a : anode) (Φ : aview -> Z -> Z -> bool -> iProp Σ) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    nview (fs_gamma_L γfs) q jpin a -∗
    (∀ (av : aview) (i d : Z) (full : bool),
       ⌜av !! jpin = Some a⌝ -∗ nview (fs_gamma_L γfs) q jpin a -∗ Φ av i d full) -∗
    adots_commit_at (fs_gamma_L γfs) E Φ.
  Proof.
    iIntros (HE) "#Hai Hn HΦ". rewrite /adots_commit_at.
    iIntros (I i d full) "%Hrow Ha".
    iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
    iMod (app_step_acc E γfs i I _ HE
            (abs_view_lookup_is_Some I i _ Hrow) with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    iFrame "Ha'". iApply ("HΦ" $! (abs_view I) i d full with "[%] Hn"). done.
  Qed.

  Lemma aunarm_commit_at_pinned (γfs : fs_names) E (q : Qp) (jpin : Z)
      (a : anode) (Φ : aview -> Z -> iProp Σ) :
    ↑appN ⊆ E ->
    app_inv γfs -∗
    nview (fs_gamma_L γfs) q jpin a -∗
    (∀ (av : aview) (i : Z),
       ⌜av !! jpin = Some a⌝ -∗ nview (fs_gamma_L γfs) q jpin a -∗ Φ av i) -∗
    aunarm_commit_at (fs_gamma_L γfs) E Φ.
  Proof.
    iIntros (HE) "#Hai Hn HΦ". rewrite /aunarm_commit_at.
    iIntros (I i c) "%Hrow Ha".
    iDestruct (mkf_auth_nview with "Ha Hn") as %Hav.
    iMod (app_step_acc E γfs i I _ HE
            (abs_view_lookup_is_Some I i _ Hrow) with "Hai") as "Hstep".
    iModIntro. iFrame "Ha Hstep". iIntros (I') "%Heq Ha'". iModIntro.
    iFrame "Ha'". iApply ("HΦ" $! (abs_view I) i with "[%] Hn"). done.
  Qed.

  (* =================================================================== *)
  (*  2.  THE TWO-PHASE RETAG ENGINES: [ftopN] opened, the caller's two   *)
  (*      phases on either side of the [ghost_map_update]                 *)
  (* =================================================================== *)

  (* UNDER THE ARMED REGISTRY ([InodeRegion.ireg_top_retag_armed_gen]'s
     critical section with [FsAbsMknodFire.mkf_acre_fire]'s two phases
     inside): the receipt names this inum, so the row says nothing about
     it and the new node may be anything -- a directory with a count and
     no dots included.  The caller's step is delivered at the RAW insert
     (the specific fires below rewrite it from the delta), and the phase-2
     fupd runs at the post map before the body closes. *)
  Lemma caf_armed_retag (γfs : fs_names) (E : coPset) (k t : nat) (q : Qp)
      (S : gset Z) (i : Z) (n n' : fs_node) (R : iProp Σ) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    i ∈ S ->
    ftop_inv γfs -∗ app_inv γfs -∗ ireg_armed k t q S -∗
    (∀ I : gmap Z fs_node, ⌜I !! i = Some n⌝ -∗
       ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
       ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗
       app_step i I (abs_view (<[i := n']> I)) ∗
       (ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) (<[i := n']> I) ={appE}=∗
        ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) (<[i := n']> I) ∗ R)) -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗
      ireg_armed k t q S ∗ top_frag (fs_gamma_L γfs) i n' ∗ R.
  Proof.
    iIntros (HE Hin) "#Hi #Hai Hrec Hcm Hf". rewrite /ireg_armed.
    (* [γtop (fs_gamma_L γfs)] IS [fs_top γfs] ([FsAbs.ftop_gamma_top], by
       reflexivity), spelled the body's way before the invariant is opened
       -- exactly what [InodeRegion.ireg_top_retag_*] does *)
    rewrite /top_frag /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hla Hrec") as %HAt.
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I with "[//] Hta") as "(Hta & Hstep & Hph2)".
    (* THE MOVE, at the whole authority ([AppInv.app_top_update]) *)
    iMod (app_top_update appE γfs I i n n' ltac:(rewrite /appE; done)
            with "Hai [Hstep] Hta Hf") as "[Hta Hf]".
    { iIntros (_) "_ Hp". iApply (app_step_at i I _ n' eq_refl with "Hstep Hp"). }
    iMod ("Hph2" with "Hta") as "[Hta HR]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[i := n']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros j m Hj Hun. destruct (decide (j = i)) as [-> | Hne].
      - (* this inum IS armed, so the row's own hypothesis is refuted *)
        exfalso. exact (Hun k t q S HAt Hin).
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl j m Hj Hun). }
    iModIntro. iFrame "Hrec Hf HR".
  Qed.

  (* ...and the PLAIN one ([ireg_top_retag_gen]'s section): the new node
     owes the row *)
  Lemma caf_retag (γfs : fs_names) (E : coPset) (i : Z) (n n' : fs_node)
      (R : iProp Σ) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local i n' ->
    ftop_inv γfs -∗ app_inv γfs -∗
    (∀ I : gmap Z fs_node, ⌜I !! i = Some n⌝ -∗
       ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ={appE}=∗
       ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗
       app_step i I (abs_view (<[i := n']> I)) ∗
       (ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) (<[i := n']> I) ={appE}=∗
        ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) (<[i := n']> I) ∗ R)) -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗ top_frag (fs_gamma_L γfs) i n' ∗ R.
  Proof.
    iIntros (HE Hloc) "#Hi #Hai Hcm Hf".
    rewrite /top_frag /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I with "[//] Hta") as "(Hta & Hstep & Hph2)".
    iMod (app_top_update appE γfs I i n n' ltac:(rewrite /appE; done)
            with "Hai [Hstep] Hta Hf") as "[Hta Hf]".
    { iIntros (_) "_ Hp". iApply (app_step_at i I _ n' eq_refl with "Hstep Hp"). }
    iMod ("Hph2" with "Hta") as "[Hta HR]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[i := n']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros j m Hj Hun. destruct (decide (j = i)) as [-> | Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl j m Hj Hun). }
    iModIntro. iFrame "Hf HR".
  Qed.

  (* =================================================================== *)
  (*  3.  THE FIRES, ONE PER LEG                                          *)
  (* =================================================================== *)

  (* THE ARM (sites #8/#18/#23): the claim box ([abs_of n = None] --
     [FsAbsDefs.abs_of_bare]) becomes the row [(c, 1)]; under the registry,
     because a directory child is half-built from here to its dots. *)
  Lemma caf_arm_fire (γfs : fs_names) (E : coPset) (k t : nat) (q : Qp)
      (S : gset Z) (i : Z) (c : absnode) (Φ : aview -> Z -> iProp Σ)
      (n n' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    i ∈ S ->
    abs_of n = None ->
    abs_of n' = Some (MkAnode c 1%nat) ->
    ftop_inv γfs -∗ app_inv γfs -∗ ireg_armed k t q S -∗
    aarm_commit_at (fs_gamma_L γfs) appE c Φ -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗
      ireg_armed k t q S ∗ top_frag (fs_gamma_L γfs) i n' ∗ cre_arm_fired Φ i.
  Proof.
    iIntros (HE Hin Hnone Hrow) "#Hi #Hai Hrec Hcm Hf".
    iApply (caf_armed_retag γfs E k t q S i n n' _ HE Hin
              with "Hi Hai Hrec [Hcm] Hf").
    iIntros (I Hlk) "Hta".
    assert (Hav : abs_view I !! i = None)
      by (rewrite (abs_view_lookup_of I i n Hlk); exact Hnone).
    assert (Hsome : is_Some (I !! i)) by (by eexists).
    assert (Hdelta : abs_view (<[i := n']> I) = delta_arm i c (abs_view I))
      by exact (abs_view_insert I i n' _ Hrow).
    iMod ("Hcm" $! I i with "[//] [//] Hta") as "(Hta & Hstep & Hph2)".
    iModIntro. iEval (rewrite -Hdelta) in "Hstep". iFrame "Hta Hstep".
    iIntros "Hta".
    iMod ("Hph2" $! (<[i := n']> I) with "[//] Hta") as "[Hta HΦ]".
    iModIntro. iFrame "Hta". rewrite /cre_arm_fired.
    iExists (abs_view I). iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* THE DOTS (sites #13, #9, #10): the empty directory at count 1 gains
     its dots -- both, or the first alone -- still under the registry
     (the success arm's [cr_dirty_clear] disarms right after) *)
  Lemma caf_dots_fire (γfs : fs_names) (E : coPset) (k t : nat) (q : Qp)
      (S : gset Z) (i d : Z) (full : bool)
      (Φ : aview -> Z -> Z -> bool -> iProp Σ) (n n' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    i ∈ S ->
    abs_of n = Some (MkAnode (ADir ∅) 1%nat) ->
    abs_of n' = Some (MkAnode (ADir (dots_ents full i d)) 1%nat) ->
    ftop_inv γfs -∗ app_inv γfs -∗ ireg_armed k t q S -∗
    adots_commit_at (fs_gamma_L γfs) appE Φ -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗
      ireg_armed k t q S ∗ top_frag (fs_gamma_L γfs) i n' ∗ cre_dots_fired Φ i d full.
  Proof.
    iIntros (HE Hin Hrow Hrow') "#Hi #Hai Hrec Hcm Hf".
    iApply (caf_armed_retag γfs E k t q S i n n' _ HE Hin
              with "Hi Hai Hrec [Hcm] Hf").
    iIntros (I Hlk) "Hta".
    assert (Hav : abs_view I !! i = Some (MkAnode (ADir ∅) 1%nat))
      by (rewrite (abs_view_lookup_of I i n Hlk); exact Hrow).
    assert (Hdelta : abs_view (<[i := n']> I) = dots_delta full i d (abs_view I)).
    { rewrite (abs_view_insert I i n' _ Hrow').
      by rewrite (dots_delta_fresh (abs_view I) i d full Hav). }
    iMod ("Hcm" $! I i d full with "[//] Hta") as "(Hta & Hstep & Hph2)".
    iModIntro. iEval (rewrite -Hdelta) in "Hstep". iFrame "Hta Hstep".
    iIntros "Hta".
    iMod ("Hph2" $! (<[i := n']> I) with "[//] Hta") as "[Hta HΦ]".
    iModIntro. iFrame "Hta". rewrite /cre_dots_fired.
    iExists (abs_view I). iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* THE UNARM under the registry (site #13b, mkdir's fail tail): the
     dotless or half-dotted directory at count 1 DISAPPEARS *)
  Lemma caf_unarm_fire_armed (γfs : fs_names) (E : coPset) (k t : nat) (q : Qp)
      (S : gset Z) (i : Z) (c : absnode) (Φ : aview -> Z -> iProp Σ)
      (n n' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    i ∈ S ->
    abs_of n = Some (MkAnode c 1%nat) ->
    abs_of n' = None ->
    ftop_inv γfs -∗ app_inv γfs -∗ ireg_armed k t q S -∗
    aunarm_commit_at (fs_gamma_L γfs) appE Φ -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗
      ireg_armed k t q S ∗ top_frag (fs_gamma_L γfs) i n' ∗ cre_unarm_fired Φ i.
  Proof.
    iIntros (HE Hin Hrow Hnone) "#Hi #Hai Hrec Hcm Hf".
    iApply (caf_armed_retag γfs E k t q S i n n' _ HE Hin
              with "Hi Hai Hrec [Hcm] Hf").
    iIntros (I Hlk) "Hta".
    assert (Hav : abs_view I !! i = Some (MkAnode c 1%nat))
      by (rewrite (abs_view_lookup_of I i n Hlk); exact Hrow).
    assert (Hdelta : abs_view (<[i := n']> I) = delta_unarm i (abs_view I))
      by exact (abs_view_insert_None I i n' Hnone).
    iMod ("Hcm" $! I i c with "[//] Hta") as "(Hta & Hstep & Hph2)".
    iModIntro. iEval (rewrite -Hdelta) in "Hstep". iFrame "Hta Hstep".
    iIntros "Hta".
    iMod ("Hph2" $! (<[i := n']> I) with "[//] Hta") as "[Hta HΦ]".
    iModIntro. iFrame "Hta". rewrite /cre_unarm_fired.
    iExists (abs_view I), c. iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* ...and at a PLAIN fragment (sites #16/#21/#26, the non-directory
     child's fail arm: the row was never suspended) -- the zeroed record
     owes [inode_local], which the site's re-pack proves anyway *)
  Lemma caf_unarm_fire (γfs : fs_names) (E : coPset) (i : Z) (c : absnode)
      (Φ : aview -> Z -> iProp Σ) (n n' : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local i n' ->
    abs_of n = Some (MkAnode c 1%nat) ->
    abs_of n' = None ->
    ftop_inv γfs -∗ app_inv γfs -∗
    aunarm_commit_at (fs_gamma_L γfs) appE Φ -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗
      top_frag (fs_gamma_L γfs) i n' ∗ cre_unarm_fired Φ i.
  Proof.
    iIntros (HE Hloc Hrow Hnone) "#Hi #Hai Hcm Hf".
    iApply (caf_retag γfs E i n n' _ HE Hloc with "Hi Hai [Hcm] Hf").
    iIntros (I Hlk) "Hta".
    assert (Hav : abs_view I !! i = Some (MkAnode c 1%nat))
      by (rewrite (abs_view_lookup_of I i n Hlk); exact Hrow).
    assert (Hdelta : abs_view (<[i := n']> I) = delta_unarm i (abs_view I))
      by exact (abs_view_insert_None I i n' Hnone).
    iMod ("Hcm" $! I i c with "[//] Hta") as "(Hta & Hstep & Hph2)".
    iModIntro. iEval (rewrite -Hdelta) in "Hstep". iFrame "Hta Hstep".
    iIntros "Hta".
    iMod ("Hph2" $! (<[i := n']> I) with "[//] Hta") as "[Hta HΦ]".
    iModIntro. iFrame "Hta". rewrite /cre_unarm_fired.
    iExists (abs_view I), c. iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

End CreateFire.
