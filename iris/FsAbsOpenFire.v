(* FsAbsOpenFire.v -- sys_open's TWO FIRE POINTS, DISCHARGED AGAINST THE
   INVARIANT, plus the row readings and the walk-premise bridge
   [SpecSysOpenAU]'s header owes its prover (items 1, 2 and 3).

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the open AU
   prover).  A NEW LEAF rather than an append to [FsAbsMknodFire.v], for the
   mirror's reason the campaign's other leaves record ([FsAbsNpar],
   [FsAbsPins], [FsAbsStart]): the build mirror forbids touching a tracked
   file.  Fuse the era leaves when one of them is next edited.

   ==== ITEM 1: THE WALK PREMISE, RECONCILED ============================

   [SpecSysOpenAU] was authored the same day the relative start landed, so
   its [open_walk_pre_era] is the ONE-SHOT OVER ALL PATHS
   ([FsAbsEraMknod.mknod_walk_pre_era]'s shape at the FULL element list)
   while the era contracts now take [FsAbsStart.ex_start] -- the same shot
   at a FIXED [pl].  The reconciliation is therefore the namei-side twin of
   [FsAbsNparMknod.np_start_of_mknod] and nothing in the contract moves:
   [opf_start_of_open] specialises the one-shot to the string the walk
   fetched, and the two [ROOTINO]s agree by computation
   ([FsAbsNparMknod.np_rootino_agree], reused rather than restated).

   ROUTE TAKEN, AND WHY.  The alternative offered was to restate
   [open_walk_pre_era] AT [ex_start] in place (statement and seal moving
   together, as the ret-0 escape retirement did).  A discharge lemma is
   cleaner HERE because the two shapes are not the same predicate: the
   contract's one-shot is universally quantified over [pl] -- it is handed
   down BEFORE argstr has fetched anything -- while [ex_start] is at the
   string already in the buffer.  A syscall-level caller cannot name that
   string, so the contract has to quantify; the walk is where the two meet.
   ([SpecSysMknodAUEra] carries the same asymmetry for the same reason.)

   ==== ITEM 2: THE TERMINAL FIRE =======================================

   [opf_open_fire] is [FsAbsMknodFire.mkf_dlookup_fire]'s single-phase
   read-only mold with the row read WHOLE ([abs_of n], not just its entry
   map): open observes the node it is about to hand a descriptor to, and
   the arms are keyed by that whole [anode].  The resource it reads off is
   the FIRING FUNCTION'S OWN era fragment -- sys_open holds
   [IcacheEscrow.ic_loaded]'s [top_frag] for the opened inode from its
   [ilock] to its [iunlock], so no walk lend is involved at this instant
   and the fragment goes straight back.

   ==== ITEM 3: THE TRUNC FIRE ==========================================

   [opf_atrunc_fire] is [mkf_acre_fire]'s two-phase mold at
   [SpecSysOpenAU.delta_trunc], FUSED WITH THE ROW RETAG -- it replaces the
   [InodeRegion.ireg_top_retag] sys_open performs after [itrunc] returns
   (the O_TRUNC bridge), with one extra premise (the caller's commit) and
   one extra payout (the receipt).  Same premise as the retag it replaces
   ([inode_local] at the truncated record), same payout (the moved
   fragment), plus the caller's two phases on either side of the
   [ghost_map_update] INSIDE the one [ftopN] critical section.

   THE READING BRIDGE is [opf_trunc_row]: the truncated record reads
   [AFile []] because [SpecItrunc.di_trunc] zeroes [di_size] and
   [fn_file_bytes] is [file_bytes _ 0 = []], while the TYPE and the COUNT
   ride untouched -- which is what makes the delta collapse to the one-row
   insert and what makes the receipt's nlink the OBSERVED one.

   THE OBSERVED-ROW TIE ([SpecSysOpenAU]'s header, THE ONE DELTA; owner
   question 2) IS PAID BY THE FRAGMENT, not by a custody argument in prose:
   both fires read the row off the SAME [top_frag], and sys_open holds it
   whole across the window (ilock ... filealloc/fdalloc ... itrunc), so the
   pre-row phase 1 sees IS the row the terminal observation saw.  The
   caller's [Φt] receipt is delivered at that state.

   BINDERS: [FsAbsMknodFire]'s section list VERBATIM (which is
   [SpecSysMknodAU]'s) -- [fileG] is bound and [icacheG]/[icfg] resolve only
   through its fields. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import DinodeEnc.
Require Import DirView.          (* [T_DIR_z]                               *)
Require Import FsBlocks.         (* [fs_names]                              *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                            *)
Require Import BlkmapDefs.
Require Import IrefSlots.
Require Import Xv6Cameras.
(* the three binder classes the section list names, IMPORTED rather than
   inherited ([FsAbsMknodFire]'s header records why). *)
Require Import FdSlots.          (* [fdslotG]                               *)
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]   *)
Require Import ProcAvail.        (* [pavG]                                  *)
Require Import FsStateEra.       (* [era_node], [era_node_rec]              *)
Require Import InodeRegion.      (* [ftop_inv]/[ftop_body]/[ftop_clean]     *)
Require Import Xv6G.
Require Import SpecItrunc.       (* [di_trunc]                              *)
Require Import SpecSysMknodAU.   (* [abs_view_insert]                       *)
Require Import SpecSysOpenAU.    (* the contract this file serves           *)
Require Import FsAbsEra.       (* [ex_start]                              *)
Require Import FsAbsMknodFire.   (* [mkf_abs_of_dir], [mkf_era_is_dir]      *)
Require FsImg.                   (* [T_FILE_z], [ROOTINO] -- Require, NOT
                                    Import (SpecSysOpenAU's reason)         *)
Require Import FsAbsInv.        (* [fsabsN]/[fsabsE]: the commit mask *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)                 *)
Require TsoCtx.   (* qualified: the class only, no notation flip *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE ROW READINGS OF AN ERA NODE (pure, no binder)                 *)
(* ===================================================================== *)

Lemma opf_era_type `{XI : TsoCtx.CurCtx} (dn : dinode) (bm : blkmap) (data : nat -> list (bv 8)) :
  fn_type (era_node dn bm data) = bv_unsigned (di_type dn).
Proof. by rewrite /fn_type era_node_rec. Qed.

Lemma opf_era_not_dir `{XI : TsoCtx.CurCtx} (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> T_DIR_z ->
  fn_is_dir (era_node dn bm data) = false.
Proof.
  intros H. rewrite /fn_is_dir opf_era_type.
  by apply bool_decide_eq_false_2.
Qed.

(* THE FILE ROW: the abstract node is the record's bytes at its own count. *)
Lemma opf_era_file_row `{XI : TsoCtx.CurCtx} (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) = FsImg.T_FILE_z ->
  abs_of (era_node dn bm data)
  = MkAnode (AFile (fn_file_bytes (era_node dn bm data)))
            (fn_nlink (era_node dn bm data)).
Proof.
  intros Hty.
  assert (Hnd : fn_is_dir (era_node dn bm data) = false).
  { apply opf_era_not_dir. rewrite Hty /T_DIR_z /FsImg.T_FILE_z.
    discriminate. }
  rewrite /abs_of /abs_node Hnd.
  destruct (decide (fn_type (era_node dn bm data) = FsImg.T_FILE_z))
    as [_ | Hno]; [reflexivity |].
  exfalso. apply Hno. rewrite opf_era_type. exact Hty.
Qed.

(* THE DEVICE ROW: the major/minor pair straight off the record. *)
Lemma opf_era_dev_row `{XI : TsoCtx.CurCtx} (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) <> T_DIR_z ->
  bv_unsigned (di_type dn) <> FsImg.T_FILE_z ->
  abs_of (era_node dn bm data)
  = MkAnode (ADev (bv_unsigned (di_major dn)) (bv_unsigned (di_minor dn)))
            (fn_nlink (era_node dn bm data)).
Proof.
  intros Hnd Hnf.
  rewrite /abs_of /abs_node (opf_era_not_dir dn bm data Hnd).
  destruct (decide (fn_type (era_node dn bm data) = FsImg.T_FILE_z))
    as [Hyes | _].
  - exfalso. apply Hnf. rewrite -(opf_era_type dn bm data). exact Hyes.
  - by rewrite /fn_major /fn_minor era_node_rec.
Qed.

(* THE DIRECTORY ROW, for symmetry: [FsAbsMknodFire]'s two facts joined. *)
Lemma opf_era_dir_row `{XI : TsoCtx.CurCtx} (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) = T_DIR_z ->
  abs_of (era_node dn bm data)
  = MkAnode (ADir (dir_entries (era_node dn bm data)))
            (fn_nlink (era_node dn bm data)).
Proof.
  intros Hty. exact (mkf_abs_of_dir _ (mkf_era_is_dir dn bm data Hty)).
Qed.

(* ---- THE TRUNC READING BRIDGE (item 3) ------------------------------ *)

(* [di_trunc] zeroes the size, so the truncated record's bytes are the
   empty list; the type and the count are untouched, so the row stays a
   FILE at the OBSERVED nlink. *)
Lemma opf_trunc_size `{XI : TsoCtx.CurCtx} (dn : dinode) (bm' : blkmap)
    (data' : nat -> list (bv 8)) :
  fn_size (era_node (di_trunc dn) bm' data') = 0.
Proof.
  rewrite /fn_size era_node_rec /di_trunc /=. apply bv_0_unsigned.
Qed.

Lemma opf_trunc_bytes `{XI : TsoCtx.CurCtx} (dn : dinode) (bm' : blkmap)
    (data' : nat -> list (bv 8)) :
  fn_file_bytes (era_node (di_trunc dn) bm' data') = [].
Proof.
  rewrite /fn_file_bytes (opf_trunc_size dn bm' data') /=.
  reflexivity.
Qed.

Lemma opf_trunc_nlink `{XI : TsoCtx.CurCtx} (dn : dinode) (bm bm' : blkmap)
    (data data' : nat -> list (bv 8)) :
  fn_nlink (era_node (di_trunc dn) bm' data')
  = fn_nlink (era_node dn bm data).
Proof. by rewrite /fn_nlink !era_node_rec. Qed.

Lemma opf_trunc_row `{XI : TsoCtx.CurCtx} (dn : dinode) (bm bm' : blkmap)
    (data data' : nat -> list (bv 8)) :
  bv_unsigned (di_type dn) = FsImg.T_FILE_z ->
  abs_of (era_node (di_trunc dn) bm' data')
  = MkAnode (AFile []) (fn_nlink (era_node dn bm data)).
Proof.
  intros Hty.
  assert (Htyt : bv_unsigned (di_type (di_trunc dn)) = FsImg.T_FILE_z)
    by exact Hty.
  rewrite (opf_era_file_row (di_trunc dn) bm' data' Htyt).
  by rewrite (opf_trunc_bytes dn bm' data')
             (opf_trunc_nlink dn bm bm' data data').
Qed.

Section OpenFire.
  (* [FsAbsMknodFire]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  ITEM 1: THE WALK PREMISE                                        *)
  (* =================================================================== *)

  (* The contract's one-shot, specialised to the string the walk fetched:
     [FsAbsStart.ex_start] at that [pl] IS [open_walk_pre_era] there (same
     quantifier over the start, same tie, same family over
     [path_elems pl]), so this is a rename plus the two ROOTINOs agreeing.
     The namei-side twin of [FsAbsNparMknod.np_start_of_mknod]. *)
  Lemma opf_start_of_open `{XI : TsoCtx.CurCtx} (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    open_walk_pre_era γfs P Pmiss -∗ ex_start γfs P Pmiss pl.
  Proof.
    iIntros "Hpre". rewrite /ex_start. iIntros (r Hr).
    rewrite /open_walk_pre_era.
    iMod ("Hpre" $! pl r with "[%]") as "[$ $]"; [| done].
    intros Hsl. rewrite -np_rootino_agree. exact (Hr Hsl).
  Qed.

  (* =================================================================== *)
  (*  2.  ITEM 2: THE TERMINAL FIRE                                       *)
  (* =================================================================== *)

  (* [mkf_dlookup_fire]'s mold, at the WHOLE row.  Any share suffices: the
     commit only reads. *)
  Lemma opf_open_fire `{XI : TsoCtx.CurCtx} (γfs : fs_names) (E : coPset) (dq : dfrac)
      (Φ : aview -> Z -> anode -> iProp Σ) (i : Z) (n : fs_node) :
    ↑ftopN ∪ ↑fsabsN ⊆ E ->
    ftop_inv γfs -∗
    aopen_commit_at (fs_gamma_L γfs) fsabsE Φ -∗
    top_frag_q (fs_gamma_L γfs) dq i n ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq i n
      ∗ ∃ av : aview,
          ⌜av !! i = Some (abs_of n)⌝ ∗ Φ av i (abs_of n).
  Proof.
    intros HE. iIntros "#Hi Hcm Hf".
    (* the same re-spelling [mkf_dlookup_fire] does, and for the same
       reason: the unifier cannot solve [γtop ?Γ =?= fs_top γfs]. *)
    rewrite /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : abs_view I !! i = Some (abs_of n))
      by exact (abs_view_lookup I i n Hlk).
    iMod (fupd_mask_subseteq fsabsE) as "Hcl2"; [rewrite /fsabsE; solve_ndisj |].
    iMod ("Hcm" $! I i (abs_of n) with "[//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, A. by iFrame. }
    iModIntro. iFrame "Hf". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* the [DfracOwn 1] reading, which is the spelling sys_open holds
     ([top_frag] whole, from its [ilock] to its [iunlock]) *)
  Lemma opf_open_fire_1 `{XI : TsoCtx.CurCtx} (γfs : fs_names) (E : coPset)
      (Φ : aview -> Z -> anode -> iProp Σ) (i : Z) (n : fs_node) :
    ↑ftopN ∪ ↑fsabsN ⊆ E ->
    ftop_inv γfs -∗
    aopen_commit_at (fs_gamma_L γfs) fsabsE Φ -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗
      top_frag (fs_gamma_L γfs) i n
      ∗ ∃ av : aview,
          ⌜av !! i = Some (abs_of n)⌝ ∗ Φ av i (abs_of n).
  Proof.
    intros HE. rewrite top_frag_1. exact (opf_open_fire γfs E _ Φ i n HE).
  Qed.

  (* =================================================================== *)
  (*  3.  ITEM 3: THE TRUNC FIRE, FUSED WITH THE ROW RETAG                *)
  (* =================================================================== *)

  (* [mkf_acre_fire]'s mold at [delta_trunc].  Replaces the
     [InodeRegion.ireg_top_retag] sys_open calls after [itrunc] returns:
     same [inode_local] premise, same payout, plus the caller's two phases
     inside the one [ftopN] critical section.  The receipt's pre-state row
     is the OBSERVED one -- the fragment is the same one the terminal
     observation read. *)
  Lemma opf_atrunc_fire `{XI : TsoCtx.CurCtx} (γfs : fs_names) (E : coPset)
      (Φ : aview -> Z -> list (bv 8) -> iProp Σ)
      (i : Z) (bs0 : list (bv 8)) (nl : nat) (n n' : fs_node) :
    ↑ftopN ∪ ↑fsabsN ⊆ E ->
    inode_local i n' ->
    abs_of n = MkAnode (AFile bs0) nl ->
    abs_of n' = MkAnode (AFile []) nl ->
    ftop_inv γfs -∗
    atrunc_commit_at (fs_gamma_L γfs) fsabsE Φ -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗
      top_frag (fs_gamma_L γfs) i n'
      ∗ ∃ av : aview,
          ⌜av !! i = Some (MkAnode (AFile bs0) nl)⌝ ∗ Φ av i bs0.
  Proof.
    intros HE Hloc Habs Habs'. iIntros "#Hi Hcm Hf".
    rewrite /top_frag /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : abs_view I !! i = Some (MkAnode (AFile bs0) nl)).
    { by rewrite (abs_view_lookup I i n Hlk) Habs. }
    (* the delta collapses to the ONE-ROW insert, and the insert's reading
       is the truncated record's own row *)
    assert (Hdelta : abs_view (<[i := n']> I) = delta_trunc i (abs_view I)).
    { rewrite (abs_view_insert I i n') Habs'.
      by rewrite (delta_trunc_file (abs_view I) i bs0 nl Hrow). }
    iMod (fupd_mask_subseteq fsabsE) as "Hcl2"; [rewrite /fsabsE; solve_ndisj |].
    iMod ("Hcm" $! I i bs0 nl with "[//] Hta") as "[Hta Hph2]".
    iMod (ghost_map_update n' with "Hta Hf") as "[Hta Hf]".
    iMod ("Hph2" $! (<[i := n']> I) with "[//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[i := n']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros j mm Hj Hun. destruct (decide (j = i)) as [-> | Hne].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne)].
        exact (Hcl j mm Hj Hun). }
    iModIntro. iFrame "Hf". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

End OpenFire.
