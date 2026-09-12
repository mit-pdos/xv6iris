(* FsAbsMknodFire.v -- THE mknod/create AU's FIRE POINTS, DISCHARGED
   AGAINST THE INVARIANT, plus the two bridges the contract's prover needs:
   the reading bridge at the parent-row update and the halfword tie on the
   device numbers.

   ==== WHY THE COMMITS ARE SHAPED AT THE AUTHORITY ======================

   A commit stated over [FsAbs.astate],

       astate Γ av ={E}=∗ astate Γ av ∗ Φ ...                (dlookup)
       astate Γ av ={E}=∗ astate Γ av ∗ (astate Γ (δ av) ={E}=∗ ...)  (acre)

   is NOT dischargeable, and the obstruction is a shape finding rather
   than a proof gap.  The prover's only source of [astate] is the γtop
   authority inside [InodeRegion.ftop_inv].  Borrowing it
   ([FsAbs.ftop_astate_ro] / [ftop_astate_acc]) is fine; GIVING IT BACK is
   not.  [astate Γ av] is [∃ I, ghost_map_auth (γtop Γ) 1 I ∗
   ⌜av = abs_view I⌝], and [abs_view] IS NOT INJECTIVE ([abs_of] forgets
   the record: the block map, the size's slack, every field [inode_local]
   constrains).  So what comes back out of a caller's fupd is an authority
   at SOME map with the right reading -- and [ftop_body]'s row
   ([ftop_clean I A]) is a statement about the RECORDS.  Neither give-back
   wand can be paid:

     - [ftop_astate_ro]'s wants the SAME [I] the borrow named, and nothing
       in [astate Γ av] says the returned map is that one;
     - [ftop_astate_acc]'s wants [inode_local] at EVERY entry of whatever
       map comes back, which is exactly the fact [abs_view] threw away.

   So the commits ([FsAbsCreateFire], re-exported below) take the RAW MAP
   and hand the very same [ghost_map_auth] back.  Everything a client
   wants of them is offered at that shape: the trivial-receipt units, and
   the agreement seeds ([_pinned]) the stable corollaries are derived from.

   ==== WHAT THE TWO FIRE LEMMAS DO ====================================

   [mkf_dlookup_fire] and [caf_acre_fire] are the two fire points as ONE
   step each, [ftopN] opened and closed inside.  The resource they read
   the row off is NOT a walk's lend but the FIRING FUNCTION'S OWN era
   fragment -- create holds [FsState.top_frag] for the parent inside
   [IcacheEscrow.ic_loaded] across both its dirlookup and its dirlink, so
   no seam is needed at these two instants at all (that is why they are
   dischargeable while [FsAbsEraMknod]'s hop-side twins needed the era
   walk).  [caf_acre_fire] (section 5) FUSES the parent-row retag: the two
   phases and the [ghost_map_update] are one [ftopN] critical section, so
   the pair is ONE instant to every other party, and it pays the row
   obligation [InodeRegion.ireg_top_retag_*] charges every mover -- so a
   walk at the parent calls THIS instead of [ireg_top_retag_*], with one
   extra premise (the caller's commit) and one extra payout (the receipt).

   ==== THE TWO BRIDGES =================================================

   [mkf_parent_row] is the reading bridge (item 2): the written parent
   record's abstract row.  Its real half -- [dir_entries] of the appended
   record is [<[nm := i]>] of the old one -- is ALREADY LANDED as
   [FsStateEra.dir_entries_dirlink_ins], so this lemma takes that equation
   as a premise and does the [abs_of] arithmetic around it.
   [mkf_child_dev] is item 4's abstract half ([FsAbsCreateFire.create_made]
   read through [abs_of]) and [mkf_low16_mod] / [mkf_dev_arg] are its
   bit-level half: the low halfword of the [argint]'d word, read unsigned,
   IS [SysMknodDefs.dev_arg].

   BINDERS: [SysMknodDefs]'s section list VERBATIM -- [fileG] is bound
   and [icacheG]/[icfg] resolve only through its fields (SpecCreate's
   header: a standalone [icfg] beside [fileG] gives two instance paths and
   the propositions print identically while failing to unify). *)


(* ==== WHAT IS IN THIS FILE (the mknod/create leaves, fused 2026-08-30) ==

   ONE FILE FOR THE mknod/create AU's ABSTRACT-STATE WORK.  Four leaves were
   one lane's, split only by the build mirror's rule that a tracked file is
   not touched -- and three of the four headers below say, in as many
   words, to fuse them the next time one of them is edited.  This is that
   edit.  Every statement and proof is the original text, in its original
   section at its original binder list (and all four sections take the SAME
   binder list, which is what made them one file's worth of work):

     sections 1-4  the authority-shaped commits, the two fires and the
                   halfword bridge -- this file's own.
     section 5     the era-lend walk predicates -- WAS
                   iris/FsAbsEraMknod.v.
     section 6     the nameiparent acceptance test -- WAS
                   iris/FsAbsNparMknod.v.
     section 7     FIRE 2 at a non-directory child -- WAS
                   iris/FsAbsCreateFire.v.

   NOT FUSED, AND IT IS NOT A JUDGEMENT CALL: the other fire leaves
   ([FsAbsOpenFire], [FsAbsWriteFire], [FsAbsUnlinkFire], [FsAbsReadFire])
   each stand on a DIFFERENT [Spec*AU] contract, and three of those
   contracts require THIS file -- so merging any of them here is a
   dependency CYCLE, not a tidy-up.  One fire leaf per syscall is the
   shape the cone forces.

   All three old names survive as stubs that [Require Export] this file, so
   no consumer moved. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.  (* [nth_byte], [assemble_bytes]            *)
Require Import RiscvExtras.      (* [trunc32]                               *)
Require Import VcGen.            (* [trunc32_unsigned]                      *)
Require Import RiscvPtsto.
Require Import DinodeEnc.
Require Import DirView.          (* [T_DIR_z]                               *)
Require Import FsTree.           (* [fname]                                 *)
Require Import FsBlocks.         (* [fs_names]                              *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                            *)
Require Import InodeInv.
Require Import IrefSlots.
Require Import Xv6Cameras.
(* the three binder classes [SysMknodDefs]'s section list names, IMPORTED
   rather than inherited: [Require Import] does not re-import a required
   file's own imports, and an unbound [fileG] in a [`{! ...}] binder is
   silently generalised into a [gFunctors -> Type] VARIABLE -- at which
   point [icfg] has no field to resolve through. *)
Require Import FdSlots.          (* [fdslotG]                               *)
Require Import FileInvDefs.      (* [fileG]: carries [icacheG] and [icfg]   *)
Require Import ProcAvail.        (* [pavG]                                  *)
Require Import FsStateEra.       (* [era_node], [era_node_rec]              *)
Require Import InodeRegion.      (* [ftop_inv]/[ftop_body]/[ftop_clean]     *)
Require Import Xv6G.
Require Import SysMknodDefs.   (* [dev_arg], [npar_elems]         *)
Require Export FsAbsCreateFire.  (* the commits ([acre_commit_at], [dlookup_commit_at], the legs' -- moved there in round E2 so SpecCreate can name them), their units and seeds, [mkf_auth_nview] *)
Require Import AppInv.          (* [appN]/[appE]: the application's namespace, the commit mask (app-instances.md round A) *)
Require Import PieceFam.        (* [pfam]: a one-shot piece's receipt beside its refund *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)                 *)

Local Open Scope Z_scope.

Section MknodFire.
  (* [SysMknodDefs]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  1.  THE AUTHORITY-SHAPED COMMITS -- moved to FsAbsCreateFire.v      *)
  (*      (round E2, lane E2-C: [SpecCreate]'s bundle names them and this *)
  (*      file sits above SpecCreate).  Re-exported above, so every name  *)
  (*      resolves as before.                                             *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  2.  THE ROW READINGS                                                *)
  (* =================================================================== *)

  (* a LIVE directory's row (E2-V2 added the count: the parent every
     create/link/unlink fire reads has passed a [dp->nlink == 0] guard or
     holds a live entry -- [DirView.dir_orphan_clean]) *)
  Lemma mkf_abs_of_dir (n : fs_node) :
    fn_is_dir n = true -> fn_nlink n <> 0%nat ->
    abs_of n = Some (MkAnode (ADir (dir_entries n)) (fn_nlink n)).
  Proof. apply abs_of_dir. Qed.

  Lemma mkf_era_is_dir (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    fn_is_dir (era_node dn bm data) = true.
  Proof.
    intros Hty. rewrite /fn_is_dir /fn_type era_node_rec.
    by apply bool_decide_eq_true_2.
  Qed.

  Lemma mkf_era_nlink (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    fn_nlink (era_node dn bm data) = Z.to_nat (bv_unsigned (di_nlink dn)).
  Proof. by rewrite /fn_nlink era_node_rec. Qed.

  (* ...and a nonzero record count is a nonzero [fn_nlink] (E2-V2) *)
  Lemma mkf_era_live (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    bv_unsigned (di_nlink dn) <> 0 -> fn_nlink (era_node dn bm data) <> 0%nat.
  Proof.
    intros Hnz. rewrite mkf_era_nlink.
    pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dn))). lia.
  Qed.

  (* ---- ITEM 2: THE READING BRIDGE AT THE WRITE ---------------------- *)

  (* The real half is [FsStateEra.dir_entries_dirlink_ins] (LANDED): the
     appended record's entry map IS [<[s := v]>] of the old one, by
     [dir_view]'s first-match reading over the written slot.  This lemma
     is the [abs_of] arithmetic around it: dirlink keeps the TYPE (so the
     row stays an [ADir]) and the COUNT (so the nlink field does not
     move), which is exactly what makes the fused delta collapse to the
     one-row parent insert. *)
  Lemma mkf_parent_row (dn dn' : dinode) (bm bm' : blkmap)
      (data data' : nat -> list (bv 8)) (s : fname) (v : Z) :
    bv_unsigned (di_type dn) = T_DIR_z ->
    di_type dn' = di_type dn ->
    di_nlink dn' = di_nlink dn ->
    bv_unsigned (di_nlink dn) <> 0 ->
    dir_entries (era_node dn' bm' data')
      = <[s := v]> (dir_entries (era_node dn bm data)) ->
    abs_of (era_node dn' bm' data')
    = Some (MkAnode (ADir (<[s := v]> (dir_entries (era_node dn bm data))))
                    (fn_nlink (era_node dn bm data))).
  Proof.
    intros Hty Hty' Hnl' Hnl Hents.
    assert (Hdir' : fn_is_dir (era_node dn' bm' data') = true).
    { apply mkf_era_is_dir. by rewrite Hty'. }
    rewrite (mkf_abs_of_dir _ Hdir'
               (mkf_era_live dn' bm' data' ltac:(rewrite Hnl'; exact Hnl))) Hents.
    by rewrite !mkf_era_nlink Hnl'.
  Qed.

  (* ---- ITEM 4: THE MINTED CHILD'S ROW ------------------------------- *)

  Lemma mkf_child_dev (dn : dinode) (bm : blkmap)
      (data : nat -> list (bv 8)) (major minor : mword 16) :
    dn = create_made T_DEVICE major minor ->
    abs_of (era_node dn bm data)
    = Some (MkAnode (ADev (bv_unsigned major) (bv_unsigned minor)) 1%nat).
  Proof.
    intros ->. apply abs_of_create_dev. by rewrite era_node_rec.
  Qed.

  (* =================================================================== *)
  (*  3.  THE TWO FIRE POINTS, [ftopN] OPENED AND CLOSED                  *)
  (* =================================================================== *)

  (* THE READ-ONLY FIRE, at create's dirlookup(found) under the parent's
     lock.  The row comes off the FIRING FUNCTION's own era fragment (the
     one [IcacheEscrow.ic_loaded] carries), so no walk lend is involved
     and the fragment goes straight back. *)
  Lemma mkf_dlookup_fire (γfs : fs_names) (E : coPset) (dq : dfrac)
      (Fex : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (d i : Z) (nm : fname) (n : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    fn_is_dir n = true ->
    fn_nlink n <> 0%nat ->
    dir_entries n !! nm = Some i ->
    ftop_inv γfs -∗
    pf_at (dlookup_commit_at (fs_gamma_L γfs) appE) Fex -∗
    top_frag_q (fs_gamma_L γfs) dq d n ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq d n
      ∗ ∃ av : aview,
          ⌜av !! d = Some (MkAnode (ADir (dir_entries n)) (fn_nlink n))⌝
          ∗ ⌜dir_entries n !! nm = Some i⌝
          ∗ Fex.(pf_recv) av d nm i.
  Proof.
    intros HE Hdir Hnl Hnm. iIntros "#Hi Hcm Hf".
    (* THE PIECE IS SPENT: the fire eliminates to the AU side. *)
    iDestruct (pf_at_au with "Hcm") as "Hcm".
    (* [γtop (fs_gamma_L γfs)] and [fs_top γfs] are the SAME gname
       ([FsAbs.ftop_gamma_top], by reflexivity) but the unifier cannot
       solve [γtop ?Γ =?= fs_top γfs], so the fragment is put in the
       body's own spelling before the invariant is opened -- exactly what
       [InodeRegion.ireg_top_retag_*] does at its own retag. *)
    rewrite /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : abs_view I !! d
                   = Some (MkAnode (ADir (dir_entries n)) (fn_nlink n))).
    { by rewrite (abs_view_lookup_of I d n Hlk) (mkf_abs_of_dir n Hdir Hnl). }
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I d i nm (dir_entries n) (fn_nlink n)
            with "[//] [//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, A. by iFrame. }
    iModIntro. iFrame "Hf". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

End MknodFire.

(* ===================================================================== *)
(*  4.  ITEM 4's BIT-LEVEL HALF: THE HALFWORD ARGUMENT                    *)
(* ===================================================================== *)

(* sys_mknod's [lh a2,-148(s0)] reads back the low HALFWORD of the [int]
   [argint] wrote, i.e. [hw_lo (arg_int32 v)] in [ProofSysMknod]'s
   vocabulary; the record field reads back UNSIGNED.  So the abstract
   child's major number is the low sixteen bits of the trapframe word --
   [SysMknodDefs.dev_arg] on the nose.  Stated over the byte spelling
   rather than over [hw_lo] because [hw_lo] lives in a PROOF file. *)
(* the pure split, at the shape the byte assembly leaves behind:
   [Z.rem_mul_r] IS this fact ("the low half plus the next digit"), so the
   two bytes need no bit-shifting of their own. *)
Lemma mkf_split16 (u : Z) :
  (u mod 2 ^ 8 + 2 ^ 8 * ((u / 2 ^ 8) mod 2 ^ 8 + 2 ^ 8 * 0)) mod 2 ^ 16
  = u mod 2 ^ 16.
Proof.
  assert (Hp : (2:Z) ^ 16 = 2 ^ 8 * 2 ^ 8) by (vm_compute; reflexivity).
  rewrite Hp (Z.rem_mul_r u (2 ^ 8) (2 ^ 8)
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)).
  rewrite Z.mul_0_r Z.add_0_r.
  apply Z.mod_small.
  pose proof (Z.mod_pos_bound u (2 ^ 8)
                ltac:(vm_compute; reflexivity)) as [Ha0 Ha1].
  pose proof (Z.mod_pos_bound (u / 2 ^ 8) (2 ^ 8)
                ltac:(vm_compute; reflexivity)) as [Hb0 Hb1].
  change (2 ^ 8) with 256 in *. lia.
Qed.

Lemma mkf_low16_mod (w : mword 32) :
  bv_unsigned (Z_to_bv 16 (assemble_bytes [nth_byte w 0; nth_byte w 1])
               : bv 16)
  = bv_unsigned w mod 2 ^ 16.
Proof.
  rewrite Z_to_bv_unsigned /bv_wrap /bv_modulus.
  cbn [assemble_bytes].
  rewrite !nth_byte_unsigned.
  change (Z.of_N (8 * N.of_nat 0)) with 0.
  change (Z.of_N (8 * N.of_nat 1)) with 8.
  change (Z.of_N 16) with 16.
  rewrite Z.shiftr_0_r (Z.shiftr_div_pow2 (bv_unsigned w) 8 ltac:(lia)).
  apply mkf_split16.
Qed.

Lemma mkf_dev_arg (v : mword 64) :
  bv_unsigned (Z_to_bv 16 (assemble_bytes [nth_byte (trunc32 v) 0;
                                           nth_byte (trunc32 v) 1])
               : bv 16)
  = dev_arg v.
Proof.
  rewrite mkf_low16_mod trunc32_unsigned /dev_arg /bv_wrap /bv_modulus.
  change (Z.of_N 32) with 32.
  assert (Hp : (2:Z) ^ 32 = 2 ^ 16 * 2 ^ 16) by (vm_compute; reflexivity).
  rewrite Hp (Z.rem_mul_r (bv_unsigned v) (2 ^ 16) (2 ^ 16)
                ltac:(vm_compute; discriminate)
                ltac:(vm_compute; reflexivity)).
  rewrite (Z.mul_comm (2 ^ 16) ((bv_unsigned v / 2 ^ 16) mod 2 ^ 16)).
  rewrite Z_mod_plus_full.
  apply Z.mod_mod. vm_compute. discriminate.
Qed.


(* ===================================================================== *)
(*  5.  THE ERA-LEND WALK PREDICATES                                      *)
(*      (was iris/FsAbsEraMknod.v, fused 2026-08-30)                       *)
(* ===================================================================== *)

(* THE THREE REQUIRES THIS HALF ADDS, and they sit HERE rather than at the
   top for the reason [FsAbs.v]'s section 5 gives: nothing above this line
   may have a name of theirs resolved by accident.  [FsImg] is REQUIRED and
   NOT imported (both halves below spell [FsImg.ROOTINO] / [FsImg.T_FILE_z]
   qualified, and an import would shadow [InodeInv.ROOTINO]). *)
Require Import PathElems.       (* [path_elems], [SLASH] *)
Require FsImg.
Require Import FsAbsEra.        (* [elend], [ex_hops_from], [elend_astate],
                                   and (since the era leaves fused) the
                                   parent prefix and the deferred start *)

(* THE WALK PREDICATES THE PARENT-PREFIX ONE-SHOT IS BUILT FROM (was
   iris/FsAbsEraMknod.v).  They ride the ERA LEND, and that is what makes
   every fire point below reachable: [FsAbsEra.elend_astate] reads the row
   straight off the authority, because the lent fragment and the carrier
   are THE SAME GHOST.  A lend that says nothing about gamma-top cannot do
   it -- no amount of opening ftopN at the fire instant would identify the
   authority's row for the directory the walk is standing on ([FsAbsSeam],
   findings 2 and 3).

   WHAT IS NOT HERE.  The nameiparent WALK.  These predicates are about the
   HOP, and the hop is the same on both sides of namex's [a1] test; the
   walk itself is [SpecNparEra] / [SpecNparWrapEra].

   The two predicates are the walk premise of EVERY path syscall that
   resolves with nameiparent -- mknod, unlink, open's create arm, create
   itself -- so their [mknod_] prefix names the family's mold, not one
   caller. *)
Section EraMknod.
  (* [SysMknodDefs]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  THE WALK PREDICATES OVER THE ERA LEND                               *)
  (* =================================================================== *)

  (* THE PARENT-PREFIX ONE-SHOT: one fupd, universally quantified over the
     fetched string, yielding the cursor at the start and one [ax_hop] per
     parent element.
       THE START: [FsAbsStart.um_start_of cw pl] -- ROOTINO on an absolute
     fetch, the calling process's cwd inum [cw] on a relative one; the
     syscall contract passes its block's [pv_cwi]. *)
  Definition npar_walk_pre_era (γfs : fs_names) (cw : Z)
      (P Pmiss : nat -> Z -> iProp Σ) : iProp Σ :=
    (∀ (pl : list (bv 8)) (r : Z),
       ⌜r = um_start_of cw pl⌝ ={⊤}=∗
       P 0%nat r
       ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss
           (npar_elems pl) 0%nat)%I.

  Definition npar_walk_dead_era (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) : iProp Σ :=
    (∃ (k : nat) (d : Z),
       ⌜(k < length (npar_elems pl))%nat⌝ ∗
       ((P k d ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss
                   (npar_elems pl) k)
        ∨ (Pmiss k d
           ∗ ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss
               (npar_elems pl) (S k))))%I.

  (* sealed: they are big-ops behind Definitions at syscall altitude *)

End EraMknod.

Global Typeclasses Opaque npar_walk_pre_era npar_walk_dead_era.

(* ===================================================================== *)
(*  6.  THE ACCEPTANCE TEST                                               *)
(*      (was iris/FsAbsNparMknod.v, fused 2026-08-30)                      *)
(* ===================================================================== *)

(* THE ACCEPTANCE TEST, DISCHARGED (was iris/FsAbsNparMknod.v): the two
   walk predicates above are exactly what the nameiparent era walk's
   contract ([SpecNparEra]) consumes and produces.

   THREE FACTS, and two of them are [reflexivity].

   (1) THE FAMILIES ARE THE SAME FAMILY.  [FsAbsNpar.np_elems pl] and
       [SysMknodDefs.npar_elems pl] are both
       [removelast (path_elems pl)] -- so [ep_hops_from] and the
       [ax_hops_from] inside [npar_walk_pre_era] are the same big-op, and
       the walk's trace premise IS what the syscall's one-shot hands out.
       This is not a coincidence to be maintained: it is why the npar
       contract ranges over the parent prefix at all (FsAbsNpar's header).

   (2) THE PRE.  [np_pre_of_mknod] fires the one-shot at the string the
       walk fetched and at [ROOTINO], which is where an ABSOLUTE fetch
       starts.  The two [ROOTINO]s -- [InodeInv.ROOTINO : mword 32], read
       off namex's [li a1,1], and [FsImg.ROOTINO : Z], the image's --
       agree by computation.  [np_start_of_mknod] is the general form the
       walk actually takes: the START INUM is the walk's to choose, so no
       firing happens at all.

   (3) THE DEAD.  This one is NOT an identity, and the mismatch is worth
       recording rather than papering over.  [npar_walk_dead_era] bounds
       its death index STRICTLY ([k < length ps]) in BOTH disjuncts; the
       walk can die at [k = length ps], because namex runs the level's
       type test and nlink guard at the PARENT's own level too
       ([FsAbsNpar]'s header, case (1)), and at [k = 0 = length ps] when
       the path has no elements at all (case (2)).  So the honest
       statement is a DISJUNCTION: either the predicate above, or the
       cursor at the parent index -- and the second alternative is exactly
       what [SpecCreate.cre_fail_arms]'s walk-death arm carries, which a
       create that never got to dirlink refunds anyway.  So mknod's post is
       dischargeable as it stands; what is NOT true is that
       [npar_walk_dead_era] alone covers the walk's failures. *)

Section NparMknod.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  (1) the families                                                   *)
  (* ------------------------------------------------------------------ *)

  Lemma np_elems_is_mknod_parent_elems (pl : list (bv 8)) :
    np_elems pl = npar_elems pl.
  Proof. reflexivity. Qed.

  Lemma ep_hops_is_mknod_hops (γfs : fs_names)
      (P Pmiss : nat -> Z -> iProp Σ) (pl : list (bv 8)) (n : nat) :
    ep_hops_from γfs P Pmiss pl n
    = ax_hops_from (elend (fs_gamma_L γfs)) P Pmiss (npar_elems pl) n.
  Proof. reflexivity. Qed.

  (* the roots agree *)
  Lemma np_rootino_agree :
    bv_unsigned InodeInv.ROOTINO = FsImg.ROOTINO.
  Proof. vm_compute. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (*  (2) lane W's one-shot supplies the walk's two trace premises       *)
  (* ------------------------------------------------------------------ *)

  (* THE FORM THE WALK ACTUALLY TAKES SINCE LANE A-iii: no firing at all,
     because the START INUM is the walk's to choose ([FsAbsStart]'s
     header).  [ep_start] at a fixed [pl] IS [npar_walk_pre_era]
     specialized to that [pl] -- same quantifier, same tie, same family --
     so this is a rename plus the two ROOTINOs agreeing. *)
  Lemma np_start_of_mknod (γfs : fs_names) (cw : Z) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    npar_walk_pre_era γfs cw P Pmiss -∗ ep_start γfs cw P Pmiss pl.
  Proof.
    iIntros "Hpre". rewrite /ep_start. iIntros (r Hr).
    rewrite /npar_walk_pre_era.
    iMod ("Hpre" $! pl r with "[%]") as "[$ $]"; [exact Hr | done].
  Qed.

  Lemma np_pre_of_mknod (γfs : fs_names) (cw : Z) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    pl !! 0%nat = Some SLASH ->
    npar_walk_pre_era γfs cw P Pmiss ={⊤}=∗
      P 0%nat (bv_unsigned InodeInv.ROOTINO)
      ∗ ep_hops_from γfs P Pmiss pl 0%nat.
  Proof.
    iIntros (Hsl) "Hpre". rewrite /npar_walk_pre_era.
    iMod ("Hpre" $! pl (bv_unsigned InodeInv.ROOTINO) with "[%]") as "[$ $]".
    { rewrite (um_start_of_slash _ _ Hsl). exact np_rootino_agree. }
    done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  (3) the walk's death arm, folded into lane W's two shapes          *)
  (* ------------------------------------------------------------------ *)

  Lemma np_dead_to_mknod (γfs : fs_names) (P Pmiss : nat -> Z -> iProp Σ)
      (pl : list (bv 8)) :
    np_dead γfs P Pmiss pl -∗
      npar_walk_dead_era γfs P Pmiss pl
      ∨ (∃ d : Z, P (length (npar_elems pl)) d).
  Proof.
    rewrite /np_dead /npar_walk_dead_era.
    iIntros "[Hl | Hr]".
    - iDestruct "Hl" as (k d) "(%Hk & HP & Hh)".
      destruct (decide (k < length (np_elems pl))%nat) as [Hlt | Hge].
      + iLeft. iExists k, d. iSplitR; [by iPureIntro |]. iLeft. iFrame.
      + (* [k = length ps]: the parent's OWN level died.  The family from
           there is empty, and the cursor at the parent index is the whole
           refund -- mknod's third fold arm. *)
        assert (Hkeq : k = length (np_elems pl)) by lia.
        iRight. iExists d. rewrite -Hkeq. iClear "Hh". iExact "HP".
    - iDestruct "Hr" as (k d) "(%Hk & HP & Hh)".
      iLeft. iExists k, d. iSplitR; [by iPureIntro |]. iRight. iFrame.
  Qed.

  (* ...and the SUCCESS side needs no lemma at all: the walk returns
     [P (length (np_elems pl)) iL], which IS
     [P (length (npar_elems pl)) iL]. *)
  Lemma np_ok_is_mknod_ok (P : nat -> Z -> iProp Σ) (pl : list (bv 8))
      (iL : Z) :
    P (length (np_elems pl)) iL = P (length (npar_elems pl)) iL.
  Proof. reflexivity. Qed.

End NparMknod.

(* ===================================================================== *)
(*  7.  FIRE 2, AT A NON-DIRECTORY CHILD                                  *)
(*      (was iris/FsAbsCreateFire.v, fused 2026-08-30)                     *)
(* ===================================================================== *)

(* [TsoCtx] is IMPORTED here (and only here) because [Section CreateFire]
   binds [CurCtx]; it is deliberately the LAST require in the file, so no
   notation of its flips under anything above. *)
Require Import TsoCtx.

(* FsAbsCreateFire.v -- the create AU's SUCCESS FIRE AT A NON-DIRECTORY
   CHILD, and the [T_FILE] row reading that instantiates it.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W (the T_FILE
   create-AU carry).  (WAS A LEAF, iris/FsAbsCreateFire.v, for the mirror's
   reason the campaign's other leaves record: the build mirror forbids
   touching a tracked file.  FUSED IN 2026-08-30 -- "fuse the fire leaves
   when one of them is next edited", as far as the cone allows: the OTHER
   fire leaves each stand on a different syscall's statement leaf, and each
   of those requires this file, so they cannot follow without a cycle.)

   ==== WHY THIS FILE EXISTS ============================================

   THE SUCCESS FIRE IS STATED AT AN ARBITRARY NON-[ADir] CHILD, not at a
   device.  The delta's collapse is discharged with
   [SysMknodDefs.delta_create_dev], the "under [cre_pre] with a DEVICE
   child, the fused delta IS the one-row parent insert" lemma; reading
   that lemma's proof shows the device-ness is not used -- what is used is
   that the child is NOT A DIRECTORY, which is what makes
   [SysMknodDefs.acre_bump] zero (so the parent's count does not move)
   and what makes [cre_pre_ne] separate parent from child (so the child's
   insert is the identity on its already-minted row).

   So the two lemmas below are the [ADev]-free forms:

     [caf_delta_create_nondir]  -- [delta_create_dev] at any non-[ADir] [c]
     [caf_acre_fire]            -- the success fire, fused with the
                                   parent-row retag, at any non-[ADir] [c]

   and [caf_child_file] is the [T_FILE] instance of the minted child's row
   ([FsAbsMknodFire.mkf_child_dev]'s twin): [FsAbsCreateFire.create_made T_FILE
   major minor] reads as [AFile []] at nlink 1, because that record's size
   is zero and [fn_file_bytes] of a zero-size node is [file_bytes _ 0 = []]
   -- the same arithmetic [FsAbsOpenFire.opf_trunc_bytes] does at itrunc's
   own zeroing.

   BINDERS: [FsAbsMknodFire]'s section list VERBATIM (which is
   [SysMknodDefs]'s) -- [fileG] is bound and [icacheG]/[icfg] resolve
   only through its fields (SpecCreate's header: a standalone [icfg] beside
   [fileG] gives two instance paths and the propositions print identically
   while failing to unify). *)

(* ===================================================================== *)
(*  1.  THE DELTA'S COLLAPSE AT A NON-DIRECTORY CHILD (pure)              *)
(* ===================================================================== *)

(* [acre_bump] is zero at everything but a directory: the parent's count
   moves only when the child's ".." takes a token. *)
Lemma caf_acre_bump_nondir (c : absnode) :
  (forall e, c <> ADir e) -> acre_bump c = 0%nat.
Proof.
  intros Hc. destruct c as [bs | ents | ma mi]; [reflexivity | | reflexivity].
  exfalso. exact (Hc ents eq_refl).
Qed.

(* [SysMknodDefs.delta_create_dev] with the device-ness dropped: under
   [cre_pre] at a NON-DIRECTORY child the fused delta IS the one-row parent
   insert.  The child's own insert is the identity on the row [cre_pre]'s
   third conjunct already observes, and [cre_pre_ne] is what keeps the two
   inserts from being at the same key. *)
Lemma caf_delta_create_nondir (av : aview) (d : Z) (nm : fname)
    (ents : gmap fname Z) (nl : nat) (i : Z) (c : absnode) :
  (forall e, c <> ADir e) ->
  cre_pre av d nm ents nl i c ->
  delta_create d nm i c av
  = <[d := MkAnode (ADir (<[nm := i]> ents)) nl]> av.
Proof.
  intros Hc Hp.
  assert (Hne : d <> i) by exact (cre_pre_ne av d nm ents nl i c Hp Hc).
  destruct Hp as (Hd & Hnm & Hi).
  rewrite /delta_create Hd /= (caf_acre_bump_nondir c Hc) Nat.add_0_r.
  rewrite (insert_commute _ i d); [| congruence].
  by rewrite (insert_id av i (MkAnode c 1%nat) Hi).
Qed.

(* ===================================================================== *)
(*  2.  THE MINTED CHILD'S ROW AT [T_FILE]                                *)
(* ===================================================================== *)

(* [SysMknodDefs.abs_of_create_dev]'s twin.  Three readings, each off
   [create_made]'s own fields: the type is not [T_DIR_z] (so the row is not
   an [ADir]) and IS [T_FILE_z] (so it is an [AFile]); the size is zero, so
   the byte list is [file_bytes _ 0 = []]; the count is one. *)
Lemma caf_abs_of_create_file (n : fs_node) (major minor : mword 16) :
  fn_rec n = create_made T_FILE major minor ->
  abs_of n = Some (MkAnode (AFile []) 1%nat).
Proof.
  intros Hr.
  assert (Hnd : fn_is_dir n = false).
  { rewrite /fn_is_dir /fn_type Hr. by apply bool_decide_eq_false_2. }
  assert (Hfl : fn_type n = FsImg.T_FILE_z)
    by (rewrite /fn_type Hr; reflexivity).
  assert (Hbytes : fn_file_bytes n = []).
  { rewrite /fn_file_bytes /fn_size Hr. reflexivity. }
  assert (Hnl : fn_nlink n = 1%nat)
    by (rewrite /fn_nlink Hr; reflexivity).
  by rewrite (abs_of_file n Hnd Hfl ltac:(rewrite Hnl; lia)) Hbytes Hnl.
Qed.

(* ...and at the era node, which is the shape a walk holds
   ([FsAbsMknodFire.mkf_child_dev]'s spelling). *)
Lemma caf_child_file (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) (major minor : mword 16) :
  dn = create_made T_FILE major minor ->
  abs_of (era_node dn bm data) = Some (MkAnode (AFile []) 1%nat).
Proof.
  intros ->. apply (caf_abs_of_create_file _ major minor).
  by rewrite era_node_rec.
Qed.

Section CreateFire.
  (* [FsAbsMknodFire]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* =================================================================== *)
  (*  3.  THE SUCCESS FIRE AT A NON-DIRECTORY CHILD                       *)
  (* =================================================================== *)

  (* THE SUCCESS FIRE, FUSED WITH THE PARENT-ROW RETAG, at an arbitrary
     non-[ADir] child [cf d i].  Replaces the
     [InodeRegion.ireg_top_retag_*] a mover would otherwise call at this
     instant: same premise (the new node is well-formed), same payout (the
     moved fragment), plus the caller's two phases fired on either side of
     the [ghost_map_update] INSIDE the one [ftopN] critical section.  The
     child's fragment is only READ (its row is what the armed-child
     observation [cre_pre]'s third conjunct asks for: nlink 1, not yet in
     the parent) and comes back untouched. *)
  Lemma caf_acre_fire (γfs : fs_names) (E : coPset) (cf : Z -> Z -> absnode)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (d i : Z) (nm : fname) (dqc : dfrac) (np np' nc : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local d np' ->
    fn_is_dir np = true ->
    fn_nlink np <> 0%nat ->
    dir_entries np !! nm = None ->
    abs_of np' = Some (MkAnode (ADir (<[nm := i]> (dir_entries np)))
                               (fn_nlink np + acre_bump (cf d i))%nat) ->
    abs_of nc = Some (MkAnode (cf d i) 1%nat) ->
    ftop_inv γfs -∗ app_inv γfs -∗
    pf_at (acre_commit_at_gen (fs_gamma_L γfs) appE cf Farm) Fok -∗
    (* THE ARM'S PERMIT, SPENT HERE: the create's child IS the inode
       [ialloc] armed, and the leg that ends the inode is the one that
       spends the permit ([FsAbsCreateFire.acre_commit_at_gen]'s note). *)
    cre_arm_fired Farm i -∗
    top_frag (fs_gamma_L γfs) d np -∗
    top_frag_q (fs_gamma_L γfs) dqc i nc ={E}=∗
      top_frag (fs_gamma_L γfs) d np'
      ∗ top_frag_q (fs_gamma_L γfs) dqc i nc
      ∗ ∃ av : aview,
          ⌜cre_pre av d nm (dir_entries np) (fn_nlink np) i (cf d i)⌝
          ∗ Fok.(pf_recv) av d nm i.
  Proof.
    intros HE Hloc Hdir Hnl Hnone Habsp' Habsc.
    iIntros "#Hi #Hai Hcm Harm Hfp Hfc".
    iDestruct (pf_at_au with "Hcm") as "Hcm".
    (* the re-spelling is needed because
       [γtop (fs_gamma_L γfs)] and [fs_top γfs] are the SAME gname
       ([FsAbs.ftop_gamma_top], by reflexivity) but the unifier cannot
       solve [γtop ?Γ =?= fs_top γfs]. *)
    rewrite /top_frag /top_frag_q /fs_gamma_L /=.
    (* PARENT AND CHILD ARE DISTINCT KEYS: the parent's fragment is whole,
       so the two cannot share an element *)
    iDestruct (ghost_map_elem_ne with "Hfp Hfc") as %Hne.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hfp") as %Hlkp.
    iDestruct (ghost_map_lookup with "Hta Hfc") as %Hlkc.
    assert (Hpre : cre_pre (abs_view I) d nm (dir_entries np)
                     (fn_nlink np) i (cf d i)).
    { rewrite /cre_pre. split_and!.
      - by rewrite (abs_view_lookup_of I d np Hlkp) (mkf_abs_of_dir np Hdir Hnl).
      - exact Hnone.
      - by rewrite (abs_view_lookup_of I i nc Hlkc) Habsc. }
    (* the fused delta collapses to the ONE-ROW parent insert at the ARMED
       child ([FsAbsDelta.delta_create_armed]) *)
    assert (Hdelta : abs_view (<[d := np']> I)
                     = delta_create d nm i (cf d i) (abs_view I)).
    { rewrite (abs_view_insert I d np' _ Habsp').
      by rewrite (delta_create_armed (abs_view I) d nm (dir_entries np)
                    (fn_nlink np) i (cf d i) Hpre Hne). }
    iMod (fupd_mask_subseteq appE) as "Hcl2"; [rewrite /appE; solve_ndisj |].
    iMod ("Hcm" $! I d i nm (dir_entries np) (fn_nlink np)
            with "[//] Harm Hta") as "(Hta & Hstep & Hph2)".
    (* THE MOVE, at the whole authority: the application's half comes out
       of [appN] beside its claim, which the caller's step re-establishes
       under the later ([AppInv.app_top_update]) *)
    iMod (app_top_update appE γfs I d np np' ltac:(rewrite /appE; done)
            with "Hai [Hstep] Hta Hfp") as "[Hta Hfp]".
    { iIntros (_) "Hp". iApply (app_step_at d I _ np' Hdelta with "Hstep Hp"). }
    iMod ("Hph2" $! (<[d := np']> I) with "[//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists (<[d := np']> I), A.
      iFrame "Hta Hla Hpark". iPureIntro.
      intros jj mm Hj Hun. destruct (decide (jj = d)) as [-> | Hne'].
      - rewrite lookup_insert in Hj. injection Hj as <-. exact Hloc.
      - rewrite lookup_insert_ne in Hj; [| exact (not_eq_sym Hne')].
        exact (Hcl jj mm Hj Hun). }
    iModIntro. iFrame "Hfp Hfc". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* the [AFile []] instance, which is the one the T_FILE create-AU fires:
     a file child is never an [ADir]. *)
  Lemma caf_acre_fire_file (γfs : fs_names) (E : coPset)
      (Farm : pfam Σ (aview -> Z -> iProp Σ))
      (Fok : pfam Σ (aview -> Z -> fname -> Z -> iProp Σ))
      (d i : Z) (nm : fname) (dqc : dfrac) (np np' nc : fs_node) :
    ↑ftopN ∪ ↑appN ⊆ E ->
    inode_local d np' ->
    fn_is_dir np = true ->
    fn_nlink np <> 0%nat ->
    dir_entries np !! nm = None ->
    abs_of np' = Some (MkAnode (ADir (<[nm := i]> (dir_entries np))) (fn_nlink np)) ->
    abs_of nc = Some (MkAnode (AFile []) 1%nat) ->
    ftop_inv γfs -∗ app_inv γfs -∗
    pf_at (acre_commit_at (fs_gamma_L γfs) appE (AFile []) Farm) Fok -∗
    cre_arm_fired Farm i -∗
    top_frag (fs_gamma_L γfs) d np -∗
    top_frag_q (fs_gamma_L γfs) dqc i nc ={E}=∗
      top_frag (fs_gamma_L γfs) d np'
      ∗ top_frag_q (fs_gamma_L γfs) dqc i nc
      ∗ ∃ av : aview,
          ⌜cre_pre av d nm (dir_entries np) (fn_nlink np) i (AFile [])⌝
          ∗ Fok.(pf_recv) av d nm i.
  Proof.
    intros HE Hloc Hdir Hnl Hnone Habsp' Habsc.
    iIntros "Hi Hai Hcm Harm Hfp Hfc".
    iApply (caf_acre_fire γfs E (fun _ _ => AFile []) Farm Fok d i nm dqc
              np np' nc HE Hloc Hdir Hnl Hnone
              ltac:(rewrite Habsp'; cbn [acre_bump]; by rewrite Nat.add_0_r)
              Habsc with "Hi Hai Hcm Harm Hfp Hfc").
  Qed.

  (* THE MINTED CHILD'S ROW AT ANY TYPE: [FsAbsCreateFire.create_made] at a
     nonzero type reads as [cre_c0] of the type and the two halfwords --
     the row the general create's ARM fires at ([FsAbsCreateFire.cre_c0]). *)
  Lemma caf_made_row_node (n : fs_node) (ty major minor : mword 16) :
    fn_rec n = create_made ty major minor ->
    bv_unsigned ty <> 0 ->
    abs_of n
    = Some (MkAnode (cre_c0 (bv_unsigned ty) (bv_unsigned major) (bv_unsigned minor))
                    1%nat).
  Proof.
    intros Hr Hty.
    assert (Hnty : fn_type n = bv_unsigned ty)
      by (rewrite /fn_type Hr; reflexivity).
    assert (Hnl : fn_nlink n = 1%nat) by (rewrite /fn_nlink Hr; reflexivity).
    (* the three arms are [FsAbsDefs]'s three named readings, so the row's
       [decide]s are never unfolded here -- only [cre_c0]'s, which
       [case_decide] takes at the goal's own instance (durable-notes:
       [destruct (decide P)] does not reduce a [decide] baked into another
       file's definition) *)
    rewrite /cre_c0. case_decide as Hd.
    - rewrite (abs_of_dir n
                 ltac:(rewrite /fn_is_dir Hnty; by apply bool_decide_eq_true_2)
                 ltac:(rewrite Hnl; discriminate)).
      rewrite (dir_entries_size_0 n
                 ltac:(rewrite /fn_size Hr; reflexivity)) Hnl. reflexivity.
    - assert (Hnd : fn_is_dir n = false)
        by (rewrite /fn_is_dir Hnty; by apply bool_decide_eq_false_2).
      case_decide as Hf.
      + rewrite (abs_of_file n Hnd ltac:(rewrite Hnty; exact Hf)
                   ltac:(rewrite Hnl; discriminate)).
        assert (Hb : fn_file_bytes n = [])
          by (rewrite /fn_file_bytes /fn_size Hr; reflexivity).
        rewrite Hb Hnl. reflexivity.
      + rewrite (abs_of_dev n Hnd ltac:(rewrite Hnty; exact Hf)
                   ltac:(rewrite Hnty; exact Hty)
                   ltac:(rewrite Hnl; discriminate)).
        assert (Hma : fn_major n = bv_unsigned major)
          by (rewrite /fn_major Hr; reflexivity).
        assert (Hmi : fn_minor n = bv_unsigned minor)
          by (rewrite /fn_minor Hr; reflexivity).
        rewrite Hma Hmi Hnl. reflexivity.
  Qed.

  Lemma caf_made_row (ty major minor : mword 16) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    bv_unsigned ty <> 0 ->
    abs_of (era_node (create_made ty major minor) bm data)
    = Some (MkAnode (cre_c0 (bv_unsigned ty) (bv_unsigned major) (bv_unsigned minor))
                    1%nat).
  Proof.
    intros Hty.
    exact (caf_made_row_node _ ty major minor
             (era_node_rec (create_made ty major minor) bm data) Hty).
  Qed.

End CreateFire.
