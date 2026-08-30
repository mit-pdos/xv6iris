(* FsAbsSeam.v -- LANE A ITEM (iii): THE HOP SEAM, AND THE ONE RESOURCE THE
   LANDED FIRE DID NOT LEND.

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane A, item (iii)
   ("the dview retirement").  Design of record:
   claude-notes/design/fs-syscall-specs.md v3.

   ===== TOMBSTONE (THE DVIEW RETIREMENT, 2026-08-30) =====================
   THIS FILE'S QUESTION IS ANSWERED AND ITS SUBJECT IS DELETED.  It asked
   whether [FsAbs.apn_walk]'s abstracted lend law could be discharged at
   [F := DirViewG.dv_half], the resource the landed ghost-trace namei
   ([SpecNameiTr.nx_hop]) lent at every hop.  Three findings came out of it,
   all machine-checked, and they are what routed the campaign:

     1. THE TIE IS PURE AND WAS ALREADY LANDED -- the payload's contents
        reading and its era fragment's are ONE function.  That lemma is the
        only thing here that SURVIVES the retirement, restated at the
        surviving spelling: [dir_entries_era_ok] (and its abstract-node
        form [abs_of_era_dir]), which [FsAbsEra.elend_of_era] consumes.
     2. [lend_agrees] WAS THE WRONG LAW at that lend, because [dv_half]
        rode a FILE too -- which is exactly the weakness the era fragment
        does not have (it carries the type), so [FsAbsEra]'s lend
        discharges the strong law after all.
     3. NO CLIENT CAN HOLD [nview] WHILE THE WALK RUNS.  That is the
        finding that outlived the ghost: sections 3-4 below are still
        theorems about the landed payload and still say that a pin against
        a live inum is refuted.

   DELETED WITH THE GHOST: [dv_top_seam] (section 2, the two payload
   conjuncts against a lent [dv_half] and a client-held [nview]);
   [dv_lend_arm] / [dv_lend_arm_reads] / [apn_walk_arm] (section 3's
   concrete lend at the READ arm and the pinned-walk package fired at it --
   [FsAbsEra.apn_walk_era] is its replacement, at a lend that needs no
   [dv_half]).  KEPT: [inode_rd_era_nview] (the one producer of a
   client-held [nview]) and section 4's three exclusion lemmas.
   =======================================================================

   BINDERS.  [IcacheEscrow]'s own list, verbatim: the BUNDLE [xv6G] and never
   a member (durable-notes, "ONE BUNDLE PER GHOST CLASS" -- [icacheG],
   [fsTopG] and [fsLinkG] are all members, and [FsAbs]'s own lemmas take them
   from it).  [FsAbs] is REQUIRED LAST so its [Require Export FsState] is the
   one that wins on the [FsState*] stack's shadowed names. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.      (* [riscvGS]                                  *)
Require Import DinodeEnc.       (* [dinode], [di_type], [di_size]             *)
Require Import FsTree.          (* [fname], [dir_view]                        *)
Require Import Xv6Cameras.
Require Import InodeInv.        (* [blkmap]                                   *)
Require Import InodeLock.       (* [inode_ok]                                 *)
Require Import IrefSlots.       (* [irefslotG]                                *)
Require Import FsBlocks.        (* [fs_names]                                 *)
Require Import FsBytesGamma.    (* [fs_gamma_L]: the LIVE Gamma               *)
Require Import FsStateEra.      (* [era_node], [dir_entries_era_node]         *)
Require Import IcacheRef.       (* [icfg]                                     *)
Require Import IcacheEscrow.    (* the three payload arms                     *)
Require Import Xv6G.            (* the bundle                                 *)
Require Import FsAbs.           (* LAST: [nview], [abs_of], [lend_reads]      *)
Require TsoCtx.   (* qualified: the class only, no notation flip *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PURE HALF: A PAYLOAD NODE'S [dir_entries] IS ITS [dir_view]    *)
(* ===================================================================== *)

(* [FsStateEra.dir_entries_era_node] with its guard discharged: the two side
   conditions are [inode_ok] conjuncts, so every payload arm has them in the
   same [Hiok] its other clauses come out of, and the directory guard is the
   one the walk has already tested.  (This was [dv_of_dir_entries], stated at
   the deleted [DirViewG.dv_of]; the right-hand side is that function,
   spelled out.) *)
Lemma dir_entries_era_ok (cov : gset Z) (logstart : Z) (dn : dinode)
    (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov logstart dn bm data ->
  fn_is_dir (era_node dn bm data) = true ->
  dir_entries (era_node dn bm data)
  = dir_view data (dir_nrec (bv_unsigned (di_size dn))).
Proof.
  intros (_ & _ & _ & _ & Hsz & Hh & _) Hd.
  rewrite /fn_is_dir /fn_type era_node_rec in Hd.
  by rewrite (dir_entries_era_node dn bm data Hh Hsz) Hd.
Qed.

(* ...and the same fact as the ABSTRACT NODE's arm, which is the form the
   lend law's conclusion is stated in. *)
Lemma abs_of_era_dir (cov : gset Z) (logstart : Z) (dn : dinode)
    (bm : blkmap) (data : nat -> list (bv 8)) :
  inode_ok cov logstart dn bm data ->
  fn_is_dir (era_node dn bm data) = true ->
  an_node (abs_of (era_node dn bm data))
  = ADir (dir_view data (dir_nrec (bv_unsigned (di_size dn)))).
Proof.
  intros Hok Hd.
  by rewrite (abs_of_dir _ Hd) (dir_entries_era_ok cov logstart dn bm data Hok Hd).
Qed.

Section FsAbsSeam.
  (* [IcacheEscrow]'s binder list, verbatim (header). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.
  Context `{ICFG : icfg}.
  Context `{XI : TsoCtx.CurCtx}.

  (* =================================================================== *)
  (*  2-3.  THE SEAM AT [dv_half], AND THE LEND FIRED AT THE READ ARM:    *)
  (*        RETIRED WITH THE GHOST (see the header's tombstone)           *)
  (* =================================================================== *)

  (* THE ONE PRODUCER OF A CLIENT-HELD [nview] IN THE LANDED TREE, and it is
     the other half of the read arm: what a read-locking [ilock] withdraws
     ([IcacheEscrow.ic_rd_held] carries [inode_rd_era] at a quarter) IS a
     carrier share, on the nose.  So [apn_pin] is satisfiable -- for an inum
     the client HAS READ-LOCKED, and for no other.  The byte legs come back
     beside it because a read-locker needs them to call [readi]. *)
  Lemma inode_rd_era_nview (γfs : fs_names) (q : Qp) (inum : mword 32)
      (n : fs_node) :
    inode_rd_era γfs (DfracOwn q) inum n -∗
      inode_dat_q (fs_gamma_L γfs) (DfracOwn q) n
      ∗ nview (fs_gamma_L γfs) q (bv_unsigned inum) (abs_of n).
  Proof.
    rewrite /inode_rd_era. iIntros "[$ Ht]". by iApply nview_of_frag.
  Qed.

  (* =================================================================== *)
  (*  4.  ...AND WHY THE WRITE ARM CANNOT BE THE ONE                      *)
  (* =================================================================== *)

  (* THE REFUTATION.  [ic_loaded] carries the era leg at [DfracOwn 1], so it
     carries [top_frag] WHOLE; a client-held [nview] share of that inum is
     not merely unavailable, it is inconsistent.  This is what stops the
     package above from being instantiated against namei's own fire, whose
     directory is checked out on the WRITE arm at the fire instant. *)
  Lemma ic_loaded_nview_excl (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (q : Qp) (a : anode) :
    ic_loaded γfs γi cov logstart k inum dn bm -∗
    nview (fs_gamma_L γfs) q (bv_unsigned inum) a -∗ False.
  Proof.
    iIntros "Hl Hn".
    iDestruct (ic_loaded_open with "Hl") as (data)
      "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp)".
    iApply (top_frag_1_nview_excl with "Htp Hn").
  Qed.

  (* ...and the same at the POOL row, which is where an allocated inum's
     element parks when no cache slot holds it -- so the refutation covers
     every allocated inum, cached or not. *)
  Lemma ipool_alloc_nview_excl (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (inum : mword 32) (q : Qp) (a : anode) :
    ipool_alloc γfs γi cov logstart inum -∗
    nview (fs_gamma_L γfs) q (bv_unsigned inum) a -∗ False.
  Proof.
    rewrite /ipool_alloc. iIntros "Hp Hn".
    iDestruct "Hp" as (dn0 bm0 data0) "(_ & _ & _ & _ & _ & Hleg)".
    iDestruct (ic_inode_leg_open with "Hleg") as "[_ Hown]".
    iDestruct (inode_owned_era_to_q with "Hown") as "(_ & _ & _ & Htp)".
    iApply (top_frag_1_nview_excl with "Htp Hn").
  Qed.

  (* the same statement in the walk package's own vocabulary: a PIN cannot be
     held against a loaded payload *)
  Lemma apn_pin_loaded_excl (γfs : fs_names) (γi : gname) (cov : gset Z)
      (logstart : Z) (k : nat) (inum : mword 32) (dn : dinode) (bm : blkmap)
      (q : Qp) (av : aview) :
    ic_loaded γfs γi cov logstart k inum dn bm -∗
    apn_pin (fs_gamma_L γfs) q av (bv_unsigned inum) -∗ False.
  Proof.
    iIntros "Hl Hp". rewrite /apn_pin. iDestruct "Hp" as (a) "[_ Hn]".
    iApply (ic_loaded_nview_excl with "Hl Hn").
  Qed.

End FsAbsSeam.
