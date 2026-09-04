(* FsAbsReadFire.v -- sys_read's ONE FIRE POINT, DISCHARGED AGAINST THE
   INVARIANT, plus the row readings and the count bridge
   [SpecSysReadAU]'s header owes its prover (items 1, 2 and 6).

   Worklist: claude-notes/projects/fs-syscall-specs.md, lane W.  A NEW LEAF
   rather than an append to [FsAbsOpenFire.v] / [FsAbsMknodFire.v], for the
   mirror's reason every campaign leaf records: the build mirror forbids
   touching a tracked file.  Fuse the fire leaves when one of them is next
   edited.

   ==== WHY THE COMMIT HERE IS THE RAW-MAP ONE =========================

   [SpecSysReadAU.aread_commit] is stated over [FsAbs.astate], and that
   shape is NOT DISCHARGEABLE -- this is [FsAbsMknodFire.v]'s recorded
   raw-map finding, and its statement of the obstacle names the read-only
   borrow by name:

     "[ftop_astate_ro]'s [give-back] wants the SAME [I] the borrow named,
      and nothing in [astate Γ av] says the returned map is that one"

   [astate Γ av] is [∃ I, ghost_map_auth (γtop Γ) 1 I ∗ ⌜av = abs_view I⌝]
   and [abs_view] is not injective ([abs_of] forgets the block map, the
   size's slack, and every field [FsStateInode.inode_local] constrains), so
   an authority that comes back out of a client's fupd is an authority at
   SOME map with the right READING -- while [InodeRegion.ftop_body]'s
   [ftop_clean] is a statement about the RECORDS.  Read-onlyness does not
   help: the loss happens on the way OUT, in the existential of [astate],
   before the client does anything at all.

   [SpecSysReadAU] was authored before that finding (its header still says
   "shaped for [FsAbs.ftop_astate_ro]").  Every contract authored after it
   -- [SpecSysOpenAU]'s [aopen_commit_at]/[atrunc_commit_at],
   [FsAbsMknodFire]'s [dlookup_commit_at]/[acre_commit_at] -- carries the
   RAW-MAP form in the contract and offers the astate reading beside it as
   a weakening.  This file does the same for read: [aread_commit_at] is the
   dischargeable form, [aread_commit_at_weaken] is the one direction that
   holds ([FsAbsMknodFire.dlookup_commit_at_weaken]'s argument verbatim --
   a client that can serve the authority form can serve the [astate] form
   by unfolding it), and [arf_read_fire] fires it.

   R10 IS INTACT: [SpecSysReadAU.v] is untouched, and everything the frozen
   file offers a client is offered here at the same strength (the
   trivial-receipt unit, and the two agreement seeds the stable corollary
   is derived from).  What is NOT possible is the reverse weakening, so a
   machine contract whose EXTRA is the frozen [aread_commit] cannot be
   sealed; sealing read wants a parallel body at [aread_commit_at], exactly
   as [SpecSysOpenAU] carries one.

   ==== WHAT THE FIRE DOES =============================================

   [arf_read_fire] is [FsAbsOpenFire.opf_open_fire]'s mold at the read
   commit: ONE step, [ftopN] opened and closed inside, the row read off the
   FIRING FUNCTION'S OWN fragment.  That fragment is fileread's: the inode
   arm holds [IcacheEscrow.ic_loaded]'s [top_frag] for the file's inum from
   its [ilock] to its [iunlock], and the whole transfer happens inside that
   window (SpecSysReadAU's THE ONE INSTANT), so no walk lend is involved
   and the fragment goes straight back.  The two caps [ard_pre] asks for
   ride as premises about the SAME node, which is where the caller has
   them: the offset's from [FileInvDefs.off_wf], the row's from the loaded
   record's size ([arf_size_ok] turns [fn_size <= MAXFILE*BSIZE] into
   [anode_size_ok]).

   ==== THE COUNT BRIDGE (item 2) ======================================

   [arf_count_bridge] is the pure half of the return tie: readi's arm 2
   answers [rd_clamp (di_size dn) off n'], and over a row that READS as
   [AFile bs] that IS [ard_count n' off (length bs)] -- [rd_clamp_ard]
   composed with [length_fn_file_bytes] through the [abs_of] file arm.
   [arf_ret_tie_file] / [arf_ret_tie_other] are the two arms of
   [ard_ret_tie] assembled from it and from [SpecFileread.fileread_ret]'s
   bounds.

   BINDERS: [FsAbsOpenFire]'s section list, verbatim (which is
   [FsAbsMknodFire]'s, which is [SpecSysMknodAU]'s) -- [fileG] is bound and
   [icacheG]/[icfg] resolve only through its fields. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac dfrac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.Operators_mwords.   (* [mword_of_int]              *)
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import DinodeEnc.
Require Import FsBlocks.         (* [fs_names]                              *)
Require Import FsBytesGamma.     (* [fs_gamma_L]                            *)
Require Import BioDefs.          (* [BSIZE]                                 *)
Require Import InodeInv.         (* [MAXFILE]                               *)
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
Require Import SpecReadi.        (* [rd_clamp]                              *)
Require Import SpecSysReadAU.    (* the contract this file serves           *)
Require FsImg.                   (* [T_FILE_z] -- Require, NOT Import
                                    ([FsAbsOpenFire]'s reason)              *)
Require Import FsAbsInv.        (* [fsabsN]/[fsabsE]: the commit mask *)
Require Import FsAbs.            (* LAST (FsAbs's own rule)                 *)
Require Import TsoCtx.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE ROW READINGS (pure, no binder)                                *)
(* ===================================================================== *)

(* the inverse of [FsAbs.abs_of_file], which is the direction a prover that
   has MATCHED on the observed row needs: a row that reads as a file reads
   as the record's OWN flat bytes *)
(* The three LANDED readings ([FsAbs.abs_of_dir]/[_file]/[_dev]) are what
   both lemmas below case on -- never [abs_node]'s own [if], because
   unfolding it puts the answer under a [decide] that a later [rewrite]
   cannot see through. *)
Lemma arf_abs_file_inv (n : fs_node) (bs : list (bv 8)) :
  an_node (abs_of n) = AFile bs -> bs = fn_file_bytes n.
Proof.
  destruct (fn_is_dir n) eqn:Hd.
  - rewrite (abs_of_dir n Hd). discriminate.
  - destruct (decide (fn_type n = FsImg.T_FILE_z)) as [Ht | Ht].
    + rewrite (abs_of_file n Hd Ht). intros He. injection He as He.
      symmetry. exact He.
    + rewrite (abs_of_dev n Hd Ht). discriminate.
Qed.

(* [ard_pre]'s ROW-SHAPED CAP, from the record's own size.  The other two
   kinds carry nothing, so the size premise is only ever about a file. *)
Lemma arf_size_ok (n : fs_node) :
  fn_size n <= Z.of_nat (MAXFILE * BSIZE)%nat -> anode_size_ok (abs_of n).
Proof.
  intros Hsz. rewrite /anode_size_ok.
  destruct (fn_is_dir n) eqn:Hd.
  - rewrite (abs_of_dir n Hd). exact I.
  - destruct (decide (fn_type n = FsImg.T_FILE_z)) as [Ht | Ht].
    + rewrite (abs_of_file n Hd Ht). cbv beta iota.
      rewrite length_fn_file_bytes. lia.
    + rewrite (abs_of_dev n Hd Ht). exact I.
Qed.

Lemma arf_size_ok_era (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) :
  bv_unsigned (di_size dn) <= Z.of_nat (MAXFILE * BSIZE)%nat ->
  anode_size_ok (abs_of (era_node dn bm data)).
Proof.
  intros Hsz. apply arf_size_ok. rewrite /fn_size era_node_rec. exact Hsz.
Qed.

(* ---- THE COUNT BRIDGE (prover item 2) ------------------------------- *)

(* readi's arm 2 answers [rd_clamp] over the SIZE WORD; over a row that
   reads as a file that IS [ard_count] over the OBSERVED bytes. *)
Lemma arf_count_bridge (n : fs_node) (bs : list (bv 8)) (off n' : nat) :
  an_node (abs_of n) = AFile bs ->
  rd_clamp (di_size (fn_rec n)) off n' = ard_count n' off (length bs).
Proof.
  intros Hf. rewrite (arf_abs_file_inv n bs Hf) length_fn_file_bytes /fn_size.
  apply rd_clamp_ard.
Qed.

(* ...at the spelling a walk holding a LOADED record has it *)
Lemma arf_count_bridge_era (dn : dinode) (bm : blkmap)
    (data : nat -> list (bv 8)) (bs : list (bv 8)) (off n' : nat) :
  an_node (abs_of (era_node dn bm data)) = AFile bs ->
  rd_clamp (di_size dn) off n' = ard_count n' off (length bs).
Proof.
  intros Hf.
  assert (Heq : di_size dn = di_size (fn_rec (era_node dn bm data)))
    by (rewrite era_node_rec; reflexivity).
  rewrite Heq. exact (arf_count_bridge _ bs off n' Hf).
Qed.

(* ---- THE TWO ARMS OF THE RETURN TIE --------------------------------- *)

Lemma arf_ret_tie_file (nz : Z) (a : anode) (bs : list (bv 8))
    (off : nat) (r : mword 64) :
  an_node a = AFile bs ->
  r = (mword_of_int (Z.of_nat (ard_count (Z.to_nat nz) off (length bs)))
       : mword 64) ->
  ard_ret_tie nz a off r.
Proof. intros Ha Hr. rewrite /ard_ret_tie Ha. exact Hr. Qed.

(* the directory / device fold (item 6): the landed [fileread_ret] bounds
   are exactly what the wildcard arm asks for *)
Lemma arf_ret_tie_other (nz : Z) (a : anode) (off : nat) (rv : Z) :
  (match an_node a with AFile _ => False | _ => True end) ->
  0 <= rv <= nz ->
  ard_ret_tie nz a off (mword_of_int rv).
Proof.
  rewrite /ard_ret_tie. destruct (an_node a) as [bs | ents | ma mi].
  - intros [].
  - intros _ Hrv. exists rv. split; [reflexivity | exact Hrv].
  - intros _ Hrv. exists rv. split; [reflexivity | exact Hrv].
Qed.

(* ===================================================================== *)
(*  1.  THE RAW-MAP COMMIT, AND THE ONE WEAKENING THAT HOLDS              *)
(* ===================================================================== *)

Section ReadFire.
  (* [FsAbsOpenFire]'s binder list, verbatim. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{XI : CurCtx}.
  Implicit Types Γ : fs_view_names Σ.

  (* SINGLE-PHASE AND READ-ONLY at the RAW MAP: the caller hands the very
     same [ghost_map_auth] back, which is what [ftop_astate_ro]'s give-back
     wants and what [astate]'s existential destroys (header). *)
  Definition aread_commit_at Γ (E : coPset) (i : Z)
      (Φ : aview -> nat -> anode -> iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (off : nat) (a : anode),
       ⌜ard_pre (abs_view I) i off a⌝ -∗
       ghost_map_auth (γtop Γ) 1 I ={E}=∗
       ghost_map_auth (γtop Γ) 1 I ∗ Φ (abs_view I) off a)%I.

  (* THE ONE RELATION THAT HOLDS -- [FsAbsMknodFire.dlookup_commit_at_weaken]'s
     argument verbatim.  The reverse does not: nothing ties the authority a
     client returns to the map the borrow named. *)
  Lemma aread_commit_at_weaken Γ E i Φ :
    aread_commit_at Γ E i Φ ⊢ aread_commit Γ E i Φ.
  Proof.
    iIntros "Hcm". rewrite /aread_commit.
    iIntros (av off a) "%Hpre Hst".
    iDestruct (astate_elim with "Hst") as (I) "[Ha %Hav]". subst av.
    iMod ("Hcm" $! I off a with "[//] Ha") as "[Ha HΦ]".
    iModIntro. iFrame "HΦ". iApply astate_intro. iExact "Ha".
  Qed.

  (* satisfiability: the seal cannot be vacuously blocked on the caller *)
  Lemma aread_commit_at_unit Γ E i :
    ⊢ aread_commit_at Γ E i (fun _ _ _ => True%I).
  Proof.
    rewrite /aread_commit_at. iIntros (I off a) "%Hpre Ha".
    iModIntro. by iFrame "Ha".
  Qed.

  (* THE AGREEMENT AT THE RAW AUTHORITY.  [astate_nview] reads a client
     share against [astate]; every seed below needs the same reading with
     the AUTHORITY ITSELF still in hand, because the raw-map commit must
     hand back the very map it was given -- wrapping and unwrapping loses
     it (that is the whole finding this file exists for). *)
  Lemma arf_auth_nview Γ (I : gmap Z fs_node) (q : Qp) (i : Z) (a : anode) :
    ghost_map_auth (γtop Γ) 1 I -∗ nview Γ q i a -∗
    ⌜abs_view I !! i = Some a⌝.
  Proof.
    iIntros "Ha Hn".
    iAssert (astate Γ (abs_view I)) with "[Ha]" as "Hst".
    { iApply astate_intro. iExact "Ha". }
    iApply (astate_nview with "Hst Hn").
  Qed.

  (* THE STABLE SEEDS at the raw map, both of the frozen file's, so the
     stable corollary's derivation stays assembly rather than proof. *)
  Lemma aread_commit_at_pinned Γ E (i : Z) (q : Qp) (jpin : Z) (b : anode)
      (Φ : aview -> nat -> anode -> iProp Σ) :
    nview Γ q jpin b -∗
    (∀ (av : aview) (off : nat) (a : anode),
       ⌜av !! jpin = Some b⌝ -∗ nview Γ q jpin b -∗ Φ av off a) -∗
    aread_commit_at Γ E i Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /aread_commit_at.
    iIntros (I off a) "%Hpre Ha".
    iDestruct (arf_auth_nview with "Ha Hn") as %Hav.
    (* the reading is all the seed needs, and it is the borrow's own *)
    iModIntro. iFrame "Ha".
    iApply ("HΦ" $! (abs_view I) off a with "[%] Hn").
    exact Hav.
  Qed.

  (* read's own collapse: the pin is on the READ row, so agreement forces
     the observed node to be the client's *)
  Lemma aread_commit_at_pinned_self Γ E (i : Z) (q : Qp) (b : anode)
      (Φ : aview -> nat -> anode -> iProp Σ) :
    nview Γ q i b -∗
    (∀ (av : aview) (off : nat),
       ⌜av !! i = Some b⌝ -∗ nview Γ q i b -∗ Φ av off b) -∗
    aread_commit_at Γ E i Φ.
  Proof.
    iIntros "Hn HΦ". rewrite /aread_commit_at.
    iIntros (I off a) "%Hpre Ha".
    iDestruct (arf_auth_nview with "Ha Hn") as %Hav.
    destruct Hpre as (Hrow & _ & _).
    assert (a = b) as -> by congruence.
    iModIntro. iFrame "Ha".
    iApply ("HΦ" $! (abs_view I) off with "[%] Hn").
    exact Hav.
  Qed.

  (* =================================================================== *)
  (*  2.  THE FIRE                                                        *)
  (* =================================================================== *)

  (* [FsAbsOpenFire.opf_open_fire]'s mold at the read commit.  Any share
     suffices: the commit only reads.  The two caps are premises about the
     SAME node, which is where fileread has them (header). *)
  Lemma arf_read_fire (γfs : fs_names) (E : coPset) (dq : dfrac)
      (Φ : aview -> nat -> anode -> iProp Σ) (i : Z) (off : nat)
      (n : fs_node) :
    ↑ftopN ∪ ↑fsabsN ⊆ E ->
    (off <= MAXFILE * BSIZE)%nat ->
    anode_size_ok (abs_of n) ->
    ftop_inv γfs -∗
    aread_commit_at (fs_gamma_L γfs) fsabsE i Φ -∗
    top_frag_q (fs_gamma_L γfs) dq i n ={E}=∗
      top_frag_q (fs_gamma_L γfs) dq i n
      ∗ ∃ av : aview,
          ⌜av !! i = Some (abs_of n)⌝ ∗ Φ av off (abs_of n).
  Proof.
    intros HE Hoff Hsz. iIntros "#Hi Hcm Hf".
    (* the same re-spelling [opf_open_fire] does, and for the same reason:
       the unifier cannot solve [γtop ?Γ =?= fs_top γfs]. *)
    rewrite /top_frag_q /fs_gamma_L /=.
    iMod (inv_acc E ftopN with "Hi") as "[Hbody Hclose]"; [solve_ndisj |].
    iDestruct "Hbody" as ">Hb".
    iDestruct "Hb" as (I A) "(Hta & Hla & Hpark & %Hcl)".
    iDestruct (ghost_map_lookup with "Hta Hf") as %Hlk.
    assert (Hrow : abs_view I !! i = Some (abs_of n))
      by exact (abs_view_lookup I i n Hlk).
    assert (Hpre : ard_pre (abs_view I) i off (abs_of n))
      by (split; [exact Hrow | split; [exact Hoff | exact Hsz]]).
    iMod (fupd_mask_subseteq fsabsE) as "Hcl2"; [rewrite /fsabsE; solve_ndisj |].
    iMod ("Hcm" $! I off (abs_of n) with "[//] Hta") as "[Hta HΦ]".
    iMod "Hcl2".
    iMod ("Hclose" with "[Hta Hla Hpark]") as "_".
    { iNext. rewrite /ftop_body. iExists I, A. by iFrame. }
    iModIntro. iFrame "Hf". iExists (abs_view I).
    iSplitR; [by iPureIntro |]. iExact "HΦ".
  Qed.

  (* the [DfracOwn 1] reading, which is the spelling fileread holds
     ([top_frag] whole, from its [ilock] to its [iunlock]) *)
  Lemma arf_read_fire_1 (γfs : fs_names) (E : coPset)
      (Φ : aview -> nat -> anode -> iProp Σ) (i : Z) (off : nat)
      (n : fs_node) :
    ↑ftopN ∪ ↑fsabsN ⊆ E ->
    (off <= MAXFILE * BSIZE)%nat ->
    anode_size_ok (abs_of n) ->
    ftop_inv γfs -∗
    aread_commit_at (fs_gamma_L γfs) fsabsE i Φ -∗
    top_frag (fs_gamma_L γfs) i n ={E}=∗
      top_frag (fs_gamma_L γfs) i n
      ∗ ∃ av : aview,
          ⌜av !! i = Some (abs_of n)⌝ ∗ Φ av off (abs_of n).
  Proof.
    intros HE Hoff Hsz. rewrite top_frag_1.
    exact (arf_read_fire γfs E _ Φ i off n HE Hoff Hsz).
  Qed.

  (* =================================================================== *)
  (*  3.  THE STABLE COROLLARY, ASSEMBLED (prover item 7)                 *)
  (* =================================================================== *)

  (* THE RECEIPT THE STABLE DERIVATION INSTANTIATES THE AU AT: the client's
     own receipt, plus what agreement bought -- the observed row IS the
     client's value, and the share comes back.  This is what makes the
     derivation assembly rather than a second walk. *)
  Definition arf_pin_recv Γ (i : Z) (q : Qp) (b : anode)
      (Φr : aview -> nat -> anode -> iProp Σ)
      : aview -> nat -> anode -> iProp Σ :=
    fun av off a =>
      (⌜av !! i = Some b⌝ ∗ ⌜a = b⌝ ∗ nview Γ q i b ∗ Φr av off a)%I.

  (* THE COMPOSITION: a client that holds the share AND its own commit has
     the commit at the enriched receipt.  Agreement fires at the instant --
     the whole content of [aread_commit_at_pinned_self], now carrying the
     client's own commit through instead of discarding it. *)
  Lemma arf_pin_compose Γ E (i : Z) (q : Qp) (b : anode)
      (Φr : aview -> nat -> anode -> iProp Σ) :
    nview Γ q i b -∗
    aread_commit_at Γ E i Φr -∗
    aread_commit_at Γ E i (arf_pin_recv Γ i q b Φr).
  Proof.
    iIntros "Hn Hcm". rewrite /aread_commit_at.
    iIntros (I off a) "%Hpre Ha".
    iDestruct (arf_auth_nview with "Ha Hn") as %Hav.
    destruct Hpre as (Hrow & Hoff & Hsz).
    assert (a = b) as Hab by congruence.
    iMod ("Hcm" $! I off a with "[%] Ha") as "[Ha HΦ]".
    { split; [exact Hrow | split; [exact Hoff | exact Hsz]]. }
    iModIntro. iFrame "Ha". rewrite /arf_pin_recv.
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iFrame "Hn HΦ".
  Qed.

  (* ...AND THE ARMS COLLAPSE.  This is the whole of item 7 that does not
     touch the machine: instantiate the AU at [arf_pin_recv] and every arm
     lands at the client's own value.  NOTE WHERE [0 <= n] IS SPENT -- and
     it is spent exactly where the frozen header says it is: on the GUARD
     arm, whose refund would otherwise strand the wrapped share inside the
     returned closure.  With the premise that disjunct is refuted and both
     surviving arms carry a FIRED receipt, which is why read needs no
     escape arm where write does. *)
  (* ONE LEMMA PER ARM, and the split is not cosmetic: proved as a single
     two-arm entailment the tactics all run in about a second and the
     [Qed] then does not come back (measured: >20 min, 2.6 GB, killed).
     Both arms land in the SAME conclusion, so the kernel ends up checking
     one term that mentions [read_stable_arms]'s unfolding twice over; cut
     at the disjunction each half checks in a blink.  The [ard_pre] /
     [ard_ret_tie] readings below are taken by CONVERSION ([exact]) rather
     than by [cbn], which would also unfold [ard_count] and leave terms
     that no longer match the goal's. *)
  Lemma arf_stable_ok_arm Γ (i : Z) (nz : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (Φr : aview -> nat -> anode -> iProp Σ) (r : mword 64) :
    read_post_ok Γ i nz
      (arf_pin_recv Γ i q (MkAnode (AFile bs0) nl) Φr) r
    ⊢ read_stable_arms Γ i nz q bs0 nl Φr r.
  Proof.
    rewrite /read_post_ok /read_stable_arms /arf_pin_recv.
    iIntros "Hok".
    iDestruct "Hok" as (av off a)
      "(%Hpre & %Hnn & %Htie & %Hrow & %Hab & Hnv & HΦ)".
    subst a. destruct Hpre as (Hlk & Hoff & Hsz).
    assert (Hsz' : (length bs0 <= MAXFILE * BSIZE)%nat) by exact Hsz.
    assert (Htie' : r = (mword_of_int
               (Z.of_nat (ard_count (Z.to_nat nz) off (length bs0)))
             : mword 64)) by exact Htie.
    iFrame "Hnv". iExists av, off.
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; left; exact Htie' |].
    iExact "HΦ".
  Qed.

  (* WHERE [0 <= n] IS SPENT: on the GUARD arm, whose refund would strand
     the wrapped share inside the returned closure.  With the premise that
     disjunct is refuted, so the surviving arm carries a FIRED receipt --
     which is why read needs no escape arm where write does. *)
  Lemma arf_stable_fail_arm Γ (i : Z) (nz : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (Φr : aview -> nat -> anode -> iProp Σ) (r : mword 64) :
    0 <= nz ->
    r = (mword_of_int (-1) : mword 64) ->
    read_post_fail Γ i nz
      (arf_pin_recv Γ i q (MkAnode (AFile bs0) nl) Φr)
    ⊢ read_stable_arms Γ i nz q bs0 nl Φr r.
  Proof.
    intros Hnz Hr.
    rewrite /read_post_fail /read_stable_arms /arf_pin_recv.
    iIntros "[[%Hlt _] | [%Hge Hrest]]"; [exfalso; lia |].
    iDestruct "Hrest" as (av off a) "(%Hpre & %Hrow & %Hab & Hnv & HΦ)".
    subst a. destruct Hpre as (Hlk & Hoff & Hsz).
    assert (Hsz' : (length bs0 <= MAXFILE * BSIZE)%nat) by exact Hsz.
    iFrame "Hnv". iExists av, off.
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitR; [iPureIntro; right; exact Hr |].
    iExact "HΦ".
  Qed.

  (* ...AND THE ARMS COLLAPSE.  This is the whole of item 7 that does not
     touch the machine: instantiate the AU at [arf_pin_recv] and every arm
     lands at the client's own value. *)
  Lemma arf_stable_of_arms Γ (i : Z) (nz : Z) (q : Qp)
      (bs0 : list (bv 8)) (nl : nat)
      (Φr : aview -> nat -> anode -> iProp Σ) (r : mword 64) :
    0 <= nz ->
    read_arms Γ i nz
      (arf_pin_recv Γ i q (MkAnode (AFile bs0) nl) Φr) r
    ⊢ read_stable_arms Γ i nz q bs0 nl Φr r.
  Proof.
    intros Hnz. rewrite /read_arms.
    iIntros "[Hok | [%Hr Hfail]]".
    - iApply (arf_stable_ok_arm with "Hok").
    - iApply (arf_stable_fail_arm Γ i nz q bs0 nl Φr r Hnz Hr with "Hfail").
  Qed.

End ReadFire.
