(* InodeRegion.v -- THE INODE REGION: the dinode blocks' owner, and the
   per-inum fragment that replaces the coarse [fsblock] premise in every
   inode-layer contract.  Design: claude-notes/design/fs-icache.md, §11-§12.

   [FsBlocks.fsblock] is the write permission for a block, and a dinode
   block holds SIXTEEN inodes -- so any contract that takes the block's
   half for the duration of a call is unsatisfiable by two lock holders in
   the same block (§11.1).  The fix is a CHANGE OF GRANULARITY: callers
   hold [dinode_at γi inum dn], an exclusive per-inum ghost_map fragment,
   and the block halves never leave this region's invariant.

   ---- WHY THERE IS NO CHECKED-OUT ARM (§12) ----------------------------

   The first design (§11.4) had iupdate checking the block's half OUT of
   the region across its log_write and parking it back after.  That escrow
   cannot state its checked-out arm: during the window the thread's own
   log_write footprint ([bio_held] + the client half) holds EVERY per-block
   exclusive resource -- [disk_block] in full, both [fs_L] halves, the
   machinery dirty half -- so by conservation the arm has nothing to hold,
   and a checkout could never prove the arm is parked.

   So the region is ONE-ARMED, and the only moment the client half leaves
   it is log_write's own ghost step (ProofLogWrite.v's [fsblock_update], a
   single [iMod] between two instruction dispatches, at mask ⊤).
   [ireg_write_au] below is the atomic update iupdate hands to the
   generalized SpecLogWrite premise: it opens the region THERE, lets
   [fsblock_update] run against the withdrawn half, and re-parks the block
   at the new bytes while retagging the caller's [dinode_at] in the same
   opening.  [ireg_read] is ilock's side: one mask-preserving opening in
   which the caller's payload machinery half pins the region's bytes and
   the coupling turns its [dinode_at] into [ds !!! islot inum = dn] --
   which is how [SpecIlock]'s "vv = false -> ds !!! islot inum = dn"
   premise stops being expressible rather than getting discharged (§11.3).

   ---- THE COUPLING, AND ONE NEW PURE FACT ------------------------------

   The invariant holds the ghost map's authority beside the block halves,
   with a pure coupling: slot [i] of block [bi]'s parked list IS the map's
   value at inum [16*bi + i].  Re-establishing the coupling after a write
   needs to know the parked list has not moved between iupdate's bread
   (where the caller learns [ds]) and its log_write (where the region is
   opened again).  Nothing the thread holds pins the LIST -- only its
   BYTES, via the machinery half riding in the thread's own payload -- so
   the bridge is [diblk_bytes_inj]: the encoding is injective on
   well-formed lists (§12.3).  Proved here from [bv_eq_of_bytes].

   ---- WHAT IS DELIBERATELY NOT HERE ------------------------------------

   The boot-time allocation (building the initial map from the mkfs
   image's dinode blocks and minting every [dinode_at]) is fsinit wiring
   and lives in [IcacheBoot.v], not here.  The icache pool that HOLDS the
   fragments of uncached inodes is IcacheInv's (design §10.4).            *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import invariants ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvPtsto.
Require Import RiscvModelBytes.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import BlockWords.
Require Import DinodeEnc.
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE ENCODING IS INJECTIVE ON WELL-FORMED LISTS (§12.3)            *)
(* ===================================================================== *)

(* a 16-bit field is determined by its two bytes *)
Lemma half_bytes_inj (w1 w2 : bv 16) :
  half_bytes w1 = half_bytes w2 -> w1 = w2.
Proof.
  intros H.
  apply (bv_eq_of_bytes (n := 2%N) w1 w2).
  intros j Hj.
  assert (Hj2 : (j < 2)%nat) by lia.
  pose proof (half_bytes_lookup w1 j Hj2) as L1.
  pose proof (half_bytes_lookup w2 j Hj2) as L2.
  rewrite H in L1. rewrite L2 in L1.
  apply (inj Some). exact (eq_sym L1).
Qed.

(* ...and a 32-bit one by its four *)
Lemma word_bytes_inj (w1 w2 : bv 32) :
  word_bytes w1 = word_bytes w2 -> w1 = w2.
Proof.
  intros H.
  apply (bv_eq_of_bytes (n := 4%N) w1 w2).
  intros j Hj.
  assert (Hj4 : (j < 4)%nat) by lia.
  pose proof (word_bytes_lookup w1 j Hj4) as L1.
  pose proof (word_bytes_lookup w2 j Hj4) as L2.
  rewrite H in L1. rewrite L2 in L1.
  apply (inj Some). exact (eq_sym L1).
Qed.

Lemma ind_bytes_inj (e1 e2 : list (bv 32)) :
  length e1 = length e2 ->
  ind_bytes e1 = ind_bytes e2 -> e1 = e2.
Proof.
  revert e2. induction e1 as [|w1 e1 IH]; intros [|w2 e2] Hlen H;
    [reflexivity | discriminate | discriminate |].
  rewrite !ind_bytes_cons in H.
  apply app_inj_1 in H as [Hw He];
    [| rewrite !word_bytes_length; reflexivity].
  f_equal.
  - exact (word_bytes_inj _ _ Hw).
  - apply IH; [by injection Hlen | exact He].
Qed.

Lemma dinode_bytes_inj (d1 d2 : dinode) :
  dinode_wf d1 -> dinode_wf d2 ->
  dinode_bytes d1 = dinode_bytes d2 -> d1 = d2.
Proof.
  intros H1 H2 H. unfold dinode_bytes in H.
  apply app_inj_1 in H as [Hty H];
    [| rewrite !half_bytes_length; reflexivity].
  apply app_inj_1 in H as [Hmaj H];
    [| rewrite !half_bytes_length; reflexivity].
  apply app_inj_1 in H as [Hmin H];
    [| rewrite !half_bytes_length; reflexivity].
  apply app_inj_1 in H as [Hnl H];
    [| rewrite !half_bytes_length; reflexivity].
  apply app_inj_1 in H as [Hsz Had];
    [| rewrite !word_bytes_length; reflexivity].
  unfold dinode_wf in H1, H2.
  destruct d1, d2; cbn in *.
  f_equal.
  - exact (half_bytes_inj _ _ Hty).
  - exact (half_bytes_inj _ _ Hmaj).
  - exact (half_bytes_inj _ _ Hmin).
  - exact (half_bytes_inj _ _ Hnl).
  - exact (word_bytes_inj _ _ Hsz).
  - apply ind_bytes_inj; [congruence | exact Had].
Qed.

Lemma diblk_bytes_inj_aux (ds1 ds2 : list dinode) :
  length ds1 = length ds2 ->
  Forall dinode_wf ds1 -> Forall dinode_wf ds2 ->
  diblk_bytes ds1 = diblk_bytes ds2 -> ds1 = ds2.
Proof.
  revert ds2. induction ds1 as [|d1 ds1 IH]; intros [|d2 ds2] Hlen Hw1 Hw2 H;
    [reflexivity | discriminate | discriminate |].
  inversion Hw1 as [|? ? Hd1 Hds1]; subst.
  inversion Hw2 as [|? ? Hd2 Hds2]; subst.
  rewrite !diblk_bytes_cons in H.
  apply app_inj_1 in H as [Hd Hds];
    [| rewrite (dinode_bytes_length d1 Hd1) (dinode_bytes_length d2 Hd2);
       reflexivity].
  f_equal.
  - exact (dinode_bytes_inj d1 d2 Hd1 Hd2 Hd).
  - apply IH; [by injection Hlen | exact Hds1 | exact Hds2 | exact Hds].
Qed.

(* THE §12.3 OBLIGATION.  This is what lets iupdate conclude the region's
   parked list at log_write time is the one it read at bread time: its own
   payload's machinery half pinned the BYTES the whole way, and the bytes
   determine the list. *)
Lemma diblk_bytes_inj (ds1 ds2 : list dinode) :
  diblk_wf ds1 -> diblk_wf ds2 ->
  diblk_bytes ds1 = diblk_bytes ds2 -> ds1 = ds2.
Proof.
  intros [Hl1 Hw1] [Hl2 Hw2].
  apply diblk_bytes_inj_aux; [congruence | exact Hw1 | exact Hw2].
Qed.

(* the slot update a flush performs keeps the block well formed *)
Lemma diblk_wf_insert (ds : list dinode) (k : nat) (d : dinode) :
  diblk_wf ds -> dinode_wf d -> diblk_wf (<[k := d]> ds).
Proof.
  intros [Hlen Hall] Hd. split.
  - rewrite length_insert. exact Hlen.
  - apply Forall_insert; [exact Hall | exact Hd].
Qed.

(* ===================================================================== *)
(*  2.  THE inum <-> (block, slot) ARITHMETIC                             *)
(* ===================================================================== *)

(* block index [bi] (relative to inodestart) of an inum, as a nat *)
Definition ireg_bi (inum : bv 32) : nat := Z.to_nat (bv_unsigned inum / 16).

Lemma ireg_bi_iblock (inum : bv 32) (inodestart : Z) :
  IBLOCK inum inodestart = inodestart + Z.of_nat (ireg_bi inum).
Proof.
  unfold IBLOCK, ireg_bi.
  pose proof (bv_unsigned_in_range _ inum) as [Hlo _].
  rewrite Z2Nat.id; [lia |].
  apply Z.div_pos; lia.
Qed.

(* the key the coupling files an inum under IS the inum *)
Lemma ireg_key_split (inum : bv 32) :
  bv_unsigned inum
  = 16 * Z.of_nat (ireg_bi inum) + Z.of_nat (islot inum).
Proof.
  unfold ireg_bi, islot.
  pose proof (bv_unsigned_in_range _ inum) as [Hlo _].
  pose proof (Z.mod_pos_bound (bv_unsigned inum) 16 ltac:(lia)) as Hm.
  pose proof (Z.div_pos (bv_unsigned inum) 16 Hlo ltac:(lia)) as Hd.
  rewrite !Z2Nat.id; [| lia | lia].
  pose proof (Z.div_mod (bv_unsigned inum) 16 ltac:(lia)). lia.
Qed.

Lemma ireg_bi_lt (inum : bv 32) (nib : nat) :
  bv_unsigned inum < 16 * Z.of_nat nib -> (ireg_bi inum < nib)%nat.
Proof.
  intros Hin. unfold ireg_bi.
  pose proof (bv_unsigned_in_range _ inum) as [Hlo _].
  assert (Hq : bv_unsigned inum / 16 < Z.of_nat nib)
    by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

(* two slots of ONE block have distinct keys; a slot of ANOTHER block has a
   distinct key.  Both are the same fact, and it is what keeps a one-inum
   update from disturbing any other slot's coupling. *)
Lemma ireg_key_inj (j1 j2 i1 i2 : nat) :
  (i1 < 16)%nat -> (i2 < 16)%nat ->
  (16 * Z.of_nat j1 + Z.of_nat i1)%Z = (16 * Z.of_nat j2 + Z.of_nat i2)%Z ->
  j1 = j2 /\ i1 = i2.
Proof. intros H1 H2 Heq. lia. Qed.

(* ===================================================================== *)
(*  3.  THE GHOST, AND WHAT A CALLER HOLDS                                *)
(* ===================================================================== *)

Class iregG (Σ : gFunctors) := IregG {
  ireg_inG :: ghost_mapG Σ Z dinode;
}.
Definition iregΣ : gFunctors := #[ghost_mapΣ Z dinode].
Global Instance subG_iregΣ {Σ} : subG iregΣ Σ -> iregG Σ.
Proof. solve_inG. Qed.

Section InodeRegion.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ, !iregG Σ}.

  (* THE per-inum resource: this inum's on-disk record is [dn].  EXCLUSIVE
     (a full-fraction ghost_map element), keyed by the inum's value; the
     block address falls out of [IBLOCK] and never needs a second ghost.
     This is what replaces [fsblock γfs (IBLOCK inum inodestart)
     (diblk_bytes ds)] in SpecIupdate / SpecIlock / SpecWritei /
     SpecItrunc / SpecFileread (§11.3). *)
  Definition dinode_at (γi : gname) (inum : bv 32) (dn : dinode) : iProp Σ :=
    bv_unsigned inum ↪[γi] dn.

  Global Instance dinode_at_timeless γi inum dn :
    Timeless (dinode_at γi inum dn).
  Proof. rewrite /dinode_at. apply _. Qed.

  Lemma dinode_at_excl γi inum dn1 dn2 :
    dinode_at γi inum dn1 -∗ dinode_at γi inum dn2 -∗ False.
  Proof.
    rewrite /dinode_at. iIntros "H1 H2".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv _].
    exfalso. exact (exclusive_l (DfracOwn 1) (DfracOwn 1) Hv).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The invariant                                                      *)
  (* ------------------------------------------------------------------ *)

  (* slot [i] of block [bi]'s parked list is the map's value at the inum
     that lives there *)
  Definition ireg_couple (m : gmap Z dinode) (bi : nat) (ds : list dinode)
    : Prop :=
    forall i : nat, (i < 16)%nat ->
      m !! (16 * Z.of_nat bi + Z.of_nat i)%Z = Some (ds !!! i).

  Definition ireg_blk (γfs : fs_names) (inodestart : Z)
      (m : gmap Z dinode) (bi : nat) : iProp Σ :=
    (∃ ds : list dinode,
       ⌜diblk_wf ds⌝ ∗ ⌜ireg_couple m bi ds⌝ ∗
       fsblock γfs (inodestart + Z.of_nat bi) (diblk_bytes ds))%I.

  Definition ireg_body (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) : iProp Σ :=
    (∃ m : gmap Z dinode,
       ghost_map_auth γi 1 m ∗
       [∗ list] bi ∈ seq 0 nib, ireg_blk γfs inodestart m bi)%I.

  Definition iregN : namespace := nroot .@ "ireg".

  Definition ireg_inv (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) : iProp Σ :=
    inv iregN (ireg_body γi γfs inodestart nib).

  Global Instance ireg_inv_persistent γi γfs inodestart nib :
    Persistent (ireg_inv γi γfs inodestart nib).
  Proof. apply _. Qed.

  Global Instance ireg_blk_timeless γfs inodestart m bi :
    Timeless (ireg_blk γfs inodestart m bi).
  Proof. rewrite /ireg_blk /fsblock. apply _. Qed.

  Global Instance ireg_body_timeless γi γfs inodestart nib :
    Timeless (ireg_body γi γfs inodestart nib).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  The block accessor (writer form)                                   *)
  (* ------------------------------------------------------------------ *)

  (* a block's conjunct only reads the map at its OWN sixteen keys *)
  Lemma ireg_blk_mono (γfs : fs_names) (inodestart : Z)
      (m m' : gmap Z dinode) (bi : nat) :
    (forall i : nat, (i < 16)%nat ->
       m' !! (16 * Z.of_nat bi + Z.of_nat i)%Z
       = m !! (16 * Z.of_nat bi + Z.of_nat i)%Z) ->
    ireg_blk γfs inodestart m bi -∗ ireg_blk γfs inodestart m' bi.
  Proof.
    intros Hag. rewrite /ireg_blk.
    iIntros "(%ds & %Hwf & %Hcp & Hfsb)".
    iExists ds. iFrame "Hfsb". iSplitR; [done |].
    iPureIntro. intros i Hi. rewrite (Hag i Hi). exact (Hcp i Hi).
  Qed.

  (* the big-op's slot [bi], with the rest re-buildable at a map that
     changed only at [bi]'s keys -- IcacheInv.islots_acc_upd's shape *)
  Lemma ireg_blks_acc_upd (γfs : fs_names) (inodestart : Z)
      (m : gmap Z dinode) (nib bi : nat) :
    (bi < nib)%nat ->
    ([∗ list] j ∈ seq 0 nib, ireg_blk γfs inodestart m j) -∗
      ireg_blk γfs inodestart m bi ∗
      (∀ m' : gmap Z dinode,
         ⌜forall (j i : nat), j <> bi -> (i < 16)%nat ->
            m' !! (16 * Z.of_nat j + Z.of_nat i)%Z
            = m !! (16 * Z.of_nat j + Z.of_nat i)%Z⌝ -∗
         ireg_blk γfs inodestart m' bi -∗
         [∗ list] j ∈ seq 0 nib, ireg_blk γfs inodestart m' j).
  Proof.
    intros Hbi. iIntros "Hs".
    iDestruct (big_sepL_delete _ (seq 0 nib) bi bi
                 ltac:(apply lookup_seq; split; [lia | exact Hbi]) with "Hs")
      as "[Hblk Hrest]".
    iFrame "Hblk". iIntros (m') "%Hag Hblk".
    iApply (big_sepL_delete _ (seq 0 nib) bi bi
              ltac:(apply lookup_seq; split; [lia | exact Hbi])).
    iFrame "Hblk".
    iApply (big_sepL_impl with "Hrest").
    iIntros "!>" (j x Hjx) "H".
    destruct (decide (j = bi)) as [->|Hne]; [iExact "H" |].
    apply lookup_seq in Hjx as [Hx _].
    iApply (ireg_blk_mono with "H").
    intros i Hi. apply Hag; [lia | exact Hi].
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  ilock's READ (§12.2): one mask-preserving opening                  *)
  (* ------------------------------------------------------------------ *)

  (* The caller is between bread and brelse, so its handle's payload
     carries the block's machinery half at the returned bytes [bsl]; that
     half against the region's client half pins [bsl] to the parked list's
     bytes, and the coupling against [dinode_at] names the caller's slot.
     Everything goes back; only pure facts come out. *)
  Lemma ireg_read (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn : dinode)
      (b : Z) (bsl : list (bv 8)) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    b = IBLOCK inum inodestart ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    (b ↪[fs_L γfs]{#(1/2)} bsl) ={E}=∗
    ⌜exists ds : list dinode,
       diblk_wf ds /\ bsl = diblk_bytes ds /\ ds !!! islot inum = dn⌝ ∗
    dinode_at γi inum dn ∗ (b ↪[fs_L γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE Hin Hb) "#Hinv Hdn Hhalf".
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds) "(>%Hwf & >%Hcp & >Hfsb)".
    rewrite /fsblock -(ireg_bi_iblock inum inodestart) -Hb.
    iDestruct (ghost_map_elem_agree with "Hhalf Hfsb") as %Hbytes.
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    assert (Hslot : ds !!! islot inum = dn).
    { pose proof (islot_lt inum) as Hsl.
      specialize (Hcp (islot inum) Hsl).
      rewrite -ireg_key_split in Hcp. congruence. }
    iMod ("Hclose" with "[Ha Hfsb Hback]") as "_".
    { iNext. iExists m. iFrame "Ha".
      iApply ("Hback" $! m with "[%] [Hfsb]"); [done |].
      iExists ds. rewrite /fsblock (ireg_bi_iblock inum inodestart) in Hb.
      rewrite Hb. by iFrame "Hfsb". }
    iModIntro. iFrame "Hdn Hhalf". iPureIntro.
    exists ds. auto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  iupdate's WRITE (§12.2): the atomic update log_write fires          *)
  (* ------------------------------------------------------------------ *)

  (* Exactly the shape SpecLogWrite's generalized fsblock premise takes:
     the fupd opens the region and surrenders the block's client half at
     whatever the parked bytes are; log_write's own [fsblock_update]
     agreement (against the machinery half in the caller's handle) is what
     delivers [bsl' = diblk_bytes ds], and [diblk_bytes_inj] then pins the
     parked LIST to the [ds] the caller learned at its bread.  The closing
     wand takes the half back at the flushed bytes, retags the caller's
     [dinode_at] against the authority, and re-couples the block. *)
  Lemma ireg_write_au (E : coPset) (γi : gname) (γfs : fs_names)
      (inodestart : Z) (nib : nat) (inum : bv 32) (dn dn' : dinode)
      (ds : list dinode) :
    ↑iregN ⊆ E ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    diblk_wf ds ->
    dinode_wf dn' ->
    ireg_inv γi γfs inodestart nib -∗
    dinode_at γi inum dn -∗
    |={E, E ∖ ↑iregN}=> ∃ bsl' : list (bv 8),
      fsblock γfs (IBLOCK inum inodestart) bsl' ∗
      (⌜bsl' = diblk_bytes ds⌝ -∗
       fsblock γfs (IBLOCK inum inodestart)
               (diblk_bytes (<[islot inum := dn']> ds))
       ={E ∖ ↑iregN, E}=∗ dinode_at γi inum dn').
  Proof.
    iIntros (HE Hin Hwf Hdn') "#Hinv Hdn".
    iMod (inv_acc E iregN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (m) "(>Ha & Hblks)".
    pose proof (ireg_bi_lt inum nib Hin) as Hbi.
    iDestruct (ireg_blks_acc_upd γfs inodestart m nib (ireg_bi inum) Hbi
                with "Hblks") as "[Hblk Hback]".
    iDestruct "Hblk" as (ds0) "(>%Hwf0 & >%Hcp0 & >Hfsb)".
    iModIntro.
    rewrite (ireg_bi_iblock inum inodestart).
    iExists (diblk_bytes ds0).
    iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    (* the parked list IS the caller's: bytes equal, both wf, encode inj *)
    assert (Hds0 : ds0 = ds) by exact (diblk_bytes_inj ds0 ds Hwf0 Hwf Hbytes).
    subst ds0.
    (* retag the caller's fragment against the authority *)
    rewrite /dinode_at.
    iDestruct (ghost_map_lookup with "Ha Hdn") as %Hm.
    iMod (ghost_map_update dn' with "Ha Hdn") as "[Ha Hdn]".
    set (m' := <[bv_unsigned inum := dn']> m).
    (* re-park the block at the flushed bytes, re-coupled at m' *)
    iMod ("Hclose" with "[Ha Hfsb' Hback]") as "_".
    { iNext. iExists m'. iFrame "Ha".
      iApply ("Hback" $! m' with "[%] [Hfsb']").
      { (* other blocks' keys never collide with this inum's *)
        intros j i Hne Hi. rewrite /m' lookup_insert_ne; [done |].
        rewrite (ireg_key_split inum). intros Hc.
        pose proof (islot_lt inum) as Hsl.
        destruct (ireg_key_inj (ireg_bi inum) j (islot inum) i Hsl Hi Hc)
          as [Hj _].
        exact (Hne (eq_sym Hj)). }
      iExists (<[islot inum := dn']> ds).
      iSplitR; [iPureIntro; exact (diblk_wf_insert ds (islot inum) dn' Hwf Hdn') |].
      iSplitR.
      { iPureIntro. intros i Hi.
        pose proof (islot_lt inum) as Hsl.
        destruct Hwf as [Hlen _].
        destruct (decide (i = islot inum)) as [->|Hne].
        - rewrite /m' -(ireg_key_split inum) lookup_insert.
          rewrite list_lookup_total_insert; [done | lia].
        - rewrite /m' lookup_insert_ne; last first.
          { rewrite (ireg_key_split inum). intros Hc.
            destruct (ireg_key_inj (ireg_bi inum) (ireg_bi inum)
                        (islot inum) i Hsl Hi Hc) as [_ Hi'].
            exact (Hne (eq_sym Hi')). }
          rewrite list_lookup_total_insert_ne; [| by apply not_eq_sym].
          exact (Hcp0 i Hi). }
      iExact "Hfsb'". }
    iModIntro. iExact "Hdn".
  Qed.

End InodeRegion.
