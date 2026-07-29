(* ====================================================================== *)
(* DiskPtsto.v -- the disk points-to.                                      *)
(*                                                                         *)
(* The virtio disk's image is a total function [v_disk : Z -> bv 8].  The  *)
(* driver-facing resource for it is a byte-granularity ghost map: the      *)
(* AUTH rides inside the device invariant (VirtioProto.v), tied to the     *)
(* image by [disk_view] -- the exact analogue of [mem_view]: a fragment    *)
(* exists only for offsets somebody minted, and the model's disk stays     *)
(* total underneath.  [disk_bytes]/[disk_block] are the derived forms the  *)
(* function specs use ([virtio_disk_rw] moves a whole 1024-byte block).   *)
(*                                                                         *)
(* This file also owns the OTHER driver-protocol ghosts, so a single       *)
(* [disk_names] record travels through [dev_inv] (mirroring [uart_names]): *)
(*   dn_img  -- the disk image map above;                                  *)
(*   dn_slot -- ghost_map nat vslot: the auth covers every in-flight       *)
(*              request; the FRAGMENT for position [p] is the publisher's  *)
(*              RECEIPT, and presenting it is what licenses the reclaim;   *)
(*   dn_nc   -- mono_nat over the completed count: an interrupt handler's  *)
(*              used-index read mints a persistent lower bound that        *)
(*              survives to its later per-slot reads;                      *)
(*   dn_np   -- ghost_var nat over the published count: the OTHER half     *)
(*              lives in the vdisk_lock's resource, so only a lock holder  *)
(*              can publish, and a lock holder KNOWS the published index.  *)
(*                                                                         *)
(* Design rationale: claude-notes/design/virtio-driver.md.                 *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own ghost_map ghost_var mono_nat.
From iris.algebra.lib Require Import dfrac_agree.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import VirtioModel.
Require Import VirtioQueue.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* THE CLAIM VALUE.                                                        *)
(*                                                                         *)
(* [dn_claim] is the publisher's private handle on its own position, and    *)
(* the ONLY thing a process that slept through the request still holds      *)
(* when it wakes.  So every fact the woken publisher needs about "its"      *)
(* request has to be recoverable from the claim's VALUE -- recovering the   *)
(* [struct buf] alone would not even tell it that the parked payoff is the  *)
(* one IT published.  Four fields, one per downstream obligation:           *)
(*                                                                         *)
(*   dc_buf   the [struct buf]: which cache entry the payoff belongs to;    *)
(*   dc_slot  the published slot: fixes [vs_data] (a write's payload) and   *)
(*            [vs_sector_off] (which block), i.e. the postcondition's       *)
(*            [disk_block bno (if wr then bs_buf else bs_disk)];            *)
(*   dc_tri   the three descriptors of the chain: [disk_res] ties it to     *)
(*            the triple map, whose "no member is free" conjunct is what    *)
(*            tells the woken publisher its descriptors were NOT recycled   *)
(*            while it slept -- hence that [free_desc] may have them back;  *)
(*   dc_pin   the pinned bytes: [free_chain] has to take the descriptor     *)
(*            entries apart again, and the reclaim payoff hands them back   *)
(*            as one opaque [phys_map].  Naming the map is what lets the    *)
(*            publisher split it back into the windows it wrote.            *)
(* ---------------------------------------------------------------------- *)
Record dclaim := DClaim {
  dc_buf  : Arch.pa;
  dc_slot : vslot;
  dc_tri  : nat * nat * nat;
  dc_pin  : gmap Arch.pa (bv 8);
}.

(* ---------------------------------------------------------------------- *)
(* the ghost classes and the name bundle                                   *)
(* ---------------------------------------------------------------------- *)

Class diskGhostG (Σ : gFunctors) := DiskGhostG {
  disk_img_inG  :: ghost_mapG Σ Z (bv 8);
  (* a receipt records the slot AND the pin map deposited at publish *)
  disk_slot_inG :: ghost_mapG Σ nat (vslot * gmap Arch.pa (bv 8));
  disk_nc_inG   :: mono_natG Σ;
  disk_np_inG   :: ghost_varG Σ nat;
  (* the publisher's private claim map: dom = the positions whose state is
     still live in disk_res (in flight or parked); the fragment is how a
     sleeping rw re-finds its own request (DiskInv.v).  See [dclaim]. *)
  disk_claim_inG :: ghost_mapG Σ nat dclaim;
  (* the LIVE configuration, frozen: the invariant publishes it as a
     persistent fact so a driver can tie [v_cfg v] to the pages it
     programmed at init (see [disk_cfg] below) *)
  disk_cfg_inG :: inG Σ (dfrac_agreeR (leibnizO virtio_cfg));
}.

Definition diskGhostΣ : gFunctors :=
  #[ghost_mapΣ Z (bv 8); ghost_mapΣ nat (vslot * gmap Arch.pa (bv 8));
    mono_natΣ; ghost_varΣ nat; ghost_mapΣ nat dclaim;
    GFunctor (dfrac_agreeR (leibnizO virtio_cfg))].

Global Instance subG_diskGhostG Σ : subG diskGhostΣ Σ -> diskGhostG Σ.
Proof. solve_inG. Qed.

Record disk_names := DiskNames {
  dn_img   : gname;
  dn_slot  : gname;
  dn_nc    : gname;
  dn_np    : gname;
  dn_claim : gname;
  dn_cfg   : gname;
}.

(* ---------------------------------------------------------------------- *)
(* the disk view and the points-to                                         *)
(* ---------------------------------------------------------------------- *)

Definition disk_view (dmap : gmap Z (bv 8)) (dk : Z -> bv 8) : Prop :=
  forall (o : Z) (b : bv 8), dmap !! o = Some b -> dk o = b.

(* peeling the first byte off a disk range read *)
Lemma disk_read_cons (dk : Z -> bv 8) (o : Z) (n : nat) :
  disk_read dk o (S n) = dk o :: disk_read dk (o + 1) n.
Proof.
  assert (Htail : (fun j : nat => dk (o + Z.of_nat j)) <$> seq 1 n
                  = (fun j : nat => dk (o + 1 + Z.of_nat j)) <$> seq 0 n).
  { apply list_eq. intro i. rewrite !list_lookup_fmap.
    destruct (decide (i < n)%nat) as [Hi|Hi].
    - rewrite (lookup_seq_lt 1 n i Hi) (lookup_seq_lt 0 n i Hi).
      cbn [fmap option_fmap option_map]. do 2 f_equal. lia.
    - rewrite (lookup_seq_ge 1 n i); [| lia].
      rewrite (lookup_seq_ge 0 n i); [| lia]. reflexivity. }
  unfold disk_read. cbn [seq]. rewrite fmap_cons.
  assert (Hz : o + Z.of_nat 0%nat = o) by lia. rewrite Hz.
  f_equal. exact Htail.
Qed.

Section DiskPtsto.
  Context `{!diskGhostG Σ}.

  (* -- the frozen live configuration ------------------------------------ *)

  (* [virtio_disk_init] freezes the configuration it programmed into this
     persistent fact.  A driver holding it and the copy the device invariant
     exports (from any accessor) learns [v_cfg v = the config it programmed],
     hence the three queue-page addresses.

     BEFORE the freeze the SAME cell is the boot chain's CONFIG TRACKER: the
     not-live arm of [virtio_proto] holds [disk_cfg_is γ (DfracOwn (1/2))
     (v_cfg v)] and the driver holds the other half, so a boot chain that
     programs the queue from inside the device invariant keeps deterministic
     knowledge of the configuration it has written so far (the device never
     touches [v_cfg], so the pair is stable across device steps), and the two
     halves recombine to the exclusive fraction exactly at the live flip,
     which is what [disk_cfg_set] consumes.  One cell serves both roles: a
     separate ghost_var over the same object would be redundant. *)
  Definition disk_cfg_is (γ : disk_names) (dq : dfrac) (c : virtio_cfg)
    : iProp Σ := own (dn_cfg γ) (to_dfrac_agree dq (c : leibnizO virtio_cfg)).

  Definition disk_cfg (γ : disk_names) (c : virtio_cfg) : iProp Σ :=
    disk_cfg_is γ DfracDiscarded c.

  Global Instance disk_cfg_persistent γ c : Persistent (disk_cfg γ c).
  Proof. rewrite /disk_cfg /disk_cfg_is. apply _. Qed.
  Global Instance disk_cfg_timeless γ c : Timeless (disk_cfg γ c).
  Proof. rewrite /disk_cfg /disk_cfg_is. apply _. Qed.
  Global Instance disk_cfg_is_timeless γ dq c : Timeless (disk_cfg_is γ dq c).
  Proof. rewrite /disk_cfg_is. apply _. Qed.

  Lemma disk_cfg_agree (γ : disk_names) (c c' : virtio_cfg) :
    disk_cfg γ c -∗ disk_cfg γ c' -∗ ⌜c = c'⌝.
  Proof.
    iIntros "Ha Hb". rewrite /disk_cfg /disk_cfg_is.
    by iDestruct (own_valid_2 with "Ha Hb") as %[_ ?]%dfrac_agree_op_valid_L.
  Qed.

  (* the tracker form: any two views of the cell agree on the value.  This is
     what makes the boot chain's half deterministic knowledge -- it is the one
     lemma [virtio_disk_init]'s caller uses to identify the configuration it
     was handed with the one the invariant currently holds. *)
  Lemma disk_cfg_is_agree (γ : disk_names) (dq dq' : dfrac) (c c' : virtio_cfg) :
    disk_cfg_is γ dq c -∗ disk_cfg_is γ dq' c' -∗ ⌜c = c'⌝.
  Proof.
    iIntros "Ha Hb". rewrite /disk_cfg_is.
    by iDestruct (own_valid_2 with "Ha Hb") as %[_ ?]%dfrac_agree_op_valid_L.
  Qed.

  (* the exclusive fraction splits into the invariant's half and the driver's,
     and rejoins for [disk_cfg_set] at the live flip *)
  Lemma disk_cfg_is_split (γ : disk_names) (c : virtio_cfg) :
    disk_cfg_is γ (DfracOwn 1) c -∗
    disk_cfg_is γ (DfracOwn (1/2)) c ∗ disk_cfg_is γ (DfracOwn (1/2)) c.
  Proof.
    iIntros "H". rewrite /disk_cfg_is.
    iEval (rewrite -Qp.half_half -dfrac_op_own dfrac_agree_op own_op) in "H".
    iDestruct "H" as "[$ $]".
  Qed.

  Lemma disk_cfg_is_join (γ : disk_names) (c c' : virtio_cfg) :
    disk_cfg_is γ (DfracOwn (1/2)) c -∗ disk_cfg_is γ (DfracOwn (1/2)) c' -∗
    disk_cfg_is γ (DfracOwn 1) c.
  Proof.
    iIntros "Ha Hb".
    iDestruct (disk_cfg_is_agree with "Ha Hb") as %<-.
    rewrite /disk_cfg_is.
    iEval (rewrite -Qp.half_half -dfrac_op_own dfrac_agree_op own_op).
    iFrame "Ha Hb".
  Qed.

  Lemma disk_cfg_alloc (c : virtio_cfg) :
    ⊢ |==> ∃ g : gname, own g (to_dfrac_agree (DfracOwn 1) (c : leibnizO virtio_cfg)).
  Proof. iApply own_alloc. done. Qed.

  (* set the value (full fraction is exclusive) and then freeze it *)
  Lemma disk_cfg_set (γ : disk_names) (c c' : virtio_cfg) :
    disk_cfg_is γ (DfracOwn 1) c ==∗ disk_cfg γ c'.
  Proof.
    iIntros "H". rewrite /disk_cfg_is /disk_cfg /disk_cfg_is.
    iMod (own_update _ _ (to_dfrac_agree (DfracOwn 1) (c' : leibnizO virtio_cfg))
            with "H") as "H".
    { apply cmra_update_exclusive. done. }
    iApply (own_update with "H"). apply dfrac_agree_persist.
  Qed.

  (* -- the disk points-to ----------------------------------------------- *)

  Definition disk_byte (γ : disk_names) (o : Z) (b : bv 8) : iProp Σ :=
    o ↪[dn_img γ] b.

  Definition disk_bytes (γ : disk_names) (o : Z) (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] j ↦ b ∈ bs, disk_byte γ (o + Z.of_nat j) b)%I.

  (* the block form [virtio_disk_rw]'s spec moves: xv6's BSIZE = 1024 *)
  Definition disk_block (γ : disk_names) (bno : Z) (bs : list (bv 8)) : iProp Σ :=
    (⌜length bs = 1024%nat⌝ ∗ disk_bytes γ (1024 * bno) bs)%I.

  Global Instance disk_byte_timeless γ o b : Timeless (disk_byte γ o b).
  Proof. apply _. Qed.
  Global Instance disk_bytes_timeless γ o bs : Timeless (disk_bytes γ o bs).
  Proof. apply _. Qed.
  Global Instance disk_block_timeless γ bno bs : Timeless (disk_block γ bno bs).
  Proof. apply _. Qed.

  (* -- structural peeling ----------------------------------------------- *)

  Lemma disk_bytes_cons (γ : disk_names) (o : Z) (b : bv 8) (bs : list (bv 8)) :
    disk_bytes γ o (b :: bs) ⊣⊢ disk_byte γ o b ∗ disk_bytes γ (o + 1) bs.
  Proof.
    rewrite /disk_bytes big_sepL_cons. cbv beta.
    assert (Hz : o + Z.of_nat 0%nat = o) by lia. rewrite Hz.
    apply bi.sep_proper; [reflexivity|].
    apply big_sepL_proper. intros k y _.
    assert (Hs : o + Z.of_nat (S k) = o + 1 + Z.of_nat k) by lia.
    rewrite Hs. reflexivity.
  Qed.

  (* -- agreement: fragments read the image ------------------------------ *)

  Lemma disk_bytes_read (γ : disk_names) (dmap : gmap Z (bv 8))
      (dk : Z -> bv 8) (o : Z) (bs : list (bv 8)) :
    disk_view dmap dk ->
    ghost_map_auth (dn_img γ) 1 dmap -∗ disk_bytes γ o bs -∗
    ⌜disk_read dk o (length bs) = bs⌝.
  Proof.
    iIntros (Hview) "Hauth Hbs".
    iAssert (⌜forall (j : nat) (b : bv 8),
               bs !! j = Some b -> dmap !! (o + Z.of_nat j)%Z = Some b⌝)%I
      as %Hlook.
    { iIntros (j b Hj).
      iDestruct (big_sepL_lookup _ _ j b Hj with "Hbs") as "Hb".
      by iDestruct (ghost_map_lookup with "Hauth Hb") as %?. }
    iPureIntro.
    unfold disk_read. apply list_eq. intro i.
    rewrite list_lookup_fmap.
    destruct (decide (i < length bs)%nat) as [Hlt|Hge].
    - rewrite (lookup_seq_lt 0 (length bs) i Hlt).
      cbn [fmap option_fmap option_map]. cbv beta.
      destruct (lookup_lt_is_Some_2 bs i Hlt) as [b Hb].
      rewrite Hb. f_equal.
      replace (0 + i)%nat with i by lia.
      apply Hview, Hlook, Hb.
    - rewrite (lookup_seq_ge 0 (length bs) i); [|lia].
      cbn [fmap option_fmap option_map].
      symmetry. apply lookup_ge_None_2. lia.
  Qed.

  (* -- update: an OUT completion rewrites a range ----------------------- *)

  (* the raw update: the new map holds [bs'] on the range and agrees with the
     old one everywhere else.  [disk_bytes_update] reads the [disk_view]
     transfer off these two clauses. *)
  Lemma disk_bytes_update_gen (γ : disk_names) (dmap : gmap Z (bv 8))
      (o : Z) (bs bs' : list (bv 8)) :
    length bs' = length bs ->
    ghost_map_auth (dn_img γ) 1 dmap -∗ disk_bytes γ o bs ==∗
    ∃ dmap' : gmap Z (bv 8),
      ghost_map_auth (dn_img γ) 1 dmap' ∗ disk_bytes γ o bs' ∗
      ⌜forall (j : nat) (b : bv 8), bs' !! j = Some b ->
         dmap' !! (o + Z.of_nat j)%Z = Some b⌝ ∗
      ⌜forall x : Z,
         (forall j : nat, (j < length bs')%nat -> (x ≠ o + Z.of_nat j)%Z) ->
         dmap' !! x = dmap !! x⌝.
  Proof.
    revert o bs dmap.
    induction bs' as [|b' bs'' IH]; intros o bs dmap Hlen.
    - iIntros "Hauth Hbs". iModIntro. iExists dmap. iFrame "Hauth".
      rewrite /disk_bytes big_sepL_nil.
      iSplitR; [done|]. iPureIntro. split.
      + intros j b Hj. rewrite lookup_nil in Hj. discriminate.
      + intros x _. reflexivity.
    - destruct bs as [|b bs]; [ discriminate | ].
      iIntros "Hauth Hbs".
      rewrite disk_bytes_cons. iDestruct "Hbs" as "[Hb Hbs]".
      iMod (ghost_map_update b' with "Hauth Hb") as "[Hauth Hb]".
      assert (Hlen' : length bs'' = length bs) by (cbn in Hlen; lia).
      iMod (IH (o + 1) bs (<[o := b']> dmap) Hlen' with "Hauth Hbs")
        as (dmap') "(Hauth & Hbs & %Ha & %Hc)".
      iModIntro. iExists dmap'. iFrame "Hauth".
      iSplitL "Hb Hbs".
      { rewrite disk_bytes_cons. iFrame "Hb Hbs". }
      iPureIntro. split.
      + intros j b0 Hj. destruct j as [|j].
        * cbn in Hj. injection Hj as <-.
          assert (Hz : o + Z.of_nat 0%nat = o) by lia. rewrite Hz.
          rewrite (Hc o); [ apply lookup_insert | ].
          intros k Hk Heq. lia.
        * cbn in Hj.
          assert (Hs : o + Z.of_nat (S j) = o + 1 + Z.of_nat j) by lia.
          rewrite Hs. exact (Ha j b0 Hj).
      + intros x Hx.
        rewrite (Hc x).
        * apply lookup_insert_ne. intro Heq.
          assert (Hne : x ≠ o + Z.of_nat 0%nat) by (apply Hx; cbn; lia). lia.
        * intros k Hk.
          assert (Hs : o + 1 + Z.of_nat k = o + Z.of_nat (S k)) by lia.
          rewrite Hs. apply Hx. cbn. lia.
  Qed.

  Lemma disk_bytes_update (γ : disk_names) (dmap : gmap Z (bv 8))
      (o : Z) (bs bs' : list (bv 8)) :
    length bs' = length bs ->
    ghost_map_auth (dn_img γ) 1 dmap -∗ disk_bytes γ o bs ==∗
    ∃ dmap' : gmap Z (bv 8),
      ghost_map_auth (dn_img γ) 1 dmap' ∗ disk_bytes γ o bs' ∗
      ⌜forall dk : Z -> bv 8,
         disk_view dmap dk -> disk_view dmap' (disk_write dk o bs')⌝.
  Proof.
    iIntros (Hlen) "Hauth Hbs".
    iMod (disk_bytes_update_gen γ dmap o bs bs' Hlen with "Hauth Hbs")
      as (dmap') "(Hauth & Hbs & %Ha & %Hc)".
    iModIntro. iExists dmap'. iFrame "Hauth Hbs". iPureIntro.
    intros dk Hview x b Hx. unfold disk_write.
    destruct (o <=? x) eqn:Hle.
    - apply Z.leb_le in Hle.
      destruct (bs' !! Z.to_nat (x - o)) as [b0|] eqn:Hb0.
      + assert (Hd : dmap' !! (o + Z.of_nat (Z.to_nat (x - o))) = Some b0)
          by exact (Ha _ _ Hb0).
        assert (Hxo : o + Z.of_nat (Z.to_nat (x - o)) = x) by lia.
        rewrite Hxo in Hd. rewrite Hd in Hx. injection Hx as <-. reflexivity.
      + assert (Hout : forall j : nat, (j < length bs')%nat -> x ≠ o + Z.of_nat j).
        { intros j Hj Heq.
          assert (Hjj : Z.to_nat (x - o) = j) by lia.
          rewrite Hjj in Hb0.
          destruct (lookup_lt_is_Some_2 bs' j Hj) as [bb Hbb].
          rewrite Hbb in Hb0. discriminate. }
        rewrite (Hc x Hout) in Hx. exact (Hview x b Hx).
    - apply Z.leb_gt in Hle.
      assert (Hout : forall j : nat, (j < length bs')%nat -> x ≠ o + Z.of_nat j)
        by (intros j _; lia).
      rewrite (Hc x Hout) in Hx. exact (Hview x b Hx).
  Qed.

  (* -- minting: fragments for untouched offsets ------------------------- *)

  Lemma disk_bytes_mint (γ : disk_names) (dmap : gmap Z (bv 8))
      (dk : Z -> bv 8) (o : Z) (n : nat) :
    disk_view dmap dk ->
    (forall j : nat, (j < n)%nat -> dmap !! (o + Z.of_nat j) = None) ->
    ghost_map_auth (dn_img γ) 1 dmap ==∗
    ∃ dmap' : gmap Z (bv 8),
      ghost_map_auth (dn_img γ) 1 dmap' ∗
      disk_bytes γ o (disk_read dk o n) ∗
      ⌜disk_view dmap' dk⌝.
  Proof.
    revert o dmap. induction n as [|n IH]; intros o dmap Hview Hfresh.
    - iIntros "Hauth". iModIntro. iExists dmap. iFrame "Hauth".
      iSplitR; [| iPureIntro; exact Hview ].
      assert (Hnil : disk_read dk o 0%nat = []) by reflexivity.
      rewrite Hnil /disk_bytes big_sepL_nil. done.
    - iIntros "Hauth".
      iMod (ghost_map_insert o (dk o) with "Hauth") as "[Hauth Hb]".
      { pose proof (Hfresh 0%nat ltac:(lia)) as Hf.
        assert (Ho : o + Z.of_nat 0%nat = o) by lia. rewrite Ho in Hf. exact Hf. }
      assert (Hview' : disk_view (<[o := dk o]> dmap) dk).
      { intros x b Hx. destruct (decide (x = o)) as [->|Hne].
        - rewrite lookup_insert in Hx. by injection Hx as <-.
        - rewrite lookup_insert_ne in Hx; [| exact (fun e => Hne (eq_sym e)) ].
          exact (Hview x b Hx). }
      assert (Hfresh' : forall j : nat, (j < n)%nat ->
                <[o := dk o]> dmap !! (o + 1 + Z.of_nat j) = None).
      { intros j Hj. rewrite lookup_insert_ne; [| lia ].
        pose proof (Hfresh (S j) ltac:(lia)) as Hf.
        assert (Hs : o + Z.of_nat (S j) = o + 1 + Z.of_nat j) by lia.
        rewrite Hs in Hf. exact Hf. }
      iMod (IH (o + 1) (<[o := dk o]> dmap) Hview' Hfresh' with "Hauth")
        as (dmap') "(Hauth & Hbs & %Hv)".
      iModIntro. iExists dmap'. iFrame "Hauth".
      iSplitL; [| iPureIntro; exact Hv ].
      rewrite disk_read_cons disk_bytes_cons. iFrame "Hb Hbs".
  Qed.

End DiskPtsto.
