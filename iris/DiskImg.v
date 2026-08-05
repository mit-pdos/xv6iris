(* ====================================================================== *)
(* DiskImg.v -- the PER-ERA disk-image ghost map.                          *)
(*                                                                         *)
(* The disk image is the ONE machine component a power cycle preserves      *)
(* (claude-notes/design/crash.md), but its GHOST mirror deliberately is     *)
(* not: each boot allocates a FRESH image map at the preserved content      *)
(* ([riscvEraGS]'s [era_disk_name]; the auth rides in that era's            *)
(* [state_interp] conjunct [RiscvPtsto.disk_dur_interp], the full           *)
(* fragments are handed to the boot client through                          *)
(* [RiscvAdequacy.power_boot_res]).  A crash abandons the whole map with    *)
(* the era, so nothing strands: fragments parked in a dead era's            *)
(* invariants are simply gone, and the next boot mints its own.  (A FIXED   *)
(* image map could never be re-minted -- [ghost_map] cannot re-create an    *)
(* existing key -- so a client layer holding fragments could not boot       *)
(* twice; claude-notes/design/fs-log.md, stage 4.)                          *)
(*                                                                         *)
(* Hence this file: the auth and the fragments must carry the SAME          *)
(* [ghost_mapG] instance, and RiscvPtsto sits BELOW DiskPtsto, so neither   *)
(* can take the class from the other.  Two sibling                          *)
(* [ghost_mapG Σ Z (bv 8)] fields -- one in [riscvFixedGS], one in         *)
(* [diskGhostG] -- would be different Σ slots whose resources cannot        *)
(* interact, and no proof can bridge two abstract instances.  A single      *)
(* class BELOW both is what makes the era auth and the driver's fragments   *)
(* talk about one ghost map.  (The class stays FIXED-layer, [riscvFixedGS]'s*)
(* [riscvF_diskGS]: it is the unique source of the instance, and only the   *)
(* NAME is per-era.)                                                        *)
(*                                                                         *)
(* The points-to itself lives here too, at a BARE GNAME, because the        *)
(* power thread mints a whole disk's worth of fragments before any          *)
(* [DiskPtsto.disk_names] record exists.  [DiskPtsto.disk_bytes] is this    *)
(* at [dn_img γ], so every client spelling is unchanged.                    *)
(* ====================================================================== *)
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
Require Import VirtioModel.

Local Open Scope Z_scope.

Class diskImgG (Σ : gFunctors) := DiskImgG {
  disk_img_inG :: ghost_mapG Σ Z (bv 8);
}.

Definition diskImgΣ : gFunctors := #[ ghost_mapΣ Z (bv 8) ].

Global Instance subG_diskImgG Σ : subG diskImgΣ Σ -> diskImgG Σ.
Proof. solve_inG. Qed.

(* The authority, tied to an image FUNCTION by [VirtioModel.disk_view]: a
   fragment exists only for offsets somebody minted, and the model's disk
   stays total underneath (the exact analogue of [mem_view]).  Stated over a
   bare gname and an arbitrary [dk] because both of its users need it at
   something other than a [gstate]: the fixed layer instantiates [dk] at
   [v_disk (dvirtio (gdev g))], and the device-thread lifting rule at
   [v_disk (dvirtio d)] for the [dev_state] it is stepping. *)
Definition disk_img_auth `{!diskImgG Σ} (γi : gname) (dk : Z -> bv 8)
    : iProp Σ :=
  (∃ dmap : gmap Z (bv 8),
     ghost_map_auth γi 1 dmap ∗ ⌜disk_view dmap dk⌝)%I.

(* ---------------------------------------------------------------------- *)
(* THE POINTS-TO, at a bare gname.  [DiskPtsto.disk_byte]/[disk_bytes] are  *)
(* these at [dn_img γ] and every lemma below is restated there verbatim, so *)
(* no client statement mentions this layer.  What needs the gname form is   *)
(* the BOOT MINT: [RiscvAdequacy.wp_power_loop] allocates the era's image   *)
(* and hands out its full fragments before the driver's [disk_names] record *)
(* exists (it is allocated by the boot client, out of the gname it is       *)
(* given).                                                                 *)
(* ---------------------------------------------------------------------- *)

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

Section DiskImgPtsto.
  Context `{!diskImgG Σ}.

  Definition disk_img_byte (γi : gname) (o : Z) (b : bv 8) : iProp Σ :=
    o ↪[γi] b.

  Definition disk_img_bytes (γi : gname) (o : Z) (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] j ↦ b ∈ bs, disk_img_byte γi (o + Z.of_nat j) b)%I.

  Global Instance disk_img_byte_timeless γi o b :
    Timeless (disk_img_byte γi o b).
  Proof. apply _. Qed.
  Global Instance disk_img_bytes_timeless γi o bs :
    Timeless (disk_img_bytes γi o bs).
  Proof. apply _. Qed.

  (* -- structural peeling ----------------------------------------------- *)

  Lemma disk_img_bytes_cons (γi : gname) (o : Z) (b : bv 8) (bs : list (bv 8)) :
    disk_img_bytes γi o (b :: bs)
      ⊣⊢ disk_img_byte γi o b ∗ disk_img_bytes γi (o + 1) bs.
  Proof.
    rewrite /disk_img_bytes big_sepL_cons. cbv beta.
    assert (Hz : o + Z.of_nat 0%nat = o) by lia. rewrite Hz.
    apply bi.sep_proper; [reflexivity|].
    apply big_sepL_proper. intros k y _.
    assert (Hs : o + Z.of_nat (S k) = o + 1 + Z.of_nat k) by lia.
    rewrite Hs. reflexivity.
  Qed.

  (* -- agreement: fragments read the image ------------------------------ *)

  Lemma disk_img_bytes_read (γi : gname) (dmap : gmap Z (bv 8))
      (dk : Z -> bv 8) (o : Z) (bs : list (bv 8)) :
    disk_view dmap dk ->
    ghost_map_auth γi 1 dmap -∗ disk_img_bytes γi o bs -∗
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
     old one everywhere else.  [disk_img_bytes_update] reads the [disk_view]
     transfer off these two clauses. *)
  Lemma disk_img_bytes_update_gen (γi : gname) (dmap : gmap Z (bv 8))
      (o : Z) (bs bs' : list (bv 8)) :
    length bs' = length bs ->
    ghost_map_auth γi 1 dmap -∗ disk_img_bytes γi o bs ==∗
    ∃ dmap' : gmap Z (bv 8),
      ghost_map_auth γi 1 dmap' ∗ disk_img_bytes γi o bs' ∗
      ⌜forall (j : nat) (b : bv 8), bs' !! j = Some b ->
         dmap' !! (o + Z.of_nat j)%Z = Some b⌝ ∗
      ⌜forall x : Z,
         (forall j : nat, (j < length bs')%nat -> (x ≠ o + Z.of_nat j)%Z) ->
         dmap' !! x = dmap !! x⌝.
  Proof.
    revert o bs dmap.
    induction bs' as [|b' bs'' IH]; intros o bs dmap Hlen.
    - iIntros "Hauth Hbs". iModIntro. iExists dmap. iFrame "Hauth".
      rewrite /disk_img_bytes big_sepL_nil.
      iSplitR; [done|]. iPureIntro. split.
      + intros j b Hj. rewrite lookup_nil in Hj. discriminate.
      + intros x _. reflexivity.
    - destruct bs as [|b bs]; [ discriminate | ].
      iIntros "Hauth Hbs".
      rewrite disk_img_bytes_cons. iDestruct "Hbs" as "[Hb Hbs]".
      iMod (ghost_map_update b' with "Hauth Hb") as "[Hauth Hb]".
      assert (Hlen' : length bs'' = length bs) by (cbn in Hlen; lia).
      iMod (IH (o + 1) bs (<[o := b']> dmap) Hlen' with "Hauth Hbs")
        as (dmap') "(Hauth & Hbs & %Ha & %Hc)".
      iModIntro. iExists dmap'. iFrame "Hauth".
      iSplitL "Hb Hbs".
      { rewrite disk_img_bytes_cons. iFrame "Hb Hbs". }
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

  Lemma disk_img_bytes_update (γi : gname) (dmap : gmap Z (bv 8))
      (o : Z) (bs bs' : list (bv 8)) :
    length bs' = length bs ->
    ghost_map_auth γi 1 dmap -∗ disk_img_bytes γi o bs ==∗
    ∃ dmap' : gmap Z (bv 8),
      ghost_map_auth γi 1 dmap' ∗ disk_img_bytes γi o bs' ∗
      ⌜forall dk : Z -> bv 8,
         disk_view dmap dk -> disk_view dmap' (disk_write dk o bs')⌝.
  Proof.
    iIntros (Hlen) "Hauth Hbs".
    iMod (disk_img_bytes_update_gen γi dmap o bs bs' Hlen with "Hauth Hbs")
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

  Lemma disk_img_bytes_mint (γi : gname) (dmap : gmap Z (bv 8))
      (dk : Z -> bv 8) (o : Z) (n : nat) :
    disk_view dmap dk ->
    (forall j : nat, (j < n)%nat -> dmap !! (o + Z.of_nat j) = None) ->
    ghost_map_auth γi 1 dmap ==∗
    ∃ dmap' : gmap Z (bv 8),
      ghost_map_auth γi 1 dmap' ∗
      disk_img_bytes γi o (disk_read dk o n) ∗
      ⌜disk_view dmap' dk⌝.
  Proof.
    revert o dmap. induction n as [|n IH]; intros o dmap Hview Hfresh.
    - iIntros "Hauth". iModIntro. iExists dmap. iFrame "Hauth".
      iSplitR; [| iPureIntro; exact Hview ].
      assert (Hnil : disk_read dk o 0%nat = []) by reflexivity.
      rewrite Hnil /disk_img_bytes big_sepL_nil. done.
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
      rewrite disk_read_cons disk_img_bytes_cons. iFrame "Hb Hbs".
  Qed.

  (* -- THE BOOT MINT ---------------------------------------------------- *)

  (* A fresh era's image: a brand-new ghost map, allocated AT the disk's
     current content over the byte range [0, n), together with the FULL
     fragments for that range.  This is what makes the design boot twice --
     every boot, the first one included, gets total fragments, and the
     previous era's (stranded in its dead invariants) are simply abandoned.
     Run by [RiscvAdequacy.wp_power_loop]'s PowerOn arm; the fragments go to
     the boot client through [power_boot_res]. *)
  Lemma disk_img_alloc (dk : Z -> bv 8) (n : nat) :
    ⊢ |==> ∃ γi : gname,
        disk_img_auth γi dk ∗ disk_img_bytes γi 0 (disk_read dk 0 n).
  Proof.
    iMod (ghost_map_alloc_empty (K := Z) (V := bv 8)) as (γi) "Hauth".
    iMod (disk_img_bytes_mint γi ∅ dk 0 n with "Hauth")
      as (dmap') "(Hauth & Hbs & %Hv)".
    { intros o b Ho. rewrite lookup_empty in Ho. discriminate. }
    { intros j _. apply lookup_empty. }
    iModIntro. iExists γi. iFrame "Hbs".
    iExists dmap'. iFrame "Hauth". iPureIntro. exact Hv.
  Qed.

End DiskImgPtsto.
