(* ====================================================================== *)
(*  SUPERSEDED BY THE SNAPSHOT; DELETED FROM THE BUILD (owner ruling,      *)
(*  lane G5).  Off [_CoqProject]: nothing in the tree imports this file,   *)
(*  and the delta-ledger fold it carries was superseded by the SNAPSHOT    *)
(*  commit (fs-state.md section 4-9: the durable instance is re-allocated  *)
(*  per commit, never updated).  It is kept as source for its findings     *)
(*  only; it does not typecheck against the type register                  *)
(*  ([Xv6Cameras.fsLinkUR], lane G5), whose fragments carry a VALUE that   *)
(*  the fold's hand -- a function of the ledger -- cannot name.            *)
(* ====================================================================== *)

(* FsDurLedger.v -- THE PURE DELTA LEDGER and THE FOLD THEOREM.

   Design of record: claude-notes/design/fs-state.md section 5' (the owner's
   STRUCTURED-BODY ruling of 2026-08-24); worklist
   claude-notes/projects/durable-disk.md, item 3c.

   THE RULING.  The durable body stays the STRUCTURED [fs_state Gamma_D S]
   ([FsDurDefer.P_wf_strict] plus the durable top map's authority and every
   one of its fragments): roles are structural, disjointness is ownership,
   and NOTHING is lifted to a pure whole-state predicate -- the kind map,
   its geometry index and every role-proving obligation are gone.

   What the log parks is a PURE per-object DELTA LEDGER.  For each object
   the batch has touched it records the object, its old and its new value,
   the pure preconditions the corresponding LIBRARY MOVER needs, and the
   BYTE-SPLICE fact that ties that object's home block's byte change to the
   value change.  Every writer extends the ledger LOCALLY at its own AU, out
   of what it already holds; no writer ever mentions the ledger's other
   entries, another transaction, or a durable byte map.

   The COMMITTER -- and only the committer -- reads it.  Holding the whole
   body with the crash invariant open, it constructs the commit's durable
   step by FOLDING the library movers at [Gamma_D] inside ONE basic update.
   That is what makes the intermediates unobservable: there is no bin
   predicate, no relaxed pool and no two-owner problem, because no
   intermediate is ever a [P_wf] that anyone else could hold.  A block that
   [balloc] has taken out of the pool and no inode names yet simply sits in
   the fold's own proof context between two steps.

   THE FILE'S SHAPE.

   section 1  THE BYTE WORKHORSE.  One [ghost_map] update lemma, at a byte
              RANGE of one home block: [dbytes_range_update].  Everything
              else in the fold reaches the durable byte authority through
              it, and it is what keeps the fold local -- the authority is
              never moved wholesale, only at the addresses the ledger's
              entries name, which are exactly the addresses the body owns.
   section 2  THE BODY at a named state, the THREE GEOMETRY EQUATIONS, and
              the fold's CONFIGURATION (the state, a hand of blocks, a hand
              of link tokens, the durable byte map).
   section 3  THE LEDGER: [dent], its pure precondition [dent_ok] and its
              pure step [dent_next], and ONE resource lemma per entry kind.
   section 4  THE FOLD THEOREM.
   section 5  THE PAYLOAD and the log's two laws. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import base countable gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop ghost_map.
Require Import BioDefs.        (* [BSIZE]                                   *)
Require Import BitmapEnc.      (* [bm_bytes], the bit laws                  *)
Require Import DinodeEnc.      (* [dinode_bytes], [diblk_bytes]             *)
Require Import FsImg.          (* [BSIZE_z], [IBLOCK], [islot]              *)
Require Import RiscvPtsto.     (* [fs_dur_names]                            *)
Require Import LogDefs.        (* [fs_dbytes], [lm_logged], [fs_home_set]   *)
Require Import DirView.        (* [dir_first], [dir_nrec]                   *)
Require Import FsTree.         (* [fname], [dir_insert_at]                  *)
Require Import FsBlocks.       (* [blk_splice] and its three lookup laws    *)
Require Import FsDurBytes.     (* [fs_gamma_D], [fs_dbelems]                *)
Require Import FsState.        (* [fs_state], [inode_owned], [free_bitmap]  *)
Require Import FsDurDefer.     (* [P_wf_strict], [dstep_strict]             *)
Require Import FsDurObj.       (* [bm_blk_write], [di_blk_write], the encs  *)

(* the proofmode import re-opens [nat_scope] on top of the scope stack *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE BYTE WORKHORSE                                                *)
(* ===================================================================== *)

(* [BSIZE] is a [nat] Definition, so [lia] cannot see through it *)
Lemma BSIZE_1024 : BSIZE = 1024%nat.
Proof. reflexivity. Qed.

(* A SPLICE IS A MAP UNION AT THE SPLICED RANGE.  The whole of what the
   durable byte authority ever has to know about a write: the flattened
   byte map of a block whose contents were spliced at [off] is the OLD
   flattened map overwritten at exactly [off .. off + |nbs|). *)
Lemma map_seqZ_splice (s : Z) (off : nat) (nbs bs : list (bv 8)) :
  (off + length nbs <= length bs)%nat ->
  (map_seqZ s (blk_splice off nbs bs) : gmap Z (bv 8))
  = (map_seqZ (s + Z.of_nat off) nbs : gmap Z (bv 8)) ∪ map_seqZ s bs.
Proof.
  intros Hb.
  assert (Hoffle : (off <= length bs)%nat) by lia.
  apply map_eq. intros i.
  rewrite lookup_union !lookup_map_seqZ.
  destruct (decide (s <= i)) as [Hle | Hgt]; last first.
  { assert (HgA : forall mx : option (bv 8), (guard (s <= i);; mx) = None).
    { intros mx. rewrite (option_guard_False (s <= i)); [reflexivity | lia]. }
    assert (HgB : forall mx : option (bv 8),
                    (guard (s + Z.of_nat off <= i);; mx) = None).
    { intros mx.
      rewrite (option_guard_False (s + Z.of_nat off <= i));
        [reflexivity | lia]. }
    rewrite !HgA !HgB (left_id_L None (∪)). reflexivity. }
  assert (HgA : forall mx : option (bv 8), (guard (s <= i);; mx) = mx).
  { intros mx. exact (option_guard_True (s <= i) mx Hle). }
  rewrite !HgA.
  destruct (Nat.lt_ge_cases (Z.to_nat (i - s)) off) as [Hlt | Hge].
  - assert (HgB : forall mx : option (bv 8),
                    (guard (s + Z.of_nat off <= i);; mx) = None).
    { intros mx.
      rewrite (option_guard_False (s + Z.of_nat off <= i));
        [reflexivity | lia]. }
    rewrite !HgB (left_id_L None (∪)).
    rewrite (blk_splice_lookup_lt off nbs bs (Z.to_nat (i - s))
               Hoffle Hlt).
    reflexivity.
  - assert (HgB : forall mx : option (bv 8),
                    (guard (s + Z.of_nat off <= i);; mx) = mx).
    { intros mx.
      exact (option_guard_True (s + Z.of_nat off <= i) mx ltac:(lia)). }
    rewrite !HgB.
    assert (Hjo : Z.to_nat (i - (s + Z.of_nat off))
                  = (Z.to_nat (i - s) - off)%nat) by lia.
    rewrite Hjo.
    destruct (Nat.lt_ge_cases (Z.to_nat (i - s)) (off + length nbs)%nat)
      as [Hmid | Hgt2].
    + rewrite (blk_splice_lookup_mid off nbs bs (Z.to_nat (i - s))
                 Hoffle Hge Hmid).
      assert (Hlt2 : (Z.to_nat (i - s) - off < length nbs)%nat) by lia.
      destruct (lookup_lt_is_Some_2 nbs (Z.to_nat (i - s) - off)%nat Hlt2)
        as [v Hv].
      rewrite Hv. destruct (bs !! Z.to_nat (i - s)); reflexivity.
    + assert (Hge2 : (off + length nbs <= Z.to_nat (i - s))%nat) by lia.
      rewrite (blk_splice_lookup_ge off nbs bs (Z.to_nat (i - s))
                 Hoffle Hge2).
      assert (Hge3 : (length nbs <= Z.to_nat (i - s) - off)%nat) by lia.
      rewrite (lookup_ge_None_2 nbs (Z.to_nat (i - s) - off)%nat Hge3).
      rewrite (left_id_L None (∪)). reflexivity.
Qed.

(* two runs of the same length occupy the same addresses *)
Lemma dom_map_seqZ_len (s : Z) (xs ys : list (bv 8)) :
  length xs = length ys ->
  dom (map_seqZ s xs : gmap Z (bv 8)) = dom (map_seqZ s ys : gmap Z (bv 8)).
Proof.
  intros Hl. apply set_eq. intros i.
  rewrite !elem_of_dom !lookup_map_seqZ_is_Some Hl //.
Qed.

Section Workhorse.
  Context `{!diskImgG Σ}.

  (* ONE BYTE RANGE'S ELEMENTS.  [FsDurBytes.blk_owned_dbelems] at an
     arbitrary offset and width; the whole-block form is [off = 0]. *)
  Lemma byte_range_dbelems (g : gname) (Γd : fs_dur_names) (b off : Z)
      (bs : list (bv 8)) :
    byte_range (fs_gamma_D g Γd) b off bs
    ⊣⊢ fs_dbelems g (map_seqZ (b * Z.of_nat BSIZE + off) bs).
  Proof.
    rewrite /fs_dbelems big_sepM_map_seqZ_gen.
    rewrite /byte_range /byte_range_q /fs_gamma_D. cbn [fsΦ].
    apply big_sepL_proper. intros k v _.
    assert (Hz : b * BSIZE_z + off + Z.of_nat k
                 = b * Z.of_nat BSIZE + off + Z.of_nat k)
      by (change BSIZE_z with 1024; rewrite dbytes_stride; lia).
    rewrite Hz //.
  Qed.

  (* THE FLATTENED MAP AFTER A SPLICE. *)
  Lemma fs_dbytes_splice (D : gmap Z (list (bv 8))) (b : Z)
      (bs : list (bv 8)) (off : nat) (nbs : list (bv 8)) :
    (forall c cs, D !! c = Some cs -> length cs = BSIZE) ->
    D !! b = Some bs -> (off + length nbs <= BSIZE)%nat ->
    fs_dbytes (<[b := blk_splice off nbs bs]> D)
    = (map_seqZ (b * Z.of_nat BSIZE + Z.of_nat off) nbs : gmap Z (bv 8))
      ∪ fs_dbytes D.
  Proof.
    intros Hlen Hb Hoff.
    assert (Hbs : length bs = BSIZE) by exact (Hlen b bs Hb).
    assert (HDd : delete b D !! b = None) by apply lookup_delete.
    assert (HlenD : forall c cs, delete b D !! c = Some cs
                                 -> length cs = BSIZE).
    { intros c cs Hc. apply (Hlen c cs).
      rewrite lookup_delete_Some in Hc. tauto. }
    assert (HeqD : D = <[b := bs]> (delete b D)).
    { symmetry. rewrite insert_delete_insert. exact (insert_id D b bs Hb). }
    assert (HeqD' : <[b := blk_splice off nbs bs]> D
                    = <[b := blk_splice off nbs bs]> (delete b D)).
    { symmetry. apply insert_delete_insert. }
    assert (HokD : dbytes_ok (delete b D))
      by exact (dbytes_ok_full (delete b D) HlenD).
    assert (Hoffb : (off + length nbs <= length bs)%nat)
      by (rewrite Hbs; exact Hoff).
    assert (Hsl : length (blk_splice off nbs bs) = BSIZE).
    { rewrite (blk_splice_length off nbs bs Hoffb). exact Hbs. }
    assert (Hsl' : (length (blk_splice off nbs bs) <= BSIZE)%nat)
      by (rewrite Hsl; lia).
    assert (Hbs' : (length bs <= BSIZE)%nat) by (rewrite Hbs; lia).
    rewrite HeqD'.
    rewrite (fs_dbytes_insert (delete b D) b (blk_splice off nbs bs)
               (dbytes_ok_insert_2 (delete b D) b _ HokD Hsl') HDd).
    rewrite {2} HeqD.
    rewrite (fs_dbytes_insert (delete b D) b bs
               (dbytes_ok_insert_2 (delete b D) b bs HokD Hbs') HDd).
    rewrite (map_seqZ_splice (b * Z.of_nat BSIZE) off nbs bs Hoffb).
    rewrite assoc_L //.
  Qed.

  (* THE ONE UPDATE.  Given the durable byte authority and the OWNERSHIP of
     one byte range of one home block, move that range.  The authority is
     touched at exactly the range's addresses; nothing about the rest of the
     map is assumed or produced.  This is what replaces the flat blob's
     wholesale rebase, and it is why the structured body needs no
     completeness clause. *)
  Lemma dbytes_range_update (g : gname) (Γd : fs_dur_names)
      (D : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8))
      (off : nat) (obs nbs : list (bv 8)) :
    (forall c cs, D !! c = Some cs -> length cs = BSIZE) ->
    D !! b = Some bs ->
    length obs = length nbs ->
    (off + length nbs <= BSIZE)%nat ->
    ghost_map_auth g 1 (fs_dbytes D) -∗
    byte_range (fs_gamma_D g Γd) b (Z.of_nat off) obs ==∗
    ghost_map_auth g 1 (fs_dbytes (<[b := blk_splice off nbs bs]> D))
    ∗ byte_range (fs_gamma_D g Γd) b (Z.of_nat off) nbs.
  Proof.
    intros Hlen Hb Hll Hoff.
    iIntros "Ha Hr".
    rewrite (byte_range_dbelems g Γd b (Z.of_nat off) obs).
    iMod (ghost_map_update_big
            (map_seqZ (b * Z.of_nat BSIZE + Z.of_nat off) obs)
            (map_seqZ (b * Z.of_nat BSIZE + Z.of_nat off) nbs)
            with "Ha Hr") as "[Ha Hr]".
    { exact (dom_map_seqZ_len _ obs nbs Hll). }
    rewrite (fs_dbytes_splice D b bs off nbs Hlen Hb Hoff).
    iFrame "Ha".
    rewrite (byte_range_dbelems g Γd b (Z.of_nat off) nbs). iFrame.
    by iModIntro.
  Qed.

End Workhorse.

(* ===================================================================== *)
(*  2.  THE BODY, THE GEOMETRY, AND THE FOLD'S CONFIGURATION              *)
(* ===================================================================== *)

(* THE FOLD'S CONFIGURATION.  [dc_S] is the durable abstract state and
   [dc_D] the durable HOME byte map; [dc_bin] and [dc_toks] are the fold's
   own HANDS -- blocks and link tokens that have left one conjunct of
   [fs_state] and not yet reached another.  They exist ONLY inside the
   fold's induction: at both ends of the ledger they are empty, and nothing
   outside this file ever names them.  That is what "intermediates are
   unobservable" means operationally -- a [balloc]'s block between the
   bitmap write that takes it out of the pool and the record write that
   adopts it is a hypothesis in the fold's proof context, never a
   predicate anyone can hold. *)
(* THE HAND'S TYPE: at each inum, the multiset of PARENT REGISTER values
   the fold is holding there.  The counting tokens are the same units --
   the count is the multiset's size (durable-disk G2). *)
Definition thand := gmap Z (gmultiset (option Z)).

Record dcfg := MkDCfg {
  dc_S    : fs_state_rec;
  dc_bin  : gset Z;
  dc_toks : thand;
  dc_D    : gmap Z (list (bv 8));
}.

(* THE HAND OF BLOCKS IS A SET, NOT A MAP, and that is forced by [balloc]:
   a block leaves [free_bitmap]'s pool at an EXISTENTIAL content
   ([FsStateBitmap.pool_elt] is [exists bs, blk_owned]), so no ledger entry
   could name its bytes.  It does not have to: the fold holds the durable
   byte AUTHORITY at [fs_dbytes (dc_D c)] and the block's own elements, so
   the content is READ OFF [dc_D] by agreement ([dblk_content] below).  That
   is the same device that lets an entry name the durable record it is
   about without the writer having to know it. *)

(* every block of the durable home map is a whole block *)
Definition dbytes_tot (D : gmap Z (list (bv 8))) : Prop :=
  forall b bs, D !! b = Some bs -> length bs = BSIZE.

(* the byte trail's one step: block [b]'s bytes spliced at [off] *)
Definition dsplice (D : gmap Z (list (bv 8))) (b : Z) (off : nat)
    (nbs : list (bv 8)) : gmap Z (list (bv 8)) :=
  <[b := blk_splice off nbs (default [] (D !! b))]> D.

Lemma dbytes_tot_splice (D : gmap Z (list (bv 8))) (b : Z) (off : nat)
    (nbs : list (bv 8)) :
  dbytes_tot D -> is_Some (D !! b) -> (off + length nbs <= BSIZE)%nat ->
  dbytes_tot (dsplice D b off nbs).
Proof.
  intros HD [bs Hb] Hoff c cs Hc.
  assert (Hbs : length bs = BSIZE) by exact (HD b bs Hb).
  rewrite /dsplice in Hc.
  apply lookup_insert_Some in Hc as [[_ <-] | [_ Hc]]; [| exact (HD c cs Hc)].
  rewrite Hb /=. rewrite (blk_splice_length off nbs bs); [exact Hbs | lia].
Qed.

Lemma dsplice_whole (D : gmap Z (list (bv 8))) (b : Z) (bs nbs : list (bv 8)) :
  D !! b = Some bs -> length nbs = length bs ->
  dsplice D b 0%nat nbs = <[b := nbs]> D.
Proof.
  intros Hb Hl. rewrite /dsplice Hb /=. rewrite (blk_splice_whole nbs bs Hl) //.
Qed.

(* the fold's hands, as multisets with a home.  EACH UNIT IS A PAIR since
   durable-disk G2: a counting token and the PARENT REGISTER unit that
   rides with it, so the hand is keyed by inum and VALUED by the multiset
   of register values it is holding at that inum -- the count is that
   multiset's size. *)
Definition tk_at (m : thand) (i : Z) : gmultiset (option Z) :=
  default ∅ (m !! i).

Definition tk_add (m : thand) (i : Z) (v : option Z) : thand :=
  <[i := tk_at m i ⊎ {[+ v +]}]> m.

Definition tk_sub (m : thand) (i : Z) (v : option Z) : thand :=
  <[i := tk_at m i ∖ {[+ v +]}]> m.

Section Ledger.
  Context `{!fsLinkG Σ, !fsTopG Σ, !diskImgG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  2a.  THE BODY                                                       *)
  (* ------------------------------------------------------------------ *)

  (* [FsDurDefer.P_wf_strict]'s body at a NAMED state.  The durable top
     map's FRAGMENTS are in it because [FsState.inode_owned] carries none
     and an authority with no elements cannot be retagged. *)
  Definition dbody (g : gname) (Γd : fs_dur_names) (S : fs_state_rec)
    : iProp Σ :=
    (ghost_map_auth (fdn_top Γd) 1 (fss_inodes S)
     ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag (fs_gamma_D g Γd) i n)
     ∗ fs_state (fs_gamma_D g Γd) S)%I.

  Lemma dbody_P_wf_strict g Γd :
    (∃ S, dbody g Γd S)%I ⊣⊢ P_wf_strict g Γd.
  Proof. rewrite /dbody /P_wf_strict //. Qed.

  (* THE THREE GEOMETRY EQUATIONS, and they are the WHOLE of what the
     structured body has to say about roles.

     A ledger entry names its object -- an inum, a block -- and the fold has
     to find that object inside [fs_state Gamma_D S].  Two of the three
     equations are what turns the entry's block number into the state's own
     geometry ([fss_sb S] is existentially bound, so nothing else relates
     the writer's block to it); the third is the per-inum EXISTENCE witness
     that fs-state.md section 4.5 (2) already listed as a residual.  It is
     needed and it cannot be avoided: the durable inode map's DOMAIN is not
     a function of the byte map (a state with fewer inodes simply owns fewer
     bytes, which no byte-level agreement refutes), and it is immutable, so
     stating it once is exactly right.

     What this is NOT is the rejected kinds/geometry tie: there is no
     per-block ROLE assignment, no [kinds_of_state], no quantifier over
     admissible states, and no supplier obligation phrased at a kind.  Each
     equation is one number, fixed at boot, and each has an era-side carrier
     already identified (the bitmap invariant, the inode region's
     invariant). *)
  Definition dgeo_ok (Γd : fs_dur_names) (S : fs_state_rec) : Prop :=
    sb_bmapstart (fss_sb S) = fdn_bmap Γd
    /\ sb_inodestart (fss_sb S) = fdn_ist Γd
    /\ (forall i : Z, 0 <= i < fdn_nin Γd -> is_Some (fss_inodes S !! i)).

  (* THE DURABLE PREDICATE.  [P_wf_strict] with the three equations. *)
  Definition P_wf_led (g : gname) (Γd : fs_dur_names) : iProp Σ :=
    (∃ S, ⌜dgeo_ok Γd S⌝ ∗ dbody g Γd S)%I.

  Lemma P_wf_led_strict g Γd : P_wf_led g Γd ⊢ P_wf_strict g Γd.
  Proof.
    rewrite /P_wf_led -dbody_P_wf_strict.
    iIntros "H". iDestruct "H" as (S) "[_ H]". by iExists S.
  Qed.

  Global Instance dbody_timeless g Γd S : Timeless (dbody g Γd S).
  Proof.
    rewrite /dbody. apply _.
  Qed.

  Global Instance P_wf_led_timeless g Γd : Timeless (P_wf_led g Γd).
  Proof. rewrite /P_wf_led. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (*  2b.  THE CONFIGURATION'S RESOURCES                                  *)
  (* ------------------------------------------------------------------ *)

  Definition dhand (g : gname) (Γd : fs_dur_names)
      (Bin : gset Z) (Tk : thand) : iProp Σ :=
    (([∗ set] b ∈ Bin, ∃ bs, blk_owned (fs_gamma_D g Γd) b bs)
     ∗ ([∗ map] i ↦ P ∈ Tk,
          link_toks (fs_gamma_D g Γd) i (size P)
          ∗ par_toks (fs_gamma_D g Γd) i P))%I.

  Definition dcfg_res (g : gname) (Γd : fs_dur_names) (c : dcfg) : iProp Σ :=
    (dbody g Γd (dc_S c) ∗ dhand g Γd (dc_bin c) (dc_toks c)
     ∗ ghost_map_auth g 1 (fs_dbytes (dc_D c)))%I.

  Lemma dhand_empty g Γd : ⊢ dhand g Γd ∅ ∅.
  Proof. rewrite /dhand big_sepS_empty big_sepM_empty. auto. Qed.

  (* one block INTO the hand, at an unknown content *)
  Lemma dhand_blk_add g Γd Bin Tk (b : Z) (bs : list (bv 8)) :
    b ∉ Bin ->
    dhand g Γd Bin Tk -∗ blk_owned (fs_gamma_D g Γd) b bs -∗
    dhand g Γd ({[b]} ∪ Bin) Tk.
  Proof.
    intros Hb. iIntros "[Hs $] Hblk".
    rewrite big_sepS_insert; [| exact Hb]. iFrame "Hs". by iExists bs.
  Qed.

  (* ...and one block OUT of it *)
  Lemma dhand_blk_sub g Γd Bin Tk (b : Z) :
    b ∈ Bin ->
    dhand g Γd Bin Tk -∗
    (∃ bs, blk_owned (fs_gamma_D g Γd) b bs) ∗ dhand g Γd (Bin ∖ {[b]}) Tk.
  Proof.
    intros Hb. iIntros "[Hs $]".
    rewrite (big_sepS_delete _ Bin b Hb). iDestruct "Hs" as "[$ $]".
  Qed.

  (* the two unit moves, at the hand: a counting token and its register
     unit travel together (durable-disk G2). *)
  Lemma dhand_tok_add (g : gname) (Γd : fs_dur_names) (Bin : gset Z)
      (Tk : thand) (i : Z) (v : option Z) :
    dhand g Γd Bin Tk -∗ link_tok (fs_gamma_D g Γd) i -∗
    par_tok (fs_gamma_D g Γd) i v -∗ dhand g Γd Bin (tk_add Tk i v).
  Proof.
    iIntros "[$ Ht] Hl Hp". rewrite /tk_add.
    destruct (Tk !! i) as [P |] eqn:HP.
    - assert (Hz : tk_at Tk i = P) by (rewrite /tk_at HP //).
      rewrite Hz (big_sepM_delete _ Tk i P HP).
      iDestruct "Ht" as "[[Hl0 Hp0] Ht]".
      rewrite big_sepM_insert_delete. iFrame "Ht".
      iSplitL "Hl0 Hl".
      + rewrite gmultiset_size_disj_union gmultiset_size_singleton.
        assert (Hs : (size P + 1 = 1 + size P)%nat) by lia.
        rewrite Hs link_toks_split. iFrame "Hl Hl0".
      + rewrite par_toks_split. iFrame "Hp0". rewrite par_toks_one.
        iExact "Hp".
    - assert (Hz : tk_at Tk i ⊎ {[+ v +]} = {[+ v +]})
        by (rewrite /tk_at HP /=; multiset_solver).
      rewrite big_sepM_insert; [| exact HP].
      rewrite Hz gmultiset_size_singleton. iFrame "Ht Hl".
      rewrite par_toks_one. iExact "Hp".
  Qed.

  Lemma dhand_tok_sub (g : gname) (Γd : fs_dur_names) (Bin : gset Z)
      (Tk : thand) (i : Z) (v : option Z) (P : gmultiset (option Z)) :
    Tk !! i = Some P -> v ∈ P ->
    dhand g Γd Bin Tk -∗
    link_tok (fs_gamma_D g Γd) i ∗ par_tok (fs_gamma_D g Γd) i v
    ∗ dhand g Γd Bin (tk_sub Tk i v).
  Proof.
    intros HP Hv. iIntros "[$ Ht]". rewrite /tk_sub.
    assert (Hz : tk_at Tk i = P) by (rewrite /tk_at HP //).
    rewrite Hz (big_sepM_delete _ Tk i P HP).
    iDestruct "Ht" as "[[Hl0 Hp0] Ht]".
    remember (P ∖ {[+ v +]}) as P0 eqn:HP0.
    assert (HPd : P = P0 ⊎ {[+ v +]}) by (rewrite HP0; multiset_solver).
    assert (Hsz : (size P = 1 + size P0)%nat).
    { rewrite HPd gmultiset_size_disj_union gmultiset_size_singleton. lia. }
    iEval (rewrite Hsz link_toks_split) in "Hl0".
    iDestruct "Hl0" as "[$ Hl0]".
    iEval (rewrite HPd par_toks_split) in "Hp0".
    iDestruct "Hp0" as "[Hp0 Hpv]". iFrame "Hpv".
    rewrite big_sepM_insert_delete. iFrame "Ht Hl0 Hp0".
  Qed.

  (* one block of the hand, out and back, at any content *)
  Lemma dhand_blk_acc g Γd Bin Tk (b : Z) :
    b ∈ Bin ->
    dhand g Γd Bin Tk -∗
    (∃ bs, blk_owned (fs_gamma_D g Γd) b bs)
    ∗ (∀ bs', blk_owned (fs_gamma_D g Γd) b bs' -∗ dhand g Γd Bin Tk).
  Proof.
    intros Hb. iIntros "[Hs Ht]".
    iEval (rewrite (big_sepS_delete _ Bin b Hb)) in "Hs".
    iDestruct "Hs" as "[Hbb Hs]". iFrame "Hbb".
    iIntros (bs') "Hblk". rewrite /dhand.
    iEval (rewrite (big_sepS_delete _ Bin b Hb)).
    iFrame "Ht Hs". by iExists bs'.
  Qed.

  (* THE ENTRY TOKEN, out of the hand and into it.  Both are stated at the
     [ent_tok] the entry-map movers consume and produce, so a [GIns]/[BIns]
     and a [BDel] never have to case on [ent_tokenless] again. *)
  Lemma dhand_ent_take (g : gname) (Γd : fs_dur_names) (Bin : gset Z)
      (Tk : thand) (i : Z) (orph : bool) (s : fname)
      (t : Z) (tokened : bool) :
    ent_tokenless i orph s t = negb tokened ->
    (tokened = true ->
       exists P, Tk !! t = Some P /\ ent_par_val i s ∈ P) ->
    dhand g Γd Bin Tk -∗
    ent_tok (fs_gamma_D g Γd) i orph s t
    ∗ dhand g Γd Bin
        (if tokened then tk_sub Tk t (ent_par_val i s) else Tk).
  Proof.
    intros Htl Hex. iIntros "Hh". destruct tokened.
    - destruct (Hex eq_refl) as (P & HP & Hv).
      iDestruct (dhand_tok_sub g Γd Bin Tk t (ent_par_val i s) P HP Hv
                   with "Hh") as "(Htok & Hptok & $)".
      rewrite /ent_tok Htl /=. iFrame "Htok Hptok".
    - rewrite /ent_tok Htl /=. iSplitR; [done | iExact "Hh"].
  Qed.

  Lemma dhand_ent_give (g : gname) (Γd : fs_dur_names) (Bin : gset Z)
      (Tk : thand) (i : Z) (orph : bool) (s : fname)
      (t : Z) (tokened : bool) :
    ent_tokenless i orph s t = negb tokened ->
    ent_tok (fs_gamma_D g Γd) i orph s t -∗ dhand g Γd Bin Tk -∗
    dhand g Γd Bin
      (if tokened then tk_add Tk t (ent_par_val i s) else Tk).
  Proof.
    intros Htl. iIntros "Htok Hh". destruct tokened.
    - rewrite /ent_tok Htl /=. iDestruct "Htok" as "[Hl Hp]".
      iApply (dhand_tok_add g Γd Bin Tk t (ent_par_val i s) with "Hh Hl Hp").
    - iExact "Hh".
  Qed.

End Ledger.

(* ===================================================================== *)
(*  3.  THE LEDGER                                                        *)
(* ===================================================================== *)

(* THE GHOST HALF OF A RECORD MOVE.  [FsStateInode.inode_ghost] is the link
   AUTHORITY at the node's own [nlink] plus the tokens its directory entries
   carry, so a record write moves it exactly when it moves [nlink] or the
   entry map.  Three shapes cover every record write in this kernel:

   - [GSame]   -- neither moves.  This is [iupdate]'s ordinary flush, and it
                  is also the BARE move (a free record becoming [ialloc]'s
                  claim box, or [iput]'s corpse): both bare nodes have
                  [nlink = 0] and no entries, so the two coincide and there
                  is deliberately no fourth constructor for them.
   - [GMint]   -- [nlink] goes up by one and the token goes to the fold's
                  hand, to be spent by the directory write that names the
                  inode.  [create]'s [ip->nlink = 1; iupdate(ip)] and
                  [mkdir]'s [dp->nlink++; iupdate(dp)].
   - [GBurn]   -- [nlink] goes DOWN by one and a token from the hand is
                  returned to the authority.  [unlink]'s [ip->nlink--],
                  [create]'s [fail:] arm, [iput]'s corpse.  Its argument is
                  the ORPHANING arm: [None] where the orphan flag does not
                  move, [Some t] where [nlink] reaches ZERO at a directory,
                  so [fn_orphan] flips and [".."]'s token -- which the
                  exemption stops charging for -- comes back to the hand at
                  its target [t].  See the note on [drec_ghost_ok] below for
                  why the MIRROR arm (a [GMint] that flips [fn_orphan] at a
                  node with non-empty entries) has no constructor.
   - [GIns]    -- the record's SIZE grows over a directory record that the
                  data write has already put in place, so one entry becomes
                  visible and takes a token.  [dirlink]'s [writei] tail.
                  [tokened] says whether the entry is one the counting rule
                  charges for ([FsStateInode.ent_tokenless] is [false]); a
                  self record or an orphan's dot entry is free and spends
                  nothing. *)
Inductive dghost :=
| GSame
(* the MINT and the BURN carry the PARENT REGISTER value of the unit they
   move (durable-disk G2): every counting token travels with one. *)
| GMint (v : option Z)
| GBurn (v : option Z) (odd : option Z)
| GIns (k0 : nat) (s : fname) (z : bv 16) (tokened : bool).

(* THE GHOST HALF OF A DATA-BLOCK WRITE.  A data write moves no [nlink], so
   the link AUTHORITY never moves here; what CAN move is the entry map of a
   DIRECTORY whose record the write makes live or dead, and with it one
   token.  Three shapes, and they are the three things a [writei] of sixteen
   bytes into a directory can do:

   - [BSame] -- the entry map does not move.  Every write to a file, and
                dirlink's APPEND sub-arm, whose record is written ABOVE the
                current count and only becomes visible when the SIZE grows
                (that growth is the record write's [GIns]).
   - [BIns]  -- dirlink's REUSE sub-arm: the record written is BELOW the
                count and was dead, so the entry becomes visible at this
                write and takes a token from the hand.
   - [BDel]  -- unlink's zeroing: the record's inum halfword goes to zero,
                the entry disappears, and its token goes to the hand. *)
Inductive dgblk :=
| BSame
| BIns (k0 : nat) (s : fname) (z : bv 16) (tokened : bool)
| BDel (s : fname) (t : Z) (tokened : bool).

(* ONE LEDGER ENTRY.  It names the OBJECT and its NEW value and nothing
   else: no other entry, no transaction, no durable byte map.  A writer
   extends the ledger by consing its own entry at its own AU. *)
Inductive dent :=
| DeRec    (i : Z) (n' : fs_node) (gh : dghost)
| DeBlk    (i : Z) (k : nat) (bs' : list (bv 8)) (gb : dgblk)
| DeHand   (b : Z) (bs' : list (bv 8))
| DeBmap   (b : Z) (alloc : bool)
| DeAdopt  (i : Z) (n' : fs_node) (k : nat) (gh : dghost).

Definition dledger : Type := list dent.

(* the home block and byte offset of inum [i]'s record, at the bundle's
   geometry -- [FsStateInode.rec_owned_at]'s two numbers *)
Definition drec_blk (Γd : fs_dur_names) (i : Z) : Z := fdn_ist Γd + i `div` 16.
Definition drec_off (i : Z) : nat := Z.to_nat (64 * (i `mod` 16)).

(* the durable content of one home block, read off the fold's byte map.  The
   hand of blocks is a SET, so this is how a block that left the pool at an
   existential content is named again once the fold has pinned it against
   the byte authority ([dblk_content]). *)
Definition dblk_at (D : gmap Z (list (bv 8))) (b : Z) : list (bv 8) :=
  default [] (D !! b).

(* the used set after a bitmap move *)
Definition dbm_used (S : fs_state_rec) (b : Z) (alloc : bool) : gset Z :=
  if alloc then fss_used S ∪ {[b]} else fss_used S ∖ {[b]}.

(* a node is its three fields *)
Lemma fs_node_eq (n1 n2 : fs_node) :
  fn_rec n1 = fn_rec n2 -> fn_ent n1 = fn_ent n2 -> fn_blk n1 = fn_blk n2 ->
  n1 = n2.
Proof. destruct n1, n2; simpl; intros -> -> ->; reflexivity. Qed.

(* THE ENTRY-MAP SIDE OF A COUNT MOVE, and the ONE shape that needed a
   decision rather than a transcription (worklist item 3c, design issue 2).

   [ent_toks] is indexed by [fn_orphan], so a count move that CROSSES zero
   re-prices every dot entry the node holds.  The two directions are not
   symmetric:

   - DOWN ([GBurn] at [nlink = 1 -> 0]): the exemption WIDENS, so every
     entry's token is still enough ([FsStateInode.ent_tok_orph_up]) and the
     [".."] token, no longer charged for, comes free to the hand.  That is
     [ent_toks_orphan], and [GBurn (Some t)] is exactly it.
   - UP ([GMint] at [nlink = 0 -> 1]): the exemption NARROWS, so the dot
     entries would have to be paid for out of nothing.  There is no lemma
     and there is no constructor -- and none is owed, because THIS KERNEL
     NEVER DOES IT: [dir_entries] is empty at anything that is not a
     directory, [create] raises [nlink] on a freshly [ialloc]ed child whose
     entry map is empty, [sys_link] refuses a directory outright, and every
     other [nlink++] ([mkdir]'s [dp->nlink++]) is at a directory that is
     already live.  So [GMint] asks for "the entries do not move AND either
     the orphan flag does not move or the entry map is empty", which is
     satisfied by every mint in the tree and by nothing that would need the
     missing lemma.  A future arm that re-links an orphan DIRECTORY would
     have to hand in one token per newly charged dot entry, and that is a
     ruling, not a gap in this file. *)
Definition drec_ghost_ok (i : Z) (n n' : fs_node) (gh : dghost)
    (Tk : thand) : Prop :=
  match gh with
  | GSame => fn_nlink n' = fn_nlink n
             /\ dir_entries n' = dir_entries n
             /\ fn_orphan n' = fn_orphan n
  | GMint _ => fn_nlink n' = S (fn_nlink n)
             /\ dir_entries n' = dir_entries n
             /\ (fn_orphan n' = fn_orphan n \/ dir_entries n = ∅)
  | GBurn v odd =>
      fn_nlink n = S (fn_nlink n')
      /\ dir_entries n' = dir_entries n
      /\ (exists P, Tk !! i = Some P /\ v ∈ P)
      /\ match odd with
         | None => fn_orphan n' = fn_orphan n \/ dir_entries n = ∅
         | Some t => fn_orphan n = false /\ fn_orphan n' = true
                     /\ dir_entries n !! DOTDOT = Some t /\ t <> i
         end
  | GIns k0 s z tokened =>
      fn_nlink n' = fn_nlink n
      /\ fn_orphan n' = fn_orphan n
      /\ fn_is_dir n = true /\ fn_is_dir n' = true
      /\ dir_first (fn_data n) (fn_nrec n) s = None
      /\ dir_insert_at (fn_data n) (fn_data n') (fn_nrec n) (fn_nrec n')
                       k0 s z
      /\ ent_tokenless i (fn_orphan n) s (bv_unsigned z) = negb tokened
      /\ (tokened = true ->
            exists P, Tk !! bv_unsigned z = Some P
                      /\ ent_par_val i s ∈ P)
  end.

Definition drec_ghost_next (i : Z) (gh : dghost) (Tk : thand) : thand :=
  match gh with
  | GSame => Tk
  | GMint v => tk_add Tk i v
  | GBurn v odd => match odd with
                   | None => tk_sub Tk i v
                   | Some t => tk_add (tk_sub Tk i v) t None
                   end
  | GIns _ s z tokened =>
      if tokened then tk_sub Tk (bv_unsigned z) (ent_par_val i s) else Tk
  end.

(* THE DATA WRITE'S GHOST HALF.  [fn_set_blk] keeps [fn_nlink] and therefore
   [fn_orphan] ([FsStateInode.fn_nlink_set_blk] / [fn_orphan_set_blk]), so
   the link AUTHORITY never moves here and only the entry map can. *)
Definition dblk_ghost_ok (i : Z) (n n' : fs_node) (gb : dgblk)
    (Tk : thand) : Prop :=
  match gb with
  | BSame => dir_entries n' = dir_entries n
  | BIns k0 s z tokened =>
      fn_is_dir n = true /\ fn_is_dir n' = true
      /\ dir_first (fn_data n) (fn_nrec n) s = None
      /\ dir_insert_at (fn_data n) (fn_data n') (fn_nrec n) (fn_nrec n')
                       k0 s z
      /\ ent_tokenless i (fn_orphan n) s (bv_unsigned z) = negb tokened
      /\ (tokened = true ->
            exists P, Tk !! bv_unsigned z = Some P
                      /\ ent_par_val i s ∈ P)
  | BDel s t tokened =>
      dir_entries n !! s = Some t
      /\ dir_entries n' = delete s (dir_entries n)
      /\ ent_tokenless i (fn_orphan n) s t = negb tokened
  end.

Definition dblk_ghost_next (i : Z) (gb : dgblk) (Tk : thand) : thand :=
  match gb with
  | BSame => Tk
  | BIns _ s z tokened =>
      if tokened then tk_sub Tk (bv_unsigned z) (ent_par_val i s) else Tk
  | BDel s t tokened =>
      if tokened then tk_add Tk t (ent_par_val i s) else Tk
  end.

(* THE ENTRY'S PRECONDITIONS -- the LIBRARY MOVER's own, and nothing more.
   Every clause is either about the entry's two values or about the object
   the entry names; none quantifies over the ledger, over another entry, or
   over the durable byte map. *)
Definition dent_ok (Γd : fs_dur_names) (e : dent) (c : dcfg) : Prop :=
  match e with
  | DeRec i n' gh =>
      0 <= i < fdn_nin Γd
      /\ 0 <= i < 2 ^ 32
      /\ dinode_wf (fn_rec n')
      /\ is_Some (dc_D c !! drec_blk Γd i)
      /\ (forall n, fss_inodes (dc_S c) !! i = Some n ->
            dinode_wf (fn_rec n)
            /\ fn_blk n' = fn_blk n
            /\ fn_ent n' = fn_ent n
            /\ fn_indb n' = fn_indb n
            /\ fn_addrs_kept n n'
            /\ inode_local i n'
            /\ drec_ghost_ok i n n' gh (dc_toks c))
  | DeBlk i k bs' gb =>
      0 <= i < fdn_nin Γd
      /\ length bs' = BSIZE
      /\ (forall n, fss_inodes (dc_S c) !! i = Some n ->
            is_Some (fn_blk n !! k)
            /\ is_Some (dc_D c !! fn_naddr n k)
            /\ inode_local i (fn_set_blk n k bs')
            /\ dblk_ghost_ok i n (fn_set_blk n k bs') gb (dc_toks c))
  | DeHand b bs' =>
      b ∈ dc_bin c
      /\ length bs' = BSIZE
      /\ is_Some (dc_D c !! b)
  | DeBmap b alloc =>
      is_Some (dc_D c !! fdn_bmap Γd)
      /\ 0 <= b < sb_size (fss_sb (dc_S c))
      /\ (if alloc
          then b ∉ fss_used (dc_S c) /\ b ∉ dc_bin c
          else b ∈ dc_bin c)
  | DeAdopt i n' k gh =>
      0 <= i < fdn_nin Γd
      /\ 0 <= i < 2 ^ 32
      /\ dinode_wf (fn_rec n')
      /\ is_Some (dc_D c !! drec_blk Γd i)
      /\ fn_naddr n' k ∈ dc_bin c
      /\ is_Some (dc_D c !! fn_naddr n' k)
      /\ (forall n, fss_inodes (dc_S c) !! i = Some n ->
            dinode_wf (fn_rec n)
            /\ fn_blk n !! k = None
            /\ fn_ent n' = fn_ent n
            /\ fn_indb n' = fn_indb n
            /\ fn_addrs_kept n n'
            /\ fn_blk n' = <[k := dblk_at (dc_D c) (fn_naddr n' k)]> (fn_blk n)
            /\ inode_local i n'
            /\ drec_ghost_ok i n n' gh (dc_toks c))
  end.

Definition dS_upd (S : fs_state_rec) (i : Z) (n : fs_node) : fs_state_rec :=
  MkFsS (fss_sb S) (fss_sbb S) (<[i := n]> (fss_inodes S)) (fss_used S).

Definition dS_used (S : fs_state_rec) (u : gset Z) : fs_state_rec :=
  MkFsS (fss_sb S) (fss_sbb S) (fss_inodes S) u.

Definition dent_next (Γd : fs_dur_names) (e : dent) (c : dcfg) : dcfg :=
  match e with
  | DeRec i n' gh =>
      MkDCfg (dS_upd (dc_S c) i n')
             (dc_bin c)
             (drec_ghost_next i gh (dc_toks c))
             (dsplice (dc_D c) (drec_blk Γd i) (drec_off i)
                      (dinode_bytes (fn_rec n')))
  | DeBlk i k bs' gb =>
      match fss_inodes (dc_S c) !! i with
      | Some n =>
          MkDCfg (dS_upd (dc_S c) i (fn_set_blk n k bs'))
                 (dc_bin c) (dblk_ghost_next i gb (dc_toks c))
                 (dsplice (dc_D c) (fn_naddr n k) 0%nat bs')
      | None => c
      end
  | DeHand b bs' =>
      MkDCfg (dc_S c) (dc_bin c) (dc_toks c)
             (dsplice (dc_D c) b 0%nat bs')
  | DeBmap b alloc =>
      MkDCfg (dS_used (dc_S c) (dbm_used (dc_S c) b alloc))
             (if alloc then {[b]} ∪ dc_bin c else dc_bin c ∖ {[b]})
             (dc_toks c)
             (dsplice (dc_D c) (fdn_bmap Γd) 0%nat
                      (bm_bytes BSIZE (dbm_used (dc_S c) b alloc)))
  | DeAdopt i n' k gh =>
      MkDCfg (dS_upd (dc_S c) i n')
             (dc_bin c ∖ {[fn_naddr n' k]})
             (drec_ghost_next i gh (dc_toks c))
             (dsplice (dc_D c) (drec_blk Γd i) (drec_off i)
                      (dinode_bytes (fn_rec n')))
  end.

(* THE GEOMETRY IS INVARIANT.  Neither entry kind touches the superblock or
   the inode map's DOMAIN, so the three equations survive every step -- which
   is what lets the fold's induction carry them. *)
Lemma dgeo_ok_step (Γd : fs_dur_names) (e : dent) (c : dcfg) :
  dgeo_ok Γd (dc_S c) -> dgeo_ok Γd (dc_S (dent_next Γd e c)).
Proof.
  intros Hgeo. pose proof Hgeo as (H1 & H2 & H3).
  assert (Hupd : forall i n, dgeo_ok Γd (dS_upd (dc_S c) i n)).
  { intros i n. rewrite /dgeo_ok /dS_upd /=.
    split; [exact H1 |]. split; [exact H2 |].
    intros j Hj. destruct (decide (j = i)) as [-> | Hne].
    - rewrite lookup_insert. by eexists.
    - rewrite lookup_insert_ne; [exact (H3 j Hj) | congruence]. }
  destruct e as [i n' gh | i k bs' gb | b bs' | b alloc | i n' k gh]; simpl.
  - exact (Hupd i n').
  - destruct (fss_inodes (dc_S c) !! i) as [n |];
      [exact (Hupd i _) | exact Hgeo].
  - exact Hgeo.
  - exact Hgeo.
  - exact (Hupd i n').
Qed.

Section LedgerStep.
  Context `{!fsLinkG Σ, !fsTopG Σ, !diskImgG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  3a.  THE RECORD'S BYTES, at the bundle's geometry                   *)
  (* ------------------------------------------------------------------ *)

  Lemma drec_owned_at (g : gname) (Γd : fs_dur_names) (S : fs_state_rec)
      (i : Z) (dn : dinode) :
    dgeo_ok Γd S -> 0 <= i < 2 ^ 32 ->
    rec_owned (fs_gamma_D g Γd) (fss_sb S) i dn
    ⊣⊢ byte_range (fs_gamma_D g Γd) (drec_blk Γd i)
                  (Z.of_nat (drec_off i)) (dinode_bytes dn).
  Proof.
    intros (_ & Hist & _) Hi.
    rewrite (rec_owned_sb (fs_gamma_D g Γd) (fss_sb S) i dn Hi).
    rewrite /rec_owned_at /drec_blk /drec_off Hist.
    pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as [Hm0 Hm1].
    assert (Hoff : Z.of_nat (Z.to_nat (64 * (i `mod` 16))) = 64 * (i `mod` 16))
      by lia.
    rewrite Hoff //.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3a'. A WHOLE BLOCK, and the CONTENT the fold reads off the map      *)
  (* ------------------------------------------------------------------ *)

  (* the byte workhorse at a WHOLE home block -- the shape every entry that
     rewrites a block outright (a data write, a [bzero] of a block in the
     hand, the bitmap block) uses *)
  Lemma dbytes_blk_update (g : gname) (Γd : fs_dur_names)
      (D : gmap Z (list (bv 8))) (b : Z) (bs obs nbs : list (bv 8)) :
    dbytes_tot D -> D !! b = Some bs -> length nbs = BSIZE ->
    ghost_map_auth g 1 (fs_dbytes D) -∗
    blk_owned (fs_gamma_D g Γd) b obs ==∗
    ghost_map_auth g 1 (fs_dbytes (<[b := nbs]> D))
    ∗ blk_owned (fs_gamma_D g Γd) b nbs.
  Proof.
    intros HD Hb Hn. iIntros "Ha Hblk".
    iDestruct (blk_owned_length with "Hblk") as %Hol.
    iEval (rewrite /blk_owned) in "Hblk". iDestruct "Hblk" as "[_ Hr]".
    assert (Hz : Z.of_nat 0%nat = 0) by lia.
    assert (Hll : length obs = length nbs) by (rewrite Hol Hn //).
    assert (Hoff : (0 + length nbs <= BSIZE)%nat) by (rewrite Hn; lia).
    iMod (dbytes_range_update g Γd D b bs 0%nat obs nbs HD Hb Hll Hoff
            with "Ha [Hr]") as "[Ha Hr]"; [rewrite Hz; iExact "Hr" |].
    rewrite (blk_splice_whole nbs bs
               ltac:(rewrite Hn (HD _ _ Hb); reflexivity)).
    iModIntro. iFrame "Ha". rewrite /blk_owned. iSplitR; [done |].
    rewrite Hz. iExact "Hr".
  Qed.

  (* THE HAND'S BLOCKS HAVE NO VALUE OF THEIR OWN, AND DO NOT NEED ONE.
     A block that left [free_bitmap]'s pool arrived at an existential
     content, so the ledger cannot name it -- but the fold holds the byte
     AUTHORITY at [fs_dbytes D] and the block's own elements, and the two
     together say the content IS [D]'s.  Same device as the record
     coherence: what a writer cannot name, agreement pins. *)
  Lemma dblk_content (g : gname) (Γd : fs_dur_names)
      (D : gmap Z (list (bv 8))) (b : Z) (bs cs : list (bv 8)) :
    dbytes_tot D -> D !! b = Some cs ->
    ghost_map_auth g 1 (fs_dbytes D) -∗
    blk_owned (fs_gamma_D g Γd) b bs -∗ ⌜bs = cs⌝.
  Proof.
    intros HD Hb. iIntros "Ha Hblk".
    iDestruct (blk_owned_length with "Hblk") as %Hlb.
    assert (Hlc : length cs = BSIZE) by exact (HD b cs Hb).
    assert (Hok : dbytes_ok D) by exact (dbytes_ok_full D HD).
    iEval (rewrite /blk_owned) in "Hblk". iDestruct "Hblk" as "[_ Hr]".
    assert (Hz : (0 : Z) = Z.of_nat 0%nat) by lia.
    rewrite Hz (byte_range_dbelems g Γd b (Z.of_nat 0%nat) bs) /fs_dbelems.
    iDestruct (ghost_map_lookup_big with "Ha Hr") as %Hsub.
    iPureIntro. apply list_eq. intros j.
    destruct (decide (j < BSIZE)%nat) as [Hj | Hj]; last first.
    { rewrite (lookup_ge_None_2 bs j ltac:(lia))
              (lookup_ge_None_2 cs j ltac:(lia)) //. }
    destruct (lookup_lt_is_Some_2 bs j ltac:(lia)) as [v Hv].
    destruct (lookup_lt_is_Some_2 cs j ltac:(lia)) as [w Hw].
    rewrite Hv Hw. f_equal.
    assert (Hm : (map_seqZ (b * Z.of_nat BSIZE + Z.of_nat 0%nat) bs
                  : gmap Z (bv 8))
                 !! (b * Z.of_nat BSIZE + Z.of_nat j) = Some v).
    { rewrite lookup_map_seqZ.
      rewrite (option_guard_True
                 (b * Z.of_nat BSIZE + Z.of_nat 0%nat
                  <= b * Z.of_nat BSIZE + Z.of_nat j)); [| lia].
      assert (Hjj : Z.to_nat (b * Z.of_nat BSIZE + Z.of_nat j
                              - (b * Z.of_nat BSIZE + Z.of_nat 0%nat)) = j)
        by lia.
      rewrite Hjj Hv //. }
    assert (Hv' : fs_dbytes D !! (b * Z.of_nat BSIZE + Z.of_nat j) = Some v)
      by exact (lookup_weaken _ _ _ _ Hm Hsub).
    assert (Hw' : fs_dbytes D !! (b * Z.of_nat BSIZE + Z.of_nat j) = Some w)
      by exact (fs_dbytes_lookup D b cs j w Hok Hb Hw).
    rewrite Hv' in Hw'. by injection Hw'.
  Qed.

  (* the bitmap piece of the state, out and back *)
  Lemma fs_state_bm_acc (Γ : fs_view_names Σ) (S : fs_state_rec) :
    fs_state Γ S ⊢ free_bitmap Γ (fss_sb S) (fss_used S)
      ∗ (∀ u', free_bitmap Γ (fss_sb S) u' -∗ fs_state Γ (dS_used S u')).
  Proof.
    rewrite /fs_state /dS_used. iIntros "(Hsb & Hin & $)".
    iIntros (u') "Hbm". cbn [fss_sb fss_sbb fss_inodes fss_used]. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3b.  THE GHOST HALF OF A RECORD MOVE                                *)
  (* ------------------------------------------------------------------ *)

  Lemma dghost_move (g : gname) (Γd : fs_dur_names) (i : Z) (n n' : fs_node)
      (gh : dghost) (Bin : gset Z) (Tk : thand) :
    drec_ghost_ok i n n' gh Tk ->
    inode_local i n' ->
    inode_ghost (fs_gamma_D g Γd) i n -∗ dhand g Γd Bin Tk ==∗
    inode_ghost (fs_gamma_D g Γd) i n'
    ∗ dhand g Γd Bin (drec_ghost_next i gh Tk).
  Proof.
    intros Hgh Hloc. iIntros "(Ha & Ht & _ & Hpa) Hh".
    rewrite /inode_ghost.
    destruct gh as [| v | v odd | k0 s z tokened]; simpl.
    - destruct Hgh as (Hnl & Hde & Ho).
      iDestruct (inode_par_cong (fs_gamma_D g Γd) i n n'
                   ltac:(lia) with "Hpa") as "Hpa".
      rewrite Hnl -(ent_toks_cong_ent (fs_gamma_D g Γd) i n n' Ho Hde).
      iModIntro. iFrame "Ha Ht Hh Hpa". by iPureIntro.
    - destruct Hgh as (Hnl & Hde & Horph).
      iMod (link_mint (fs_gamma_D g Γd) i (fn_nlink n) with "Ha")
        as "[Ha Htok]".
      iMod (inode_par_mint (fs_gamma_D g Γd) i n n' v ltac:(lia) with "Hpa")
        as "[Hpa Hptok]".
      iDestruct (dhand_tok_add g Γd Bin Tk i v with "Hh Htok Hptok") as "Hh".
      rewrite Hnl. iModIntro. iFrame "Ha Hh Hpa".
      iSplitL "Ht"; [| by iPureIntro].
      destruct Horph as [Ho | Hemp].
      + rewrite -(ent_toks_cong_ent (fs_gamma_D g Γd) i n n' Ho Hde).
        iExact "Ht".
      + rewrite /ent_toks Hde Hemp big_sepM_empty. done.
    - destruct Hgh as (Hnl & Hde & (P & HP & Hv) & Harm).
      iDestruct (dhand_tok_sub g Γd Bin Tk i v P HP Hv with "Hh")
        as "(Htok & Hptok & Hh)".
      iEval (rewrite Hnl) in "Ha".
      iMod (link_return (fs_gamma_D g Γd) i (fn_nlink n') with "Ha Htok")
        as "Ha".
      iMod (inode_par_retire (fs_gamma_D g Γd) i n n' v ltac:(lia)
              with "Hpa Hptok") as "Hpa".
      destruct odd as [t |].
      + destruct Harm as (Ho & Ho' & Hdd & Hne).
        iDestruct (ent_toks_orphan (fs_gamma_D g Γd) i n n' t Hde Ho Ho' Hdd
                     Hne with "Ht") as "[[Htk Hptk] Ht]".
        iDestruct (dhand_tok_add g Γd Bin (tk_sub Tk i v) t None
                     with "Hh Htk Hptk") as "Hh".
        iModIntro. iFrame "Ha Ht Hh Hpa". by iPureIntro.
      + iModIntro. iFrame "Ha Hh Hpa". iSplitL "Ht"; [| by iPureIntro].
        destruct Harm as [Ho | Hemp].
        * rewrite -(ent_toks_cong_ent (fs_gamma_D g Γd) i n n' Ho Hde).
          iExact "Ht".
        * rewrite /ent_toks Hde Hemp big_sepM_empty. done.
    - destruct Hgh as (Hnl & Ho & Hd & Hd' & Hfirst & Hins & Htl & Htk).
      iDestruct (inode_par_cong (fs_gamma_D g Γd) i n n'
                   ltac:(lia) with "Hpa") as "Hpa".
      rewrite Hnl.
      iDestruct (dhand_ent_take g Γd Bin Tk i (fn_orphan n) s
                   (bv_unsigned z) tokened Htl Htk with "Hh") as "[Htok Hh]".
      iDestruct (ent_toks_insert (fs_gamma_D g Γd) i n n' k0 s z
                   Ho Hd Hd' Hfirst Hins with "Ht Htok") as "Ht".
      iModIntro. iFrame "Ha Ht Hh Hpa". by iPureIntro.
  Qed.

  (* ...and of a DATA-BLOCK write.  The authority never moves ([fn_set_blk]
     keeps [fn_nlink]); only a directory's entry map can. *)
  Lemma dblk_ghost_move (g : gname) (Γd : fs_dur_names) (i : Z)
      (n n' : fs_node) (gb : dgblk) (Bin : gset Z) (Tk : thand) :
    dblk_ghost_ok i n n' gb Tk ->
    fn_nlink n' = fn_nlink n -> fn_orphan n' = fn_orphan n ->
    inode_local i n' ->
    inode_ghost (fs_gamma_D g Γd) i n -∗ dhand g Γd Bin Tk ==∗
    inode_ghost (fs_gamma_D g Γd) i n'
    ∗ dhand g Γd Bin (dblk_ghost_next i gb Tk).
  Proof.
    intros Hgb Hnl Ho Hloc. iIntros "(Ha & Ht & _ & Hpa) Hh".
    iDestruct (inode_par_cong (fs_gamma_D g Γd) i n n'
                 ltac:(lia) with "Hpa") as "Hpa".
    rewrite /inode_ghost Hnl.
    destruct gb as [| k0 s z tokened | s t tokened]; simpl.
    - rewrite -(ent_toks_cong_ent (fs_gamma_D g Γd) i n n' Ho Hgb).
      iModIntro. iFrame "Ha Ht Hh Hpa". by iPureIntro.
    - destruct Hgb as (Hd & Hd' & Hfirst & Hins & Htl & Htk).
      iDestruct (dhand_ent_take g Γd Bin Tk i (fn_orphan n) s
                   (bv_unsigned z) tokened Htl Htk with "Hh") as "[Htok Hh]".
      iDestruct (ent_toks_insert (fs_gamma_D g Γd) i n n' k0 s z
                   Ho Hd Hd' Hfirst Hins with "Ht Htok") as "Ht".
      iModIntro. iFrame "Ha Ht Hh Hpa". by iPureIntro.
    - destruct Hgb as (Hs & Hdel & Htl).
      iDestruct (ent_toks_delete (fs_gamma_D g Γd) i n n' s t Ho Hs Hdel
                   with "Ht") as "[Htok Ht]".
      iDestruct (dhand_ent_give g Γd Bin Tk i (fn_orphan n) s t tokened Htl
                   with "Htok Hh") as "Hh".
      iModIntro. iFrame "Ha Ht Hh Hpa". by iPureIntro.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  3c.  ONE LEDGER STEP, AT THE RESOURCES                              *)
  (* ------------------------------------------------------------------ *)

  Theorem dent_step_res (g : gname) (Γd : fs_dur_names) (e : dent)
      (c : dcfg) :
    dbytes_tot (dc_D c) -> dgeo_ok Γd (dc_S c) -> dent_ok Γd e c ->
    dcfg_res g Γd c ==∗ dcfg_res g Γd (dent_next Γd e c).
  Proof.
    intros HD Hgeo Hok.
    iIntros "(Hb & Hh & Hauth)".
    iDestruct "Hb" as "(Htop & Hfr & Hst)".
    destruct e as [i n' gh | i k bs' gb | b bs' | b alloc | i n' k gh].
    - (* ---- the RECORD move ---- *)
      destruct Hok as (Hrng & H32 & Hwf' & [bs Hbs] & Hn).
      destruct Hgeo as (Hbm & Hist & Hex) eqn:Hgeoeq.
      destruct (Hex i Hrng) as [n Hni].
      destruct (Hn n Hni)
        as (Hwf & Hblk & Hent & Hindb & Hkept & Hloc' & Hgh).
      (* the state's inode, out and back *)
      iDestruct (fs_state_inode_acc (fs_gamma_D g Γd) (dc_S c) i n Hni
                   with "Hst") as "[Hin Hstback]".
      iDestruct "Hin" as "[Hphi Hgho]".
      iDestruct (inode_phi_rec_move (fs_gamma_D g Γd) (fss_sb (dc_S c)) i n n'
                   Hblk Hent Hindb Hkept with "Hphi") as "[Hrec Hphiback]".
      (* the bytes *)
      rewrite (drec_owned_at g Γd (dc_S c) i (fn_rec n) Hgeo H32).
      assert (Hl : length (dinode_bytes (fn_rec n))
                   = length (dinode_bytes (fn_rec n'))).
      { rewrite (dinode_bytes_length _ Hwf) (dinode_bytes_length _ Hwf') //. }
      pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as [Hm0 Hm1].
      assert (Hoffb : (drec_off i + length (dinode_bytes (fn_rec n'))
                       <= BSIZE)%nat).
      { rewrite (dinode_bytes_length _ Hwf') /drec_off BSIZE_1024. lia. }
      iMod (dbytes_range_update g Γd (dc_D c) (drec_blk Γd i) bs
              (drec_off i) (dinode_bytes (fn_rec n))
              (dinode_bytes (fn_rec n')) HD Hbs Hl Hoffb
              with "Hauth Hrec") as "[Hauth Hrec]".
      rewrite -(drec_owned_at g Γd (dc_S c) i (fn_rec n') Hgeo H32).
      iDestruct ("Hphiback" with "Hrec") as "Hphi".
      (* the ghost half *)
      iMod (dghost_move g Γd i n n' gh (dc_bin c) (dc_toks c) Hgh Hloc'
              with "Hgho Hh") as "[Hgho Hh]".
      iDestruct ("Hstback" $! n' with "[Hphi Hgho]") as "Hst";
        [by iFrame |].
      (* the top map *)
      iDestruct (big_sepM_insert_acc _ _ i n Hni with "Hfr") as "[Hf Hfrback]".
      iMod (ghost_map_update n' with "Htop Hf") as "[Htop Hf]".
      iDestruct ("Hfrback" $! n' with "Hf") as "Hfr".
      assert (Hnext : dent_next Γd (DeRec i n' gh) c
                      = MkDCfg (dS_upd (dc_S c) i n') (dc_bin c)
                          (drec_ghost_next i gh (dc_toks c))
                          (<[drec_blk Γd i
                             := blk_splice (drec_off i)
                                  (dinode_bytes (fn_rec n')) bs]> (dc_D c))).
      { cbn [dent_next]. rewrite /dsplice Hbs //. }
      iModIntro. rewrite Hnext /dcfg_res /dbody /dS_upd.
      cbn [dc_S dc_bin dc_toks dc_D fss_sb fss_sbb fss_inodes fss_used].
      iFrame.
    - (* ---- one DATA block's bytes ---- *)
      destruct Hok as (Hrng & Hlen' & Hn).
      destruct Hgeo as (Hbm & Hist & Hex) eqn:Hgeoeq.
      destruct (Hex i Hrng) as [n Hni].
      destruct (Hn n Hni) as (Hk & [bs Hbs] & Hloc' & Hgb).
      destruct Hk as [obs Hobs].
      iDestruct (fs_state_inode_acc (fs_gamma_D g Γd) (dc_S c) i n Hni
                   with "Hst") as "[Hin Hstback]".
      iDestruct "Hin" as "[Hphi Hgho]".
      iDestruct (inode_phi_blk_move (fs_gamma_D g Γd) (fss_sb (dc_S c)) i n k
                   obs bs' Hobs with "Hphi") as "[Hblk Hphiback]".
      iMod (dbytes_blk_update g Γd (dc_D c) (fn_naddr n k) bs obs bs'
              HD Hbs Hlen' with "Hauth Hblk") as "[Hauth Hblk]".
      iDestruct ("Hphiback" with "Hblk") as "Hphi".
      (* the ghost half *)
      iMod (dblk_ghost_move g Γd i n (fn_set_blk n k bs') gb (dc_bin c)
              (dc_toks c) Hgb (fn_nlink_set_blk n k bs')
              (fn_orphan_set_blk n k bs') Hloc' with "Hgho Hh")
        as "[Hgho Hh]".
      iDestruct ("Hstback" $! (fn_set_blk n k bs') with "[Hphi Hgho]")
        as "Hst"; [by iFrame |].
      iDestruct (big_sepM_insert_acc _ _ i n Hni with "Hfr") as "[Hf Hfrback]".
      iMod (ghost_map_update (fn_set_blk n k bs') with "Htop Hf")
        as "[Htop Hf]".
      iDestruct ("Hfrback" $! (fn_set_blk n k bs') with "Hf") as "Hfr".
      assert (Hnext : dent_next Γd (DeBlk i k bs' gb) c
                      = MkDCfg (dS_upd (dc_S c) i (fn_set_blk n k bs'))
                          (dc_bin c) (dblk_ghost_next i gb (dc_toks c))
                          (<[fn_naddr n k := bs']> (dc_D c))).
      { cbn [dent_next]. rewrite Hni.
        rewrite (dsplice_whole (dc_D c) (fn_naddr n k) bs bs' Hbs
                   ltac:(rewrite Hlen' (HD _ _ Hbs); reflexivity)) //. }
      iModIntro. rewrite Hnext /dcfg_res /dbody /dS_upd.
      cbn [dc_S dc_bin dc_toks dc_D fss_sb fss_sbb fss_inodes fss_used].
      iFrame.
    - (* ---- a block held in the HAND ---- *)
      destruct Hok as (Hbin & Hlen' & [cs Hcs]).
      iDestruct (dhand_blk_acc g Γd (dc_bin c) (dc_toks c) b Hbin with "Hh")
        as "[Hblk Hhback]".
      iDestruct "Hblk" as (obs) "Hblk".
      iMod (dbytes_blk_update g Γd (dc_D c) b cs obs bs' HD Hcs Hlen'
              with "Hauth Hblk") as "[Hauth Hblk]".
      iDestruct ("Hhback" $! bs' with "Hblk") as "Hh".
      assert (Hnext : dent_next Γd (DeHand b bs') c
                      = MkDCfg (dc_S c) (dc_bin c) (dc_toks c)
                          (<[b := bs']> (dc_D c))).
      { cbn [dent_next].
        rewrite (dsplice_whole (dc_D c) b cs bs' Hcs
                   ltac:(rewrite Hlen' (HD _ _ Hcs); reflexivity)) //. }
      iModIntro. rewrite Hnext /dcfg_res /dbody.
      cbn [dc_S dc_bin dc_toks dc_D]. iFrame.
    - (* ---- the BITMAP block, and one block between pool and hand ---- *)
      destruct Hok as ([bs Hbs] & Hrng & Harm).
      pose proof Hgeo as (Hbm & Hist & Hex).
      iDestruct (fs_state_bm_acc (fs_gamma_D g Γd) (dc_S c) with "Hst")
        as "[Hbmp Hstback]".
      assert (Hbs' : dc_D c !! sb_bmapstart (fss_sb (dc_S c)) = Some bs)
        by (rewrite Hbm; exact Hbs).
      assert (Hlbs : length bs = BSIZE) by exact (HD _ _ Hbs).
      rewrite /free_bitmap.
      destruct alloc.
      + (* ALLOCATE: the bit is set and the block leaves the pool *)
        destruct Harm as (Hnu & Hnbin).
        iDestruct (bitmap_alloc (fs_gamma_D g Γd)
                     (sb_bmapstart (fss_sb (dc_S c)))
                     (sb_size (fss_sb (dc_S c))) (fss_used (dc_S c)) b
                     Hrng Hnu with "Hbmp") as "(Hnew & Hbmblk & Hbmback)".
        iDestruct "Hnew" as (obs) "Hnew".
        iMod (dbytes_blk_update g Γd (dc_D c)
                (sb_bmapstart (fss_sb (dc_S c))) bs
                (bm_bytes BSIZE (fss_used (dc_S c)))
                (bm_bytes BSIZE (fss_used (dc_S c) ∪ {[b]}))
                HD Hbs' (bm_bytes_length _ _) with "Hauth Hbmblk")
          as "[Hauth Hbmblk]".
        iDestruct ("Hbmback" with "Hbmblk") as "Hbmp".
        iDestruct ("Hstback" $! (fss_used (dc_S c) ∪ {[b]}) with "Hbmp")
          as "Hst".
        iDestruct (dhand_blk_add g Γd (dc_bin c) (dc_toks c) b obs Hnbin
                     with "Hh Hnew") as "Hh".
        assert (Hnext : dent_next Γd (DeBmap b true) c
                = MkDCfg (dS_used (dc_S c) (fss_used (dc_S c) ∪ {[b]}))
                    ({[b]} ∪ dc_bin c) (dc_toks c)
                    (<[sb_bmapstart (fss_sb (dc_S c))
                       := bm_bytes BSIZE (fss_used (dc_S c) ∪ {[b]})]>
                       (dc_D c))).
        { assert (Hln : length (bm_bytes BSIZE (fss_used (dc_S c) ∪ {[b]}))
                        = length bs)
            by (rewrite bm_bytes_length Hlbs; reflexivity).
          cbn [dent_next]. rewrite /dbm_used /=. rewrite -Hbm.
          rewrite (dsplice_whole (dc_D c) (sb_bmapstart (fss_sb (dc_S c))) bs
                     (bm_bytes BSIZE (fss_used (dc_S c) ∪ {[b]})) Hbs' Hln) //. }
        iModIntro. rewrite Hnext /dcfg_res /dbody /dS_used.
        cbn [dc_S dc_bin dc_toks dc_D fss_sb fss_sbb fss_inodes fss_used].
        iFrame.
      + (* FREE: the block goes back into the pool and the bit is cleared *)
        iDestruct (dhand_blk_sub g Γd (dc_bin c) (dc_toks c) b Harm with "Hh")
          as "[Hold Hh]".
        iDestruct "Hold" as (obs) "Hold".
        iDestruct (bitmap_free (fs_gamma_D g Γd) (fs_gamma_D_excl g Γd)
                     (sb_bmapstart (fss_sb (dc_S c)))
                     (sb_size (fss_sb (dc_S c))) (fss_used (dc_S c)) b obs
                     Hrng with "Hbmp Hold") as "(_ & Hbmblk & Hbmback)".
        iMod (dbytes_blk_update g Γd (dc_D c)
                (sb_bmapstart (fss_sb (dc_S c))) bs
                (bm_bytes BSIZE (fss_used (dc_S c)))
                (bm_bytes BSIZE (fss_used (dc_S c) ∖ {[b]}))
                HD Hbs' (bm_bytes_length _ _) with "Hauth Hbmblk")
          as "[Hauth Hbmblk]".
        iDestruct ("Hbmback" with "Hbmblk") as "Hbmp".
        iDestruct ("Hstback" $! (fss_used (dc_S c) ∖ {[b]}) with "Hbmp")
          as "Hst".
        assert (Hnext : dent_next Γd (DeBmap b false) c
                = MkDCfg (dS_used (dc_S c) (fss_used (dc_S c) ∖ {[b]}))
                    (dc_bin c ∖ {[b]}) (dc_toks c)
                    (<[sb_bmapstart (fss_sb (dc_S c))
                       := bm_bytes BSIZE (fss_used (dc_S c) ∖ {[b]})]>
                       (dc_D c))).
        { assert (Hln : length (bm_bytes BSIZE (fss_used (dc_S c) ∖ {[b]}))
                        = length bs)
            by (rewrite bm_bytes_length Hlbs; reflexivity).
          cbn [dent_next]. rewrite /dbm_used /=. rewrite -Hbm.
          rewrite (dsplice_whole (dc_D c) (sb_bmapstart (fss_sb (dc_S c))) bs
                     (bm_bytes BSIZE (fss_used (dc_S c) ∖ {[b]})) Hbs' Hln) //. }
        iModIntro. rewrite Hnext /dcfg_res /dbody /dS_used.
        cbn [dc_S dc_bin dc_toks dc_D fss_sb fss_sbb fss_inodes fss_used].
        iFrame.
    - (* ---- a block from the HAND joins the inode at the record write ---- *)
      destruct Hok as (Hrng & H32 & Hwf' & [bs Hbs] & Hbin & [cs Hcs] & Hn).
      destruct Hgeo as (Hbm & Hist & Hex) eqn:Hgeoeq.
      destruct (Hex i Hrng) as [n Hni].
      destruct (Hn n Hni)
        as (Hwf & Hkn & Hent & Hindb & Hkept & Hblk' & Hloc' & Hgh).
      (* the block, out of the hand, and its content read off the map *)
      iDestruct (dhand_blk_sub g Γd (dc_bin c) (dc_toks c) (fn_naddr n' k)
                   Hbin with "Hh") as "[Hnew Hh]".
      iDestruct "Hnew" as (obs) "Hnew".
      iDestruct (dblk_content g Γd (dc_D c) (fn_naddr n' k) obs cs HD Hcs
                   with "Hauth Hnew") as %->.
      assert (Hcsat : dblk_at (dc_D c) (fn_naddr n' k) = cs)
        by (rewrite /dblk_at Hcs //).
      (* the intermediate node: the new RECORD, the old blocks *)
      pose (n1 := MkNode (fn_rec n') (fn_ent n) (fn_blk n)).
      assert (Hnn : forall j, fn_naddr n1 j = fn_naddr n' j).
      { intros j. rewrite /fn_naddr /n1 /=. rewrite Hent //. }
      assert (Hb1 : fn_blk n1 = fn_blk n) by reflexivity.
      assert (He1 : fn_ent n1 = fn_ent n) by reflexivity.
      assert (Hi1 : fn_indb n1 = fn_indb n).
      { rewrite /fn_indb /n1 /=. exact Hindb. }
      assert (Hk1 : fn_addrs_kept n n1).
      { intros j Hj. rewrite Hnn. exact (Hkept j Hj). }
      iDestruct (fs_state_inode_acc (fs_gamma_D g Γd) (dc_S c) i n Hni
                   with "Hst") as "[Hin Hstback]".
      iDestruct "Hin" as "[Hphi Hgho]".
      iDestruct (inode_phi_rec_move (fs_gamma_D g Γd) (fss_sb (dc_S c)) i n n1
                   Hb1 He1 Hi1 Hk1 with "Hphi") as "[Hrec Hphiback]".
      (* the record's bytes *)
      rewrite (drec_owned_at g Γd (dc_S c) i (fn_rec n) Hgeo H32).
      assert (Hl : length (dinode_bytes (fn_rec n))
                   = length (dinode_bytes (fn_rec n'))).
      { rewrite (dinode_bytes_length _ Hwf) (dinode_bytes_length _ Hwf') //. }
      pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as [Hm0 Hm1].
      assert (Hoffb : (drec_off i + length (dinode_bytes (fn_rec n'))
                       <= BSIZE)%nat).
      { rewrite (dinode_bytes_length _ Hwf') /drec_off BSIZE_1024. lia. }
      iMod (dbytes_range_update g Γd (dc_D c) (drec_blk Γd i) bs
              (drec_off i) (dinode_bytes (fn_rec n))
              (dinode_bytes (fn_rec n')) HD Hbs Hl Hoffb
              with "Hauth Hrec") as "[Hauth Hrec]".
      rewrite -(drec_owned_at g Γd (dc_S c) i (fn_rec n') Hgeo H32).
      iDestruct ("Hphiback" with "[Hrec]") as "Hphi"; [iExact "Hrec" |].
      (* the block joins *)
      assert (Hkn1 : fn_blk n1 !! k = None) by exact Hkn.
      iDestruct (inode_phi_blk_add (fs_gamma_D g Γd) (fss_sb (dc_S c)) i n1 k
                   cs Hkn1 with "[Hphi Hnew]") as "Hphi".
      { rewrite Hnn. iFrame. }
      assert (Hn1n' : fn_set_blk n1 k cs = n').
      { apply fs_node_eq; simpl.
        - reflexivity.
        - rewrite Hent //.
        - rewrite Hblk' Hcsat //. }
      rewrite Hn1n'.
      (* the ghost half *)
      iMod (dghost_move g Γd i n n' gh (dc_bin c ∖ {[fn_naddr n' k]})
              (dc_toks c) Hgh Hloc' with "Hgho Hh") as "[Hgho Hh]".
      iDestruct ("Hstback" $! n' with "[Hphi Hgho]") as "Hst";
        [by iFrame |].
      iDestruct (big_sepM_insert_acc _ _ i n Hni with "Hfr") as "[Hf Hfrback]".
      iMod (ghost_map_update n' with "Htop Hf") as "[Htop Hf]".
      iDestruct ("Hfrback" $! n' with "Hf") as "Hfr".
      assert (Hnext : dent_next Γd (DeAdopt i n' k gh) c
                      = MkDCfg (dS_upd (dc_S c) i n')
                          (dc_bin c ∖ {[fn_naddr n' k]})
                          (drec_ghost_next i gh (dc_toks c))
                          (<[drec_blk Γd i
                             := blk_splice (drec_off i)
                                  (dinode_bytes (fn_rec n')) bs]> (dc_D c))).
      { cbn [dent_next]. rewrite /dsplice Hbs //. }
      iModIntro. rewrite Hnext /dcfg_res /dbody /dS_upd.
      cbn [dc_S dc_bin dc_toks dc_D fss_sb fss_sbb fss_inodes fss_used].
      iFrame.
  Qed.

  (* the byte trail is total at every step *)
  Lemma dbytes_tot_step (Γd : fs_dur_names) (e : dent) (c : dcfg) :
    dbytes_tot (dc_D c) -> dgeo_ok Γd (dc_S c) -> dent_ok Γd e c ->
    dbytes_tot (dc_D (dent_next Γd e c)).
  Proof.
    intros HD Hgeo Hok.
    destruct e as [i n' gh | i k bs' gb | b bs' | b alloc | i n' k gh]; simpl.
    - destruct Hok as (Hrng & H32 & Hwf' & Hbs & Hn).
      pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as [Hm0 Hm1].
      apply (dbytes_tot_splice _ _ _ _ HD Hbs).
      rewrite (dinode_bytes_length _ Hwf') /drec_off BSIZE_1024. lia.
    - destruct Hok as (Hrng & Hlen' & Hn).
      destruct Hgeo as (_ & _ & Hex).
      destruct (Hex i Hrng) as [n Hni]. rewrite Hni.
      destruct (Hn n Hni) as (_ & Hbs & _ & _).
      apply (dbytes_tot_splice _ _ _ _ HD Hbs). rewrite Hlen'. lia.
    - destruct Hok as (_ & Hlen' & Hbs).
      apply (dbytes_tot_splice _ _ _ _ HD Hbs). rewrite Hlen'. lia.
    - destruct Hok as (Hbs & _ & _).
      apply (dbytes_tot_splice _ _ _ _ HD Hbs).
      rewrite bm_bytes_length. lia.
    - destruct Hok as (Hrng & H32 & Hwf' & Hbs & _ & _ & Hn).
      pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as [Hm0 Hm1].
      apply (dbytes_tot_splice _ _ _ _ HD Hbs).
      rewrite (dinode_bytes_length _ Hwf') /drec_off BSIZE_1024. lia.
  Qed.

End LedgerStep.

(* ===================================================================== *)
(*  4.  THE FOLD THEOREM                                                  *)
(* ===================================================================== *)

(* THE LEDGER'S COHERENCE.  [dled_run Gd le c c'] says the ledger's entries,
   IN ORDER, carry the configuration [c] to [c'] with every entry's own
   preconditions met on the way.  Order is kept because same-object deltas
   compose in it (the era serialization that recorded them is what justifies
   that); disjoint-object deltas commute, which is [FsDurObj]'s
   [dpool_commute] and is not needed here -- the fold walks the list. *)
Inductive dled_run (Γd : fs_dur_names) : dledger -> dcfg -> dcfg -> Prop :=
| DLnil c : dled_run Γd [] c c
| DLcons e le c c'' :
    dent_ok Γd e c ->
    dled_run Γd le (dent_next Γd e c) c'' ->
    dled_run Γd (e :: le) c c''.

Lemma dled_run_geo (Γd : fs_dur_names) (le : dledger) (c c' : dcfg) :
  dled_run Γd le c c' -> dgeo_ok Γd (dc_S c) -> dgeo_ok Γd (dc_S c').
Proof.
  induction 1 as [| e le c c'' Hok Hrun IH]; [done |].
  intros Hgeo. apply IH. exact (dgeo_ok_step Γd e c Hgeo).
Qed.

Lemma dled_run_tot (Γd : fs_dur_names) (le : dledger) (c c' : dcfg) :
  dled_run Γd le c c' -> dbytes_tot (dc_D c) -> dgeo_ok Γd (dc_S c) ->
  dbytes_tot (dc_D c').
Proof.
  induction 1 as [| e le c c'' Hok Hrun IH]; [done |].
  intros HD Hgeo. apply IH.
  - exact (dbytes_tot_step Γd e c HD Hgeo Hok).
  - exact (dgeo_ok_step Γd e c Hgeo).
Qed.

Section Fold.
  Context `{!fsLinkG Σ, !fsTopG Σ, !diskImgG Σ}.

  (* THE FOLD, at the configuration.  One induction, one basic update: this
     is where the intermediates live and die.  Nothing outside it ever sees
     a configuration whose hands are non-empty. *)
  Theorem dled_fold (g : gname) (Γd : fs_dur_names) (le : dledger)
      (c c' : dcfg) :
    dled_run Γd le c c' -> dbytes_tot (dc_D c) -> dgeo_ok Γd (dc_S c) ->
    dcfg_res g Γd c ==∗ dcfg_res g Γd c'.
  Proof.
    induction 1 as [c0 | e le c0 c'' Hok Hrun IH]; intros HD Hgeo.
    - iIntros "H". by iModIntro.
    - iIntros "H".
      iMod (dent_step_res g Γd e c0 HD Hgeo Hok with "H") as "H".
      iApply (IH with "H").
      + exact (dbytes_tot_step Γd e c0 HD Hgeo Hok).
      + exact (dgeo_ok_step Γd e c0 Hgeo).
  Qed.

  (* THE FOLD THEOREM, as the committer uses it.  The durable body at [S]
     and the byte authority at [D0] go in; the body at [S'] and the
     authority at [Dc] come out.  The ledger is PURE and the hands are empty
     at both ends.

     Read against fs-state.md section 4's two walls: there is no
     completeness clause and no wholesale rebase (the authority moves only
     at the byte ranges the entries name, via [dbytes_range_update]), and a
     supplier NAMES its object by an inum whose existence comes from the
     body's own third geometry equation -- neither wall is met because
     neither device is used. *)
  Theorem dled_fold_body (g : gname) (Γd : fs_dur_names) (le : dledger)
      (S S' : fs_state_rec) (D0 Dc : gmap Z (list (bv 8))) :
    dgeo_ok Γd S -> dbytes_tot D0 ->
    dled_run Γd le (MkDCfg S ∅ ∅ D0) (MkDCfg S' ∅ ∅ Dc) ->
    ghost_map_auth g 1 (fs_dbytes D0) -∗ dbody g Γd S ==∗
    ghost_map_auth g 1 (fs_dbytes Dc) ∗ dbody g Γd S'.
  Proof.
    intros Hgeo HD Hrun. iIntros "Hauth Hbody".
    iAssert (dcfg_res g Γd (MkDCfg S ∅ ∅ D0)) with "[Hauth Hbody]" as "Hc".
    { rewrite /dcfg_res. cbn [dc_S dc_bin dc_toks dc_D].
      iFrame "Hbody Hauth". iApply dhand_empty. }
    iMod (dled_fold g Γd le _ _ Hrun HD Hgeo with "Hc") as "Hc".
    rewrite /dcfg_res. cbn [dc_S dc_bin dc_toks dc_D].
    iDestruct "Hc" as "(Hbody & _ & Hauth)". iModIntro. iFrame.
  Qed.

  (* ...and at [P_wf_led], where the state is existential on both sides.
     This is the shape [FsDurDefer.dstep_strict] takes at the structured
     body: the durable step the commit runs. *)
  Theorem dled_dstep (g : gname) (Γd : fs_dur_names) (le : dledger)
      (S S' : fs_state_rec) (D0 Dc : gmap Z (list (bv 8))) :
    dgeo_ok Γd S -> dbytes_tot D0 ->
    dled_run Γd le (MkDCfg S ∅ ∅ D0) (MkDCfg S' ∅ ∅ Dc) ->
    ghost_map_auth g 1 (fs_dbytes D0) -∗ dbody g Γd S ==∗
    ghost_map_auth g 1 (fs_dbytes Dc) ∗ P_wf_led g Γd.
  Proof.
    intros Hgeo HD Hrun. iIntros "Hauth Hbody".
    iMod (dled_fold_body g Γd le S S' D0 Dc Hgeo HD Hrun with "Hauth Hbody")
      as "[$ Hbody]".
    iModIntro. rewrite /P_wf_led. iExists S'.
    iSplitR; [| iExact "Hbody"]. iPureIntro.
    apply (dled_run_geo Γd le (MkDCfg S ∅ ∅ D0) (MkDCfg S' ∅ ∅ Dc) Hrun Hgeo).
  Qed.

End Fold.

(* the body and the hands are nests of block-sized big-ops; seal them the
   day they are written (durable-notes.md, the [iFrame] hang) *)
Global Typeclasses Opaque dbody P_wf_led dhand dcfg_res.
