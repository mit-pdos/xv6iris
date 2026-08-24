(* FsDurWire.v -- WIRING THE OBJECT-GRANULAR CORE INTO THE DURABLE
   PREDICATE: what the validated algebra can and cannot be instantiated at,
   and the shapes that survive.

   Design of record: claude-notes/design/fs-state.md sections 4, 4.5, 4.5a,
   4.75, 4.75a, 4.875 and 4.875a; worklist claude-notes/projects/durable-disk.md,
   item 3a-obj.  Its three predecessors are iris/FsDurRefute.v (the home-view
   accessor ruling's two walls), iris/FsDurDefer.v (the deferred-justification
   ruling's third wall, and the four landed shapes) and iris/FsDurObj.v (the
   object-granular pool, its algebra, the encode bridge, and the close).
   Read all three first; this file reuses their names verbatim.

   THE LANE'S TASK was to WIRE FsDurObj's validated core: flip [P_wf] to the
   strict body, put the pending pool in the log's parked payload, convert the
   eleven suppliers, and close the commit.  The first two steps do not
   type-check at the DURABLE instance, and this file is that finding, its
   minimal witnesses, and -- because the finding is CONSTRUCTIVE -- the
   shapes that replace them, as terms.

   (1) THE POOL IS INERT AT THE DURABLE READING -- section 1.  [FsDurObj]'s
       algebra is stated over an ARBITRARY per-object reading [R] and its
       concrete lemmas over an ARBITRARY [Gamma], and both are load-bearing
       for the repair in its own section 2e.  What no lemma there does is
       instantiate [Gamma] at the DURABLE view [FsDurBytes.fs_gamma_D] and
       ask what a pending entry can be RUN against there.  Nothing.  An
       object's durable resources are [ghost_map] elements of the durable
       byte view (and, for an inode slot, of the durable top map); moving a
       [ghost_map] element needs the AUTHORITY; and by [P_wf]'s completeness
       -- which fs-state.md section 4 shows is FORCED, since
       [LogDefs.fs_dstep] must move [ghost_map_auth g 1 (fs_dbytes D)] and
       [step_forces_the_element] says the mover owns every changed address
       -- that authority and those elements are BOTH inside [P_wf], where no
       mortal may reach them (crash.md, principle 1).

       [dpend_dur_blk_False] is that in the exact configuration the commit
       is in: the durable byte authority, the object's own durable resources
       and the entry, together, give [False].  [dpool_run] is applied
       precisely there ([FsDurObj.dpool_run_frame]'s [Body] IS [P_wf] and
       the auth is lent beside it), so the pool cannot be run in the only
       place it is meant to be run -- [dpool_run_dur_False].  Holding a
       content-moving entry is therefore worthless whoever holds it, which
       is the operative form of the finding.  The inode slot's twin is
       [dpend_dur_slot_False], through the top map's authority instead of
       the byte view's, so the wall is not an artefact of the byte
       flattening.  What DOES survive is [FsDurObj.dpend_flat_bit] read the
       other way round: the bit object's entry is derivable because the flat
       reading makes it resource-free, i.e. because it promises nothing.

   (2) AND [fs_state] WITH THE FULL POOL IS CONTRADICTORY -- section 2.
       The lane's instruction reads [P_wf_strict]-shaped "with
       [free_pool_at_full]", i.e. [FsDurDefer.P_wf_strict] (which contains
       [FsState.fs_state]) at [FsDurRefute.free_pool_at] taken to the full
       block set.  [fs_state] ALREADY owns the bitmap block, through
       [FsStateBitmap.free_bitmap_at]'s first conjunct, and the full pool
       owns every block below the count -- so the two collide at the bitmap
       block itself.  [free_bitmap_at_full_False] is the collision in five
       lines and [fs_state_full_pool_False] is it inside [fs_state].  The
       flat reading does not need the collision: "every home block is
       [DBlk]-owned" means the flat ownership INSTEAD OF the coupled
       decomposition, not beside it -- which is what section 4's body
       spells, and [P_wf_dec_blocks] is the identification.

   (3) THE FINDING IS CONSTRUCTIVE, and section 3 is why.  [P_wf] owns every
       durable resource -- that is the completeness the step forces -- and a
       predicate holding an authority AND all of its elements can be REBASED
       to any target at all, with no client resource whatsoever.
       [LogDefs.fs_dview_rebase] is that for the byte view and [top_rebase]
       is its twin for the durable top map.  So nothing is LOST by the pool
       being inert: what the commit needs from the client is not a bundle of
       fupds but the PURE fact that the batch's logged bytes decode to a
       coherent state.  That is fs-state.md section 4.875's own decision 4
       -- "the bridge to bytes is ONE maintained invariant" -- promoted from
       a side condition to the whole content.

   (4) THE SHAPES THAT REPLACE THEM -- sections 4 to 7, as type-checked
       terms, so the next lane starts from terms and not from a paraphrase.
       [P_wf_dec] is the durable body: the flat completeness (every home
       block owned, which IS "all home blocks [DBlk]-owned"), the durable
       top map's authority and ALL its fragments, and the PURE bridge
       [dwire_bridge] -- each home block's bytes are its objects' values
       encoded, at [FsDurObj.kind_enc].  [dstep_dec] is
       [FsDurDefer.dstep_strict] at that body, and [dstep_dec_of_bridge] is
       the headline: THE DURABLE STEP IS DERIVABLE FROM THE TARGET'S PURE
       BRIDGE AND NOTHING ELSE.  [Psi_dec] is the log's parked payload and
       it is PURE and PERSISTENT; [Psi_dec_commit] proves
       [LogInv.log_psi_commit]'s law for it, and [Psi_dec_write] is
       [SpecLogWrite]'s byte-shaped premise, discharged at the two shared
       block kinds off [FsDurObj]'s own encode-bridge lemmas
       ([bm_write_obligation], [di_write_obligation]) -- so a supplier's
       obligation names its own block and its own object and nothing else.
       [dur_stands_at_logged] is the close, and [dwire_bridge_close] is its
       byte-level half, through [FsDurObj.dobj_close] applied unchanged.

   THREE CONSEQUENCES FOR THE INTERFACE, each visible at its term.  The
   QUIESCENCE TOKEN fs-state.md section 4.75a asks the log to add has
   nothing left to gate once the payload is pure and persistent -- there is
   no intermediate object to collapse at [out = 0] -- so the log's interface
   is section 5 UNCHANGED and [SpecEndOp] does not grow a row.  The
   payload's SECOND INDEX is not read: [Psi_dec] ignores [D0], because the
   commit's step is derivable from the target's bridge alone.  And
   [LogInv.log_psi_step] -- "hand the payload a durable step and it
   re-indexes" -- CANNOT BE DISCHARGED at a pure payload: to read the
   target's bridge out of [dstep_dec Dc Dc'] one would have to APPLY it, and
   applying it needs the durable byte authority and the body, neither of
   which the payload's holder has.  (Note this is a statement about the
   obligation, not a refutation: nothing here says the law is false.)  Its
   replacement is [Psi_dec_step_of_bridge], the same law with the target's
   bridge supplied, which is what a supplier proves anyway.

   WHAT THE LANDED BODY DOES NOT SAY, and it is the next lane's first
   question.  [FsDurDefer.P_wf_strict] contains [FsState.fs_state Gamma_D S]
   -- the durable disk IS a well-formed file system, with the ownership
   decomposition -- and [P_wf_dec] replaces that by flat ownership plus the
   PURE tie [kinds_of_state].  The crash guarantee it gives is therefore
   exactly as strong as [kinds_of_state] is made, and this file leaves it at
   the two clauses the encode bridge needs (the bitmap block's kind is the
   used set; every inode's record is at its own slot).  Strengthening it is
   PURE work and costs the resource story nothing -- [fs_state]'s content
   splits into ownership, which the flat conjunct already supplies, and
   local clauses ([FsStateInode.inode_local], the link accounting, the
   pool/used coupling), which are propositions about [S].  The one part
   that is genuinely ghost is [FsState.inode_ghost]'s link family, and it
   lives in a plain [gmapUR Z (authR natUR)] held by [own], so it is
   rebasable by the same argument as section 3's two maps once the body
   holds all of it.

   NOTHING HERE IS A PROOF DIFFICULTY.  As in [FsDurRefute], [FsDurDefer]
   and [FsDurObj], every statement is about what a resource can say; no
   existing statement in the tree moved, and no [P_wf] body was flipped. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import base countable gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop ghost_map ghost_var.
Require Import BioDefs.        (* [BSIZE]                                   *)
Require Import BitmapEnc.      (* [bm_bytes], [bm_bytes_length]             *)
Require Import DinodeEnc.      (* [diblk_bytes], [dinode_wf]                *)
Require Import FsImg.          (* [fs_sb]'s fields                          *)
Require Import RiscvPtsto.     (* [fs_dur_names]                            *)
Require Import LogDefs.        (* [fs_dview], [fs_dbytes], [fs_home_set]    *)
Require Import FsBlocks.       (* [blk_splice]                              *)
Require Import FsDurBytes.     (* [fs_gamma_D], [fs_dview_dbytes]           *)
Require Import FsState.        (* [fs_state], [top_frag], [free_bitmap_at]  *)
Require Import FsDurRefute.    (* [free_pool_at]                            *)
Require Import FsDurDefer.     (* [P_wf_strict], [dstep_strict]             *)
Require Import FsDurObj.       (* the validated core                        *)

(* the proofmode import re-opens [nat_scope] on top of the scope stack *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE POOL IS INERT AT THE DURABLE READING                          *)
(* ===================================================================== *)

Section PoolAtTheDurableView.
  Context {Σ : gFunctors}.
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.

  (* the two readings this section needs, as [FsDurObj.dres_blk]'s siblings
     -- both hold by [done], the definitions being matches on constructors *)
  Lemma dres_slot (Γ : fs_view_names Σ) (G : dgeom) (i : Z) (n : fs_node) :
    dres Γ G (DSlot i) (OVNode n)
    ⊣⊢ rec_owned_at Γ (dg_ist G) i (fn_rec n)
        ∗ top_frag Γ i n ∗ inode_ghost Γ i n.
  Proof. done. Qed.

  Lemma byte_range_D (g : gname) (Γd : fs_dur_names) (b off : Z)
      (bs : list (bv 8)) :
    byte_range (fs_gamma_D g Γd) b off bs
    ⊣⊢ ([∗ list] k ↦ v ∈ bs, (b * BSIZE_z + off + Z.of_nat k) ↪[g] v)%I.
  Proof. done. Qed.

  (* THE ONE FACT, AT ONE BYTE.  A basic update that moves a [ghost_map]
     element's value cannot coexist with the authority that pins it.  This
     is fs-state.md section 4's [step_forces_the_element] read from the
     other side: there the question was which elements a MOVER must own,
     here it is that an element cannot move at all without the authority --
     and the authority is [P_fs]'s, never a client's. *)
  Lemma dur_elem_move_False (g : gname) (B : gmap Z (bv 8))
      (a : Z) (v v' : bv 8) :
    v <> v' ->
    ghost_map_auth g 1 B -∗ a ↪[g] v -∗ (a ↪[g] v ==∗ a ↪[g] v') ==∗
      ⌜False⌝.
  Proof.
    iIntros (Hne) "Ha Hel Hstep".
    iDestruct (ghost_map_lookup with "Ha Hel") as %Hold.
    iMod ("Hstep" with "Hel") as "Hel'".
    iDestruct (ghost_map_lookup with "Ha Hel'") as %Hnew.
    iPureIntro. rewrite Hold in Hnew. apply Hne. by injection Hnew.
  Qed.

  (* THE SAME AT A BYTE RUN, which is what every byte-bearing object's
     resources are at [Gamma_D] ([FsDurBytes.fs_gamma_D]'s [fsΦ] IS the
     durable byte view's full element). *)
  Lemma byte_range_move_False (g : gname) (Γd : fs_dur_names)
      (B : gmap Z (bv 8)) (b off : Z) (bs bs' : list (bv 8))
      (k : nat) (v v' : bv 8) :
    bs !! k = Some v -> bs' !! k = Some v' -> v <> v' ->
    ghost_map_auth g 1 B -∗
    byte_range (fs_gamma_D g Γd) b off bs -∗
    (byte_range (fs_gamma_D g Γd) b off bs ==∗
     byte_range (fs_gamma_D g Γd) b off bs') ==∗
      ⌜False⌝.
  Proof.
    iIntros (Hk Hk' Hne) "Ha Hbr Hstep".
    rewrite !byte_range_D.
    iDestruct (big_sepL_lookup_acc _ _ k v Hk with "Hbr") as "[Hel Hcl]".
    iDestruct (ghost_map_lookup with "Ha Hel") as %Hold.
    iDestruct ("Hcl" with "Hel") as "Hbr".
    iMod ("Hstep" with "Hbr") as "Hbr'".
    iDestruct (big_sepL_lookup _ _ k v' Hk' with "Hbr'") as "Hel'".
    iDestruct (ghost_map_lookup with "Ha Hel'") as %Hnew.
    iPureIntro. rewrite Hold in Hnew. apply Hne. by injection Hnew.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  1a.  A BLOCK OBJECT'S PENDING ENTRY                               *)
  (* ---------------------------------------------------------------- *)

  (* THE COMMIT'S CONFIGURATION, AND THE ENTRY IS [False] IN IT.  At the
     commit the log's permit lends [ghost_map_auth g 1 (fs_dbytes D)] and
     [P_wf] to the client's prepared step (fs-state.md section 5, "the
     permit LENDS gamma_D's auth AND P_wf to the returned step"), and [P_wf]
     holds block [b]'s own durable bytes -- that is what
     [FsDurObj.dpool_run_frame]'s [Body] is.  A pending entry for [DBlk b]
     that moves the block's content is refuted right there.

     Note what is NOT assumed: nothing about the pool's other entries,
     nothing about the ledger, nothing about [D].  Only that the two
     contents differ at ONE byte position -- which is what "the batch wrote
     this block" means. *)
  Theorem dpend_dur_blk_False (g : gname) (Γd : fs_dur_names) (G : dgeom)
      (B : gmap Z (bv 8)) (b : Z) (bs bs' : list (bv 8))
      (k : nat) (v v' : bv 8) :
    bs !! k = Some v -> bs' !! k = Some v' -> v <> v' ->
    ghost_map_auth g 1 B -∗
    dres_flat (fs_gamma_D g Γd) G (DBlk b) (OVBytes bs) -∗
    dpend (dres_flat (fs_gamma_D g Γd) G) (DBlk b)
      (OVBytes bs, OVBytes bs') ==∗
      ⌜False⌝.
  Proof.
    iIntros (Hk Hk' Hne) "Ha Hres Hpend".
    rewrite /dpend. cbn [fst snd].
    rewrite (dres_flat_not_bit (fs_gamma_D g Γd) G (DBlk b) (OVBytes bs));
      [| intros b0; discriminate].
    rewrite (dres_flat_not_bit (fs_gamma_D g Γd) G (DBlk b) (OVBytes bs'));
      [| intros b0; discriminate].
    rewrite !dres_blk /blk_owned.
    iDestruct "Hres" as "[%Hlen Hbr]".
    iApply (byte_range_move_False g Γd B b 0 bs bs' k v v' Hk Hk' Hne
              with "Ha Hbr [Hpend]").
    iIntros "Hbr".
    iMod ("Hpend" with "[Hbr]") as "[%Hlen' Hbr']";
      [iSplitR; [iPureIntro; exact Hlen | iExact "Hbr"] |].
    iModIntro. iExact "Hbr'".
  Qed.

  (* AND THEREFORE THE POOL CANNOT BE RUN WHERE IT IS MEANT TO BE RUN.
     [FsDurObj.dpool_run] takes the pool and the objects' resources at their
     OLD values and returns them at their NEW ones; at the durable reading
     the authority is present too (it is lent to the step), so a pool
     holding ONE content-moving entry gives [False].  This is the wall in
     the shape the next ruling has to answer: the deposit interface is a
     bundle of BASIC UPDATES, and a basic update is exactly what a durable
     resource move may not be. *)
  Theorem dpool_run_dur_False (g : gname) (Γd : fs_dur_names) (G : dgeom)
      (B : gmap Z (bv 8)) (P : gmap dobj (oval * oval))
      (b : Z) (bs bs' : list (bv 8)) (k : nat) (v v' : bv 8) :
    P !! DBlk b = Some (OVBytes bs, OVBytes bs') ->
    bs !! k = Some v -> bs' !! k = Some v' -> v <> v' ->
    ghost_map_auth g 1 B -∗
    dpool (dres_flat (fs_gamma_D g Γd) G) P -∗
    dres_map (dres_flat (fs_gamma_D g Γd) G) (dvals_old P) ==∗
      ⌜False⌝.
  Proof.
    iIntros (HP Hk Hk' Hne) "Ha HP HV".
    rewrite /dpool /dres_map /dvals_old.
    iDestruct (big_sepM_lookup _ P (DBlk b) (OVBytes bs, OVBytes bs') HP
                 with "HP") as "Hpend".
    assert (Hfm : (fst <$> P) !! DBlk b = Some (OVBytes bs)).
    { rewrite lookup_fmap HP //. }
    iDestruct (big_sepM_lookup _ (fst <$> P) (DBlk b) (OVBytes bs) Hfm
                 with "HV") as "Hres".
    iApply (dpend_dur_blk_False g Γd G B b bs bs' k v v' Hk Hk' Hne
              with "Ha Hres Hpend").
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  1b.  AN INODE SLOT'S PENDING ENTRY                                *)
  (* ---------------------------------------------------------------- *)

  (* The same wall through the DURABLE TOP MAP rather than the byte view --
     so it is not an artefact of the byte flattening.  [FsDurObj.dres]'s
     [DSlot] reading carries [FsState.top_frag], and
     [FsDurDefer.P_wf_strict] holds the top map's AUTHORITY beside the
     fragments (it is in the body for the reason recorded there: an
     authority with no elements cannot be retagged).  So the authority is
     present wherever the fragment is, and an entry that moves the node
     value is refuted. *)
  Theorem dpend_dur_slot_False (g : gname) (Γd : fs_dur_names) (G : dgeom)
      (M : gmap Z fs_node) (i : Z) (n n' : fs_node) :
    n <> n' ->
    ghost_map_auth (fdn_top Γd) 1 M -∗
    dres (fs_gamma_D g Γd) G (DSlot i) (OVNode n) -∗
    dpend (dres (fs_gamma_D g Γd) G) (DSlot i) (OVNode n, OVNode n') ==∗
      ⌜False⌝.
  Proof.
    iIntros (Hne) "Ha Hres Hpend".
    rewrite /dpend. cbn [fst snd]. rewrite !dres_slot /top_frag.
    iDestruct "Hres" as "(Hr & Ht & Hg)".
    iDestruct (ghost_map_lookup with "Ha Ht") as %Hold.
    iMod ("Hpend" with "[$Hr $Ht $Hg]") as "(_ & Ht' & _)".
    iDestruct (ghost_map_lookup with "Ha Ht'") as %Hnew.
    iPureIntro. rewrite Hold in Hnew. apply Hne. by injection Hnew.
  Qed.

  (* WHAT SURVIVES, AND WHY IT SAYS NOTHING.  [FsDurObj.dpend_flat_bit] is
     derivable at BOTH bit values precisely because the flat reading makes
     the bit object resource-free -- so the entries a client CAN hold are
     the ones that promise nothing, and the entries that would carry the
     batch's content are the ones it cannot.  Stated here so the two halves
     sit side by side. *)
  Lemma dpend_dur_bit_trivial (g : gname) (Γd : fs_dur_names) (G : dgeom)
      (b : Z) (u u' : bool) :
    ⊢ dpend (dres_flat (fs_gamma_D g Γd) G) (DBit b) (OVBit u, OVBit u').
  Proof. iApply dpend_flat_bit. Qed.

End PoolAtTheDurableView.

(* ===================================================================== *)
(*  2.  [fs_state] WITH THE FULL POOL IS CONTRADICTORY                    *)
(* ===================================================================== *)

Section StrictBodyAtTheFullPool.
  Context {Σ : gFunctors}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  (* [FsStateBitmap.free_bitmap_at] is the bitmap BLOCK beside the pool, and
     [FsDurObj.free_pool_at_full] says the pool at the full block set owns
     every block below the count -- the bitmap block included.  Two owners
     of one block's bytes. *)
  Lemma free_bitmap_at_full_False Γ (Hex : phi_excl Γ) (bms nb : Z)
      (u : gset Z) :
    0 <= bms < nb ->
    free_bitmap_at Γ bms nb u -∗
    free_pool_at Γ nb (list_to_set (seqZ 0 nb)) -∗ False.
  Proof.
    intros Hrng. rewrite /free_bitmap_at. iIntros "[Hbm _] Hpool".
    rewrite free_pool_at_full.
    assert (Hlt : Z.of_nat (Z.to_nat bms) < nb) by lia.
    pose proof (seqZ_lookup_nat nb (Z.to_nat bms) Hlt) as Hlk.
    rewrite Z2Nat.id in Hlk; [| lia].
    iDestruct (big_sepL_lookup _ _ (Z.to_nat bms) bms Hlk with "Hpool")
      as (bs) "Hblk".
    iDestruct (blk_owned_excl Γ Hex with "Hbm Hblk") as "[]".
  Qed.

  (* ...and hence inside [FsState.fs_state], which is what
     [FsDurDefer.P_wf_strict]'s body is. *)
  Theorem fs_state_full_pool_False Γ (Hex : phi_excl Γ) (S : fs_state_rec) :
    0 <= sb_bmapstart (fss_sb S) < sb_size (fss_sb S) ->
    fs_state Γ S -∗
    free_pool_at Γ (sb_size (fss_sb S))
      (list_to_set (seqZ 0 (sb_size (fss_sb S)))) -∗ False.
  Proof.
    intros Hrng. rewrite /fs_state /free_bitmap.
    iIntros "(_ & _ & Hfb) Hpool".
    iApply (free_bitmap_at_full_False Γ Hex _ _ (fss_used S) Hrng
              with "Hfb Hpool").
  Qed.

End StrictBodyAtTheFullPool.

(* ===================================================================== *)
(*  3.  THE COMPLEMENT: A COMPLETE BODY REBASES UNCONDITIONALLY           *)
(* ===================================================================== *)

Section Rebase.
  Context {Σ : gFunctors}.
  Context `{!fsTopG Σ}.

  (* THE DURABLE TOP MAP'S TWIN OF [LogDefs.fs_dview_rebase].  A predicate
     holding the authority AND every one of its elements moves to any map at
     all -- whole-map delete then whole-map insert, no domain premise,
     because the elements ARE the domain.  This is why the pool being inert
     costs nothing: [P_wf] holds both authorities and all their elements, so
     the durable step needs no resource from the client. *)
  Lemma top_rebase (γ : gname) (M M' : gmap Z fs_node) :
    ghost_map_auth γ 1 M -∗ ([∗ map] i ↦ n ∈ M, i ↪[γ] n) ==∗
      ghost_map_auth γ 1 M' ∗ ([∗ map] i ↦ n ∈ M', i ↪[γ] n).
  Proof.
    iIntros "Ha Hel".
    iMod (ghost_map_delete_big M with "Ha Hel") as "Ha".
    rewrite map_difference_diag.
    iMod (ghost_map_insert_big M' with "Ha") as "[Ha Hel]";
      [apply map_disjoint_empty_r |].
    rewrite right_id_L. by iFrame.
  Qed.

End Rebase.

(* ===================================================================== *)
(*  4.  THE BRIDGE, AND THE DURABLE BODY IT INDEXES                       *)
(* ===================================================================== *)

(* fs-state.md section 4.875 decision 4, as the WHOLE content rather than as
   a side condition: each home block's bytes are its objects' current values
   encoded, at [FsDurObj.kind_enc].  Everything in this section is pure
   except the body itself. *)

Definition dwire_bridge (K : Z -> blk_kind) (D : gmap Z (list (bv 8)))
    (cov : gset Z) (ls : Z) : Prop :=
  dom D = fs_home_set cov ls
  /\ (forall b, b ∈ fs_home_set cov ls -> D !! b = Some (kind_enc (K b))).

(* every home block's encoding is a block *)
Definition kinds_blocksized (K : Z -> blk_kind) (cov : gset Z) (ls : Z)
    : Prop :=
  forall b, b ∈ fs_home_set cov ls -> length (kind_enc (K b)) = BSIZE.

Lemma dwire_bridge_blocksized (K : Z -> blk_kind)
    (D : gmap Z (list (bv 8))) (cov : gset Z) (ls : Z) :
  dwire_bridge K D cov ls -> kinds_blocksized K cov ls ->
  forall b bs, D !! b = Some bs -> length bs = BSIZE.
Proof.
  intros [Hdom Henc] Hlen b bs Hb.
  assert (Hin : b ∈ fs_home_set cov ls).
  { rewrite -Hdom. apply elem_of_dom. by exists bs. }
  rewrite (Henc b Hin) in Hb. injection Hb as <-. exact (Hlen b Hin).
Qed.

(* THE BYTE-LEVEL CLOSE, through [FsDurObj.dobj_close] APPLIED UNCHANGED:
   two block maps carrying the same kind assignment on the home set are the
   same map, and one of them is the batch's logged view.  No [fs_restrict]
   arithmetic appears outside [lm_logged]'s own definition. *)
Corollary dwire_bridge_close (K : Z -> blk_kind)
    (D' L : gmap Z (list (bv 8))) (cov : gset Z) (ls : Z) :
  dwire_bridge K D' cov ls ->
  (forall b, b ∈ fs_home_set cov ls -> L !! b = Some (kind_enc (K b))) ->
  D' = lm_logged L cov ls.
Proof.
  intros [Hdom Henc] HL. exact (dobj_close K D' L cov ls Hdom Henc HL).
Qed.

(* THE ABSTRACT STATE'S TIE TO THE KIND ASSIGNMENT.  Four clauses, and each
   is the ONE thing its block kind knows about the state.

   [ko_bitmap] and [ko_slot] are the content: the bitmap block's kind IS the
   state's used set, and every inode's record sits at its own slot of its
   own inode block ([FsDurObj.dobj_home_slot]'s numbering, read at the
   region's start).  [ko_inodeblk] and [ko_recwf] are ROLE clauses -- every
   block of the inode region has an inode KIND, and any kind that is an
   inode kind carries well-formed records -- and they are here because a
   SUPPLIER needs them.  Without [ko_inodeblk] the writer of an inode slot
   cannot name the block's current slot values (they are inside [K], which
   is existential in the payload) and so cannot say what its own spliced
   bytes encode; without [ko_recwf] it cannot apply
   [FsDurObj.di_vals_enc].  Both are facts about the geometry and about
   every record on the disk, not about any one transaction. *)
Record kinds_of_state (S : fs_state_rec) (K : Z -> blk_kind) : Prop :=
  MkKindsOfState {
  ko_bitmap : K (sb_bmapstart (fss_sb S)) = KBitmap (fss_used S);
  ko_inodeblk : forall j : Z, 0 <= j -> 16 * j < sb_ninodes (fss_sb S) ->
      exists nd : nat -> fs_node, K (sb_inodestart (fss_sb S) + j) = KInode nd;
  ko_slot : forall (i : Z) (n : fs_node), 0 <= i ->
      fss_inodes S !! i = Some n ->
      exists nd : nat -> fs_node,
        K (sb_inodestart (fss_sb S) + i `div` 16) = KInode nd
        /\ nd (Z.to_nat (i `mod` 16)) = n;
  ko_recwf : forall (b : Z) (nd : nat -> fs_node), K b = KInode nd ->
      forall j : nat, dinode_wf (fn_rec (nd j));
}.

(* the kind assignment updated at ONE block -- the only shape a writer ever
   produces, since a [log_write] writes one block *)
Definition kind_upd (K : Z -> blk_kind) (b : Z) (k : blk_kind)
    : Z -> blk_kind :=
  fun c => if decide (c = b) then k else K c.

Lemma kind_upd_at (K : Z -> blk_kind) (b : Z) (k : blk_kind) :
  kind_upd K b k b = k.
Proof.
  rewrite /kind_upd. destruct (decide (b = b)) as [_ | Hne];
    [reflexivity | exfalso; exact (Hne eq_refl)].
Qed.

Lemma kind_upd_ne (K : Z -> blk_kind) (b : Z) (k : blk_kind) (c : Z) :
  c <> b -> kind_upd K b k c = K c.
Proof.
  intros Hne. rewrite /kind_upd. destruct (decide (c = b)) as [He | _];
    [exfalso; exact (Hne He) | reflexivity].
Qed.

(* the bridge is maintained by a write of ONE home block, at the matching
   kind -- pure, and it names only the written block *)
Lemma dwire_bridge_write (K : Z -> blk_kind) (D : gmap Z (list (bv 8)))
    (cov : gset Z) (ls : Z) (b : Z) (k : blk_kind) :
  dwire_bridge K D cov ls -> b ∈ fs_home_set cov ls ->
  dwire_bridge (kind_upd K b k) (<[b := kind_enc k]> D) cov ls.
Proof.
  intros [Hdom Henc] Hb. split.
  - rewrite dom_insert_L Hdom. set_solver.
  - intros c Hc. destruct (decide (c = b)) as [-> | Hne].
    + rewrite lookup_insert kind_upd_at //.
    + rewrite lookup_insert_ne; [| exact (not_eq_sym Hne)].
      rewrite (kind_upd_ne K b k c Hne). exact (Henc c Hc).
Qed.

Lemma kinds_blocksized_write (K : Z -> blk_kind) (cov : gset Z) (ls : Z)
    (b : Z) (k : blk_kind) :
  kinds_blocksized K cov ls -> length (kind_enc k) = BSIZE ->
  kinds_blocksized (kind_upd K b k) cov ls.
Proof.
  intros HK Hk c Hc. destruct (decide (c = b)) as [-> | Hne].
  - rewrite kind_upd_at. exact Hk.
  - rewrite (kind_upd_ne K b k c Hne). exact (HK c Hc).
Qed.

Section Body.
  Context {Σ : gFunctors}.
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.

  (* THE DURABLE BODY.  Three parts and no more:

     - the FLAT COMPLETENESS, [LogDefs.fs_dview] at the byte flattening of
       [D].  fs-state.md section 4 shows this is FORCED, and
       [FsDurBytes.fs_dview_dbytes] says it IS "every home block owned as a
       whole block at [Gamma_D]" -- i.e. the lane's instruction "all home
       blocks as [DBlk]-owned", one rewrite away ([P_wf_dec_blocks]), and
       with no second owner beside it, so section 2's collision is absent;
     - the DURABLE TOP MAP's authority and ALL its fragments.  The fragments
       are in it for [FsDurDefer.P_wf_strict]'s reason
       ([FsState.inode_owned] carries none and an authority with no elements
       cannot be retagged), and their being ALL of them is what makes
       section 3's rebase apply;
     - the PURE BRIDGE, at an abstract state [S] and a kind assignment [K].

     The bit objects are resource-free BY CONSTRUCTION here: no clause
     mentions them, and their values are read off the bitmap block's kind
     ([FsDurObj.bm_vals] is the same reading).  That is 3a-val's [dres_flat]
     repair, arriving as the body's SHAPE rather than as a second
     predicate. *)
  Definition P_wf_dec (g : gname) (Γd : fs_dur_names) (cov : gset Z)
      (ls : Z) (D : gmap Z (list (bv 8))) : iProp Σ :=
    (∃ (S : fs_state_rec) (K : Z -> blk_kind),
       ⌜dwire_bridge K D cov ls⌝ ∗ ⌜kinds_blocksized K cov ls⌝
       ∗ ⌜kinds_of_state S K⌝
       ∗ fs_dview g (fs_dbytes D)
       ∗ ghost_map_auth (fdn_top Γd) 1 (fss_inodes S)
       ∗ ([∗ map] i ↦ n ∈ fss_inodes S, top_frag (fs_gamma_D g Γd) i n))%I.

  (* ...AND IT REALLY IS "ALL HOME BLOCKS [DBlk]-OWNED".  The flat conjunct
     is the [∗] of the object resources of one [DBlk] per home block, at the
     REPAIRED reading [FsDurObj.dres_flat] -- which is the lane's
     instruction, with section 2's collision absent because there is no
     second owner. *)
  Lemma P_wf_dec_blocks (g : gname) (Γd : fs_dur_names) (G : dgeom)
      (K : Z -> blk_kind) (D : gmap Z (list (bv 8))) (cov : gset Z) (ls : Z) :
    dwire_bridge K D cov ls -> kinds_blocksized K cov ls ->
    fs_dview g (fs_dbytes D)
    ⊣⊢ ([∗ map] b ↦ bs ∈ D,
          dres_flat (fs_gamma_D g Γd) G (DBlk b) (OVBytes bs)).
  Proof.
    intros Hbr Hlen.
    rewrite (fs_dview_dbytes g Γd D
               (dwire_bridge_blocksized K D cov ls Hbr Hlen)).
    apply big_sepM_proper. intros b bs _.
    rewrite (dres_flat_not_bit (fs_gamma_D g Γd) G (DBlk b) (OVBytes bs));
      [| intros b0; discriminate].
    rewrite dres_blk //.
  Qed.

  (* [FsDurDefer.dstep_strict] at this body: the durable byte authority and
     the body are LENT for the instant, exactly as today, and the step lands
     both at the new index. *)
  Definition dstep_dec (g : gname) (Γd : fs_dur_names) (cov : gset Z)
      (ls : Z) (D D' : gmap Z (list (bv 8))) : iProp Σ :=
    (ghost_map_auth g 1 (fs_dbytes D) -∗ P_wf_dec g Γd cov ls D ==∗
     ghost_map_auth g 1 (fs_dbytes D') ∗ P_wf_dec g Γd cov ls D')%I.

  Lemma dstep_dec_id g Γd cov ls D : ⊢ dstep_dec g Γd cov ls D D.
  Proof. rewrite /dstep_dec. iIntros "Ha Hw". iModIntro. iFrame. Qed.

  Lemma dstep_dec_trans g Γd cov ls D D' D'' :
    dstep_dec g Γd cov ls D D' -∗ dstep_dec g Γd cov ls D' D'' -∗
    dstep_dec g Γd cov ls D D''.
  Proof.
    rewrite /dstep_dec. iIntros "H1 H2 Ha Hw".
    iMod ("H1" with "Ha Hw") as "[Ha Hw]".
    iApply ("H2" with "Ha Hw").
  Qed.

  (* ================================================================ *)
  (*  THE HEADLINE.  The durable step is derivable from the TARGET'S   *)
  (*  PURE BRIDGE and nothing else -- no pool, no deposit, no client    *)
  (*  resource of any kind.  Both authorities and all their elements    *)
  (*  are inside the body (that is the completeness the step forces),   *)
  (*  so section 3's two rebases carry it.                              *)
  (*                                                                    *)
  (*  This is what makes section 1's finding CONSTRUCTIVE: the pool was  *)
  (*  carrying resources that can never leave [P_wf], and what the       *)
  (*  commit actually needs from the client is a PURE fact.              *)
  (* ================================================================ *)
  Theorem dstep_dec_of_bridge (g : gname) (Γd : fs_dur_names)
      (cov : gset Z) (ls : Z) (D D' : gmap Z (list (bv 8)))
      (S' : fs_state_rec) (K' : Z -> blk_kind) :
    dwire_bridge K' D' cov ls -> kinds_blocksized K' cov ls ->
    kinds_of_state S' K' ->
    ⊢ dstep_dec g Γd cov ls D D'.
  Proof.
    intros Hbr Hlen Hst. rewrite /dstep_dec /P_wf_dec.
    iIntros "Ha Hw".
    iDestruct "Hw" as (S K) "(_ & _ & _ & Hd & Htop & Hfr)".
    iMod (fs_dview_rebase g (fs_dbytes D) (fs_dbytes D') with "Ha Hd")
      as "[Ha Hd]".
    rewrite /top_frag.
    iMod (top_rebase (fdn_top Γd) (fss_inodes S) (fss_inodes S')
            with "Htop Hfr") as "[Htop Hfr]".
    iModIntro. iFrame "Ha". iExists S', K'.
    iSplitR; [iPureIntro; exact Hbr |].
    iSplitR; [iPureIntro; exact Hlen |].
    iSplitR; [iPureIntro; exact Hst |].
    iFrame "Hd Htop Hfr".
  Qed.

  (* ...AND THE ABSTRACT READING OF THE SAME FACT: at the batch's logged
     values the durable body STANDS, and the block map it stands at is the
     logged view on every home block ([dwire_bridge_close] is the byte-level
     half).  This is the lane's closing statement. *)
  Theorem dur_stands_at_logged (g : gname) (Γd : fs_dur_names)
      (cov : gset Z) (ls : Z) (D0 : gmap Z (list (bv 8)))
      (L : gmap Z (list (bv 8))) (S' : fs_state_rec) (K' : Z -> blk_kind) :
    dwire_bridge K' (lm_logged L cov ls) cov ls ->
    kinds_blocksized K' cov ls -> kinds_of_state S' K' ->
    ghost_map_auth g 1 (fs_dbytes D0) -∗ P_wf_dec g Γd cov ls D0 ==∗
      ghost_map_auth g 1 (fs_dbytes (lm_logged L cov ls))
      ∗ P_wf_dec g Γd cov ls (lm_logged L cov ls).
  Proof.
    intros Hbr Hlen Hst. iIntros "Ha Hw".
    iApply (dstep_dec_of_bridge g Γd cov ls D0 (lm_logged L cov ls) S' K'
              Hbr Hlen Hst with "Ha Hw").
  Qed.

End Body.

(* ===================================================================== *)
(*  5.  THE LOG'S PARKED PAYLOAD                                          *)
(* ===================================================================== *)

(* fs-state.md section 5's [Psi D0 Dc] at this body -- and it is PURE.
   [LogInv.log_psi_commit]'s law is [Psi_dec_commit]; [SpecLogWrite]'s
   byte-shaped premise is [Psi_dec_write], discharged at the two shared
   block kinds in section 6 by the writer's own read-modify-write fact off
   [FsDurObj]'s encode-bridge lemmas.

   [D0] IS NOT READ.  The payload's second index exists so that the commit's
   law can return a step from the committed view; here the step is derivable
   from the TARGET's bridge alone ([dstep_dec_of_bridge]), so the index is
   carried and ignored.  That is a simplification of section 5, not a hedge:
   the conjunct that would mention [D0] is absent rather than trivial. *)

Section Payload.
  Context {Σ : gFunctors}.
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.

  Definition Psi_dec (cov : gset Z) (ls : Z)
      (D0 Dc : gmap Z (list (bv 8))) : iProp Σ :=
    (∃ (S : fs_state_rec) (K : Z -> blk_kind),
       ⌜dwire_bridge K Dc cov ls⌝ ∗ ⌜kinds_blocksized K cov ls⌝
       ∗ ⌜kinds_of_state S K⌝)%I.

  Global Instance Psi_dec_persistent cov ls D0 Dc :
    Persistent (Psi_dec cov ls D0 Dc).
  Proof. rewrite /Psi_dec. apply _. Qed.

  (* [LogInv.log_psi_commit]'s law, at [dstep_dec]: hand out the accumulated
     debt and re-park at the new committed index.  The debt IS the bridge --
     section 4's headline is what turns the payload's pure content into the
     step the commit permit runs. *)
  Theorem Psi_dec_commit (g : gname) (Γd : fs_dur_names)
      (cov : gset Z) (ls : Z) :
    ⊢ □ (∀ D0 Dc : gmap Z (list (bv 8)),
           Psi_dec cov ls D0 Dc ==∗
             Psi_dec cov ls Dc Dc ∗ dstep_dec g Γd cov ls D0 Dc).
  Proof.
    iModIntro. iIntros (D0 Dc) "#Hpsi".
    iDestruct "Hpsi" as (S K) "(%Hbr & %Hlen & %Hst)".
    iModIntro. iSplitR.
    - iExists S, K.
      iSplitR; [iPureIntro; exact Hbr |].
      iSplitR; [iPureIntro; exact Hlen |].
      iPureIntro; exact Hst.
    - iApply (dstep_dec_of_bridge g Γd cov ls D0 Dc S K Hbr Hlen Hst).
  Qed.

  (* THE REPLACEMENT FOR [LogInv.log_psi_step].  The log's WRITE law says
     "absorb a durable step and re-index"; at a pure payload it cannot be
     discharged, because reading the target's bridge out of the step would
     mean APPLYING the step, and applying it needs the durable byte
     authority and the body -- neither of which the payload's holder has.
     What IS absorbed is the target's BRIDGE.  A supplier has it -- section
     6 is how it gets it -- and the log needs no law at all beyond it. *)
  Theorem Psi_dec_step_of_bridge (cov : gset Z) (ls : Z) :
    ⊢ □ (∀ (D0 Dc' : gmap Z (list (bv 8))) (S' : fs_state_rec)
           (K' : Z -> blk_kind),
           ⌜dwire_bridge K' Dc' cov ls⌝ -∗ ⌜kinds_blocksized K' cov ls⌝ -∗
           ⌜kinds_of_state S' K'⌝ -∗ Psi_dec cov ls D0 Dc').
  Proof.
    iModIntro. iIntros (D0 Dc' S' K') "%Hbr %Hlen %Hst".
    iExists S', K'.
    iSplitR; [iPureIntro; exact Hbr |].
    iSplitR; [iPureIntro; exact Hlen |].
    iPureIntro; exact Hst.
  Qed.

  (* [SpecLogWrite]'s BYTE-SHAPED PREMISE, at this payload.  The writer
     supplies the new kind of its OWN block and the new abstract state; the
     [forall S K] is plumbing rather than non-locality, since [S] and [K]
     are existential inside [Psi_dec] so a client cannot name them, and
     section 6 discharges the premise by reading off exactly the one clause
     of [kinds_of_state] its own block's kind owns. *)
  Theorem Psi_dec_write (cov : gset Z) (ls : Z)
      (D0 Dc : gmap Z (list (bv 8))) (b : Z) (bs : list (bv 8)) :
    b ∈ fs_home_set cov ls -> length bs = BSIZE ->
    (forall (S : fs_state_rec) (K : Z -> blk_kind),
       dwire_bridge K Dc cov ls -> kinds_blocksized K cov ls ->
       kinds_of_state S K ->
       exists (S' : fs_state_rec) (k' : blk_kind),
         kind_enc k' = bs /\ kinds_of_state S' (kind_upd K b k')) ->
    Psi_dec cov ls D0 Dc ==∗ Psi_dec cov ls D0 (<[b := bs]> Dc).
  Proof.
    intros Hb Hlen Hstep. iIntros "Hpsi".
    iDestruct "Hpsi" as (S K) "(%Hbr & %Hks & %Hst)".
    destruct (Hstep S K Hbr Hks Hst) as (S' & k' & Hk' & Hst').
    iModIntro. iExists S', (kind_upd K b k').
    iSplitR.
    { iPureIntro. rewrite -Hk'.
      exact (dwire_bridge_write K Dc cov ls b k' Hbr Hb). }
    iSplitR.
    { iPureIntro. apply (kinds_blocksized_write K cov ls b k' Hks).
      rewrite Hk'. exact Hlen. }
    iPureIntro; exact Hst'.
  Qed.

  (* THE FORM A SUPPLIER CAN ACTUALLY DISCHARGE, and the interface finding
     it carries.  [Psi_dec_write]'s premise is quantified over the payload's
     index, and at the BITMAP block that costs nothing ([bm_write_obligation]
     never reads [K] at the written block).  At an INODE block it is not
     dischargeable: the writer's spliced bytes encode the block's sixteen
     slot values, fifteen of which it does not know, and the only handle on
     them is [K] at its own block -- reachable only if [Dc] agrees with the
     bytes the writer read.  So [SpecLogWrite]'s AU must carry the
     BLOCK-LOCAL tie [Dc !! b = Some oldbs], which is exactly
     [FsDurDefer.lw_arm_justify]'s [Dj !! b = Lg !! b]: landed there, and
     needed here.  It is not [FsDurRefute]'s wall (B) -- the tie is at ONE
     block and the log reads it off row (b) -- but it is not free either. *)
  Theorem Psi_dec_write_tied (cov : gset Z) (ls : Z)
      (D0 Dc : gmap Z (list (bv 8))) (b : Z) (oldbs bs : list (bv 8)) :
    b ∈ fs_home_set cov ls -> Dc !! b = Some oldbs -> length bs = BSIZE ->
    (forall (S : fs_state_rec) (K : Z -> blk_kind),
       kinds_blocksized K cov ls -> kinds_of_state S K ->
       kind_enc (K b) = oldbs ->
       exists (S' : fs_state_rec) (k' : blk_kind),
         kind_enc k' = bs /\ kinds_of_state S' (kind_upd K b k')) ->
    Psi_dec cov ls D0 Dc ==∗ Psi_dec cov ls D0 (<[b := bs]> Dc).
  Proof.
    intros Hb Htie Hlen Hstep.
    iApply (Psi_dec_write cov ls D0 Dc b bs Hb Hlen).
    intros S K Hbr Hks Hst. apply (Hstep S K Hks Hst).
    destruct Hbr as [_ Henc]. rewrite (Henc b Hb) in Htie.
    by injection Htie.
  Qed.

End Payload.

(* ===================================================================== *)
(*  6.  THE SUPPLIER'S OBLIGATION, AT THE TWO SHARED BLOCK KINDS          *)
(* ===================================================================== *)

(* [Psi_dec_write]'s premise, discharged.  Both instances are PURE, both go
   through [FsDurObj]'s own encode-bridge lemmas, and both name only the
   writer's block and the writer's object -- which is fs-state.md section
   4.875 decision 3's modularity requirement, met where it actually bites.

   The one thing each needs from the geometry is that its block is not the
   OTHER kind's block; that is a premise, and it is a fact about the
   superblock, not about the file system's state. *)

(* ---- the bitmap block: [balloc] / [bfree] -------------------------- *)

(* THE STATE MOVE a bitmap write performs: the used set, and nothing else. *)
Definition state_bm_upd (S : fs_state_rec) (u' : gset Z) : fs_state_rec :=
  MkFsS (fss_sb S) (fss_sbb S) (fss_inodes S) u'.

(* THE GEOMETRY PREMISE both movers take, and it is a fact about the
   superblock: no block of the inode region is the bitmap block.  It follows
   from [FsImg.fs_sb_ok]'s [sbo_bmapstart] and is stated as a hypothesis
   here because this file has no superblock in hand. *)
Definition dwire_geom (S : fs_state_rec) : Prop :=
  forall j : Z, 0 <= j ->
    sb_inodestart (fss_sb S) + j <> sb_bmapstart (fss_sb S).

Lemma kinds_of_state_bm (S : fs_state_rec) (K : Z -> blk_kind) (u' : gset Z) :
  kinds_of_state S K -> dwire_geom S ->
  kinds_of_state (state_bm_upd S u')
    (kind_upd K (sb_bmapstart (fss_sb S)) (KBitmap u')).
Proof.
  intros [Hbm Hib Hslot Hwf] Hgeo.
  split; cbn [state_bm_upd fss_sb fss_inodes fss_used].
  - by rewrite kind_upd_at.
  - intros j Hj Hn. destruct (Hib j Hj Hn) as [nd HK]. exists nd.
    rewrite (kind_upd_ne K (sb_bmapstart (fss_sb S)) (KBitmap u')
               (sb_inodestart (fss_sb S) + j) (Hgeo j Hj)).
    exact HK.
  - intros i n Hi Hn. destruct (Hslot i n Hi Hn) as (nd & HK & Hnd).
    exists nd. split; [| exact Hnd].
    assert (Hdiv : 0 <= i `div` 16) by (apply Z.div_pos; lia).
    rewrite (kind_upd_ne K (sb_bmapstart (fss_sb S)) (KBitmap u')
               (sb_inodestart (fss_sb S) + i `div` 16) (Hgeo _ Hdiv)).
    exact HK.
  - intros b nd HKb j.
    destruct (decide (b = sb_bmapstart (fss_sb S))) as [-> | Hne].
    + rewrite kind_upd_at in HKb. discriminate.
    + rewrite (kind_upd_ne K (sb_bmapstart (fss_sb S)) (KBitmap u') b Hne)
        in HKb.
      exact (Hwf b nd HKb j).
Qed.

(* THE SUPPLIER'S DISCHARGE, at the bitmap block -- AND IT IS UNIFORM IN THE
   PAYLOAD'S INDEX.  The writer needs only a KIND whose encoding is the
   bytes it is about to log, and its own bytes are a bitmap encoding by its
   own era-side knowledge ([bm_write_bytes_are_a_kind], off
   [FsDurObj.bm_blk_write_enc]; [FsDurObj.bm_new_byte_code] is what says the
   byte spliced is the one [bp->data[bi/8] |= m] / [&= ~m] stores).  So this
   obligation is discharged without ever reading [K] at the written block --
   which is why the bitmap suppliers need no tie to [Dc] at all. *)
Theorem bm_write_obligation (S : fs_state_rec) (K : Z -> blk_kind)
    (u' : gset Z) :
  kinds_of_state S K -> dwire_geom S ->
  exists (S' : fs_state_rec) (k' : blk_kind),
    kind_enc k' = bm_bytes BSIZE u'
    /\ kinds_of_state S' (kind_upd K (sb_bmapstart (fss_sb S)) k').
Proof.
  intros Hst Hgeo.
  exists (state_bm_upd S u'), (KBitmap u'). split; [reflexivity |].
  exact (kinds_of_state_bm S K u' Hst Hgeo).
Qed.

(* ...and the writer's spliced block really is such an encoding *)
Corollary bm_write_bytes_are_a_kind (u : gset Z) (bi : Z) (v : bool) :
  0 <= bi < 8 * Z.of_nat BSIZE ->
  bm_blk_write (bm_bytes BSIZE u) (bm_wr u bi v) bi
  = kind_enc (KBitmap (bm_wr u bi v)).
Proof. intros H. cbn [kind_enc]. exact (bm_blk_write_enc u bi v H). Qed.

(* ...and the encoding really is a block, which is [Psi_dec_write]'s other
   premise *)
Lemma bm_kind_blocksize (u : gset Z) :
  length (kind_enc (KBitmap u)) = BSIZE.
Proof. cbn [kind_enc]. apply bm_bytes_length. Qed.

(* ---- an inode block: [ialloc] / [iupdate] -------------------------- *)

(* THE STATE MOVE an inode-slot write performs: one entry of the inode map,
   and nothing else. *)
Definition state_slot_upd (S : fs_state_rec) (i : Z) (n : fs_node)
    : fs_state_rec :=
  MkFsS (fss_sb S) (fss_sbb S) (<[i := n]> (fss_inodes S)) (fss_used S).

(* the arithmetic the slot numbering rests on: inum [16*bi + k] is slot [k]
   of inode block [bi] ([FsDurObj.dobj_home_slot]'s numbering) *)
Lemma slot_div (bi : Z) (k : nat) :
  (k < 16)%nat -> (16 * bi + Z.of_nat k) `div` 16 = bi.
Proof.
  intros Hk.
  assert (Hk0 : Z.of_nat k `div` 16 = 0) by (apply Z.div_small; lia).
  rewrite (Z.mul_comm 16 bi) Z.div_add_l; [| lia]. rewrite Hk0. lia.
Qed.

Lemma slot_mod (bi : Z) (k : nat) :
  (k < 16)%nat -> (16 * bi + Z.of_nat k) `mod` 16 = Z.of_nat k.
Proof.
  intros Hk.
  rewrite (Z.mul_comm 16 bi) Z.add_comm Z_mod_plus_full.
  apply Z.mod_small. lia.
Qed.

Lemma kinds_of_state_slot (S : fs_state_rec) (K : Z -> blk_kind)
    (bi : Z) (k : nat) (nd : nat -> fs_node) (n : fs_node) :
  kinds_of_state S K -> (k < 16)%nat -> dwire_geom S -> 0 <= bi ->
  K (sb_inodestart (fss_sb S) + bi) = KInode nd ->
  dinode_wf (fn_rec n) ->
  kinds_of_state
    (state_slot_upd S (16 * bi + Z.of_nat k) n)
    (kind_upd K (sb_inodestart (fss_sb S) + bi) (KInode (nd_upd nd k n))).
Proof.
  intros [Hbm Hib Hslot Hwf] Hk Hgeo Hbi HK Hn.
  split; cbn [state_slot_upd fss_sb fss_inodes fss_used].
  - rewrite (kind_upd_ne K (sb_inodestart (fss_sb S) + bi)
               (KInode (nd_upd nd k n)) (sb_bmapstart (fss_sb S))
               (not_eq_sym (Hgeo bi Hbi))).
    exact Hbm.
  - intros j Hj Hnj.
    destruct (decide (j = bi)) as [-> | Hnej].
    + exists (nd_upd nd k n). rewrite kind_upd_at //.
    + destruct (Hib j Hj Hnj) as [nd1 HK1]. exists nd1.
      assert (Hne2 : sb_inodestart (fss_sb S) + j
                     <> sb_inodestart (fss_sb S) + bi) by lia.
      rewrite (kind_upd_ne K (sb_inodestart (fss_sb S) + bi)
                 (KInode (nd_upd nd k n))
                 (sb_inodestart (fss_sb S) + j) Hne2).
      exact HK1.
  - intros i m Hi Hm.
    destruct (decide (i = 16 * bi + Z.of_nat k)) as [-> | Hnei].
    + rewrite lookup_insert in Hm. injection Hm as <-.
      exists (nd_upd nd k n). split.
      * rewrite (slot_div bi k Hk) kind_upd_at //.
      * rewrite (slot_mod bi k Hk) Nat2Z.id /nd_upd.
        destruct (Nat.eq_dec k k) as [_ | Hbad];
          [reflexivity | exfalso; exact (Hbad eq_refl)].
    + rewrite lookup_insert_ne in Hm; [| exact (not_eq_sym Hnei)].
      destruct (Hslot i m Hi Hm) as (nd0 & HK0 & Hnd0).
      assert (Hmb : 0 <= i `mod` 16 < 16) by (apply Z.mod_pos_bound; lia).
      destruct (decide (i `div` 16 = bi)) as [Hdiv | Hdiv].
      * rewrite Hdiv in HK0. rewrite HK0 in HK. injection HK as ->.
        exists (nd_upd nd k n). split.
        { rewrite Hdiv kind_upd_at //. }
        { rewrite /nd_upd.
          destruct (Nat.eq_dec (Z.to_nat (i `mod` 16)) k) as [Heq | _];
            [| exact Hnd0].
          exfalso. apply Hnei.
          assert (Hmod : i `mod` 16 = Z.of_nat k).
          { rewrite -Heq. rewrite Z2Nat.id; [reflexivity | lia]. }
          pose proof (Z.div_mod i 16 ltac:(lia)) as Hi16.
          rewrite Hdiv Hmod in Hi16. exact Hi16. }
      * exists nd0. split; [| exact Hnd0].
        assert (Hne2 : sb_inodestart (fss_sb S) + i `div` 16
                       <> sb_inodestart (fss_sb S) + bi) by lia.
        rewrite (kind_upd_ne K (sb_inodestart (fss_sb S) + bi)
                   (KInode (nd_upd nd k n))
                   (sb_inodestart (fss_sb S) + i `div` 16) Hne2).
        exact HK0.
  - intros b nd2 HKb j.
    destruct (decide (b = sb_inodestart (fss_sb S) + bi)) as [-> | Hne3].
    + rewrite kind_upd_at in HKb. injection HKb as <-.
      rewrite /nd_upd. destruct (Nat.eq_dec j k) as [-> | _];
        [exact Hn | exact (Hwf _ nd HK j)].
    + rewrite (kind_upd_ne K (sb_inodestart (fss_sb S) + bi)
                 (KInode (nd_upd nd k n)) b Hne3) in HKb.
      exact (Hwf b nd2 HKb j).
Qed.

(* THE SUPPLIER'S DISCHARGE, at an inode block -- AND HERE THE TIE TO [Dc]
   IS LOAD-BEARING, which is the interface finding of section 5.  The
   writer's bytes are its read-modify-write of the block it read
   ([FsDurObj.di_blk_write], the record's 64 bytes spliced at offset
   [64k]), and to say what they ENCODE it has to name the block's other
   fifteen slot values.  Those live in [K], which is existential in the
   payload, so the writer reaches them only through
   [kind_enc (K b) = <its own old bytes>] -- i.e. through
   [FsDurDefer.lw_arm_justify]'s [Dc !! b = Lg !! b].  [ko_inodeblk] is what
   turns that byte equation into a KIND, and [ko_recwf] is what lets
   [FsDurObj.di_vals_enc] apply. *)
Theorem di_write_obligation (S : fs_state_rec) (K : Z -> blk_kind)
    (bi : Z) (k : nat) (n : fs_node) (oldbs : list (bv 8)) :
  kinds_of_state S K -> (k < 16)%nat -> dwire_geom S ->
  0 <= bi -> 16 * bi < sb_ninodes (fss_sb S) ->
  kind_enc (K (sb_inodestart (fss_sb S) + bi)) = oldbs ->
  dinode_wf (fn_rec n) ->
  exists (S' : fs_state_rec) (k' : blk_kind),
    kind_enc k' = di_blk_write oldbs k (fn_rec n)
    /\ kinds_of_state S' (kind_upd K (sb_inodestart (fss_sb S) + bi) k').
Proof.
  intros Hst Hk Hgeo Hbi Hnib Hold Hn.
  destruct (ko_inodeblk S K Hst bi Hbi Hnib) as [nd HK].
  exists (state_slot_upd S (16 * bi + Z.of_nat k) n),
         (KInode (nd_upd nd k n)).
  split.
  - rewrite -Hold HK. cbn [kind_enc]. symmetry.
    exact (di_vals_enc nd k n (ko_recwf S K Hst _ nd HK) Hn Hk).
  - exact (kinds_of_state_slot S K bi k nd n Hst Hk Hgeo Hbi HK Hn).
Qed.

(* ...and its encoding is a block *)
Lemma di_kind_blocksize (nd : nat -> fs_node) :
  (forall j, dinode_wf (fn_rec (nd j))) ->
  length (kind_enc (KInode nd)) = BSIZE.
Proof.
  intros Hall. cbn [kind_enc].
  rewrite (diblk_bytes_length (di_recs nd)).
  - rewrite di_recs_length. reflexivity.
  - apply Forall_lookup_2. intros j x Hx.
    destruct (Nat.lt_ge_cases j 16%nat) as [Hj | Hj].
    + rewrite (di_recs_lookup nd j Hj) in Hx. injection Hx as <-.
      exact (Hall j).
    + rewrite lookup_ge_None_2 in Hx;
        [discriminate | rewrite di_recs_length; lia].
Qed.

(* ===================================================================== *)
(*  7.  NON-VACUITY                                                       *)
(* ===================================================================== *)

(* durable-notes.md, "INCONSISTENT PREMISES ARE THE WORST DEFECT, AND
   NOTHING IN THE BUILD SEES THEM".  The bridge, the kind tie and the
   payload all have a model, exhibited at a witness. *)

(* the witness node: the smallest well-formed record, no indirect entries,
   no blocks ([FsDurObj.dobj_wit_dinode] is the record) *)
Definition dwire_wit_node : fs_node :=
  MkNode dobj_wit_dinode [] ∅.

Lemma dwire_wit_node_wf : dinode_wf (fn_rec dwire_wit_node).
Proof. exact dobj_wit_dinode_wf. Qed.

(* the state whose inode map is empty: [ko_slot] holds vacuously and the two
   ROLE clauses hold because every block but the bitmap block is given an
   inode kind, at the witness node *)
Definition dwire_wit_state (sb : fs_sb) (sbb : list (bv 8)) (u : gset Z)
    : fs_state_rec := MkFsS sb sbb ∅ u.

Definition dwire_wit_kinds (sb : fs_sb) (u : gset Z) : Z -> blk_kind :=
  kind_upd (fun _ => KInode (fun _ => dwire_wit_node))
    (sb_bmapstart sb) (KBitmap u).

Lemma dwire_wit_kinds_of_state (sb : fs_sb) (sbb : list (bv 8))
    (u : gset Z) :
  dwire_geom (dwire_wit_state sb sbb u) ->
  kinds_of_state (dwire_wit_state sb sbb u) (dwire_wit_kinds sb u).
Proof.
  intros Hgeo. split; cbn [dwire_wit_state fss_sb fss_inodes fss_used].
  - rewrite /dwire_wit_kinds kind_upd_at //.
  - intros j Hj _. exists (fun _ => dwire_wit_node).
    rewrite /dwire_wit_kinds.
    rewrite (kind_upd_ne (fun _ => KInode (fun _ => dwire_wit_node))
               (sb_bmapstart sb) (KBitmap u)
               (sb_inodestart sb + j) (Hgeo j Hj)) //.
  - intros i n _ Hi. rewrite lookup_empty in Hi. discriminate.
  - intros b nd HKb j. rewrite /dwire_wit_kinds in HKb.
    destruct (decide (b = sb_bmapstart sb)) as [-> | Hne].
    + rewrite kind_upd_at in HKb. discriminate.
    + rewrite (kind_upd_ne (fun _ => KInode (fun _ => dwire_wit_node))
                 (sb_bmapstart sb) (KBitmap u) b Hne) in HKb.
      injection HKb as <-. exact dwire_wit_node_wf.
Qed.

Lemma dwire_wit_blocksized (sb : fs_sb) (u : gset Z) (cov : gset Z) (ls : Z) :
  kinds_blocksized (dwire_wit_kinds sb u) cov ls.
Proof.
  intros b _. rewrite /dwire_wit_kinds.
  destruct (decide (b = sb_bmapstart sb)) as [-> | Hne].
  - rewrite kind_upd_at. apply bm_kind_blocksize.
  - rewrite (kind_upd_ne (fun _ => KInode (fun _ => dwire_wit_node))
               (sb_bmapstart sb) (KBitmap u) b Hne).
    apply di_kind_blocksize. intros j. exact dwire_wit_node_wf.
Qed.

(* the block map that IS the kinds encoded on the home set satisfies the
   bridge -- [FsDurObj.dobj_wit_close]'s shape, at this file's predicate *)
Lemma dwire_bridge_wit (K : Z -> blk_kind) (cov : gset Z) (ls : Z) :
  dwire_bridge K (fs_restrict (fun b => kind_enc (K b)) (fs_home_set cov ls))
    cov ls.
Proof.
  split; [apply fs_restrict_dom |].
  intros b Hb. by apply fs_restrict_lookup_Some.
Qed.

Section Witness.
  Context {Σ : gFunctors}.
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.

  (* THE PAYLOAD HAS A MODEL: the pure content is inhabited at the witness
     state and the witness kinds, over the block map they encode. *)
  Theorem Psi_dec_wit (cov : gset Z) (ls : Z) (sb : fs_sb)
      (sbb : list (bv 8)) (u : gset Z) :
    dwire_geom (dwire_wit_state sb sbb u) ->
    ⊢ Psi_dec (Σ := Σ) cov ls ∅
        (fs_restrict (fun b => kind_enc (dwire_wit_kinds sb u b))
           (fs_home_set cov ls)).
  Proof.
    intros Hgeo.
    iExists (dwire_wit_state sb sbb u), (dwire_wit_kinds sb u).
    iSplitR; [iPureIntro; apply dwire_bridge_wit |].
    iSplitR; [iPureIntro; apply (dwire_wit_blocksized sb u cov ls) |].
    iPureIntro. exact (dwire_wit_kinds_of_state sb sbb u Hgeo).
  Qed.

  (* ...AND THE GEOMETRY PREMISE IS SATISFIABLE, so the witness is not
     vacuous: any superblock whose inode region starts ABOVE the bitmap
     block has it, and so does xv6's own layout read the other way
     ([FsImg.fs_sb_ok]'s [sbo_bmapstart] puts the bitmap block above the
     region).  Exhibited at a superblock rather than assumed. *)
  Lemma dwire_geom_wit (sbb : list (bv 8)) (u : gset Z) :
    dwire_geom (dwire_wit_state
                  (MkFsSb 0 0 0 0 0 0 1 0) sbb u).
  Proof. intros j Hj. cbn [dwire_wit_state fss_sb]. cbn. lia. Qed.

End Witness.

(* the bodies are nests of block-sized big-ops; seal them the day they are
   written (durable-notes.md, the [iFrame] hang) *)
Global Typeclasses Opaque P_wf_dec dstep_dec Psi_dec.
