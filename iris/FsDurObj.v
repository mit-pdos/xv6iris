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

(* FsDurObj.v -- THE OBJECT-GRANULAR PENDING POOL (fs-state.md section 4.875),
   as machine-checked statements rather than as prose.

   Design of record: claude-notes/design/fs-state.md sections 4, 4.5, 4.5a,
   4.75, 4.75a and -- THE RULING THIS FILE VALIDATES -- 4.875; worklist
   claude-notes/projects/durable-disk.md, item 3a-val.  Its two predecessors
   are iris/FsDurRefute.v (the home-view accessor ruling's two walls) and
   iris/FsDurDefer.v (the deferred-justification ruling's third wall, and
   the four landed shapes this file reuses); read both first.

   THE RULING OF 2026-08-24, in four decisions:

     1. a transaction's durable promise is about its OBJECTS, never its
        blocks -- objects inside a shared block (bitmap bits, inode slots,
        dir records) are disjoint, so the block's final logged bytes are a
        FUNCTION of the set of per-object final values;
     2. the justification unit is the BATCH, the deposit unit is the
        TRANSACTION, the promise unit is the OBJECT: [end_op] deposits one
        self-contained fupd per touched object and a later writer of the
        same object COMPOSES onto the existing entry at deposit time;
     3. modularity is the [∗]: the pending state is a [[∗ object]], a
        client mentions only its own objects, and the batch-scope reasoning
        happens ONCE at quiescence as frame-composition;
     4. the bridge to bytes is ONE maintained invariant -- each home block's
        logged bytes encode its objects' current logged values, maintained
        per-write from the writer's own read-modify-write fact and consumed
        once at the close.

   WHAT THIS FILE ANSWERS, and the verdict on each.

   (1) THE POOL AND ITS ALGEBRA -- section 2.  The object name is four
       constructors ([dobj]); an object's durable resources are byte runs at
       [fs_gamma_D]'s [fsΦ], plus the [γtop] fragment and the link tokens for
       the one kind that has them (the inode slot).  A pending entry is
       [dpend]: the basic update "this object's durable resources move from
       [x] to [x']", and NOTHING else -- no ledger, no index by a durable
       byte map, no other op.  DEPOSIT is [dpool_deposit] (the [∗]-extension)
       and [dobj_modular_deposit] (a whole op's entries at once,
       disjointness the only interface); SAME-OBJECT RECOMPOSITION is
       [dpool_recompose] (sequential composition of the two fupds, done at
       deposit time by the party that observed [x']); DISJOINT-OBJECT
       COMMUTATION is [dpool_commute], and [dobj_two_ops_order_free] is
       3a-def's [dfr_ledger_order_blind] scenario HANDLED -- same pool, same
       final values, and (with section 3) the same final block bytes, which
       is exactly what the block-level ledger could not have;
       [dobj_3adef_scenario_handled] is all four conjuncts in ONE statement,
       its first being 3a-def's own lemma applied unchanged.  QUIESCENCE is
       [dpool_run] / [dpool_run_frame], with a CONCRETE instance at the
       shared bitmap block ([dpool_run_bitmap_alloc] / [_free]) so the
       schema is not vacuous.  PROVED -- and every law is stated over an
       ARBITRARY per-object reading [R], which is what makes (1') cost the
       algebra nothing.

   (1') THE ONE REFUTATION, AND ITS REPAIR -- section 2e.  The ruling's
       object NAMES are right; the natural resource READING of the bit
       object is not.  [FsStateBitmap.pool_elt] makes a clear bit own the
       block, so a [balloc] MOVES the block from [DBit b] to [DBlk b] --
       and the pool composes its entries by [∗], which cannot thread a
       resource out of one entry's conclusion into another's premise.
       [dres_bit_blk_excl] is the collision; [dres_map_alloc_incoherent]
       says the allocating op's own value assignment is contradictory; and
       [dres_blk_forces_source] ([FsDurRefute]'s [step_forces_the_element]
       idiom at one block) says the block cannot be conjured by the entry
       that needs it.  THE REPAIR IS ONE LINE OF THE READING: [dres_flat]
       makes the bit object RESOURCE-FREE and gives every block its own
       [DBlk] object, free or allocated ([dpend_flat_bit],
       [dres_flat_orphan_home]).  The price is [FsDurRefute] section (C)'s
       explicit-set pool at the FULL block set ([free_pool_at_full]) --
       i.e. no durable [FsStateBitmap.free_pool_used] -- which 3a-def
       already priced at zero, that argument being consumed on the ERA
       side.  What it buys is 3a-def's ORPHANED BLOCK having a durable home
       at every instant, which is the wall the ruling was written to clear.

   (2) THE ENCODE BRIDGE, PER WRITE, AT THE SHARED BITMAP -- section 3.
       The writer's read-modify-write fact is [FsBlocks.blk_splice]: the new
       block bytes are the old ones with MY object's field spliced in.  For
       the bitmap that is one byte ([bm_blk_write]); [bm_blk_write_enc] says
       the spliced block IS the encoding of the new used set, and
       [bm_new_byte_code] says the byte spliced is the one xv6's
       [bp->data[bi/8] |= m] / [&= ~m] actually stores.  THE 3a-def KILLER
       SCENARIO -- ops A and B interleaved on ONE bitmap block, A sets bit
       [i], B clears bit [j], [i <> j], BOTH orders -- is
       [bm_two_ops_order_free]: after each write the invariant holds with
       only the writer's bit's value moved ([bm_vals_write]), and the final
       bytes agree regardless of order.  The inode-block twin is
       [di_two_slots_order_free] (A writes slot [k], B writes slot [k'],
       [k <> k']).  PROVED.

   (3) THE CLOSE -- section 4.  [dobj_close] is the byte-level conclusion
       [D' = lm_logged L cov ls] at HOME MAPS, from "every home block's
       bytes are its objects' final values encoded" on both sides;
       [dobj_close_dstep] reads it into [FsDurDefer.dstep_strict]'s shape,
       i.e. into [FsDurDefer.commit_conclusion].  The MODULARITY THEOREM the
       owner asked for is [dobj_modular_deposit] plus the audit note at the
       end of section 2: NO lemma in this file quantifies over the ledger,
       over another op, or over a durable byte map, EXCEPT the one
       quiescence composition [dpool_run] (and the close, which is a pure
       equation between two maps).  PROVED.

   (4) THE ERA-SIDE WITNESS -- section 5.  Same-object recomposition needs
       the second writer to KNOW the first's pending target [x'].  It read
       [x'] through the era protocol, and what it must be handed is a
       HALF of a per-object [ghost_var] at the object's current pending
       value, minted by the era-side write that installed [x'] under the
       object's own serializer (the buffer lock for a block, the region
       invariant for an inode slot, the bitmap invariant for a bit).
       [dpool_recompose_era] is recomposition with that witness and NO
       hypothesis naming the first writer: the receipt supplies the
       [y = x'] the composition needs.  This is the implementation lane's
       interface requirement, stated as a term.

   NOTHING HERE IS A PROOF DIFFICULTY.  As in [FsDurRefute] and
   [FsDurDefer], every statement is about what a resource can say; no
   existing statement in the tree moved, and no [P_wf] body was flipped. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import base countable gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop ghost_map ghost_var.
Require Import BioDefs.        (* [BSIZE]                                   *)
Require Import BitmapEnc.      (* [bm_bytes], [bm_byte], the three bit laws *)
Require Import DinodeEnc.      (* [diblk_bytes], [dinode_bytes], [diblk_wf] *)
Require Import FsImg.          (* [BSIZE_z]                                 *)
Require Import RiscvPtsto.     (* [fs_dur_names] -- Gamma_D's two gnames    *)
Require Import LogDefs.        (* [lm_logged], [fs_home_set], [fs_restrict] *)
Require Import FsBlocks.       (* [blk_splice] and its three lookup laws    *)
Require Import FsDurBytes.     (* [fs_gamma_D]                              *)
Require Import FsState.        (* [fs_state], [free_bitmap_at], [top_frag]  *)
Require Import FsDurRefute.    (* [free_pool_at] -- 4.5a (C)'s explicit pool *)
Require Import FsDurDefer.     (* [P_wf_strict], [dstep_strict]             *)

(* the proofmode import re-opens [nat_scope] on top of the scope stack *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE OBJECT NAME                                                   *)
(* ===================================================================== *)

(* THE FOUR SHARING GRANULARITIES, as one type.  The shape is the one the
   deleted [FsObjType.fsobj] had ([git show 4cae0856:iris/FsObjType.v]) and
   it is redefined here rather than resurrected: that file existed because
   [Xv6Cameras] needed the type in a ledger field, and under this ruling the
   LOG has no object field at all (fs-state.md section 4.875, decision 2) --
   so the type belongs to the FS side alone, and nothing below it needs it.

   [DBit b] is the allocation bit OF block number [b], NOT a byte of the
   bitmap block: two bits of one byte are different objects, which is
   exactly why the bitmap block's BYTES are their own object ([DBlk] at the
   bitmap block) and the bits' values are read back out of them by the
   encoder in section 3.  That asymmetry is the whole reason the ruling's
   item 1 is order-free where the block-level ledger was not. *)
Inductive dobj :=
| DRec (b : Z) (k : nat)   (* bytes [16k, 16k+16) of home block [b]  *)
| DBit (b : Z)             (* the allocation bit OF block number [b] *)
| DSlot (i : Z)            (* the dinode record of inum [i]          *)
| DBlk (b : Z).            (* all of home block [b]                  *)

Global Instance dobj_eq_dec : EqDecision dobj.
Proof. solve_decision. Defined.

Definition dobj_enc (o : dobj) : Z * nat + Z + Z + Z :=
  match o with
  | DRec b k => inl (inl (inl (b, k)))
  | DBit b => inl (inl (inr b))
  | DSlot i => inl (inr i)
  | DBlk b => inr b
  end.

Definition dobj_dec (c : Z * nat + Z + Z + Z) : dobj :=
  match c with
  | inl (inl (inl (b, k))) => DRec b k
  | inl (inl (inr b)) => DBit b
  | inl (inr i) => DSlot i
  | inr b => DBlk b
  end.

Lemma dobj_dec_enc (o : dobj) : dobj_dec (dobj_enc o) = o.
Proof. by destruct o. Qed.

Global Instance dobj_countable : Countable dobj :=
  inj_countable' dobj_enc dobj_dec dobj_dec_enc.

(* THE GEOMETRY an object needs to find its home block, and nothing more.
   Two numbers, exactly as [FsStateBitmap.free_bitmap_at] and
   [FsStateInode.rec_owned_at] take theirs: a predicate about ONE object may
   not demand an [fs_sb] it has no way to hold. *)
Record dgeom := MkDGeom {
  dg_bmap : Z;    (* the bitmap block's number   *)
  dg_ist  : Z;    (* the inode region's start    *)
}.

(* the home block an object lives in *)
Definition dobj_home (G : dgeom) (o : dobj) : Z :=
  match o with
  | DRec b _ => b
  | DBit _ => dg_bmap G
  | DSlot i => dg_ist G + i `div` 16
  | DBlk b => b
  end.

(* THE TILING, at the two shared block kinds: the sixteen slot objects of
   one inode block, and every bit object, have ONE home block -- which is
   what makes the encode bridge of section 3 a per-BLOCK invariant.  Slot
   [k] of block [bi] is inum [16*bi + k] ([FsStateInode.rec_owned_at_slot]'s
   numbering, and [di_vals] below is stated at it). *)
Lemma dobj_home_slot (G : dgeom) (bi : Z) (k : nat) :
  (k < 16)%nat -> dobj_home G (DSlot (16 * bi + Z.of_nat k)) = dg_ist G + bi.
Proof.
  intros Hk. cbn [dobj_home].
  assert (Hk0 : Z.of_nat k `div` 16 = 0) by (apply Z.div_small; lia).
  assert (Hd : (16 * bi + Z.of_nat k) `div` 16 = bi).
  { rewrite (Z.mul_comm 16 bi) Z.div_add_l; [| lia]. rewrite Hk0. lia. }
  rewrite Hd //.
Qed.

Lemma dobj_home_bit (G : dgeom) (b : Z) : dobj_home G (DBit b) = dg_bmap G.
Proof. reflexivity. Qed.

(* AN OBJECT'S VALUE.  Three shapes, one per kind of thing an object can be:
   a byte run (a dir/data record, or a whole block), a bit, or a whole
   inode NODE (the record plus everything the link RA counts about it --
   an inode slot's promise is not a byte promise, see [dres] below). *)
Inductive oval :=
| OVBytes (bs : list (bv 8))
| OVBit (used : bool)
| OVNode (n : fs_node).

(* ===================================================================== *)
(*  2.  THE PENDING POOL, AND ITS ALGEBRA                                 *)
(* ===================================================================== *)

Section Pool.
  Context {Σ : gFunctors}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Implicit Types Γ : fs_view_names Σ.
  Implicit Types G : dgeom.

  (* ---------------------------------------------------------------- *)
  (*  2a.  AN OBJECT'S DURABLE RESOURCES                                *)
  (* ---------------------------------------------------------------- *)

  (* [dres Γ G o x] is everything the durable view holds ON BEHALF OF [o]
     when [o]'s value is [x].  At the durable instance [Γ := fs_gamma_D g Γd]
     the byte runs are [ghost_map] elements of the durable byte view, so
     this really is "object [o]'s durable resources" and nothing else.

     The four readings, and each is the tree's own:

     - [DRec b k]: a sixteen-byte run at offset [16k] of block [b].  A
       directory entry, or a sixteen-byte slice of a file's data block.
     - [DBit b]: [FsStateBitmap.pool_elt] VERBATIM -- [emp] at a set bit and
       the BLOCK ITSELF at a clear one.  This is the one object whose
       resources are not a run of its own home block's bytes, and the reason
       is the design's: nobody carries a bit resource, and a block nobody
       owns is a leaked block.
     - [DSlot i]: the record's 64-byte run ([rec_owned_at], the
       geometry-free reading), the [γtop] FRAGMENT, and the link ghost
       ([FsState.inode_ghost] = the link authority, the entry tokens, and
       the record's own local well-formedness).  The fragment is in it for
       [FsDurDefer.P_wf_strict]'s reason: [FsState.inode_owned] carries none
       and an authority with no elements cannot be retagged.
     - [DBlk b]: a whole block, at its full width. *)
  Definition dres Γ G (o : dobj) (x : oval) : iProp Σ :=
    match o with
    | DRec b k =>
        match x with
        | OVBytes bs => (⌜length bs = 16%nat⌝
                         ∗ byte_range Γ b (16 * Z.of_nat k) bs)%I
        | _ => ⌜False⌝%I
        end
    | DBit b =>
        match x with
        | OVBit used => (if used then emp else ∃ bs, blk_owned Γ b bs)%I
        | _ => ⌜False⌝%I
        end
    | DSlot i =>
        match x with
        | OVNode n => (rec_owned_at Γ (dg_ist G) i (fn_rec n)
                       ∗ top_frag Γ i n ∗ inode_ghost Γ i n)%I
        | _ => ⌜False⌝%I
        end
    | DBlk b =>
        match x with
        | OVBytes bs => blk_owned Γ b bs
        | _ => ⌜False⌝%I
        end
    end.

  (* THE BIT OBJECT IS THE FREE POOL'S SLOT, DEFINITIONALLY.  This is what
     makes section 2c's concrete quiescence instance a rewrite rather than a
     construction. *)
  Lemma dres_bit_pool_elt Γ G (u : gset Z) (b : Z) :
    dres Γ G (DBit b) (OVBit (bool_decide (b ∈ u))) ⊣⊢ pool_elt Γ u b.
  Proof. rewrite /pool_elt. destruct (bool_decide (b ∈ u)); done. Qed.

  (* ...and the block object is [blk_owned] *)
  Lemma dres_blk Γ G (b : Z) (bs : list (bv 8)) :
    dres Γ G (DBlk b) (OVBytes bs) ⊣⊢ blk_owned Γ b bs.
  Proof. done. Qed.

  (* THE GEOMETRY IS READ BY ONE KIND ONLY, and this is why the bitmap
     lemmas of section 2c carry no geometry premise at all: [DRec], [DBit]
     and [DBlk] each name their home block in the object itself, so their
     resources are a function of the object and the value.  Only [DSlot]
     reads [dg_ist] -- an inum's record's ADDRESS is the region's, not the
     inum's -- which is exactly the asymmetry
     [FsStateInode.rec_owned_at] was factored for. *)
  Lemma dres_geom_irrel Γ G G' (o : dobj) (x : oval) :
    (forall i, o <> DSlot i) -> dres Γ G o x ⊣⊢ dres Γ G' o x.
  Proof.
    intros Hns. destruct o as [b k | b | i | b]; try done.
    exfalso. exact (Hns i eq_refl).
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2b.  THE PENDING ENTRY AND THE POOL                               *)
  (* ---------------------------------------------------------------- *)

  (* ONE PENDING ENTRY.  fs-state.md section 4.875 decision 2's
     "self-contained fupd per touched object": from [o]'s durable resources
     at the value the batch started from, to [o]'s durable resources at the
     value the batch has logged.  It mentions [o] and two values.  It does
     NOT mention the durable byte map, the ledger, the batch, or any other
     object -- which is what retires 3a-prime's wall (B) (there is no
     [forall Dc]) and 3a-def's wall (there is no cross-op obligation to
     inherit). *)
  (* THE READING IS A PARAMETER, and every law of this subsection is blind
     to it: (a)-(d) below are facts about a [[∗ map]] of basic updates and
     unfold [R] nowhere.  That is not decoration -- section 2e REPAIRS the
     reading, and the repair costs the algebra nothing precisely because of
     this.  [dres Γ G] is the ruled reading; [dres_flat Γ G] is the
     repaired one; both are instances. *)
  Implicit Types R : dobj -> oval -> iProp Σ.

  Definition dpend R (o : dobj) (p : oval * oval) : iProp Σ :=
    (R o p.1 ==∗ R o p.2)%I.

  (* THE POOL.  [P] maps a touched object to (its value at the last commit,
     its value now).  Decision 3: the pending state is a [[∗ object]]. *)
  Definition dpool R (P : gmap dobj (oval * oval)) : iProp Σ :=
    ([∗ map] o ↦ p ∈ P, dpend R o p)%I.

  Definition dvals_old (P : gmap dobj (oval * oval)) : gmap dobj oval :=
    fst <$> P.
  Definition dvals_new (P : gmap dobj (oval * oval)) : gmap dobj oval :=
    snd <$> P.

  (* the objects' resources, at an assignment of values *)
  Definition dres_map R (V : gmap dobj oval) : iProp Σ :=
    ([∗ map] o ↦ x ∈ V, R o x)%I.

  (* ---------------------------------------------------------------- *)
  (*  (a)  DEPOSIT                                                      *)
  (* ---------------------------------------------------------------- *)

  (* A FRESH OBJECT'S ENTRY GOES IN BY [∗]-EXTENSION, and there is nothing
     else to it.  No premise about the pool's other entries, no batch index,
     no ledger: the depositor supplies a proposition about [o]. *)
  Lemma dpool_deposit R P o p :
    P !! o = None ->
    dpool R P -∗ dpend R o p -∗ dpool R (<[o := p]> P).
  Proof.
    intros Ho. rewrite /dpool (big_sepM_insert _ P o p Ho).
    iIntros "HP Hp". iFrame.
  Qed.

  (* ...AND A WHOLE TRANSACTION'S ENTRIES GO IN AT ONCE.  This is the
     MODULARITY THEOREM of decision 3, and disjointness of the two domains
     is the ENTIRE interface: [Q] is the op's own objects, [P] is everything
     else in the batch, and no clause of either mentions the other's
     content.  ("Not durable yet" appears nowhere.) *)
  Theorem dobj_modular_deposit R (P Q : gmap dobj (oval * oval)) :
    P ##ₘ Q ->
    dpool R P -∗ dpool R Q -∗ dpool R (P ∪ Q).
  Proof.
    intros Hd. rewrite /dpool (big_sepM_union _ _ _ Hd).
    iIntros "HP HQ". iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  (b)  SAME-OBJECT RECOMPOSITION                                    *)
  (* ---------------------------------------------------------------- *)

  (* A SECOND WRITER OF OBJECT [o] COMPOSES ONTO THE EXISTING ENTRY.  The
     composition is SEQUENTIAL and it happens at DEPOSIT TIME -- by the
     party that observed [x'], which is why its own entry starts at [x']
     (section 5 is what supplies it that fact).  The pool afterwards holds
     ONE entry for [o], at [(x, x'')]: the batch's promise about [o] is a
     single move from the last commit to now, however many transactions
     touched it. *)
  Lemma dpool_recompose R P o x x' x'' :
    P !! o = Some (x, x') ->
    dpool R P -∗ dpend R o (x', x'') -∗ dpool R (<[o := (x, x'')]> P).
  Proof.
    intros Ho. rewrite /dpool.
    iIntros "HP Hnew".
    iDestruct (big_sepM_delete _ P o (x, x') Ho with "HP") as "[Hold HP]".
    rewrite -(insert_delete_insert P o (x, x'')).
    rewrite (big_sepM_insert _ (delete o P) o (x, x'')
               (lookup_delete P o)).
    iFrame "HP". rewrite /dpend. cbn [fst snd].
    iIntros "Hx". iMod ("Hold" with "Hx") as "Hx'".
    iApply ("Hnew" with "Hx'").
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  (c)  DISJOINT-OBJECT COMMUTATION                                  *)
  (* ---------------------------------------------------------------- *)

  (* TWO ENTRIES AT DIFFERENT OBJECTS COMPOSE IN EITHER ORDER TO THE SAME
     POOL.  At the map level this is [insert_commute]; the point is that
     unlike 3a-def's block ledger, the ORDER-BLINDNESS IS NOT A DEFECT
     HERE -- section 3 shows the target the pool is measured against is
     order-free too. *)
  Lemma dpool_commute (P : gmap dobj (oval * oval)) o1 p1 o2 p2 :
    o1 <> o2 ->
    <[o1 := p1]> (<[o2 := p2]> P) = <[o2 := p2]> (<[o1 := p1]> P).
  Proof. intros H. by apply insert_commute. Qed.

  (* ...and hence the POOL PROPOSITIONS are the same proposition. *)
  Lemma dpool_commute_res R (P : gmap dobj (oval * oval)) o1 p1 o2 p2 :
    o1 <> o2 ->
    dpool R (<[o1 := p1]> (<[o2 := p2]> P))
    ⊣⊢ dpool R (<[o2 := p2]> (<[o1 := p1]> P)).
  Proof. intros H. by rewrite (dpool_commute P o1 p1 o2 p2 H). Qed.

  (* 3a-def's SCENARIO, HANDLED.  [FsDurDefer.dfr_ledger_order_blind] is two
     open ops writing ONE home block once each, in either order, leaving the
     same ledger -- and [defer_overlay_order_blind] then refutes any
     order-free row, because the block-level TARGET ([lm_logged L]) moves
     with the order.  In the object vocabulary the same two ops touch two
     DIFFERENT objects of that block, so:

     - the pool is the same map under both orders (this lemma's first
       conjunct);
     - the final VALUES are the same assignment (its second);
     - and the final BYTES are the same too -- which is the conjunct
       3a-def could not have, and it is section 3's
       [bm_two_ops_order_free] / [di_two_slots_order_free].

     Note what is NOT assumed: no disjointness of the two ops' blocks, no
     ordering ghost, no sequence number.  Only [o1 <> o2]. *)
  Theorem dobj_two_ops_order_free (P : gmap dobj (oval * oval))
      (o1 o2 : dobj) (p1 p2 : oval * oval) :
    o1 <> o2 ->
    <[o1 := p1]> (<[o2 := p2]> P) = <[o2 := p2]> (<[o1 := p1]> P)
    /\ dvals_new (<[o1 := p1]> (<[o2 := p2]> P))
       = dvals_new (<[o2 := p2]> (<[o1 := p1]> P))
    /\ dvals_old (<[o1 := p1]> (<[o2 := p2]> P))
       = dvals_old (<[o2 := p2]> (<[o1 := p1]> P)).
  Proof.
    intros H. pose proof (dpool_commute P o1 p1 o2 p2 H) as Heq.
    split; [exact Heq |]. split; by rewrite Heq.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  (d)  THE QUIESCENCE RUN                                           *)
  (* ---------------------------------------------------------------- *)

  (* RUNNING THE WHOLE POOL IS ONE BASIC UPDATE.  This is the ONLY lemma in
     the file that looks at more than one object at a time, and it is the
     generic frame-composition decision 3 promises: the [∗] over disjoint
     objects, run once. *)
  Lemma dpool_run R P :
    dpool R P -∗ dres_map R (dvals_old P) ==∗ dres_map R (dvals_new P).
  Proof.
    rewrite /dpool /dres_map /dvals_old /dvals_new !big_sepM_fmap.
    iIntros "HP HR".
    iAssert ([∗ map] o ↦ p ∈ P, dpend R o p ∗ R o p.1)%I
      with "[HP HR]" as "H".
    { rewrite big_sepM_sep. iFrame. }
    iApply big_sepM_bupd.
    iApply (big_sepM_impl with "H").
    iModIntro. iIntros (o p _) "[Hp Hx]". iApply ("Hp" with "Hx").
  Qed.

  (* THE STRICT-BODY READING.  [Body] is the strict predicate at the old
     values -- [FsDurDefer.P_wf_strict]'s shape, or any part of it -- and the
     two premises are the TILING: the objects the pool moved come out of the
     body by [∗], the rest is untouched, and the body re-forms at the new
     values.  Everything about which objects tile which block is in those two
     premises and in nothing else. *)
  Lemma dpool_run_frame R P (Body Rest Body' : iProp Σ) :
    (Body ⊢ dres_map R (dvals_old P) ∗ Rest) ->
    (dres_map R (dvals_new P) ∗ Rest ⊢ Body') ->
    dpool R P -∗ Body ==∗ Body'.
  Proof.
    intros Hout Hin. iIntros "HP HB".
    rewrite Hout. iDestruct "HB" as "[HV HR]".
    iMod (dpool_run R P with "HP HV") as "HV'".
    iModIntro. rewrite -Hin. iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2c.  THE RUN, CONCRETELY, AT THE SHARED BITMAP BLOCK              *)
  (*                                                                    *)
  (*  A [balloc] touches TWO objects of the strict body's bitmap piece:  *)
  (*  the bit ([DBit b], whose resources go from "the block" to [emp])   *)
  (*  and the bitmap block's bytes ([DBlk bms]).  The two entries it     *)
  (*  deposits run against [free_bitmap_at] and land it at the new used  *)
  (*  set.  [bfree] is the mirror.  These are [FsStateBitmap]'s own two   *)
  (*  movers, read in the object vocabulary -- so the schema above is    *)
  (*  instantiated at a real piece of [fs_state] and not left vacuous.   *)
  (* ---------------------------------------------------------------- *)

  Lemma bitmap_alloc_obj Γ G (bms nb : Z) (u : gset Z) (b : Z) :
    0 <= b < nb -> b ∉ u ->
    free_bitmap_at Γ bms nb u ⊢
      dres Γ G (DBit b) (OVBit false)
      ∗ dres Γ G (DBlk bms) (OVBytes (bm_bytes BSIZE u))
      ∗ (dres Γ G (DBit b) (OVBit true)
         -∗ dres Γ G (DBlk bms) (OVBytes (bm_bytes BSIZE (u ∪ {[b]})))
         -∗ free_bitmap_at Γ bms nb (u ∪ {[b]})).
  Proof.
    intros Hrng Hnu.
    rewrite (bitmap_alloc Γ bms nb u b Hrng Hnu).
    iIntros "(Hblk & Hbm & Hclose)". iFrame "Hblk Hbm".
    iIntros "_ Hbm'". iApply ("Hclose" with "Hbm'").
  Qed.

  Lemma bitmap_free_obj Γ (Hex : phi_excl Γ) G (bms nb : Z) (u : gset Z)
      (b : Z) (bs : list (bv 8)) :
    0 <= b < nb ->
    free_bitmap_at Γ bms nb u -∗ blk_owned Γ b bs -∗
      ⌜b ∈ u⌝
      ∗ dres Γ G (DBlk bms) (OVBytes (bm_bytes BSIZE u))
      ∗ (dres Γ G (DBlk bms) (OVBytes (bm_bytes BSIZE (u ∖ {[b]})))
         -∗ free_bitmap_at Γ bms nb (u ∖ {[b]})).
  Proof.
    intros Hrng. iIntros "Hbm Hblk".
    iDestruct (bitmap_free Γ Hex bms nb u b bs Hrng with "Hbm Hblk")
      as "(%Hin & Hbmb & Hclose)".
    iSplitR; [done |]. iFrame "Hbmb". iIntros "Hbm'".
    iApply ("Hclose" with "Hbm'").
  Qed.

  (* THE RUN AT A [balloc]: the two entries, run, move the bitmap piece of
     the strict body from [u] to [u ∪ {[b]}].  This is (1d) at a real piece
     of [fs_state] and it holds at the RULED reading.

     READ IT WITH SECTION 2e, though, and do not take it as the endorsed
     shape: at this reading the bit's entry SWALLOWS the block (its
     conclusion [dres (DBit b) (OVBit true)] is [emp]), so the [balloc]
     modelled here leaks the very block it allocated.  Under [dres_flat]
     the same two entries run with the block untouched, because the block
     is [DBlk b]'s throughout and the bit moves only a value. *)
  Lemma dpool_run_bitmap_alloc Γ G (bms nb : Z) (u : gset Z) (b : Z) :
    0 <= b < nb -> b ∉ u ->
    dpend (dres Γ G) (DBit b) (OVBit false, OVBit true) -∗
    dpend (dres Γ G) (DBlk bms)
      (OVBytes (bm_bytes BSIZE u), OVBytes (bm_bytes BSIZE (u ∪ {[b]}))) -∗
    free_bitmap_at Γ bms nb u ==∗ free_bitmap_at Γ bms nb (u ∪ {[b]}).
  Proof.
    intros Hrng Hnu. iIntros "Hbit Hblk Hfb".
    rewrite (bitmap_alloc_obj Γ G bms nb u b Hrng Hnu).
    iDestruct "Hfb" as "(Hslot & Hbm & Hclose)".
    rewrite /dpend. cbn [fst snd].
    iMod ("Hbit" with "Hslot") as "Hslot'".
    iMod ("Hblk" with "Hbm") as "Hbm'".
    iModIntro. iApply ("Hclose" with "Hslot' Hbm'").
  Qed.

  (* THE MIRROR AT A [bfree], and the ASYMMETRY here is section 2e seen from
     the other side.  Only the BITMAP BLOCK object's entry is run: the freed
     block is threaded through the LEMMA (the freer holds it and
     [FsStateBitmap.bitmap_free] puts it back into the pool, having first
     proved the bit reads allocated -- so xv6's [panic("freeing free
     block")] arm is dead), and NOT through the bit object's entry.  It
     cannot be: under the ruled reading that entry would have to PRODUCE
     [∃ bs, blk_owned Γ b bs] out of [emp], which [dres_blk_forces_source]
     refutes.  Under [dres_flat] the question does not arise. *)
  Lemma dpool_run_bitmap_free Γ (Hex : phi_excl Γ) G (bms nb : Z)
      (u : gset Z) (b : Z) (bs : list (bv 8)) :
    0 <= b < nb ->
    dpend (dres Γ G) (DBlk bms)
      (OVBytes (bm_bytes BSIZE u), OVBytes (bm_bytes BSIZE (u ∖ {[b]}))) -∗
    free_bitmap_at Γ bms nb u -∗ blk_owned Γ b bs ==∗
      ⌜b ∈ u⌝ ∗ free_bitmap_at Γ bms nb (u ∖ {[b]}).
  Proof.
    intros Hrng. iIntros "Hblk Hfb Hin".
    iDestruct (bitmap_free_obj Γ Hex G bms nb u b bs Hrng
                 with "Hfb Hin") as "(%Hu & Hbm & Hclose)".
    rewrite /dpend. cbn [fst snd].
    iMod ("Hblk" with "Hbm") as "Hbm'".
    iModIntro. iSplitR; [done |]. iApply ("Hclose" with "Hbm'").
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  2d.  THE AUDIT NOTE (decision 3's tractability requirement)       *)
  (*                                                                    *)
  (*  Read the statements above and check the quantifiers: [dpend],     *)
  (*  [dpool_deposit], [dobj_modular_deposit], [dpool_recompose],       *)
  (*  [dpool_commute] and the four concrete bitmap lemmas mention ONE   *)
  (*  object (or two disjoint ones) and no ledger, no batch index, no   *)
  (*  durable byte map and no other transaction.  [dpool_run] and       *)
  (*  [dpool_run_frame] are the ONE quiescence composition, and section *)
  (*  4's [dobj_close] is a pure equation between two block maps.  That *)
  (*  is the whole of the file's non-local surface.                     *)
  (*                                                                    *)
  (*  Two statements elsewhere DO name more, and neither is part of the *)
  (*  interface: [dobj_3adef_scenario_handled] names 3a-def's ledger    *)
  (*  because it IS 3a-def's scenario, restated to be compared with it; *)
  (*  and section 4's [dobj_close] names the batch's logged view,       *)
  (*  because that is what a CLOSE is.  A client proof mentions         *)
  (*  neither.                                                          *)
  (* ---------------------------------------------------------------- *)

  (* ---------------------------------------------------------------- *)
  (*  2e.  THE ONE THING THAT DOES NOT WORK, AND THE MINIMAL REPAIR     *)
  (* ---------------------------------------------------------------- *)

  (* THE RULING'S OBJECT VOCABULARY IS CORRECT AND ITS BIT OBJECT'S
     RESOURCE READING IS NOT, and this subsection is that finding, its
     minimal refutation, and the repair.  Nothing above changes: the
     algebra is stated over an arbitrary reading [R] precisely so that the
     repair is a change of instance and not a change of theory.

     THE READING AT ISSUE is the natural one, and it is the tree's own:
     [FsStateBitmap.pool_elt] gives [emp] at a set bit and THE BLOCK ITSELF
     at a clear one, so [dres Γ G (DBit b) (OVBit false)] owns block [b].
     That is exactly right as an invariant of [fs_state] -- a block nobody
     owns is a leaked block -- and it is wrong as a PER-OBJECT PENDING
     READING, for one reason:

       A [balloc] MOVES BLOCK [b] BETWEEN TWO OBJECTS.  Before it, block
       [b] is inside [DBit b] at [OVBit false]; after it, [DBit b] is
       [OVBit true] (which owns nothing) and the block is the allocating
       op's, to become a [DBlk b] object.  The pool composes its entries by
       [∗], and a [∗] cannot thread a resource out of one entry's
       conclusion into another entry's premise.

     Three lemmas below, and then the repair. *)

  Lemma dres_bit_free Γ G (b : Z) :
    dres Γ G (DBit b) (OVBit false) ⊣⊢ ∃ bs, blk_owned Γ b bs.
  Proof. done. Qed.

  Lemma dres_bit_used Γ G (b : Z) :
    dres Γ G (DBit b) (OVBit true) ⊣⊢ emp.
  Proof. done. Qed.

  (* (i) THE TWO OBJECTS CANNOT BOTH HOLD THE BLOCK. *)
  Lemma dres_bit_blk_excl Γ (Hex : phi_excl Γ) G (b : Z) (bs : list (bv 8)) :
    dres Γ G (DBit b) (OVBit false) -∗ dres Γ G (DBlk b) (OVBytes bs) -∗
      False.
  Proof.
    rewrite dres_bit_free dres_blk.
    iIntros "Hbit Hblk". iDestruct "Hbit" as (bs0) "Hbit".
    iDestruct (blk_owned_excl Γ Hex with "Hbit Hblk") as "[]".
  Qed.

  (* (ii) SO THE ASSIGNMENT A [balloc] PRODUCES IS CONTRADICTORY.  The
     allocating op's own value map holds [DBit b] free (it has not yet
     logged the bitmap block) and [DBlk b] at the block's content (it has
     the block).  Under the ruled reading no such assignment exists, so the
     pool cannot be run at it. *)
  Lemma dres_map_alloc_incoherent Γ (Hex : phi_excl Γ) G
      (V : gmap dobj oval) (b : Z) (bs : list (bv 8)) :
    V !! DBit b = Some (OVBit false) ->
    V !! DBlk b = Some (OVBytes bs) ->
    dres_map (dres Γ G) V -∗ False.
  Proof.
    intros Hbit Hblk. rewrite /dres_map. iIntros "HV".
    iDestruct (big_sepM_delete _ V (DBit b) (OVBit false) Hbit with "HV")
      as "[Hbit HV]".
    assert (Hblk' : delete (DBit b) V !! DBlk b = Some (OVBytes bs)).
    { rewrite lookup_delete_ne; [exact Hblk | intros Hbad; discriminate]. }
    iDestruct (big_sepM_delete _ (delete (DBit b) V) (DBlk b) (OVBytes bs)
                 Hblk' with "HV") as "[Hblk _]".
    iDestruct (dres_bit_blk_excl Γ Hex G b bs with "Hbit Hblk") as "[]".
  Qed.

  (* (iii) AND THE MISSING RESOURCE CANNOT BE CONJURED BY THE ENTRY THAT
     NEEDS IT.  This is [FsDurRefute]'s [step_forces_the_element] idiom:
     any [P] whose update produces block [b]'s object ALREADY excludes an
     outside holder of the block, i.e. the block came from somewhere and
     the pool is not that somewhere.  [P] is arbitrary -- in particular it
     may be the bit object's entry, or the whole rest of the pool. *)
  Lemma dres_blk_forces_source Γ (Hex : phi_excl Γ) G (P : iProp Σ)
      (b : Z) (bs bs' : list (bv 8)) :
    (P ==∗ dres Γ G (DBlk b) (OVBytes bs)) -∗ P -∗
    blk_owned Γ b bs' ==∗ False.
  Proof.
    iIntros "Hstep HP Hout".
    iMod ("Hstep" with "HP") as "Hblk". rewrite dres_blk.
    iDestruct (blk_owned_excl Γ Hex with "Hblk Hout") as "[]".
  Qed.

  (* THE REPAIR, AND IT IS ONE LINE OF THE READING: make the BIT OBJECT
     RESOURCE-FREE, and give every block its own [DBlk] object -- free or
     allocated.  The bit then promises only a VALUE, which is all the
     encoder of section 3 ever reads off it, and no ownership crosses an
     object boundary at a [balloc] or a [bfree].

     WHAT IT COSTS, and 3a-def already priced it at zero.  With the bit
     resource-free the durable free pool is [FsDurRefute.free_pool_at] at
     the FULL block set ([free_pool_at_full] below), i.e. exactly section
     4.5a (C)'s explicit-set decoupling taken to its limit -- so
     [FsStateBitmap.free_pool_used] ("you own this block, therefore its bit
     reads allocated", which kills xv6's [panic("freeing free block")]) is
     not a durable theorem any more.  fs-state.md section 4.75a already
     records that that argument is consumed on the ERA side, where the
     coupled pool stays; what is left durably is the per-BATCH endpoint
     condition at the commit.

     WHAT IT BUYS, and this is the point: 3a-def's ORPHANED BLOCK has a
     durable home at every instant.  That wall was "after the evicting
     writer's bitmap step the other op's block is marked USED, so
     [free_pool] gives nothing at it ([FsDurDefer.free_pool_used_no_block])
     and no inode names it yet".  Under the flat reading the block is
     [DBlk b]'s throughout and the bit's value says nothing about who owns
     it -- [dres_flat_orphan_home] is that, in one line. *)
  Definition dres_flat Γ G (o : dobj) (x : oval) : iProp Σ :=
    match o with
    | DBit _ => match x with OVBit _ => emp%I | _ => ⌜False⌝%I end
    | _ => dres Γ G o x
    end.

  Lemma dres_flat_bit Γ G (b : Z) (u : bool) :
    dres_flat Γ G (DBit b) (OVBit u) ⊣⊢ emp.
  Proof. done. Qed.

  Lemma dres_flat_not_bit Γ G (o : dobj) (x : oval) :
    (forall b, o <> DBit b) -> dres_flat Γ G o x ⊣⊢ dres Γ G o x.
  Proof.
    intros Hnb. destruct o as [b k | b | i | b]; try done.
    exfalso. exact (Hnb b eq_refl).
  Qed.

  (* THE BIT'S ENTRY IS NOW FREE AT BOTH VALUES, so nothing crosses. *)
  Lemma dpend_flat_bit Γ G (b : Z) (u u' : bool) :
    ⊢ dpend (dres_flat Γ G) (DBit b) (OVBit u, OVBit u').
  Proof.
    rewrite /dpend. cbn [fst snd]. rewrite !dres_flat_bit.
    iIntros "_". by iModIntro.
  Qed.

  (* ...AND THE ASSIGNMENT (ii) REFUTED IS NOW COHERENT: the free bit and
     the block object sit side by side, and what they hold together is
     exactly the block. *)
  Lemma dres_flat_orphan_home Γ G (b : Z) (bs : list (bv 8)) (u : bool) :
    dres_flat Γ G (DBlk b) (OVBytes bs) ∗ dres_flat Γ G (DBit b) (OVBit u)
    ⊣⊢ blk_owned Γ b bs.
  Proof.
    rewrite dres_flat_bit (dres_flat_not_bit Γ G (DBlk b) (OVBytes bs));
      [| intros b0; discriminate].
    rewrite dres_blk right_id //.
  Qed.

  (* THE PRICE, AS A TERM: the durable free pool at the FULL block set.
     [FsDurRefute.free_pool_at] is section 4.5a (C)'s explicit-set pool, and
     this says the flat reading's [DBlk] objects ARE it, with no coupling to
     the used set left. *)
  Lemma free_pool_at_full Γ (nb : Z) :
    free_pool_at Γ nb (list_to_set (seqZ 0 nb))
    ⊣⊢ ([∗ list] b ∈ seqZ 0 nb, ∃ bs, blk_owned Γ b bs).
  Proof.
    rewrite /free_pool_at. apply big_sepL_proper.
    intros k b Hb.
    assert (Hin : b ∈ (list_to_set (seqZ 0 nb) : gset Z)).
    { apply elem_of_list_to_set. exact (elem_of_list_lookup_2 _ _ _ Hb). }
    rewrite (bool_decide_eq_true_2 _ Hin) //.
  Qed.

End Pool.

(* ===================================================================== *)
(*  3.  THE ENCODE BRIDGE, PER WRITE                                      *)
(* ===================================================================== *)

(* fs-state.md section 4.875 decision 4: "each home block's logged bytes
   encode its objects' current logged values", maintained per-write by the
   writer's own read-modify-write fact.  That fact is [FsBlocks.blk_splice]:
   the whole-block content a writer's stores produce is the old block with
   ITS field spliced at ITS offset.  Everything below is pure -- lists,
   [gset Z] and the two encoders -- and none of it mentions a resource. *)

(* ---- the missing splice law -------------------------------------- *)

(* A ONE-BYTE SPLICE IS A LIST INSERT.  MARKED FOR RELOCATION to
   [FsBlocks.v], beside [blk_splice_whole]: it is the same kind of fact
   (a splice at a degenerate width, read as the operation the caller
   already has) and it belongs with the other three lookup laws.  It is
   here only because this file may not edit an existing statement. *)
Lemma blk_splice_one (off : nat) (v : bv 8) (bs : list (bv 8)) :
  (off < length bs)%nat -> blk_splice off [v] bs = <[off := v]> bs.
Proof.
  intros Hoff. apply list_eq. intros j.
  destruct (Nat.lt_total j off) as [Hlt | [-> | Hgt]].
  - rewrite (blk_splice_lookup_lt off [v] bs j ltac:(lia) Hlt).
    rewrite list_lookup_insert_ne; [reflexivity | lia].
  - rewrite (blk_splice_lookup_mid off [v] bs off ltac:(lia) ltac:(lia)
               ltac:(cbn [length]; lia)).
    rewrite Nat.sub_diag list_lookup_insert; [reflexivity | exact Hoff].
  - rewrite (blk_splice_lookup_ge off [v] bs j ltac:(lia)
               ltac:(cbn [length]; lia)).
    rewrite list_lookup_insert_ne; [reflexivity | lia].
Qed.

(* ---- the bitmap block -------------------------------------------- *)

(* the used set after a write of bit [bi] *)
Definition bm_wr (u : gset Z) (bi : Z) (b : bool) : gset Z :=
  if b then u ∪ {[bi]} else u ∖ {[bi]}.

(* ONLY THE WRITER'S OWN BIT MOVES.  Every other bit of the block -- in
   particular every bit another open transaction is holding -- reads the
   same before and after. *)
Lemma bm_wr_off (u : gset Z) (bi : Z) (b : bool) (x : Z) :
  x <> bi -> (x ∈ bm_wr u bi b <-> x ∈ u).
Proof. intros Hne. rewrite /bm_wr. destruct b; set_solver. Qed.

Lemma bm_wr_at (u : gset Z) (bi : Z) (b : bool) :
  (bi ∈ bm_wr u bi b) <-> b = true.
Proof.
  rewrite /bm_wr. destruct b.
  - split; [intros _; reflexivity | intros _; set_solver].
  - split; [intros Hin; exfalso; set_solver | intros Hb; discriminate].
Qed.

(* THE WRITER'S READ-MODIFY-WRITE FACT, at the bitmap block: the new block
   content is the old one with the ONE byte holding [bi] spliced. *)
Definition bm_blk_write (bs : list (bv 8)) (u' : gset Z) (bi : Z)
    : list (bv 8) :=
  blk_splice (Z.to_nat (bi `div` 8)) [bm_byte u' (bi `div` 8)] bs.

(* THE MAINTENANCE.  The spliced block IS the encoding of the new used set.
   [BitmapEnc.bm_bytes_set] / [_clear] are the encoder half; [blk_splice_one]
   is the splice half; the composition is the invariant's per-write step. *)
Lemma bm_blk_write_enc (u : gset Z) (bi : Z) (b : bool) :
  0 <= bi < 8 * Z.of_nat BSIZE ->
  bm_blk_write (bm_bytes BSIZE u) (bm_wr u bi b) bi
  = bm_bytes BSIZE (bm_wr u bi b).
Proof.
  intros Hbi.
  assert (Hlt : (Z.to_nat (bi `div` 8) < BSIZE)%nat)
    by (apply bit_byte_lt; lia).
  rewrite /bm_blk_write blk_splice_one;
    [| rewrite bm_bytes_length; exact Hlt].
  destruct b.
  - exact (bm_bytes_set BSIZE u bi ltac:(lia) Hlt).
  - exact (bm_bytes_clear BSIZE u bi ltac:(lia) Hlt).
Qed.

(* AND THE BYTE SPLICED IS THE ONE THE CODE STORES.  xv6's [balloc] does
   [bp->data[bi/8] |= m] and [bfree] does [&= ~m]; [BitmapEnc]'s two bit
   laws say those are the encoder's byte at the new set, so the writer's
   own stores produce exactly [bm_blk_write]'s argument.  Without this the
   maintenance lemma would be about a byte nobody writes. *)
Lemma bm_new_byte_code (u : gset Z) (bi : Z) (b : bool) :
  0 <= bi ->
  bv_unsigned (bm_byte (bm_wr u bi b) (bi `div` 8))
  = (if b
     then Z.lor (bv_unsigned (bm_byte u (bi `div` 8))) (2 ^ (bi `mod` 8))
     else Z.land (bv_unsigned (bm_byte u (bi `div` 8)))
                 (Z.lnot (2 ^ (bi `mod` 8)))).
Proof.
  intros Hbi. rewrite /bm_wr. destruct b.
  - symmetry. exact (bm_bit_set u bi Hbi).
  - symmetry. exact (bm_bit_clear u bi Hbi).
Qed.

(* THE INVARIANT AT THE BITMAP BLOCK, over the objects' values: every bit
   object below [nb] holds its membership in [u]. *)
Definition bm_vals (V : gmap dobj oval) (u : gset Z) (nb : Z) : Prop :=
  forall b, 0 <= b < nb -> V !! DBit b = Some (OVBit (bool_decide (b ∈ u))).

(* THE PER-WRITE MAINTENANCE OF THE VALUES: only the writer's bit moves. *)
Lemma bm_vals_write (V : gmap dobj oval) (u : gset Z) (nb bi : Z) (b : bool) :
  bm_vals V u nb -> 0 <= bi < nb ->
  bm_vals (<[DBit bi := OVBit b]> V) (bm_wr u bi b) nb.
Proof.
  intros HV Hbi x Hx.
  destruct (decide (x = bi)) as [-> | Hne].
  - rewrite lookup_insert. f_equal. f_equal. symmetry.
    destruct b.
    + apply bool_decide_eq_true_2. by apply bm_wr_at.
    + apply bool_decide_eq_false_2. intros Hin.
      apply bm_wr_at in Hin. discriminate.
  - rewrite lookup_insert_ne; [| intros Hbad; injection Hbad as ->; done].
    rewrite (HV x Hx). do 2 f_equal.
    apply bool_decide_iff_eq. symmetry. exact (bm_wr_off u bi b x Hne).
Qed.

(* ------------------------------------------------------------------- *)
(*  THE 3a-def KILLER SCENARIO, AT THE SHARED BITMAP BLOCK              *)
(* ------------------------------------------------------------------- *)

(* Ops A and B are interleaved on ONE bitmap block: A sets bit [i] (a
   [balloc]) and B clears bit [j] (a [bfree]), with [i <> j].  This is
   precisely the pair [FsDurDefer]'s section 1 uses -- and note that there
   the two ops' updates were said NOT to commute ("one op's [bfree] clearing
   a bit and another op's [balloc] setting the same bit do not commute"),
   which is TRUE AT ONE BIT and vacuous at two.  Two different bits are two
   different OBJECTS, and this is the whole content of decision 1.

   Three conclusions, and the third is the one 3a-def could not have:

   - after A's write the block is the encoding of [u ∪ {[i]}], and after
     B's it is the encoding of [(u ∪ {[i]}) ∖ {[j]}];
   - the same in the other order, at [(u ∖ {[j]}) ∪ {[i]}];
   - THE TWO ARE THE SAME SET, hence the same BYTES.  The final logged
     content of the shared block is a function of the two bits' final
     values and of nothing else -- so the pool, which is order-blind, is
     measured against a target that is order-free. *)
Theorem bm_two_ops_order_free (u : gset Z) (i j : Z) :
  i <> j ->
  0 <= i < 8 * Z.of_nat BSIZE ->
  0 <= j < 8 * Z.of_nat BSIZE ->
  (* order 1: A sets [i], then B clears [j] *)
  bm_blk_write (bm_bytes BSIZE u) (bm_wr u i true) i
    = bm_bytes BSIZE (bm_wr u i true)
  /\ bm_blk_write (bm_bytes BSIZE (bm_wr u i true))
       (bm_wr (bm_wr u i true) j false) j
     = bm_bytes BSIZE (bm_wr (bm_wr u i true) j false)
  (* order 2: B clears [j], then A sets [i] *)
  /\ bm_blk_write (bm_bytes BSIZE u) (bm_wr u j false) j
     = bm_bytes BSIZE (bm_wr u j false)
  /\ bm_blk_write (bm_bytes BSIZE (bm_wr u j false))
       (bm_wr (bm_wr u j false) i true) i
     = bm_bytes BSIZE (bm_wr (bm_wr u j false) i true)
  (* THE TARGETS AGREE *)
  /\ bm_wr (bm_wr u i true) j false = bm_wr (bm_wr u j false) i true
  /\ bm_bytes BSIZE (bm_wr (bm_wr u i true) j false)
     = bm_bytes BSIZE (bm_wr (bm_wr u j false) i true).
Proof.
  intros Hij Hi Hj.
  assert (Hset : bm_wr (bm_wr u i true) j false
                 = bm_wr (bm_wr u j false) i true).
  { rewrite /bm_wr. set_solver. }
  split; [exact (bm_blk_write_enc u i true Hi) |].
  split; [exact (bm_blk_write_enc (bm_wr u i true) j false Hj) |].
  split; [exact (bm_blk_write_enc u j false Hj) |].
  split; [exact (bm_blk_write_enc (bm_wr u j false) i true Hi) |].
  split; [exact Hset |]. by rewrite Hset.
Qed.

(* ...AND THE VALUES AGREE TOO.  The two interleavings leave the same
   assignment of bit values, by [insert_commute] at two distinct objects --
   the object-level twin of [FsDurDefer.dfr_ledger_order_blind], and here
   the order-blindness is sound because of the theorem above. *)
Theorem bm_two_ops_vals_order_free (V : gmap dobj oval) (i j : Z)
    (bi bj : bool) :
  i <> j ->
  <[DBit i := OVBit bi]> (<[DBit j := OVBit bj]> V)
  = <[DBit j := OVBit bj]> (<[DBit i := OVBit bi]> V).
Proof.
  intros Hij. apply insert_commute.
  intros Hbad. injection Hbad as ->. done.
Qed.

(* ------------------------------------------------------------------- *)
(*  3a-def's SCENARIO, END TO END, IN ONE STATEMENT                      *)
(* ------------------------------------------------------------------- *)

(* THE FOUR CONJUNCTS ARE THE WHOLE ANSWER TO 3a-def's WALL, and the first
   of them is 3a-def's OWN lemma, applied unchanged -- so the two files
   agree on what the scenario is and disagree only on what it costs.

   The setting: two OPEN transactions [oi] and [oj] ([LogInv.log_res]
   permits [out <= 3]) both touch the shared bitmap block in one batch.  Op
   [oi] runs a [balloc] that sets bit [p]; op [oj] runs a [bfree] that
   clears bit [q]; [p <> q], which is the case xv6 produces constantly and
   the case [FsDurDefer]'s section 1 refutes at BLOCK granularity.

   (1) THE LEDGER IS ORDER-BLIND -- [FsDurDefer.dfr_ledger_order_blind],
       unchanged.  This is the fact that killed the block-level row.
   (2) THE POOL IS ORDER-BLIND TOO: the two ops deposit at two DIFFERENT
       objects, so the pool is one map under both orders.
   (3) SO IS THE VALUE ASSIGNMENT.
   (4) AND -- THE CONJUNCT 3a-def COULD NOT HAVE -- SO IS THE TARGET.  The
       block's final logged bytes are the same list under both orders,
       because they are a FUNCTION of the two bits' final values.  In
       3a-def the target was [lm_logged L], which moves with the write
       order; here it is the encoder applied to the objects' values, which
       does not.  That is decision 1 of fs-state.md section 4.875, and it
       is the whole difference. *)
Theorem dobj_3adef_scenario_handled
    (* 3a-def's ledger *)
    (oi oj : nat) (di dj : dfr_map) (om : dfr_ledger)
    (* the object pool, the value assignment, and the shared block *)
    (P : gmap dobj (oval * oval)) (V : gmap dobj oval) (u : gset Z)
    (p q : Z) (pp pq : oval * oval) :
  oi <> oj -> p <> q ->
  0 <= p < 8 * Z.of_nat BSIZE -> 0 <= q < 8 * Z.of_nat BSIZE ->
  (* (1) same ledger *)
  <[oi := di]> (<[oj := dj]> om) = <[oj := dj]> (<[oi := di]> om)
  (* (2) same pool *)
  /\ <[DBit p := pp]> (<[DBit q := pq]> P)
     = <[DBit q := pq]> (<[DBit p := pp]> P)
  (* (3) same final values *)
  /\ <[DBit p := OVBit true]> (<[DBit q := OVBit false]> V)
     = <[DBit q := OVBit false]> (<[DBit p := OVBit true]> V)
  (* (4) same final BYTES, under the writers' own read-modify-writes *)
  /\ bm_blk_write (bm_blk_write (bm_bytes BSIZE u) (bm_wr u p true) p)
       (bm_wr (bm_wr u p true) q false) q
     = bm_blk_write (bm_blk_write (bm_bytes BSIZE u) (bm_wr u q false) q)
         (bm_wr (bm_wr u q false) p true) p.
Proof.
  intros Hoij Hpq Hp Hq.
  assert (Hne : DBit p <> DBit q)
    by (intros Hbad; injection Hbad as ->; done).
  split; [exact (dfr_ledger_order_blind oi oj di dj om Hoij) |].
  split; [by apply insert_commute |].
  split; [by apply insert_commute |].
  destruct (bm_two_ops_order_free u p q Hpq Hp Hq)
    as (H1 & H2 & H3 & H4 & _ & H6).
  rewrite H1 H2 H3 H4. exact H6.
Qed.

(* ---- an inode block ----------------------------------------------- *)

(* THE SAME COMMUTATION FOR THE ENCODER'S SLOT UPDATE.  [DinodeEnc]'s
   [diblk_bytes] over a sixteen-record list is the inode block's encoder;
   this is the [blk_splice] reading of a one-slot update.

   MARKED FOR RELOCATION to [DinodeEnc.v]: [InodeRegion.diblk_bytes_splice]
   is the SAME statement, proved there because that is where [FsBlocks] and
   [DinodeEnc] first met.  It is a fact about two encoders and a list
   operation and needs no Iris at all; the two copies should become one, in
   [DinodeEnc.v] (which would then Require [FsBlocks] for [blk_splice], or
   [blk_splice] should move down beside it).  Restated here rather than
   imported because [InodeRegion] carries the whole inode-region invariant
   band ([IcacheRef], [EscrowDefs], ...) and a validation leaf has no
   business on that cone. *)
Lemma diblk_bytes_splice_pure (ds : list dinode) (k : nat) (d : dinode) :
  diblk_wf ds -> dinode_wf d -> (k < 16)%nat ->
  diblk_bytes (<[k := d]> ds)
  = blk_splice (64 * k)%nat (dinode_bytes d) (diblk_bytes ds).
Proof.
  intros Hwf Hd Hk. pose proof Hwf as [Hlen Hall].
  assert (Hlb : length (diblk_bytes ds) = 1024%nat)
    by (rewrite (diblk_bytes_length ds Hall) Hlen; reflexivity).
  assert (Hsub : length (dinode_bytes d) = 64%nat)
    by exact (dinode_bytes_length d Hd).
  apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j (64 * k)%nat) as [Hlt | Hge].
  - rewrite (blk_splice_lookup_lt (64 * k)%nat (dinode_bytes d)
               (diblk_bytes ds) j ltac:(lia) Hlt).
    exact (diblk_bytes_insert_other ds k d j Hall Hd ltac:(lia)
             ltac:(left; lia)).
  - destruct (Nat.lt_ge_cases j (64 * k + 64)%nat) as [Hmid | Hgt].
    + rewrite (blk_splice_lookup_mid (64 * k)%nat (dinode_bytes d)
                 (diblk_bytes ds) j ltac:(lia) Hge ltac:(lia)).
      replace j with (64 * k + (j - 64 * k))%nat at 1 by lia.
      exact (diblk_bytes_insert_same ds k d (j - 64 * k)%nat Hall Hd
               ltac:(lia) ltac:(lia)).
    + rewrite (blk_splice_lookup_ge (64 * k)%nat (dinode_bytes d)
                 (diblk_bytes ds) j ltac:(lia) ltac:(lia)).
      exact (diblk_bytes_insert_other ds k d j Hall Hd ltac:(lia)
               ltac:(right; lia)).
Qed.

(* the writer's read-modify-write fact at an inode block: slot [k]'s 64
   bytes spliced at offset [64k] *)
Definition di_blk_write (bs : list (bv 8)) (k : nat) (d : dinode)
    : list (bv 8) :=
  blk_splice (64 * k)%nat (dinode_bytes d) bs.

Lemma di_blk_write_enc (ds : list dinode) (k : nat) (d : dinode) :
  diblk_wf ds -> dinode_wf d -> (k < 16)%nat ->
  di_blk_write (diblk_bytes ds) k d = diblk_bytes (<[k := d]> ds).
Proof.
  intros Hwf Hd Hk. symmetry. exact (diblk_bytes_splice_pure ds k d Hwf Hd Hk).
Qed.

(* THE SAME-BLOCK TWIN OF THE BITMAP SCENARIO: op A writes slot [k], op B
   writes slot [k'], [k <> k'] (two [ialloc]s, or an [ialloc] beside another
   op's [iupdate] -- [FsDurDefer]'s own list).  Both orders, same final
   bytes. *)
Theorem di_two_slots_order_free (ds : list dinode) (k k' : nat)
    (d d' : dinode) :
  k <> k' -> (k < 16)%nat -> (k' < 16)%nat ->
  diblk_wf ds -> dinode_wf d -> dinode_wf d' ->
  di_blk_write (di_blk_write (diblk_bytes ds) k d) k' d'
    = diblk_bytes (<[k' := d']> (<[k := d]> ds))
  /\ di_blk_write (di_blk_write (diblk_bytes ds) k' d') k d
     = diblk_bytes (<[k := d]> (<[k' := d']> ds))
  /\ <[k' := d']> (<[k := d]> ds) = <[k := d]> (<[k' := d']> ds)
  /\ di_blk_write (di_blk_write (diblk_bytes ds) k d) k' d'
     = di_blk_write (di_blk_write (diblk_bytes ds) k' d') k d.
Proof.
  intros Hne Hk Hk' Hwf Hd Hd'.
  assert (Hcom : <[k' := d']> (<[k := d]> ds) = <[k := d]> (<[k' := d']> ds))
    by (apply list_insert_commute; exact (not_eq_sym Hne)).
  assert (H1 : di_blk_write (diblk_bytes ds) k d
               = diblk_bytes (<[k := d]> ds))
    by exact (di_blk_write_enc ds k d Hwf Hd Hk).
  assert (H2 : di_blk_write (diblk_bytes ds) k' d'
               = diblk_bytes (<[k' := d']> ds))
    by exact (di_blk_write_enc ds k' d' Hwf Hd' Hk').
  assert (HA : di_blk_write (di_blk_write (diblk_bytes ds) k d) k' d'
               = diblk_bytes (<[k' := d']> (<[k := d]> ds))).
  { rewrite H1. apply di_blk_write_enc;
      [exact (diblk_wf_insert ds k d Hwf Hd) | exact Hd' | exact Hk']. }
  assert (HB : di_blk_write (di_blk_write (diblk_bytes ds) k' d') k d
               = diblk_bytes (<[k := d]> (<[k' := d']> ds))).
  { rewrite H2. apply di_blk_write_enc;
      [exact (diblk_wf_insert ds k' d' Hwf Hd') | exact Hd | exact Hk]. }
  split; [exact HA |]. split; [exact HB |]. split; [exact Hcom |].
  rewrite HA HB Hcom. reflexivity.
Qed.

(* THE INVARIANT AT AN INODE BLOCK, over the objects' values.  Slot [k] of
   block [bi] is inum [16*bi + k] ([FsStateInode.rec_owned_at_slot]), so the
   block's sixteen slot objects are named by the region's own numbering. *)
Definition di_vals (V : gmap dobj oval) (bi : Z) (nd : nat -> fs_node)
    : Prop :=
  forall k, (k < 16)%nat ->
    V !! DSlot (16 * bi + Z.of_nat k) = Some (OVNode (nd k)).

Definition di_recs (nd : nat -> fs_node) : list dinode :=
  (fun k => fn_rec (nd k)) <$> seq 0 16.

Definition nd_upd (nd : nat -> fs_node) (k : nat) (n : fs_node)
    : nat -> fs_node :=
  fun j => if Nat.eq_dec j k then n else nd j.

Lemma di_recs_length (nd : nat -> fs_node) : length (di_recs nd) = 16%nat.
Proof. rewrite /di_recs length_fmap length_seq //. Qed.

Lemma di_recs_lookup (nd : nat -> fs_node) (k : nat) :
  (k < 16)%nat -> di_recs nd !! k = Some (fn_rec (nd k)).
Proof.
  intros Hk. rewrite /di_recs list_lookup_fmap lookup_seq_lt //.
Qed.

Lemma di_recs_upd (nd : nat -> fs_node) (k : nat) (n : fs_node) :
  (k < 16)%nat ->
  di_recs (nd_upd nd k n) = <[k := fn_rec n]> (di_recs nd).
Proof.
  intros Hk. apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j 16%nat) as [Hj | Hj].
  - rewrite (di_recs_lookup (nd_upd nd k n) j Hj).
    destruct (Nat.eq_dec j k) as [-> | Hne].
    + rewrite list_lookup_insert; [| rewrite di_recs_length; exact Hk].
      rewrite /nd_upd. destruct (Nat.eq_dec k k); [reflexivity | done].
    + rewrite list_lookup_insert_ne; [| exact (not_eq_sym Hne)].
      rewrite (di_recs_lookup nd j Hj) /nd_upd.
      destruct (Nat.eq_dec j k); [done | reflexivity].
  - rewrite lookup_ge_None_2; [| rewrite di_recs_length; lia].
    rewrite lookup_ge_None_2;
      [reflexivity | rewrite length_insert di_recs_length; lia].
  Qed.

(* ONLY THE WRITER'S OWN SLOT MOVES. *)
Lemma di_vals_write (V : gmap dobj oval) (bi : Z) (nd : nat -> fs_node)
    (k : nat) (n : fs_node) :
  di_vals V bi nd -> (k < 16)%nat ->
  di_vals (<[DSlot (16 * bi + Z.of_nat k) := OVNode n]> V) bi (nd_upd nd k n).
Proof.
  intros HV Hk j Hj.
  destruct (Nat.eq_dec j k) as [-> | Hne].
  - rewrite lookup_insert /nd_upd.
    destruct (Nat.eq_dec k k); [reflexivity | done].
  - rewrite lookup_insert_ne; last first.
    { intros Hbad. injection Hbad as Hz. apply Hne. lia. }
    rewrite (HV j Hj) /nd_upd.
    destruct (Nat.eq_dec j k); [done | reflexivity].
Qed.

(* the inode block's bytes ARE its sixteen slot objects' values encoded *)
Lemma di_vals_enc (nd : nat -> fs_node) (k : nat) (n : fs_node) :
  (forall j, dinode_wf (fn_rec (nd j))) -> dinode_wf (fn_rec n) ->
  (k < 16)%nat ->
  di_blk_write (diblk_bytes (di_recs nd)) k (fn_rec n)
  = diblk_bytes (di_recs (nd_upd nd k n)).
Proof.
  intros Hall Hn Hk.
  assert (Hwf : diblk_wf (di_recs nd)).
  { split; [exact (di_recs_length nd) |].
    apply Forall_lookup_2. intros j x Hx.
    destruct (Nat.lt_ge_cases j 16%nat) as [Hj | Hj].
    - rewrite (di_recs_lookup nd j Hj) in Hx. injection Hx as <-.
      exact (Hall j).
    - rewrite lookup_ge_None_2 in Hx;
        [discriminate | rewrite di_recs_length; lia]. }
  rewrite (di_blk_write_enc (di_recs nd) k (fn_rec n) Hwf Hn Hk).
  rewrite (di_recs_upd nd k n Hk) //.
Qed.

(* ---- the block-kind encoder, gathered ------------------------------ *)

(* decision 4's "each home block's logged bytes encode its objects' current
   logged values", as a function.  Three kinds, and the three per-write
   maintenance laws above are its three cases. *)
Inductive blk_kind :=
| KBitmap (u : gset Z)
| KInode (nd : nat -> fs_node)
| KData (bs : list (bv 8)).

Definition kind_enc (k : blk_kind) : list (bv 8) :=
  match k with
  | KBitmap u => bm_bytes BSIZE u
  | KInode nd => diblk_bytes (di_recs nd)
  | KData bs => bs
  end.

Lemma kind_enc_bitmap_write (u : gset Z) (bi : Z) (b : bool) :
  0 <= bi < 8 * Z.of_nat BSIZE ->
  bm_blk_write (kind_enc (KBitmap u)) (bm_wr u bi b) bi
  = kind_enc (KBitmap (bm_wr u bi b)).
Proof. intros H. exact (bm_blk_write_enc u bi b H). Qed.

Lemma kind_enc_inode_write (nd : nat -> fs_node) (k : nat) (n : fs_node) :
  (forall j, dinode_wf (fn_rec (nd j))) -> dinode_wf (fn_rec n) ->
  (k < 16)%nat ->
  di_blk_write (kind_enc (KInode nd)) k (fn_rec n)
  = kind_enc (KInode (nd_upd nd k n)).
Proof. intros H1 H2 H3. exact (di_vals_enc nd k n H1 H2 H3). Qed.

(* ===================================================================== *)
(*  4.  THE CLOSE                                                         *)
(* ===================================================================== *)

(* THE BYTE-LEVEL CONCLUSION.  At quiescence the pool has run ((1d)) and the
   durable block map [D'] holds, at every home block, that block's objects'
   FINAL values encoded ([K b] is the block's kind assignment, and section 3
   is what maintains it per write).  The logged view holds the same encoding
   at the same blocks, by the invariant.  Hence the two maps are equal --
   which is [FsDurDefer.commit_conclusion]'s equation at HOME MAPS, with no
   [fs_restrict] arithmetic anywhere outside [lm_logged]'s own definition.

   Nothing here quantifies over an op: the encode invariant is per BLOCK and
   the equation is between two maps. *)
Theorem dobj_close (K : Z -> blk_kind) (D' L : gmap Z (list (bv 8)))
    (cov : gset Z) (ls : Z) :
  dom D' = fs_home_set cov ls ->
  (forall b, b ∈ fs_home_set cov ls -> D' !! b = Some (kind_enc (K b))) ->
  (forall b, b ∈ fs_home_set cov ls -> L !! b = Some (kind_enc (K b))) ->
  D' = lm_logged L cov ls.
Proof.
  intros Hdom HD HL. apply map_eq. intros b.
  rewrite /lm_logged fs_restrict_lookup.
  destruct (decide (b ∈ fs_home_set cov ls)) as [Hb | Hb].
  - rewrite (HD b Hb) (HL b Hb) //.
  - apply not_elem_of_dom. rewrite Hdom. exact Hb.
Qed.

Section Close.
  Context {Σ : gFunctors}.
  Context `{!diskImgG Σ, !fsLinkG Σ, !fsTopG Σ}.

  (* THE CLOSE, IN [FsDurDefer.dstep_strict]'S SHAPE.  The commit permit
     runs one basic update from the durable byte view at the batch's start
     to the durable byte view at the batch's logged values; [dobj_close] is
     what says the second index IS [lm_logged L cov ls].  So a client that
     has (i) the pool's run at quiescence, as a step from [D0] to [D'], and
     (ii) the encode invariant on both sides, owes exactly
     [FsDurDefer.commit_conclusion]. *)
  Theorem dobj_close_dstep (g : gname) (Γd : fs_dur_names)
      (K : Z -> blk_kind) (D0 D' L : gmap Z (list (bv 8)))
      (cov : gset Z) (ls : Z) :
    dom D' = fs_home_set cov ls ->
    (forall b, b ∈ fs_home_set cov ls -> D' !! b = Some (kind_enc (K b))) ->
    (forall b, b ∈ fs_home_set cov ls -> L !! b = Some (kind_enc (K b))) ->
    dstep_strict g Γd D0 D' -∗ commit_conclusion g Γd D0 L cov ls.
  Proof.
    intros Hdom HD HL.
    rewrite /commit_conclusion -(dobj_close K D' L cov ls Hdom HD HL).
    iIntros "$".
  Qed.

End Close.

(* ===================================================================== *)
(*  5.  THE ERA-SIDE WITNESS (the implementation lane's interface)        *)
(* ===================================================================== *)

(* SAME-OBJECT RECOMPOSITION NEEDS THE SECOND WRITER TO KNOW [x'].
   [dpool_recompose] takes [P !! o = Some (x, x')] as a Coq hypothesis; a
   client proof may not have it, because the pool is not the client's.  What
   the client DOES have is that it READ object [o] at [x'] through the era
   protocol -- the buffer lock for a whole block, the inode region's
   invariant for a slot, the bitmap invariant for a bit -- and the ruling's
   decision 1 says that serialization is where same-object order comes from.

   THIS IS WHAT THE ERA SIDE MUST HAND OVER, and it is one resource:

     A HALF OF A PER-OBJECT [ghost_var] AT THE OBJECT'S CURRENT PENDING
     VALUE.  The pool's entry for [o] carries one half; the era side hands
     the observer the other half at the value it observed.  Agreement pins
     [x'], and the deposit flips both halves to the new value in the same
     step.

   The gname is a PARAMETER of the era-side interface -- one per object,
   [γobs : dobj -> gname] at the implementation -- and NOT a new
   configuration class: it is exactly the standing rule for a ghost var in
   this tree.  [ghost_varG Σ oval] is the only class binding, and it is a
   section hypothesis here rather than a member of any bundle.

   WHAT THE ERA SIDE OWES, precisely, in three parts:

   (i)   at the object's first touch in a batch, MINT the pair at the
         object's committed value (this is the deposit of a fresh entry,
         [dpool_deposit]; the minting is [ghost_var_alloc]);
   (ii)  every era-side write of [o] that a transaction will later deposit
         must hand the writer a half at the value it INSTALLED -- so the
         half travels with whatever already serializes writes to [o] (the
         buffer lock / the region invariant / the bitmap invariant), and no
         new serialization is introduced;
   (iii) at [end_op], the depositor presents its half and its move; the
         pool's half agrees with it, both flip, and the entry recomposes.

   [dpool_recompose_era] below is (iii) as a term.  Note the shape of its
   statement: the depositor supplies [obs] AT ITS OWN OBSERVED VALUE and a
   [dpend] from that value; the [y = x'] the composition needs is a
   CONCLUSION, read off agreement, not a hypothesis.  The Coq premise
   [P !! o = Some (x, x')] is the POOL HOLDER's -- the payload knows its own
   ledger by construction -- and [dpool_recompose_era_blind] is the
   DEPOSITOR's form of the same theorem, in which the entry's start value
   and the earlier writer's target are both existential: the client knows
   only that the object is in the pool, which it knows because it is
   holding the object's receipt. *)

Section EraWitness.
  Context {Σ : gFunctors}.
  Context `{!fsLinkG Σ, !fsTopG Σ}.
  Context `{!ghost_varG Σ oval}.

  (* the receipt: "object [o]'s pending target is [x]" *)
  Definition obs (γ : gname) (x : oval) : iProp Σ :=
    ghost_var γ (1/2) x.

  Lemma obs_agree γ x y : obs γ x -∗ obs γ y -∗ ⌜x = y⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %->. done.
  Qed.

  Lemma obs_update γ x y : obs γ x -∗ obs γ x ==∗ obs γ y ∗ obs γ y.
  Proof.
    iIntros "H1 H2".
    iMod (ghost_var_update_halves y with "H1 H2") as "[$ $]". done.
  Qed.

  (* THE POOL, TIED.  Each entry carries the ledger-side half of its
     object's receipt, at the entry's own target value.  [γobs] is the
     per-object gname the implementation lane threads. *)
  Definition dpool_tied R (γobs : dobj -> gname)
      (P : gmap dobj (oval * oval)) : iProp Σ :=
    (dpool R P ∗ [∗ map] o ↦ p ∈ P, obs (γobs o) p.2)%I.

  (* (iii): RECOMPOSITION WITH THE WITNESS.  Read the premises: the
     depositor brings [obs (γobs o) y] (what the era protocol told it) and
     [dpend Γ G o (y, y')] (its own move).  It brings NOTHING about the
     pool.  The [⌜y = x'⌝] in the conclusion is the fact the era side is
     being asked to guarantee, and it is what makes the composition
     type-check at all. *)
  Theorem dpool_recompose_era R (γobs : dobj -> gname)
      (P : gmap dobj (oval * oval)) (o : dobj) (x x' y y' : oval) :
    P !! o = Some (x, x') ->
    dpool_tied R γobs P -∗
    obs (γobs o) y -∗
    dpend R o (y, y') ==∗
      ⌜y = x'⌝ ∗ dpool_tied R γobs (<[o := (x, y')]> P).
  Proof.
    intros Ho. iIntros "[HP Hobs] Hy Hpend".
    iDestruct (big_sepM_delete _ P o (x, x') Ho with "Hobs")
      as "[Hoo Hobs]".
    cbn [fst snd].
    iDestruct (obs_agree (γobs o) x' y with "Hoo Hy") as %<-.
    iMod (obs_update (γobs o) x' y' with "Hoo Hy") as "[Hoo Hy]".
    iDestruct (dpool_recompose R P o x x' y' Ho with "HP Hpend") as "HP".
    iModIntro. iSplitR; [done |]. iFrame "HP".
    rewrite -(insert_delete_insert P o (x, y')).
    rewrite (big_sepM_insert (fun o p => obs (γobs o) p.2) (delete o P) o
               (x, y') (lookup_delete P o)).
    cbn [fst snd]. iFrame.
  Qed.

  (* THE DEPOSITOR'S FORM.  Everything the earlier writer left is
     EXISTENTIAL here: the client knows only that the object is in the pool
     -- which it knows because it is holding the object's receipt -- and it
     names neither the entry's start value nor the earlier writer's target.
     THIS is the statement that says the era-side witness is sufficient. *)
  Corollary dpool_recompose_era_blind R (γobs : dobj -> gname)
      (P : gmap dobj (oval * oval)) (o : dobj) (y y' : oval) :
    is_Some (P !! o) ->
    dpool_tied R γobs P -∗
    obs (γobs o) y -∗
    dpend R o (y, y') ==∗
      ∃ x, ⌜P !! o = Some (x, y)⌝
           ∗ dpool_tied R γobs (<[o := (x, y')]> P).
  Proof.
    intros [[x x'] Ho]. iIntros "HP Hy Hpend".
    iMod (dpool_recompose_era R γobs P o x x' y y' Ho with "HP Hy Hpend")
      as "[%Heq HP]".
    iModIntro. iExists x. iSplitR; [by rewrite Ho Heq |]. iExact "HP".
  Qed.

  (* ...AND (i): a FRESH object's tied entry is the [∗]-extension plus the
     mint.  Again no hypothesis about the pool's other entries. *)
  Lemma dpool_deposit_era R (γobs : dobj -> gname)
      (P : gmap dobj (oval * oval)) (o : dobj) (p : oval * oval) :
    P !! o = None ->
    dpool_tied R γobs P -∗ dpend R o p -∗ obs (γobs o) p.2 -∗
      dpool_tied R γobs (<[o := p]> P).
  Proof.
    intros Ho. iIntros "[HP Hobs] Hpend Hy".
    iDestruct (dpool_deposit R P o p Ho with "HP Hpend") as "HP".
    rewrite /dpool_tied. iFrame "HP".
    rewrite (big_sepM_insert (fun o p => obs (γobs o) p.2) P o p Ho).
    iFrame.
  Qed.

End EraWitness.

(* ===================================================================== *)
(*  6.  NON-VACUITY: the load-bearing theorems at CONCRETE WITNESSES      *)
(* ===================================================================== *)

(* durable-notes.md, "INCONSISTENT PREMISES ARE THE WORST DEFECT, AND
   NOTHING IN THE BUILD SEES THEM".  Every theorem above whose premises are
   arithmetic or well-formedness is discharged here at a witness that
   exists, so a later reader can see that none of them is vacuous. *)

(* the smallest well-formed record and the smallest well-formed inode block *)
Definition dobj_wit_dinode : dinode :=
  MkDinode (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 32)
           (replicate 13 (bv_0 32)).

Definition dobj_wit_dinode' : dinode :=
  MkDinode (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 32)
           (replicate 13 (bv_0 32)).

Lemma dobj_wit_dinode_wf : dinode_wf dobj_wit_dinode.
Proof.
  rewrite /dinode_wf /dobj_wit_dinode. cbn [di_addrs].
  apply length_replicate.
Qed.

Lemma dobj_wit_diblk_wf : diblk_wf (replicate 16 dobj_wit_dinode).
Proof.
  split; [apply length_replicate |].
  apply Forall_forall. intros d Hd.
  apply elem_of_replicate in Hd as [-> _]. exact dobj_wit_dinode_wf.
Qed.

(* (2)'s bitmap scenario really instantiates -- AND AT THE HARDEST PAIR:
   bits 0 and 1 live in the SAME BYTE of the bitmap block, so the two
   objects the two open transactions touch are not merely in one block but
   in one byte, and the encoder is still order-free. *)
Theorem dobj_wit_bm_same_byte (u : gset Z) :
  bm_blk_write (bm_blk_write (bm_bytes BSIZE u) (bm_wr u 0 true) 0)
    (bm_wr (bm_wr u 0 true) 1 false) 1
  = bm_blk_write (bm_blk_write (bm_bytes BSIZE u) (bm_wr u 1 false) 1)
      (bm_wr (bm_wr u 1 false) 0 true) 0.
Proof.
  assert (Hb : 8 * Z.of_nat BSIZE = 8192) by (vm_compute; reflexivity).
  destruct (bm_two_ops_order_free u 0 1 ltac:(lia) ltac:(lia) ltac:(lia))
    as (H1 & H2 & H3 & H4 & _ & H6).
  rewrite H1 H2 H3 H4. exact H6.
Qed.

(* ...and so does the inode-block twin, at slots 0 and 1 of a real block *)
Theorem dobj_wit_di_two_slots :
  di_blk_write (di_blk_write (diblk_bytes (replicate 16 dobj_wit_dinode))
                  0 dobj_wit_dinode) 1 dobj_wit_dinode'
  = di_blk_write (di_blk_write (diblk_bytes (replicate 16 dobj_wit_dinode))
                    1 dobj_wit_dinode') 0 dobj_wit_dinode.
Proof.
  destruct (di_two_slots_order_free (replicate 16 dobj_wit_dinode) 0 1
              dobj_wit_dinode dobj_wit_dinode' ltac:(lia) ltac:(lia)
              ltac:(lia) dobj_wit_diblk_wf dobj_wit_dinode_wf
              dobj_wit_dinode_wf) as (_ & _ & _ & H4).
  exact H4.
Qed.

(* (3)'s close really instantiates: the durable map that IS every home
   block's objects encoded satisfies all three premises, so the theorem has
   a model and its conclusion is an equation between two maps that exist. *)
Theorem dobj_wit_close (K : Z -> blk_kind) (cov : gset Z) (ls : Z) :
  fs_restrict (fun b => kind_enc (K b)) (fs_home_set cov ls)
  = lm_logged (fs_restrict (fun b => kind_enc (K b)) (fs_home_set cov ls))
      cov ls.
Proof.
  apply (dobj_close K); [apply fs_restrict_dom | |];
    intros b Hb; apply fs_restrict_lookup_Some; done.
Qed.

(* Every definition in this file whose body is a big-op over an object map
   must be sealed the day it is written, or [iFrame] resolves its [Frame]
   instances up to delta and does not come back (durable-notes.md, "a big-op
   behind a [Definition] is a hang"). *)
Global Typeclasses Opaque
  dres dres_flat dpend dpool dres_map dpool_tied obs.
