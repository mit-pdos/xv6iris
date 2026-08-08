(* ProofItruncParts.v -- itrunc's vocabulary: everything its proof needs that
   is NOT a step of its instruction chain, so ProofItrunc.v stays about
   control flow.  (The ProofBmapParts.v / ProofBreadParts.v division of
   labour.)

   itrunc has TWO loops and they are not the same shape, which is most of
   what is in this file.

   (1) THE DIRECT LOOP walks [ip->addrs[0 .. NDIRECT)] and CLEARS each cell
       it frees ([sw zero,0(s1)] at +0x2c).  So its state is a map whose
       direct entries below the cursor are zero and whose entries at and
       above it are untouched: [bm_dir_zeroed] below.  It is stated as
       [replicate k 0 ++ drop k (bm_dir bm)] rather than as an iterated
       [<[i := 0]>] because the two ends -- "at 0 this is [bm]" and "at
       NDIRECT this is [bm_empty]'s direct part" -- are then both
       definitional, and the step is one [insert_take_drop] rewrite.

   (2) THE INDIRECT LOOP walks the 256 entries INSIDE the block
       ([a[j]] at [bp->data + 4j]) and does NOT clear them: the C frees each
       entry and then frees the whole indirect block, so the entry list is
       never written back.  Its state is therefore not a changing map at all
       -- [bm_ent bm] is fixed throughout -- only the free pool and the
       [inode_blocks] bundle move.  That asymmetry is why the two loops get
       different invariants rather than one parameterised one.

   THE FREED SET.  Both loops accumulate blocks into the pool, and the
   postcondition names the total as [InodeInv.bm_blocks bm].  The two
   partial sums here ([bm_dir_freed], [bm_ent_freed]) are what the loop
   invariants carry, and [bm_blocks_split] is the arithmetic that puts them
   back together with the indirect block itself at the end.

   THE POINTER WALKS.  Neither loop indexes; both bump a pointer by 4
   ([addi s1,s1,4]) and compare against a precomputed limit ([s2]).  The
   cursor lemmas relate "s1 after k bumps" to the addressing [InodeInv]
   already has ([i_addr]) and to the buffer window ByteBuf carries. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import InstrBytes.
Require Import RegFile.
Require Import KernelText.
Require Import BlockWords.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import ProofBmapParts.
From Kernel Require KernelSyms.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  (1) THE DIRECT LOOP'S MAP                                            *)
(* ===================================================================== *)

Definition bm_dir_zeroed (bm : blkmap) (k : nat) : blkmap :=
  MkBlkmap (replicate k (bv_0 32) ++ drop k (bm_dir bm))
           (bm_ind bm) (bm_ent bm).

Lemma bm_dir_zeroed_0 (bm : blkmap) : bm_dir_zeroed bm 0 = bm.
Proof. rewrite /bm_dir_zeroed. cbn [bm_dir bm_ind bm_ent]. destruct bm; reflexivity. Qed.

Lemma bm_dir_zeroed_len (bm : blkmap) (k : nat) :
  (k <= length (bm_dir bm))%nat ->
  length (bm_dir (bm_dir_zeroed bm k)) = length (bm_dir bm).
Proof.
  intros Hk. rewrite /bm_dir_zeroed. cbn [bm_dir bm_ind bm_ent].
  rewrite length_app length_replicate length_drop. lia.
Qed.

(* at the top of the loop the direct part is all zeros -- and with the
   [blkmap_wf] length that IS [bm_empty]'s *)
Lemma bm_dir_zeroed_full (bm : blkmap) :
  length (bm_dir bm) = NDIRECT ->
  bm_dir (bm_dir_zeroed bm NDIRECT) = replicate NDIRECT (bv_0 32).
Proof.
  intros Hlen. rewrite /bm_dir_zeroed. cbn [bm_dir bm_ind bm_ent].
  rewrite (drop_ge (bm_dir bm) NDIRECT); [|lia].
  apply app_nil_r.
Qed.

(* reading the cursor cell: at index k the loop still sees the ORIGINAL
   entry, which is what it is about to test and free *)
Lemma bm_dir_zeroed_at (bm : blkmap) (k : nat) :
  (k < length (bm_dir bm))%nat ->
  bm_dir (bm_dir_zeroed bm k) !!! k = bm_dir bm !!! k.
Proof.
  intros Hk. rewrite /bm_dir_zeroed. cbn [bm_dir bm_ind bm_ent].
  apply list_lookup_total_correct.
  rewrite lookup_app_r; [| rewrite length_replicate; lia].
  rewrite length_replicate Nat.sub_diag lookup_drop Nat.add_0_r.
  apply list_lookup_lookup_total_lt. lia.
Qed.

(* ...and below it, zero *)
Lemma bm_dir_zeroed_below (bm : blkmap) (k i : nat) :
  (i < k)%nat -> (k <= length (bm_dir bm))%nat ->
  bm_dir (bm_dir_zeroed bm k) !!! i = bv_0 32.
Proof.
  intros Hi Hk. rewrite /bm_dir_zeroed. cbn [bm_dir bm_ind bm_ent].
  apply list_lookup_total_correct.
  rewrite lookup_app_l; [| rewrite length_replicate; lia].
  apply lookup_replicate_2. lia.
Qed.

(* THE STEP: clearing the cursor cell advances the state by one *)
Lemma bm_dir_zeroed_step (bm : blkmap) (k : nat) :
  (k < length (bm_dir bm))%nat ->
  <[k := bv_0 32]> (bm_dir (bm_dir_zeroed bm k))
  = bm_dir (bm_dir_zeroed bm (S k)).
Proof.
  intros Hk. rewrite /bm_dir_zeroed. cbn [bm_dir bm_ind bm_ent].
  rewrite insert_app_r_alt; [| rewrite length_replicate; lia].
  rewrite length_replicate Nat.sub_diag.
  rewrite (drop_S (bm_dir bm) (bm_dir bm !!! k) k);
    [|apply list_lookup_lookup_total_lt; lia].
  rewrite replicate_S_end -app_assoc. cbn [insert app]. reflexivity.
Qed.

(* the slot readings the well-formedness proof needs *)
Lemma bm_dir_zeroed_slot (bm : blkmap) (k i : nat) :
  length (bm_dir bm) = NDIRECT -> (k <= NDIRECT)%nat -> (i <= MAXFILE)%nat ->
  bm_slot (bm_dir_zeroed bm k) i
  = if decide ((i < k)%nat) then bv_0 32 else bm_slot bm i.
Proof.
  intros Hlen Hk Hi.
  rewrite /bm_slot /blkmap_get /bm_dir_zeroed. cbn [bm_dir bm_ind bm_ent].
  destruct (decide (i = MAXFILE)) as [->|Hne].
  { destruct (decide (MAXFILE < k)%nat); [unfold MAXFILE, NDIRECT, NINDIRECT in *; lia|].
    reflexivity. }
  destruct (decide (i < NDIRECT)%nat) as [Hlt|Hge].
  - destruct (decide (i < k)%nat) as [Hik|Hik].
    + apply bm_dir_zeroed_below; [exact Hik | lia].
    + apply list_lookup_total_correct.
      rewrite lookup_app_r; [| rewrite length_replicate; lia].
      rewrite length_replicate lookup_drop.
      replace (k + (i - k))%nat with i by lia.
      apply list_lookup_lookup_total_lt. lia.
  - destruct (decide (i < k)%nat); [lia|]. reflexivity.
Qed.

(* WELL-FORMEDNESS SURVIVES: zeroing entries only ever REMOVES nonzero
   slots, and both of [blkmap_wf]'s interesting clauses are guarded by
   "this slot is nonzero". *)
Lemma bm_dir_zeroed_wf (cov : gset Z) (ls : Z) (bm : blkmap) (k : nat) :
  blkmap_wf cov ls bm -> (k <= NDIRECT)%nat ->
  blkmap_wf cov ls (bm_dir_zeroed bm k).
Proof.
  intros Hwf Hk.
  pose proof (blkmap_wf_dir_len _ _ _ Hwf) as Hdl.
  destruct Hwf as (Hd & He & Hni & Hcv & Hinj).
  assert (Hslot : forall i : nat, (i <= MAXFILE)%nat ->
            bm_slot (bm_dir_zeroed bm k) i
            = if decide ((i < k)%nat) then bv_0 32 else bm_slot bm i)
    by (intros i Hi; apply bm_dir_zeroed_slot; auto).
  rewrite /blkmap_wf. cbn [bm_dir bm_ind bm_ent bm_dir_zeroed].
  split; [rewrite length_app length_replicate length_drop; lia|].
  split; [exact He|].
  split; [exact Hni|].
  split.
  - intros i Hi Hnz. rewrite (Hslot i Hi) in Hnz |- *.
    destruct (decide (i < k)%nat); [exfalso; by apply Hnz|].
    exact (Hcv i Hi Hnz).
  - intros i j Hi Hj Hnz Heq.
    rewrite (Hslot i Hi) in Hnz Heq. rewrite (Hslot j Hj) in Heq.
    destruct (decide (i < k)%nat); [exfalso; by apply Hnz|].
    destruct (decide (j < k)%nat).
    + exfalso. apply Hnz. rewrite Heq. reflexivity.
    + exact (Hinj i j Hi Hj Hnz Heq).
Qed.

(* ===================================================================== *)
(*  THE FREED SETS                                                       *)
(* ===================================================================== *)

(* what the direct loop has returned to the pool after k iterations *)
Definition bm_dir_freed (bm : blkmap) (k : nat) : gset Z :=
  list_to_set (map (fun i => bv_unsigned (bm_dir bm !!! i)) (seq 0 k)) ∖ {[ 0 ]}.

(* what the indirect loop has returned after j iterations *)
Definition bm_ent_freed (bm : blkmap) (j : nat) : gset Z :=
  list_to_set (map (fun q => bv_unsigned (bm_ent bm !!! q)) (seq 0 j)) ∖ {[ 0 ]}.

Lemma bm_dir_freed_0 (bm : blkmap) : bm_dir_freed bm 0 = ∅.
Proof. rewrite /bm_dir_freed /=. set_solver. Qed.

Lemma bm_ent_freed_0 (bm : blkmap) : bm_ent_freed bm 0 = ∅.
Proof. rewrite /bm_ent_freed /=. set_solver. Qed.

Lemma bm_dir_freed_step (bm : blkmap) (k : nat) :
  bm_dir_freed bm (S k)
  = bm_dir_freed bm k ∪ ({[ bv_unsigned (bm_dir bm !!! k) ]} ∖ {[ 0 ]}).
Proof.
  rewrite /bm_dir_freed seq_S map_app list_to_set_app_L /=. set_solver.
Qed.

Lemma bm_ent_freed_step (bm : blkmap) (j : nat) :
  bm_ent_freed bm (S j)
  = bm_ent_freed bm j ∪ ({[ bv_unsigned (bm_ent bm !!! j) ]} ∖ {[ 0 ]}).
Proof.
  rewrite /bm_ent_freed seq_S map_app list_to_set_app_L /=. set_solver.
Qed.

(* THE TOTAL.  [bm_blocks] runs over [bm_slot] on [seq 0 (S MAXFILE)]; the
   two partial sums run over the direct list and the entry list.  This is
   the bridge -- the direct entries are slots [0, NDIRECT), the entries are
   slots [NDIRECT, MAXFILE), and slot MAXFILE is the indirect block. *)
(* the two membership characterisations, so the split below is set
   reasoning rather than a rewrite chain through [list_to_set] *)
Lemma bm_dir_freed_spec (bm : blkmap) (k : nat) (b : Z) :
  b ∈ bm_dir_freed bm k <->
  (b <> 0 /\ exists i : nat, (i < k)%nat /\ bv_unsigned (bm_dir bm !!! i) = b).
Proof.
  rewrite /bm_dir_freed elem_of_difference elem_of_singleton
          elem_of_list_to_set.
  split.
  - intros [Hin Hnz]. split; [exact Hnz|].
    apply elem_of_list_fmap in Hin as (i & -> & Hi).
    apply elem_of_seq in Hi. exists i. split; [lia | reflexivity].
  - intros (Hnz & i & Hi & <-). split; [|exact Hnz].
    apply elem_of_list_fmap. exists i.
    split; [reflexivity | apply elem_of_seq; lia].
Qed.

Lemma bm_ent_freed_spec (bm : blkmap) (j : nat) (b : Z) :
  b ∈ bm_ent_freed bm j <->
  (b <> 0 /\ exists q : nat, (q < j)%nat /\ bv_unsigned (bm_ent bm !!! q) = b).
Proof.
  rewrite /bm_ent_freed elem_of_difference elem_of_singleton
          elem_of_list_to_set.
  split.
  - intros [Hin Hnz]. split; [exact Hnz|].
    apply elem_of_list_fmap in Hin as (q & -> & Hq).
    apply elem_of_seq in Hq. exists q. split; [lia | reflexivity].
  - intros (Hnz & q & Hq & <-). split; [|exact Hnz].
    apply elem_of_list_fmap. exists q.
    split; [reflexivity | apply elem_of_seq; lia].
Qed.

(* THE TOTAL.  [bm_blocks] runs over [bm_slot] on [seq 0 (S MAXFILE)]; the
   two partial sums run over the direct list and the entry list.  This is
   the bridge -- the direct entries are slots [0, NDIRECT), the entries are
   slots [NDIRECT, MAXFILE), and slot MAXFILE is the indirect block. *)
Lemma bm_blocks_split (bm : blkmap) :
  length (bm_dir bm) = NDIRECT -> length (bm_ent bm) = NINDIRECT ->
  bm_blocks bm
  = bm_dir_freed bm NDIRECT ∪ bm_ent_freed bm NINDIRECT
    ∪ ({[ bv_unsigned (bm_ind bm) ]} ∖ {[ 0 ]}).
Proof.
  intros Hd He.
  (* the slot readings, once, so both directions are index arithmetic *)
  assert (Hlo : forall i : nat, (i < NDIRECT)%nat ->
            bm_slot bm i = bm_dir bm !!! i).
  { intros i Hi. rewrite (bm_slot_lt bm i ltac:(unfold MAXFILE, NDIRECT, NINDIRECT in *; lia)).
    rewrite /blkmap_get. destruct (decide (i < NDIRECT)%nat); [reflexivity|lia]. }
  assert (Hhi : forall q : nat, (q < NINDIRECT)%nat ->
            bm_slot bm (NDIRECT + q)%nat = bm_ent bm !!! q).
  { intros q Hq.
    rewrite (bm_slot_lt bm (NDIRECT + q)%nat
               ltac:(unfold MAXFILE, NDIRECT, NINDIRECT in *; lia)).
    rewrite /blkmap_get.
    destruct (decide ((NDIRECT + q) < NDIRECT)%nat); [lia|].
    f_equal. lia. }
  apply set_eq. intros b.
  rewrite !elem_of_union bm_dir_freed_spec bm_ent_freed_spec
          elem_of_difference !elem_of_singleton.
  split.
  - intros Hb. apply bm_blocks_spec in Hb as (Hnz & i & Hi & Heq).
    destruct (decide (i = MAXFILE)) as [->|Hne].
    { right. rewrite bm_slot_top in Heq.
      split; [symmetry; exact Heq | exact Hnz]. }
    destruct (decide (i < NDIRECT)%nat) as [Hlt|Hge].
    + left; left. split; [exact Hnz|]. exists i.
      split; [exact Hlt|]. rewrite -Heq (Hlo i Hlt). reflexivity.
    + left; right. split; [exact Hnz|]. exists (i - NDIRECT)%nat.
      split; [unfold MAXFILE, NDIRECT, NINDIRECT in *; lia|].
      rewrite -Heq
              -(Hhi (i - NDIRECT)%nat
                  ltac:(unfold MAXFILE, NDIRECT, NINDIRECT in *; lia)).
      do 2 f_equal. lia.
  - intros [[(Hnz & i & Hi & Heq)|(Hnz & q & Hq & Heq)]|[Heq Hnz]];
      apply bm_blocks_spec.
    + split; [exact Hnz|]. exists i.
      split; [unfold MAXFILE, NDIRECT, NINDIRECT in *; lia|].
      rewrite (Hlo i Hi). exact Heq.
    + split; [exact Hnz|]. exists (NDIRECT + q)%nat.
      split; [unfold MAXFILE, NDIRECT, NINDIRECT in *; lia|].
      rewrite (Hhi q Hq). exact Heq.
    + split; [exact Hnz|]. exists MAXFILE.
      split; [lia|]. rewrite bm_slot_top. symmetry. exact Heq.
Qed.

(* ===================================================================== *)
(*  (2) THE INDIRECT LOOP'S ENTRIES                                       *)
(* ===================================================================== *)

(* The entry list does not move, so all the indirect loop needs from the
   model is that entry [q] really is the word at byte offset [4q] of the
   block's content.  That is already [ProofBmapParts.bm_ent_read], which
   bmap's indirect arm proved for exactly the same reason -- reading a[q]
   out of the buffer -- so it is imported rather than restated.  The two
   functions differ in how they ADDRESS the word (bmap scales an index,
   itrunc bumps a pointer), not in what the word is. *)

(* ===================================================================== *)
(*  THE POINTER WALKS                                                    *)
(* ===================================================================== *)

(* the direct cursor: s1 starts at ip+80 = [i_addr ip 0] and bumps by 4 *)
Lemma it_dir_cursor (ip : mword 64) (k : nat) :
  pa_add (i_addr ip k) 4%nat = i_addr ip (S k).
Proof.
  rewrite (i_addr_from_0 ip k) (i_addr_from_0 ip (S k)) pa_add_add.
  f_equal. lia.
Qed.

(* the limit s2 = ip+128 is the cell one past the twelfth, i.e. [i_addr ip
   NDIRECT] -- which is also [ip->addrs[NDIRECT]], the indirect cell the
   code reads next.  That coincidence is the loop's exit test. *)
Lemma it_dir_limit (ip : mword 64) :
  i_addr ip NDIRECT = pa_add ip 128%nat.
Proof.
  rewrite /i_addr /pa_add /add_vec_int /NDIRECT. f_equal.
Qed.
