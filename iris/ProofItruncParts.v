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
Require Import RiscvPtsto.
Require Import RiscvModelBytes.
Require Import InstrBytes.
Require Import RegFile.
Require Import RiscvExtras.
Require Import BcacheInv.
Require Import BufOwn.
Require Import BlockWords.
Require Import FsBlocks.
Require Import InodeInv.
Require Import ProofBmapParts.
From Kernel Require KernelSyms.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
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

(* THE SKIP BRANCH.  When [ip->addrs[k]] is already zero the C frees
   nothing and stores nothing, so the loop's whole state must be unchanged
   -- and it is, definitionally: zeroing a slot that is already zero leaves
   the list alone, and adding 0 to the freed set adds nothing, since
   [bm_dir_freed] quotients 0 out. *)
Lemma bm_dir_zeroed_skip (bm : blkmap) (k : nat) :
  (k < length (bm_dir bm))%nat ->
  bv_unsigned (bm_dir bm !!! k) = 0 ->
  bm_dir_zeroed bm (S k) = bm_dir_zeroed bm k.
Proof.
  intros Hk Hz.
  assert (Hzz : bm_dir bm !!! k = bv_0 32) by (apply bv_eq; rewrite Hz; reflexivity).
  rewrite /bm_dir_zeroed. f_equal.
  rewrite (drop_S (bm_dir bm) (bm_dir bm !!! k) k);
    [| apply list_lookup_lookup_total_lt; lia].
  rewrite Hzz replicate_S_end -app_assoc. reflexivity.
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

Lemma bm_dir_freed_skip (bm : blkmap) (k : nat) :
  bv_unsigned (bm_dir bm !!! k) = 0 ->
  bm_dir_freed bm (S k) = bm_dir_freed bm k.
Proof.
  intros Hz. rewrite bm_dir_freed_step Hz. set_solver.
Qed.

Lemma bm_ent_freed_step (bm : blkmap) (j : nat) :
  bm_ent_freed bm (S j)
  = bm_ent_freed bm j ∪ ({[ bv_unsigned (bm_ent bm !!! j) ]} ∖ {[ 0 ]}).
Proof.
  rewrite /bm_ent_freed seq_S map_app list_to_set_app_L /=. set_solver.
Qed.

Lemma bm_ent_freed_skip (bm : blkmap) (q : nat) :
  bv_unsigned (bm_ent bm !!! q) = 0 ->
  bm_ent_freed bm (S q) = bm_ent_freed bm q.
Proof.
  intros Hz. rewrite bm_ent_freed_step Hz. set_solver.
Qed.

(* The pure set algebra behind "the pool grew by exactly the block just
   freed", common to both loops' step lemmas and to [bm_blocks_split]'s
   assembly: adding a nonzero block [c] to whatever is already excluded
   ([S]) is a plain set union.  Proved once, over abstract [used]/[S]/[c],
   so the itrunc instruction-chain proof discharges it with [exact] instead
   of paying [set_solver]'s [naive_solver] search over a whole-function
   proof's huge hypothesis context (see optimization.md's "never set_solver
   inside a whole-function proof" rule). *)
Lemma freed_pool_grow (used S : gset Z) (c : Z) :
  c <> 0 ->
  used ∖ S ∖ {[c]} = used ∖ (S ∪ ({[c]} ∖ {[0]})).
Proof. intros Hc. set_solver. Qed.

(* Same fact, stated for the shape [bm_ent_freed_step] leaves when [S] is
   itself already a two-piece union [A ∪ B] and the freed step lands on
   [B]'s side: substituting [bm_ent_freed bm (S j)] regroups the new block
   into [B], not onto the whole union, so the call site needs this
   associativity spelled out rather than [freed_pool_grow]'s flat form. *)
Lemma freed_pool_grow2 (used A B : gset Z) (c : Z) :
  c <> 0 ->
  used ∖ (A ∪ B) ∖ {[c]} = used ∖ (A ∪ (B ∪ ({[c]} ∖ {[0]}))).
Proof. intros Hc. set_solver. Qed.

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

(* THE LOOP'S EXIT TEST is [beq s1,s2] on two ADDRESSES, so the proof needs
   that distinct cursor positions really are distinct words -- i.e. that
   [i_addr ip] is injective over the range the loop walks.  The offsets are
   [80 + 4i] for i <= NDIRECT = 12, so they are tiny and distinct and
   nothing wraps; that is the whole content, but it has to be said. *)
Lemma i_addr_inj (ip : mword 64) (a c : nat) :
  (a <= NDIRECT)%nat -> (c <= NDIRECT)%nat ->
  i_addr ip a = i_addr ip c -> a = c.
Proof.
  intros Ha Hc Heq. unfold NDIRECT in Ha, Hc.
  rewrite /i_addr in Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite !add_vec64_unsigned !moi64_unsigned in Heq.
  rewrite (bvw64_small (80 + 4 * Z.of_nat a)) in Heq; [| lia].
  rewrite (bvw64_small (80 + 4 * Z.of_nat c)) in Heq; [| lia].
  unfold bv_wrap in Heq.
  (* the base cancels, leaving 4*(a-c) divisible by 2^64 -- and |4*(a-c)|
     is at most 48, so the quotient is 0 *)
  assert (Hz : (4 * Z.of_nat a - 4 * Z.of_nat c) mod 2 ^ 64 = 0).
  { replace (4 * Z.of_nat a - 4 * Z.of_nat c)
      with ((bv_unsigned ip + (80 + 4 * Z.of_nat a))
            - (bv_unsigned ip + (80 + 4 * Z.of_nat c))) by ring.
    rewrite Zminus_mod Heq Z.sub_diag Zmod_0_l. reflexivity. }
  apply Z.mod_divide in Hz; [| lia].
  destruct Hz as [q Hq].
  assert (Hq0 : q = 0) by nia.
  lia.
Qed.

(* The +0x36 test is a BNE, so the arm needs [neq_vec] where the loops
   needed [eq_vec].  ProofBmapParts has the eq_vec pair; these are the
   negations, and nothing more. *)
Lemma it_neqz_false (w : mword 32) : bv_unsigned w = 0 ->
  neq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = false.
Proof. intros Hw. unfold neq_vec. rewrite (bm_eqz_true w Hw). reflexivity. Qed.

Lemma it_neqz_true (w : mword 32) : bv_unsigned w <> 0 ->
  neq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = true.
Proof. intros Hw. unfold neq_vec. rewrite (bm_eqz_false w Hw). reflexivity. Qed.

(* THE INNER LOOP'S CURSOR walks bp->data by fours and stops at
   bp->data + 1024, so it needs the same injectivity the direct loop's
   exit test needed -- distinct entry positions are distinct addresses.
   Offsets are 4q for q <= 256, so again nothing wraps. *)
Lemma b_data_off_inj (pb : mword 64) (a c : nat) :
  (a <= NINDIRECT)%nat -> (c <= NINDIRECT)%nat ->
  pa_add (b_data pb) (4 * a)%nat = pa_add (b_data pb) (4 * c)%nat -> a = c.
Proof.
  intros Ha Hc Heq. unfold NINDIRECT in Ha, Hc.
  rewrite /pa_add /add_vec_int in Heq.
  apply (f_equal bv_unsigned) in Heq.
  rewrite !add_vec64_unsigned !moi64_unsigned in Heq.
  rewrite (bvw64_small (Z.of_nat (4 * a))) in Heq; [| lia].
  rewrite (bvw64_small (Z.of_nat (4 * c))) in Heq; [| lia].
  unfold bv_wrap in Heq.
  assert (Hz : (Z.of_nat (4 * a) - Z.of_nat (4 * c)) mod 2 ^ 64 = 0).
  { replace (Z.of_nat (4 * a) - Z.of_nat (4 * c))
      with ((bv_unsigned (b_data pb) + Z.of_nat (4 * a))
            - (bv_unsigned (b_data pb) + Z.of_nat (4 * c))) by ring.
    rewrite Zminus_mod Heq Z.sub_diag Zmod_0_l. reflexivity. }
  apply Z.mod_divide in Hz; [| lia].
  destruct Hz as [q Hq].
  assert (Hq0 : q = 0) by nia.
  lia.
Qed.

Lemma b_data_cursor (pb : mword 64) (q : nat) :
  pa_add (pa_add (b_data pb) (4 * q)%nat) 4%nat
  = pa_add (b_data pb) (4 * S q)%nat.
Proof. rewrite pa_add_add. f_equal. lia. Qed.

(* the limit s2 = ip+128 is the cell one past the twelfth, i.e. [i_addr ip
   NDIRECT] -- which is also [ip->addrs[NDIRECT]], the indirect cell the
   code reads next.  That coincidence is the loop's exit test. *)
Lemma it_dir_limit (ip : mword 64) :
  i_addr ip NDIRECT = pa_add ip 128%nat.
Proof.
  rewrite /i_addr /pa_add /add_vec_int /NDIRECT. f_equal.
Qed.

(* ===================================================================== *)
(*  THE RESOURCE-LEVEL VOCABULARY: the frame, and the two loop states     *)
(* ===================================================================== *)

Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import BufOwn.
Require Import WpLock.
Require Import FdSlots.
Require Import WpUart.
Require Import DiskPtsto.
Require Import BufOwn.
Require Import BioInv.
Require Import LogInv.
Require Import BitmapInv.
Require Import SpecItrunc.

Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Rs4 := (mword_of_int 20 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).

Section ItruncDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* itrunc's 48-byte frame: ra@40 s0@32 s1@24 s2@16 s3@8, and slot 6 (@0)
     which the DIRECT path never touches -- [sd s4,0(sp)] is at +0x50,
     inside the indirect arm, and the matching [ld s4,0(sp)] at +0x90.  So
     the sixth slot is owned but unconstrained: the frame claimed it at the
     [addi sp,sp,-48], and only the indirect arm gives it a value. *)
  Definition it_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈ (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈ (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈ (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈ (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈ (m !!! Regidx Rs3 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ v))%I.

  (* ------------------------------------------------------------------ *)
  (*  THE DIRECT LOOP'S STATE, at cursor k                               *)
  (* ------------------------------------------------------------------ *)

  (* Everything the loop owns and moves.  The map is [bm_dir_zeroed bm k];
     the pool has grown by [bm_dir_freed bm k]; the [inode_blocks] bundle
     has lost exactly the entries below the cursor -- which is why it is
     indexed at the ZEROED map, whose [blk_res] at those indices is [True].

     The budget is [bm_paidS], NOT a unit count: that is the whole point of
     the credited arms.  It is idempotent under bfree, so this assertion is
     literally unchanged from k = 0 to k = NDIRECT.

     [crb] and [Sb] are the CALLER's -- the credit it entered with and the
     set it entered at -- and both are CONSTANT across the loop (the running
     set is the existential inside [bm_paidS]).  So the set retrofit here is
     two threaded parameters, not a proof obligation; this is
     [ProofIalloc]'s pattern. *)
  Definition it_dir_state (γ : log_names) (γfs : fs_names)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8))
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (bn : bio_names) (crb : bool) (Sb : gset Z) (e0 : nat)
      (w : nat) (k : nat) : iProp Σ :=
    (inode_map γfs ip (bm_dir_zeroed bm k) ∗
     inode_blocks γfs (bm_dir_zeroed bm k) data ∗
     bitmap_res γfs bmapstart cov logstart size (used ∖ bm_dir_freed bm k) ∗
     bm_paidS γ bmapstart crb w Sb e0)%I.

  (* Opened and closed by LEMMA, never by [rewrite /it_dir_state]: the Iris
     context is part of the goal term, so unfolding the definition in the
     body also unfolds it inside the induction hypothesis, and the IH then
     no longer matches the bundle the loop carries. *)
  Lemma it_dir_state_open (γ : log_names) (γfs : fs_names)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8))
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (bn : bio_names) (crb : bool) (Sb : gset Z) (e0 : nat)
      (w : nat) (k : nat) :
    it_dir_state γ γfs ip bm data cov logstart bmapstart size used bn crb Sb e0 w k -∗
      inode_map γfs ip (bm_dir_zeroed bm k) ∗
      inode_blocks γfs (bm_dir_zeroed bm k) data ∗
      bitmap_res γfs bmapstart cov logstart size (used ∖ bm_dir_freed bm k) ∗
      bm_paidS γ bmapstart crb w Sb e0.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma it_dir_state_close (γ : log_names) (γfs : fs_names)
      (ip : mword 64) (bm : blkmap) (data : nat -> list (bv 8))
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (bn : bio_names) (crb : bool) (Sb : gset Z) (e0 : nat)
      (w : nat) (k : nat) :
    inode_map γfs ip (bm_dir_zeroed bm k) -∗
    inode_blocks γfs (bm_dir_zeroed bm k) data -∗
    bitmap_res γfs bmapstart cov logstart size (used ∖ bm_dir_freed bm k) -∗
    bm_paidS γ bmapstart crb w Sb e0 -∗
    it_dir_state γ γfs ip bm data cov logstart bmapstart size used bn crb Sb e0 w k.
  Proof. iIntros "A B C D". rewrite /it_dir_state. iFrame "A B C D". Qed.

  (* ------------------------------------------------------------------ *)
  (*  THE INDIRECT LOOP'S STATE, at cursor q                             *)
  (* ------------------------------------------------------------------ *)

  (* The map does NOT appear: the C never writes the entry list back, so
     [bm_ent bm] is fixed and the only things moving are the pool and the
     [inode_blocks] entries at indices [NDIRECT + q].  [it_ent_res] is what
     is LEFT of the bundle -- the entries at and above the cursor -- stated
     as a big-op over the remaining indices rather than as an [inode_blocks]
     at some doctored map, because there is no map here to doctor. *)
  Definition it_ent_res (γfs : fs_names) (bm : blkmap)
      (data : nat -> list (bv 8)) (q : nat) : iProp Σ :=
    ([∗ list] t ∈ seq q (NINDIRECT - q),
       blk_res γfs (bm_ent bm !!! t) (data (NDIRECT + t)%nat))%I.

  Definition it_ent_state (γ : log_names) (γfs : fs_names)
      (bm : blkmap) (data : nat -> list (bv 8))
      (cov : gset Z) (logstart bmapstart size : Z) (used : gset Z)
      (crb : bool) (Sb : gset Z) (e0 : nat) (w : nat) (q : nat) : iProp Σ :=
    (it_ent_res γfs bm data q ∗
     bitmap_res γfs bmapstart cov logstart size
       (used ∖ (bm_dir_freed bm NDIRECT ∪ bm_ent_freed bm q)) ∗
     bm_paidS γ bmapstart crb w Sb e0)%I.

  (* THE ONE STEP bfree TAKES, and why the loops never case-split.

     Whichever disjunct [bm_paid] is in, it yields a budget token bfree's
     credited arm can consume -- with [cr] and the spare unit chosen to
     match -- and the resource that comes back is the SAME in both cases:
     [log_opS gamma (S u) (Sb ∪ {[bmapstart]})], which is the PAID
     disjunct, since [bmapstart] is in that set by construction.

       paid   (cr = true,  u' = u):   S u  units in, S u units back
       unpaid (cr = false, u' = S u): S u+1 units in, S u units back

     So the wand closes back into [bm_paid gamma bmapstart u] either way,
     and a loop that frees an unknown number of blocks carries the single
     assertion unchanged.  This is the whole payoff of the absorption
     credit being a positive client-held claim. *)
  Lemma bm_paid_use (γ : log_names) (bmapstart : Z) (u : nat) :
    bm_paid γ bmapstart u -∗ ∃ (cr : bool) (u' : nat) (Sb : gset Z),
      ⌜cr = true -> bmapstart ∈ Sb⌝ ∗
      ⌜(if cr then S u' else u') = S u⌝ ∗
      log_opS γ (S u') Sb ∗
      (log_opS γ (S u) (Sb ∪ {[bmapstart]}) -∗ bm_paid γ bmapstart u).
  Proof.
    rewrite /bm_paid. iIntros "[H|H]".
    - (* already paid: present the credit, keep the unit *)
      iDestruct "H" as (Sb) "(%Hin & Hop)".
      iExists true, u, Sb.
      iSplitR; [iPureIntro; intros _; exact Hin|].
      iSplitR; [iPureIntro; reflexivity|].
      iFrame "Hop". iIntros "Hop". iLeft. iExists (Sb ∪ {[bmapstart]}).
      iSplitR; [iPureIntro; set_solver|]. iFrame "Hop".
    - (* not yet: spend the spare unit and become paid *)
      iDestruct "H" as (Sb) "Hop".
      iExists false, (S u), Sb.
      iSplitR; [iPureIntro; discriminate|].
      iSplitR; [iPureIntro; reflexivity|].
      iFrame "Hop". iIntros "Hop". iLeft. iExists (Sb ∪ {[bmapstart]}).
      iSplitR; [iPureIntro; set_solver|]. iFrame "Hop".
  Qed.

  (* THE SET-INDEXED TWIN of the step above (GR-2b, retrofit 4a).  The shape
     does not change AT ALL: the running set was already opened
     existentially and the wand already closes at [Sb0 ∪ {[bmapstart]}].
     All the twin adds is the caller's [Sb ⊆ Sb0] on the way out and its
     re-establishment by transitivity on the way back -- and since BOTH arms
     land in the PAID disjunct, the growth clause is discharged once per arm
     and never inside the loop.  The [crb] guard is likewise never
     re-established, because the paid disjunct does not carry it.

     The two [set_solver]s are inside a small definitional lemma, which is
     where they belong (S3l's rule); do not lift one to a call site. *)
  Lemma bm_paidS_use (γ : log_names) (bmapstart : Z) (crb : bool)
      (u : nat) (Sb : gset Z) (e0 : nat) :
    bm_paidS γ bmapstart crb u Sb e0 -∗ ∃ (cr : bool) (u' : nat) (Sb0 : gset Z),
      ⌜cr = true -> bmapstart ∈ Sb0⌝ ∗
      ⌜(if cr then S u' else u') = S u⌝ ∗
      ⌜Sb ⊆ Sb0⌝ ∗
      log_opSe γ (S u') Sb0 e0 ∗
      (log_opSe γ (S u) (Sb0 ∪ {[bmapstart]}) e0 -∗ bm_paidS γ bmapstart crb u Sb e0).
  Proof.
    rewrite /bm_paidS. iIntros "[H|[%Hc H]]".
    - (* already paid: present the credit, keep the unit *)
      iDestruct "H" as (Sb0) "(%Hsub & %Hin & Hop)".
      iExists true, u, Sb0.
      iSplitR; [iPureIntro; intros _; exact Hin|].
      iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; exact Hsub|].
      iFrame "Hop". iIntros "Hop". iLeft. iExists (Sb0 ∪ {[bmapstart]}).
      iSplitR; [iPureIntro; set_solver|].
      iSplitR; [iPureIntro; set_solver|]. iFrame "Hop".
    - (* not yet: spend the spare unit and become paid *)
      iDestruct "H" as (Sb0) "(%Hsub & Hop)".
      iExists false, (S u), Sb0.
      iSplitR; [iPureIntro; discriminate|].
      iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; exact Hsub|].
      iFrame "Hop". iIntros "Hop". iLeft. iExists (Sb0 ∪ {[bmapstart]}).
      iSplitR; [iPureIntro; set_solver|].
      iSplitR; [iPureIntro; set_solver|]. iFrame "Hop".
  Qed.

  (* TAKING A BLOCK OUT FOR GOOD.  [InodeInv.inode_blocks_acc] lends a block
     and demands it back; itrunc hands it to the free pool instead, so the
     remaining bundle must be at a map whose slot [i] is ZERO -- where
     [blk_res] is definitionally [True], and the entry simply vanishes.
     That is the whole reason the direct loop's state is indexed at
     [bm_dir_zeroed] rather than at [bm] with side conditions. *)
  Lemma inode_blocks_take (γfs : fs_names) (bm bm' : blkmap)
      (data : nat -> list (bv 8)) (i : nat) :
    (i < MAXFILE)%nat ->
    bv_unsigned (blkmap_get bm i) <> 0 ->
    bv_unsigned (blkmap_get bm' i) = 0 ->
    (forall t : nat, (t < MAXFILE)%nat -> t <> i ->
       blkmap_get bm' t = blkmap_get bm t) ->
    inode_blocks γfs bm data -∗
      (fsblock γfs (bv_unsigned (blkmap_get bm i)) (data i) ∗
       blk_own γfs (bv_unsigned (blkmap_get bm i))) ∗
      inode_blocks γfs bm' data.
  Proof.
    intros Hi Hnz Hz Hag.
    assert (Hlk : seq 0 MAXFILE !! i = Some i)
      by (apply lookup_seq; split; [lia | exact Hi]).
    rewrite /inode_blocks.
    rewrite (big_sepL_delete
               (fun (_ : nat) (k : nat) => blk_res γfs (blkmap_get bm k) (data k))
               (seq 0 MAXFILE) i i Hlk).
    rewrite (big_sepL_delete
               (fun (_ : nat) (k : nat) => blk_res γfs (blkmap_get bm' k) (data k))
               (seq 0 MAXFILE) i i Hlk).
    iIntros "[Hb Hrest]".
    rewrite {1}/blk_res.
    destruct (decide (bv_unsigned (blkmap_get bm i) = 0)) as [Hc|_];
      [exfalso; exact (Hnz Hc)|].
    iDestruct "Hb" as "[Hfs Htok]".
    iSplitL "Hfs Htok"; [iFrame "Hfs Htok"|].
    iSplitR.
    { rewrite /blk_res.
      destruct (decide (bv_unsigned (blkmap_get bm' i) = 0)) as [_|Hc];
        [done | exfalso; exact (Hc Hz)]. }
    iApply (big_sepL_mono with "Hrest").
    intros t x Hx.
    destruct (decide (t = i)) as [->|Hne]; [done|].
    apply lookup_seq in Hx as [-> Hlt].
    rewrite (Hag (0 + t)%nat ltac:(lia) ltac:(lia)). done.
  Qed.

  (* AN EMPTIED BUNDLE IS TRIVIAL, at any naming whatsoever: every slot of
     [bm_empty] is zero, so every [blk_res] is [True].  This is what lets
     itrunc's postcondition name the all-zero file content without having
     to transport the [data] it actually carried. *)
  Lemma inode_blocks_empty_any (γfs : fs_names) (data : nat -> list (bv 8)) :
    ⊢ inode_blocks γfs bm_empty data.
  Proof.
    rewrite /inode_blocks.
    iApply big_sepL_intro. iIntros "!>" (t x Hx).
    rewrite /blk_res bm_empty_get.
    destruct (decide (bv_unsigned (bv_0 32) = 0)) as [_|Hc];
      [done | exfalso; apply Hc; reflexivity].
  Qed.

  (* a nonzero slot's [blk_res] is the pair; the [if decide] lives inside an
     Iris hypothesis, where a Coq [destruct] cannot reach it *)
  Lemma blk_res_nz (γfs : fs_names) (w : bv 32) (bs : list (bv 8)) :
    bv_unsigned w <> 0 ->
    blk_res γfs w bs -∗
      fsblock γfs (bv_unsigned w) bs ∗ blk_own γfs (bv_unsigned w).
  Proof.
    intros Hnz. rewrite /blk_res.
    destruct (decide (bv_unsigned w = 0)) as [Hc|_];
      [exfalso; exact (Hnz Hc) |]. iIntros "$".
  Qed.

  (* bread hands back a handle but no buffer index bound; the handle itself
     carries it, as [bio_held]'s first conjunct.  Read it out and give the
     handle straight back. *)
  Lemma bio_locked_kbound (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsd : list (bv 8)) (d : bool) :
    bio_locked bn V k pidv dev bno bs bsd d -∗
      ⌜(k < NBUF)%nat⌝ ∗ bio_locked bn V k pidv dev bno bs bsd d.
  Proof.
    rewrite /bio_locked /bio_held.
    iIntros "(%Hk & %Hc & %Hd & Hr)".
    iSplitR; [done|].
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|]. iExact "Hr".
  Qed.

  (* the indirect block's content half and token, when it exists *)
  Lemma ind_res_nz (γfs : fs_names) (bmx : blkmap) :
    bv_unsigned (bm_ind bmx) <> 0 ->
    ind_res γfs bmx -∗
      fsblock γfs (bv_unsigned (bm_ind bmx)) (ind_bytes (bm_ent bmx)) ∗
      blk_own γfs (bv_unsigned (bm_ind bmx)).
  Proof.
    intros Hnz. rewrite /ind_res /ind_blk /ind_tok.
    destruct (decide (bv_unsigned (bm_ind bmx) = 0)) as [Hc|_];
      [exfalso; exact (Hnz Hc) |]. iIntros "$".
  Qed.

  (* opened and closed by lemma, for the same IH reason as the direct
     loop's state *)
  Lemma it_ent_state_open (γ : log_names) (γfs : fs_names) (bm : blkmap)
      (data : nat -> list (bv 8)) (cov : gset Z)
      (logstart bmapstart size : Z) (used : gset Z)
      (crb : bool) (Sb : gset Z) (e0 : nat) (w : nat) (q : nat) :
    it_ent_state γ γfs bm data cov logstart bmapstart size used crb Sb e0 w q -∗
      it_ent_res γfs bm data q ∗
      bitmap_res γfs bmapstart cov logstart size
        (used ∖ (bm_dir_freed bm NDIRECT ∪ bm_ent_freed bm q)) ∗
      bm_paidS γ bmapstart crb w Sb e0.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma it_ent_state_close (γ : log_names) (γfs : fs_names) (bm : blkmap)
      (data : nat -> list (bv 8)) (cov : gset Z)
      (logstart bmapstart size : Z) (used : gset Z)
      (crb : bool) (Sb : gset Z) (e0 : nat) (w : nat) (q : nat) :
    it_ent_res γfs bm data q -∗
    bitmap_res γfs bmapstart cov logstart size
      (used ∖ (bm_dir_freed bm NDIRECT ∪ bm_ent_freed bm q)) -∗
    bm_paidS γ bmapstart crb w Sb e0 -∗
    it_ent_state γ γfs bm data cov logstart bmapstart size used crb Sb e0 w q.
  Proof. iIntros "A B C". rewrite /it_ent_state. iFrame "A B C". Qed.

  (* THE HANDOFF from the direct loop to the indirect one.  After the direct
     loop every direct slot of the map is zero, so [inode_blocks] at that
     map is [True] on indices below NDIRECT and the entry list on the rest --
     which is exactly [it_ent_res] at cursor 0.  Stating it as a lemma keeps
     the arm from having to reason about the bundle's shape. *)
  Lemma inode_blocks_to_ent_res (γfs : fs_names) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    length (bm_dir bm) = NDIRECT -> length (bm_ent bm) = NINDIRECT ->
    inode_blocks γfs (bm_dir_zeroed bm NDIRECT) data -∗
      it_ent_res γfs bm data 0.
  Proof.
    intros Hd He. rewrite /inode_blocks /it_ent_res Nat.sub_0_r.
    (* MAXFILE = NDIRECT + NINDIRECT, and the first NDIRECT entries are all
       [True]: [bm_dir_zeroed] at the top has an all-zero direct part *)
    replace MAXFILE with (NDIRECT + NINDIRECT)%nat
      by (unfold MAXFILE, NDIRECT, NINDIRECT; lia).
    rewrite seq_app big_sepL_app.
    iIntros "[_ Hhi]".
    (* the high half runs over [seq NDIRECT NINDIRECT]; the target runs over
       [seq 0 NINDIRECT] with the index shifted, so re-index before mono *)
    replace (0 + NDIRECT)%nat with (NDIRECT + 0)%nat by lia.
    iEval (rewrite -(fmap_add_seq NDIRECT 0 NINDIRECT) big_sepL_fmap) in "Hhi".
    iApply (big_sepL_mono with "Hhi").
    intros t x Hx.
    apply lookup_seq in Hx as [-> Hlt].
    rewrite /blkmap_get. cbn [bm_dir_zeroed bm_dir bm_ind bm_ent].
    destruct (decide ((NDIRECT + (0 + t)) < NDIRECT)%nat); [lia|].
    replace (NDIRECT + (0 + t) - NDIRECT)%nat with t by lia.
    replace (NDIRECT + (0 + t))%nat with (NDIRECT + t)%nat by lia. done.
  Qed.

  (* peeling the cursor entry off the remaining bundle -- the step both the
     free and the skip take *)
  Lemma it_ent_res_peel (γfs : fs_names) (bm : blkmap)
      (data : nat -> list (bv 8)) (q : nat) :
    (q < NINDIRECT)%nat ->
    it_ent_res γfs bm data q -∗
      blk_res γfs (bm_ent bm !!! q) (data (NDIRECT + q)%nat) ∗
      it_ent_res γfs bm data (S q).
  Proof.
    intros Hq. rewrite /it_ent_res.
    replace (NINDIRECT - q)%nat with (S (NINDIRECT - S q))%nat by lia.
    rewrite -cons_seq big_sepL_cons. iIntros "[$ $]".
  Qed.

  Lemma it_ent_res_done (γfs : fs_names) (bm : blkmap)
      (data : nat -> list (bv 8)) :
    it_ent_res γfs bm data NINDIRECT ⊣⊢ emp.
  Proof.
    rewrite /it_ent_res Nat.sub_diag /=. reflexivity.
  Qed.

End ItruncDefs.
