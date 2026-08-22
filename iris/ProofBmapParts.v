(* ProofBmapParts.v -- bmap's vocabulary: everything its proof needs that is
   NOT a step of its instruction chain, so ProofBmap.v stays about control
   flow.  (The ProofBreadParts.v / ProofWriteHead.v division of labour.)

   Four groups:

   (1) THE TWO SCALINGS.  bmap computes a byte offset twice, both times as
       [slli 0x20 / srli 0x1e] -- zero-extend the 32-bit index, then multiply
       by four.  [bm_slli32_srli30] is that round trip; the arithmetic behind
       it is factored into an [mword]-free helper over plain [Z], because
       [lia] answers "Cannot find witness" as soon as a [bv_unsigned] is in
       the goal (claude-notes/durable-notes.md).

   (2) THE ADDRESSES.  The three [addrs] cells the code forms are already
       covered by [InodeInv.i_addr_indexed] / [i_addr_ndirect]; what is left
       is [bp->data] and the entry slot inside it, plus that slot's
       4-alignment (bcache geometry, as in write_head).

   (3) WORDS INSIDE THE INDIRECT BLOCK.  [InodeInv] carries the indirect
       block's content as [ind_bytes e] for an ENTRY LIST [e]; ByteBuf's
       window algebra carries it as a naming function.  [bm_ent_read] and
       [bm_ent_store] are the two bridges -- read entry [q], and install a
       new entry [q] -- and [bm_buf_word_acc] borrows that word out of the
       [buf_own] the bio handle carries.

   (4) THE HANDLE.  [bm_held_swap] exchanges the traveling bytes inside a
       [bio_held] (the whole of what bmap does to the buffer), and
       [bm_held_content] is the agreement that identifies those bytes with
       the caller's own [fsblock] half -- i.e. with [ind_bytes (bm_ent bm)].
       That agreement is the load-bearing coupling of the indirect arm: it
       is what makes the word the code reads out of the buffer BE the entry
       list's entry [q]. *)
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
Require Import RiscvExtras.
Require Import PrintintArith.
Require Import ByteCursor.
Require Import ByteBuf.
Require Import DiskPtsto.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks.
Require Import BlockWords.
Require Import InodeInv.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ===================================================================== *)
(*  (1) The [slli 0x20 / srli 0x1e] scaling                               *)
(* ===================================================================== *)

(* mword-FREE, so [lia]/[nia] work normally (durable-notes: the bitvector
   zify hook makes [lia] fail on any goal that mentions a [bv_unsigned]). *)
Local Lemma bm_scale_arith (u : Z) :
  0 <= u -> u < 4294967296 ->
  0 <= u * 4294967296
  /\ u * 4294967296 < 18446744073709551616
  /\ u * 4294967296 / 1073741824 = 4 * u
  /\ 0 <= 4 * u < 18446744073709551616.
Proof.
  intros H0 H1. split_and!; [nia | nia | | nia | nia].
  replace (u * 4294967296) with ((4 * u) * 1073741824) by ring.
  rewrite Z.div_mul; [reflexivity | lia].
Qed.

Lemma bm_slli32_srli30 (x : mword 64) :
  bv_unsigned x < 4294967296 ->
  shift_bits_right
    (shift_bits_left x (subrange_vec_dec (mword_of_int 32 : mword 6)
                          (Z.sub log2_xlen 1) 0))
    (subrange_vec_dec (mword_of_int 30 : mword 6) (Z.sub log2_xlen 1) 0)
  = (mword_of_int (4 * bv_unsigned x) : mword 64).
Proof.
  intro Hx.
  pose proof (bv_unsigned_in_range _ x) as [Hx0 _].
  destruct (bm_scale_arith (bv_unsigned x) Hx0 Hx) as (Hn & Hlt & Hdiv & Hr4).
  assert (Hl : shift_bits_left x
                 (subrange_vec_dec (mword_of_int 32 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftl x 32).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  assert (Hr : shift_bits_right (shiftl x 32)
                 (subrange_vec_dec (mword_of_int 30 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftr (shiftl x 32) 30).
  { unfold shift_bits_right. f_equal; vm_compute; reflexivity. }
  rewrite Hl Hr. apply bv_eq.
  unfold shiftl, shiftr, SailStdpp.Values.with_word, get_word,
    MachineWord.MachineWord.logical_shift_left,
    MachineWord.MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned bv_shiftl_unsigned.
  assert (H32 : bv_unsigned (MachineWord.MachineWord.N_to_word
                   (MachineWord.MachineWord.Z_idx 64)
                   (MachineWord.MachineWord.Z_idx 32)) = 32).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  assert (H30 : bv_unsigned (MachineWord.MachineWord.N_to_word
                   (MachineWord.MachineWord.Z_idx 64)
                   (MachineWord.MachineWord.Z_idx 30)) = 30).
  { unfold MachineWord.MachineWord.N_to_word, MachineWord.MachineWord.Z_idx.
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; simpl; lia. }
  rewrite H32 H30.
  rewrite Z.shiftl_mul_pow2; [| lia].
  assert (Hmod : bv_modulus (MachineWord.MachineWord.Z_idx 64)
                 = 18446744073709551616) by (vm_compute; reflexivity).
  change (2 ^ 32)%Z with 4294967296%Z.
  rewrite (bv_wrap_small 64 (bv_unsigned x * 4294967296));
    [| rewrite Hmod; split; assumption].
  rewrite Z.shiftr_div_pow2; [| lia].
  change (2 ^ 30)%Z with 1073741824%Z.
  rewrite Hdiv moi64_unsigned. symmetry. apply bvw64_small.
  change (2 ^ 64)%Z with 18446744073709551616%Z. exact Hr4.
Qed.

(* the [addiw a5,a1,-12] that turns a file index into an indirect index.
   The immediate is the decoder's POSITIVE RESIDUE (4084 = 4096 - 12). *)
Lemma bm_addiw_m12 (k : Z) : 12 <= k -> k < 2147483648 ->
  sign_extend' 64 (subrange_vec_dec
    (add_vec (mword_of_int k : mword 64)
       (sign_extend' 64 (mword_of_int 4084 : mword 12))) 31 0)
  = (mword_of_int (k - 12) : mword 64).
Proof.
  intros H0 H1.
  assert (Hm12 : (sign_extend' 64 (mword_of_int 4084 : mword 12) : mword 64)
                 = mword_of_int (-12))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite Hm12.
  assert (Hadd : add_vec (mword_of_int k : mword 64) (mword_of_int (-12))
                 = (mword_of_int (k + -12) : mword 64))
    by exact (avi_mword k (-12)).
  rewrite Hadd.
  replace (k + -12) with (k - 12) by lia.
  apply PrintintArith.sextw_moi. split; [lia|].
  change (2 ^ 31)%Z with 2147483648%Z. lia.
Qed.

(* a small non-negative literal survives the ABI's sign extension *)
Lemma bm_sext32 (z : Z) : 0 <= z -> z < 2147483648 ->
  (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = mword_of_int z.
Proof.
  intros H0 H1. apply PrintintArith.sext32_64_small.
  split; [lia | change (2 ^ 31)%Z with 2147483648%Z; lia].
Qed.

(* ...and its [uint] reading, for the two [bltu] branch conditions *)
Lemma bm_uint_moi (z : Z) : 0 <= z -> z < 18446744073709551616 ->
  uint (mword_of_int z : mword 64) = z.
Proof.
  intros H0 H1. rewrite RiscvExtras.uint_unsigned moi64_unsigned.
  apply bvw64_small. change (2 ^ 64)%Z with 18446744073709551616%Z. lia.
Qed.

(* ---- the ZERO TESTS: [c.bnez s1] / [c.beqz s1] on a word an [lw] just
   sign-extended.  Both branch conditions are about the 32-bit CELL, so the
   64-bit compare has to be read back through [sext64_32_inj]. ---- *)

Lemma bm_sext_eqv (a c : mword 32) :
  eq_vec (sign_extend' 64 a : mword 64) (sign_extend' 64 c : mword 64) = eq_vec a c.
Proof.
  destruct (eq_vec a c) eqn:Hac.
  - apply eq_vec_true_iff in Hac. subst c. apply eq_vec_true_iff. reflexivity.
  - apply eq_vec_false_iff in Hac. apply eq_vec_false_iff.
    intro Hq. apply Hac. exact (sext64_32_inj a c Hq).
Qed.

Lemma bm_zero_reg_sext :
  (zero_reg : mword 64) = sign_extend' 64 (mword_of_int 0 : mword 32).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma bm_zero32 (w : mword 32) : bv_unsigned w = 0 -> w = (mword_of_int 0 : mword 32).
Proof.
  intro Hw. apply bv_eq. rewrite Hw moi32_unsigned. reflexivity.
Qed.

Lemma bm_eqz_true (w : mword 32) : bv_unsigned w = 0 ->
  eq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = true.
Proof.
  intro Hw. rewrite bm_zero_reg_sext bm_sext_eqv.
  apply eq_vec_true_iff. exact (bm_zero32 w Hw).
Qed.

Lemma bm_eqz_false (w : mword 32) : bv_unsigned w <> 0 ->
  eq_vec (sign_extend' 64 w : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hw. rewrite bm_zero_reg_sext bm_sext_eqv.
  apply eq_vec_false_iff. intro Hq. apply Hw.
  rewrite Hq moi32_unsigned. reflexivity.
Qed.

(* the return value on the failure arms: a zero cell reads back as the
   64-bit literal zero the contract states a0 at *)
Lemma bm_sext_zero (w : mword 32) : bv_unsigned w = 0 ->
  (sign_extend' 64 w : mword 64) = mword_of_int 0.
Proof.
  intro Hw. rewrite (bm_zero32 w Hw). apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- the thirteen [addrs] cells, under a one-cell update ---- *)

Lemma bm_cells_insert_dir (bm : blkmap) (j : nat) (w : bv 32) :
  length (bm_dir bm) = NDIRECT -> (j < NDIRECT)%nat ->
  <[j := w]> (bm_cells bm)
  = bm_cells (MkBlkmap (<[j := w]> (bm_dir bm)) (bm_ind bm) (bm_ent bm)).
Proof.
  intros Hlen Hj. rewrite /bm_cells /=. rewrite insert_app_l; [reflexivity|lia].
Qed.

Lemma bm_cells_insert_ind (bm : blkmap) (w : bv 32) (e : list (bv 32)) :
  length (bm_dir bm) = NDIRECT ->
  <[NDIRECT := w]> (bm_cells bm) = bm_cells (MkBlkmap (bm_dir bm) w e).
Proof.
  intros Hlen. rewrite /bm_cells /=.
  rewrite insert_app_r_alt; [|lia]. rewrite Hlen Nat.sub_diag /=. reflexivity.
Qed.

(* ===================================================================== *)
(*  (2) Addresses                                                         *)
(* ===================================================================== *)

Lemma bm_pa_add_moi (p : mword 64) (nn : nat) :
  add_vec p (mword_of_int (Z.of_nat nn)) = pa_add p nn.
Proof. reflexivity. Qed.

(* [addi a5,a0,88] : a0 = bp, a5 = bp->data *)
Lemma bm_data_addr (p : mword 64) :
  add_vec p (sign_extend' 64 (mword_of_int 88 : mword 12)) = b_data p.
Proof.
  assert (H : (sign_extend' 64 (mword_of_int 88 : mword 12) : mword 64)
              = mword_of_int (Z.of_nat 88%nat))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H bm_pa_add_moi. reflexivity.
Qed.

(* [c.add a5,a5,a1] : a5 = bp->data + 4*(bn-NDIRECT) *)
Lemma bm_slot_addr (p : mword 64) (q : nat) :
  add_vec (b_data p) (mword_of_int (4 * Z.of_nat q)) = pa_add (b_data p) (4 * q)%nat.
Proof.
  rewrite -bm_pa_add_moi. f_equal. f_equal. lia.
Qed.

(* [lw s1,0(a5)] / [sw a0,0(s3)] : the displacement is zero *)
Lemma bm_off0 (p : mword 64) :
  add_vec p (sign_extend' 64 (mword_of_int 0 : mword 12)) = p.
Proof.
  assert (H : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
              = mword_of_int 0) by (apply bv_eq; vm_compute; reflexivity).
  rewrite H. apply kv_addv_zero.
Qed.

(* the entry slot's 4-alignment, from bcache's geometry (write_head's
   [wh_align4], re-derived: a Proof file may not import another one) *)
Local Lemma bm_align_arith (kk qq : Z) :
  0 <= kk -> kk < 30 -> 0 <= qq -> qq <= 255 ->
  (2147582488 + 1112 * kk + (88 + 4 * qq)) `mod` 4 = 0
  /\ 0 <= 2147582488 + 1112 * kk + (88 + 4 * qq)
  /\ 2147582488 + 1112 * kk + (88 + 4 * qq) < 18446744073709551616.
Proof.
  intros H1 H2 H3 H4. split_and!; [| lia | lia].
  replace (2147582488 + 1112 * kk + (88 + 4 * qq))
    with ((536895644 + 278 * kk + qq) * 4) by lia.
  apply Z_mod_mult.
Qed.

Lemma bm_align4 (k q : nat) : (k < NBUF)%nat -> (q <= 255)%nat ->
  is_aligned_paddr (Physaddr (pa_add (b_data (bnode k)) (4 * q)%nat)) 4 = true.
Proof.
  intros Hk Hq.
  unfold b_data. rewrite pa_add_add.
  unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite RiscvExtras.uint_unsigned.
  rewrite ByteCursor.pa_add_unsigned.
  rewrite (bnode_unsigned k Hk).
  unfold buf_base, buf_stride, KernelSyms.bcache.
  destruct (bm_align_arith (Z.of_nat k) (Z.of_nat q)
              ltac:(lia) ltac:(unfold NBUF in Hk; lia) ltac:(lia) ltac:(lia))
    as (Hm & Hlo & Hhi).
  replace (0x80018200 + 24 + 1112 * Z.of_nat k + Z.of_nat (88 + 4 * q))
    with (2147582488 + 1112 * Z.of_nat k + (88 + 4 * Z.of_nat q)) by lia.
  apply bb_align_z; assumption.
Qed.

(* ===================================================================== *)
(*  (3) Words inside the indirect block                                   *)
(* ===================================================================== *)

(* reading entry [q] out of the byte image *)
Lemma bm_ent_read (e : list (bv 32)) (q : nat) :
  (q < length e)%nat ->
  bb_mk (fun j => ind_bytes e !!! j) (4 * q)%nat = e !!! q.
Proof.
  intros Hq.
  apply (bv_eq_of_bytes (n := 4)). intros jj Hjj.
  assert (Hj4 : (jj < 4)%nat) by lia.
  rewrite (bb_mk_byte (fun j => ind_bytes e !!! j) (4 * q)%nat jj Hj4).
  apply list_lookup_total_correct.
  apply ind_bytes_lookup; [exact Hq | exact Hj4].
Qed.

(* installing entry [q] into the byte image, index by index *)
Lemma bm_ent_store_at (e : list (bv 32)) (q : nat) (w : mword 32) (i : nat) :
  (q < length e)%nat -> (i < 4 * length e)%nat ->
  ind_bytes (<[q := w]> e) !! i
  = Some (bb_set (fun j => ind_bytes e !!! j) (4 * q)%nat w i).
Proof.
  intros Hq Hi.
  destruct (decide ((4 * q <= i)%nat /\ (i < 4 * q + 4)%nat)) as [[H1 H2]|Hout].
  - pose proof (ind_bytes_insert_same e q w (i - 4 * q)%nat Hq ltac:(lia)) as Hs.
    replace (4 * q + (i - 4 * q))%nat with i in Hs by lia.
    rewrite Hs (bb_set_in (fun j => ind_bytes e !!! j) (4 * q)%nat w i
                  ltac:(lia) ltac:(lia)).
    reflexivity.
  - rewrite (bb_set_out (fun j => ind_bytes e !!! j) (4 * q)%nat w i ltac:(lia)).
    rewrite (ind_bytes_insert_other e q w i Hq ltac:(lia)).
    apply list_lookup_lookup_total_lt. rewrite ind_bytes_length. lia.
Qed.

(* ...and as the whole 1024-byte list the buffer carries *)
Lemma bm_ent_store (e : list (bv 32)) (q : nat) (w : mword 32) :
  length e = 256%nat -> (q < 256)%nat ->
  (bb_set (fun j => ind_bytes e !!! j) (4 * q)%nat w) <$> seq 0 1024
  = ind_bytes (<[q := w]> e).
Proof.
  intros Hlen Hq. apply list_eq. intros i.
  rewrite list_lookup_fmap.
  destruct (decide ((i < 1024)%nat)) as [Hi|Hi].
  - assert (Hlk : seq 0 1024 !! i = Some i) by (apply lookup_seq; lia).
    rewrite Hlk /=. symmetry. apply bm_ent_store_at; lia.
  - assert (Hlk : seq 0 1024 !! i = None)
      by (apply lookup_ge_None_2; rewrite length_seq; lia).
    rewrite Hlk /=. symmetry. apply lookup_ge_None_2.
    rewrite ind_bytes_length length_insert Hlen. lia.
Qed.

(* a word borrowed OUT of the buffer's byte list and put back UNCHANGED
   leaves the list where it was *)
Lemma bm_buf_restore (bs : list (bv 8)) (q : nat) :
  length bs = 1024%nat ->
  (bb_set (fun j => bs !!! j) (4 * q)%nat (bb_mk (fun j => bs !!! j) (4 * q)%nat))
    <$> seq 0 1024 = bs.
Proof.
  intros Hlen.
  etransitivity; [| exact (bb_list_id bs)].
  rewrite Hlen.
  apply list_fmap_ext. intros i x _. apply bb_set_mk.
Qed.

Section BmapRes.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (* ONE 4-byte cell of a checked-out buffer's data area, borrowed and put
     back at whatever value the store left there. *)
  Lemma bm_buf_word_acc (p : mword 64) (bno dsk : mword 32)
      (bs : list (bv 8)) (q : nat) :
    is_aligned_paddr (Physaddr (pa_add (b_data p) (4 * q)%nat)) 4 = true ->
    (q < 256)%nat ->
    buf_own p bno dsk bs -∗
      ⌜length bs = 1024%nat⌝ ∗
      (pa_add (b_data p) (4 * q)%nat ↦₄ bb_mk (fun j => bs !!! j) (4 * q)%nat) ∗
      (∀ w : mword 32,
         (pa_add (b_data p) (4 * q)%nat ↦₄ w) -∗
         buf_own p bno dsk ((bb_set (fun j => bs !!! j) (4 * q)%nat w)
                              <$> seq 0 1024)).
  Proof.
    intros Hal Hq.
    iIntros "(Hb & Hd & %Hlen & Hby)".
    iEval (rewrite (bb_bytes_of_list (b_data p) bs) Hlen) in "Hby".
    iDestruct (bb_word4_acc (b_data p) 1024 (4 * q)%nat (1024 - (4 * q + 4))%nat
                 (fun j => bs !!! j) ltac:(lia) Hal with "Hby") as "[Hw Hback]".
    iSplitR; [done|]. iSplitL "Hw"; [iExact "Hw"|].
    iIntros (w) "Hw". iDestruct ("Hback" $! w with "Hw") as "Hby".
    iEval (rewrite bb_bytes_to_list) in "Hby".
    rewrite /buf_own.
    iSplitL "Hb"; [iExact "Hb"|]. iSplitL "Hd"; [iExact "Hd"|].
    iSplitR; [iPureIntro; apply bb_fmap_len|]. iExact "Hby".
  Qed.

  (* slot-unit bookkeeping: bmap holds three and hands two to balloc, one
     to bread and one to log_write *)
  Lemma bm_slots_split (a c : nat) :
    bslots (a + c) -∗ bslots a ∗ bslots c.
  Proof. rewrite bslots_op. iIntros "$". Qed.

  Lemma bm_slots_join (a c : nat) :
    bslots a -∗ bslots c -∗ bslots (a + c).
  Proof.
    iIntros "H1 H2". rewrite bslots_op. iSplitL "H1"; [iExact "H1"|iExact "H2"].
  Qed.

  (* THE traveling-bytes swap: the whole of what bmap does to the buffer. *)
  Lemma bm_held_swap (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn V k pidv dev bno bs bsl bsd d -∗
      buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs ∗
      (∀ bs' : list (bv 8),
         buf_own (bpa k) bno (mword_of_int 0 : mword 32) bs' -∗
         bio_held bn V k pidv dev bno bs' bsl bsd d).
  Proof.
    rewrite /bio_held.
    iIntros "(%A & %B & %C & H1 & H3 & H4 & H5 & H6 & H7)".
    iSplitL "H5"; [iExact "H5"|].
    iIntros (bs') "H5".
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitL "H1"; [iExact "H1"|].
    iSplitL "H3"; [iExact "H3"|]. iSplitL "H4"; [iExact "H4"|].
    iSplitL "H5"; [iExact "H5"|]. iSplitL "H6"; [iExact "H6"|]. iExact "H7".
  Qed.

  Lemma bm_held_k (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsl bsd : list (bv 8)) (d : bool) :
    bio_held bn V k pidv dev bno bs bsl bsd d -∗ ⌜(k < NBUF)%nat⌝.
  Proof. rewrite /bio_held. iIntros "(%A & _)". done. Qed.

  (* THE COUPLING of the indirect arm: the caller's own [fsblock] half
     against the handle's machinery half pins the buffer's logical content.
     With [bio_locked] (bs = bsl) that is the BYTES, which is what makes the
     word the code reads out of [bp->data] be the entry list's entry. *)
  Lemma bm_held_content (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (pidv dv bno : mword 32)
      (bs bsl bsd bs0 : list (bv 8)) (d : bool) :
    fsblock γfs (uint bno) bs0 -∗
    bio_held bn (fs_view γfs γd dev cov) k pidv dv bno bs bsl bsd d -∗
    ⌜bsl = bs0⌝.
  Proof.
    rewrite /bio_held /bio_pay /fs_view /=.
    iIntros "Hc (_ & _ & _ & _ & _ & _ & _ & _ & Hpay)".
    destruct d.
    - iDestruct "Hpay" as "[Hm _]".
      iApply (fsblock_mdirty_agree with "Hc Hm").
    - iDestruct "Hpay" as "[Hm _]".
      iApply (fsblock_mclean_agree with "Hc Hm").
  Qed.

End BmapRes.
