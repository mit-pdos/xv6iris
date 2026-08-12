(* ProofWriteHead.v -- write_head over the SIE-agnostic sconf world.

     static void write_head(void) {
       struct buf *buf = bread(log.dev, log.start);
       struct logheader *hb = (struct logheader * ) buf->data;
       hb->n = log.lh.n;
       for (int i = 0; i < log.lh.n; i++) hb->block[i] = log.lh.block[i];
       bwrite(buf);
       brelse(buf);
     }

   THE SHAPE OF THE PROOF.  Three calls and one do-while copy loop, with a
   ghost step (the logged view's move at the header block's key) squeezed
   between the bwrite and the brelse.

   * THE HANDLE IS SPLIT ACROSS THE WHOLE BODY.  bread returns a
     [bio_locked] at some (bs0, bsd0, d0) -- the flag [d0] is NOT
     determined by this contract (the caller holds no dirty half for the
     header), and it never has to be: the proof is [d0]-generic.  The
     handle is split ONCE ([BioInv.bio_held_split]) into the payload-less
     [bio_hold0] and the payload's three pieces (the logged-view half, the
     dirty half at [d0], and -- only when [d0] -- the pinning reference).
     [bio_hold0] is what the stores edit and what bwrite consumes; the
     pieces ride untouched and are re-paired at the end, AFTER the write
     has made the disk value equal to the bytes, which is exactly when the
     clean payload's [bsd = bsl] tie can be re-established.

   * THE BYTES ARE CARRIED BY A NAMING FUNCTION.  [buf_own]'s byte list is
     traded for [bb_bytes] -- the [seq]-indexed, function-named window
     ByteBuf.v's algebra works on -- for the duration of the stores, and
     materialised back into a list ([f <$> seq 0 1024]) at the tail.  A
     4-byte store is [bb_word4_acc]: borrow the aligned word cell at offset
     [o], give it back holding [w], and the window's naming function
     becomes [bb_set f o w].  The only fact the tail needs about the final
     function is that its first four bytes spell [log.lh.n] -- which is
     [hdr_n] (LogInv.v) and the whole of the postcondition's content
     claim.  Nothing is said about the block list; that encoding is stage
     4's (claude-notes/design/fs-log.md).

   * THE LOOP is a fuel induction over the entries still to copy, with the
     two pointer cursors ([a4] = &log.lh.block[i], [a5] = buf + 4i) and the
     end sentinel [a2] = buf + 4n.  The exit test is a POINTER compare, so
     it reads back as an index compare through [ByteCursor.pa_add_eqb] --
     no no-wrap assumption on the buffer.  Both the loop's exit and the
     [blez] shortcut (n = 0) land at +0x46, so the tail is its own lemma.

   HART-GENERIC PROTOCOL.  Every callee returns through [wp_next b pj
   (fun CID => ...)]; the loop lemma therefore carries its own [CID0]
   binder and the continuation is re-anchored at each crossing with
   [WpSconfVc.wp_next_shift] -- [wh_cont] IS a [wp_next], so the generic
   lemma applies to it directly. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import VcGen.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto DiskInv.
Require Import WpLock.
Require Import SleepLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype WpSconfVc.
Require Import ByteCursor.
Require Import ByteBuf.
Require Import KstackArith.
Require Import FdSlots.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import CodeWriteHead.
Require Import SpecPanic.
Require Import SpecBread SpecBwrite SpecBrelse.
Require Import FsCrash.
Require Import SpecWriteHead.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  write_head's own pure vocabulary.  The general byte<->word window      *)
(*  algebra it runs on -- [bb_set] / [bb_mk] / [bb_bytes] / [bb_word4_acc] *)
(*  and the [bb_align_z] / [bb_uint32] side conditions -- lives in         *)
(*  ByteBuf.v; only what is specific to THIS function is below.  All of it *)
(*  is over plain [Z]/[nat], so no solver ever runs inside the WP context. *)
(* ===================================================================== *)

(* ---- the alignment of a word slot inside a buffer's data area:
   [bcache]'s geometry, then [ByteBuf.bb_align_z] ---- *)
Lemma wh_align_arith (kk qq : Z) :
  0 <= kk -> kk < 30 -> 0 <= qq -> qq <= 255 ->
  (2147582376 + 1112 * kk + (88 + 4 * qq)) `mod` 4 = 0
  /\ 0 <= 2147582376 + 1112 * kk + (88 + 4 * qq)
  /\ 2147582376 + 1112 * kk + (88 + 4 * qq) < 18446744073709551616.
Proof.
  intros H1 H2 H3 H4. split_and!; [| lia | lia].
  replace (2147582376 + 1112 * kk + (88 + 4 * qq))
    with ((536895616 + 278 * kk + qq) * 4) by lia.
  apply Z_mod_mult.
Qed.

Lemma wh_align4 (k q : nat) : (k < NBUF)%nat -> (q <= 255)%nat ->
  is_aligned_paddr (Physaddr (pa_add (b_data (bnode k)) (4 * q)%nat)) 4 = true.
Proof.
  intros Hk Hq.
  unfold b_data. rewrite pa_add_add.
  unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite RiscvExtras.uint_unsigned.
  rewrite ByteCursor.pa_add_unsigned.
  rewrite (bnode_unsigned k Hk).
  unfold buf_base, buf_stride, KernelSyms.bcache.
  destruct (wh_align_arith (Z.of_nat k) (Z.of_nat q)
              ltac:(lia) ltac:(unfold NBUF in Hk; lia) ltac:(lia) ltac:(lia))
    as (Hm & Hlo & Hhi).
  replace (0x80018190 + 24 + 1112 * Z.of_nat k + Z.of_nat (88 + 4 * q))
    with (2147582376 + 1112 * Z.of_nat k + (88 + 4 * Z.of_nat q)) by lia.
  apply bb_align_z; assumption.
Qed.

(* ---- pointer arithmetic the two cursors and the sentinel need ----
   ([pa_add p 0 = p] is [RiscvExtras.pa_add_0]; do not restate it) *)
Lemma wh_dst_addr (a : SailStdpp.Values.mword 64) (i : nat) :
  add_vec (pa_add a (4 * i)%nat) (mword_of_int 92 : SailStdpp.Values.mword 64)
  = pa_add (b_data a) (4 * S i)%nat.
Proof.
  assert (H92 : (mword_of_int 92 : SailStdpp.Values.mword 64)
                = mword_of_int (Z.of_nat 92%nat)) by (f_equal; lia).
  rewrite H92 pa_add_bump /b_data pa_add_add. f_equal. lia.
Qed.

Lemma wh_hdr_addr (a : SailStdpp.Values.mword 64) :
  add_vec a (mword_of_int 88 : SailStdpp.Values.mword 64)
  = pa_add (b_data a) (4 * 0)%nat.
Proof.
  rewrite /b_data pa_add_add.
  change (88 + 4 * 0)%nat with 88%nat. reflexivity.
Qed.

Lemma wh_cur_step (a : SailStdpp.Values.mword 64) (i : nat) :
  add_vec (pa_add a (4 * i)%nat) (mword_of_int 4 : SailStdpp.Values.mword 64)
  = pa_add a (4 * S i)%nat.
Proof.
  assert (H4 : (mword_of_int 4 : SailStdpp.Values.mword 64)
               = mword_of_int (Z.of_nat 4%nat)) by (f_equal; lia).
  rewrite H4 pa_add_bump. f_equal. lia.
Qed.

Lemma wh_blk_at (i : nat) :
  add_vec (lh_block i) (mword_of_int 0 : SailStdpp.Values.mword 64) = lh_block i.
Proof.
  assert (H0 : (mword_of_int 0 : SailStdpp.Values.mword 64)
               = mword_of_int (Z.of_nat 0%nat)) by reflexivity.
  rewrite /lh_block H0 pa_add_bump. f_equal. lia.
Qed.

Lemma wh_blk_step (i : nat) :
  add_vec (lh_block i) (mword_of_int 4 : SailStdpp.Values.mword 64) = lh_block (S i).
Proof.
  assert (H4 : (mword_of_int 4 : SailStdpp.Values.mword 64)
               = mword_of_int (Z.of_nat 4%nat)) by (f_equal; lia).
  rewrite /lh_block H4 pa_add_bump. f_equal. lia.
Qed.

Lemma wh_ptr_eqb (p : SailStdpp.Values.mword 64) (a b : nat) :
  (a <= 4096)%nat -> (b <= 4096)%nat ->
  eq_vec (pa_add p a) (pa_add p b) = Nat.eqb a b.
Proof. intros Ha Hb. apply ByteCursor.pa_add_eqb; lia. Qed.

(* the ONE content fact the postcondition states: the header's [n] field *)
Lemma wh_take4 (f : nat -> bv 8) (nn : SailStdpp.Values.mword 32) :
  (forall j, (j < 4)%nat -> f j = nth_byte nn j) ->
  hdr_n (f <$> seq 0 1024) = bv_unsigned nn.
Proof.
  intro Hf. rewrite /hdr_n.
  assert (Htk : take 4 (f <$> seq 0 1024)
                = [f 0%nat; f 1%nat; f 2%nat; f 3%nat]).
  { rewrite -fmap_take.
    assert (Hs : take 4 (seq 0 1024) = seq 0 4) by (vm_compute; reflexivity).
    rewrite Hs. reflexivity. }
  rewrite Htk. apply (bb_word_bytes _ nn); [reflexivity|].
  intros j Hj. destruct j as [|[|[|[|j']]]]; cbn; try (apply Hf; lia). lia.
Qed.

(* ---- THE FULL HEADER ENCODING (phase C2b/D1 stage 4).  [wh_take4] above
   reads the [int n] field out of the assembled window; the commit fupd needs
   the WHOLE decoding, so the same argument is run at every 4-byte offset the
   copy loop wrote.  All of it is over plain [nat]/[Z] lists, so no solver
   ever sees a [bv]. ---- *)

(* the 4-byte window at [o], as a literal list -- the offset-parametric twin
   of the [take 4 (seq 0 1024)] step inside [wh_take4] *)
Lemma wh_win4 (f : nat -> bv 8) (len o : nat) :
  (o + 4 <= len)%nat ->
  take 4 (drop o (f <$> seq 0 len))
  = [f o; f (S o); f (S (S o)); f (S (S (S o)))].
Proof.
  intro Ho. rewrite -fmap_drop -fmap_take drop_seq take_seq.
  replace (4 `min` (len - o))%nat with 4%nat by lia.
  replace (0 + o)%nat with o by lia. reflexivity.
Qed.

(* [wh_take4] at an arbitrary aligned offset *)
Lemma wh_take4_at (f : nat -> bv 8) (nn : SailStdpp.Values.mword 32) (o : nat) :
  (o + 4 <= 1024)%nat ->
  (forall j, (j < 4)%nat -> f (o + j)%nat = nth_byte nn j) ->
  assemble_bytes (take 4 (drop o (f <$> seq 0 1024))) = bv_unsigned nn.
Proof.
  intros Ho Hf. rewrite (wh_win4 f 1024 o Ho).
  apply (bb_word_bytes _ nn); [reflexivity|].
  intros j Hj.
  assert (H0 : f o = nth_byte nn 0%nat)
    by (rewrite -(Hf 0%nat ltac:(lia)); f_equal; lia).
  assert (H1 : f (S o) = nth_byte nn 1%nat)
    by (rewrite -(Hf 1%nat ltac:(lia)); f_equal; lia).
  assert (H2 : f (S (S o)) = nth_byte nn 2%nat)
    by (rewrite -(Hf 2%nat ltac:(lia)); f_equal; lia).
  assert (H3 : f (S (S (S o))) = nth_byte nn 3%nat)
    by (rewrite -(Hf 3%nat ltac:(lia)); f_equal; lia).
  destruct j as [|[|[|[|j']]]]; cbn; [exact H0|exact H1|exact H2|exact H3|lia].
Qed.

Lemma wh_uint32 (a : SailStdpp.Values.mword 32) : uint a = bv_unsigned a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [ reflexivity | lia ].
Qed.

Lemma wh_fmap_seq_ext {A : Type} (g h : nat -> A) (n : nat) :
  (forall i, (i < n)%nat -> g i = h i) -> g <$> seq 0 n = h <$> seq 0 n.
Proof.
  intro Hgh. apply list_eq. intro k. rewrite !list_lookup_fmap.
  destruct (decide (k < n)%nat) as [Hk|Hk].
  - rewrite (lookup_seq_lt 0 n k Hk) /=. by rewrite (Hgh k Hk).
  - rewrite (lookup_seq_ge 0 n k ltac:(lia)) //.
Qed.

Lemma wh_map_uint_seq (W : list (SailStdpp.Values.mword 32)) :
  map uint W = (fun i => uint (W !!! i)) <$> seq 0 (length W).
Proof.
  apply list_eq. intro k. rewrite list_lookup_fmap list_lookup_fmap.
  destruct (decide (k < length W)%nat) as [Hk|Hk].
  - rewrite (lookup_seq_lt 0 (length W) k Hk) /=.
    destruct (lookup_lt_is_Some_2 W k Hk) as [w Hw].
    rewrite Hw /= (list_lookup_total_alt W k) Hw //.
  - rewrite (lookup_seq_ge 0 (length W) k ltac:(lia))
            (lookup_ge_None_2 W k ltac:(lia)) //.
Qed.

(* THE POSTCONDITION'S ENCODING FACT: the window the copy loop assembled
   decodes to exactly the in-memory header [(n, W)].  [Hf4] is the [n] field
   ([wh_take4]'s hypothesis, unchanged) and [Henc] is the loop's strengthened
   invariant: entry [i'] went to the word at byte offset [4 * S i']. *)
Lemma wh_hdr_dec (f : nat -> bv 8) (n : nat) (W : list (SailStdpp.Values.mword 32)) :
  n = length W -> (n <= LOGBLOCKS)%nat ->
  (forall jj, (jj < 4)%nat ->
     f jj = nth_byte (mword_of_int (Z.of_nat n) : SailStdpp.Values.mword 32) jj) ->
  (forall i' jj, (i' < n)%nat -> (jj < 4)%nat ->
     f (4 * S i' + jj)%nat = nth_byte (W !!! i') jj) ->
  hdr_dec (f <$> seq 0 1024) = (n, map uint W).
Proof.
  intros HnW HnB Hf4 Henc.
  assert (Hn : hdr_n (f <$> seq 0 1024) = Z.of_nat n).
  { rewrite (wh_take4 f (mword_of_int (Z.of_nat n) : SailStdpp.Values.mword 32) Hf4).
    apply moi32_small. unfold LOGBLOCKS in HnB.
    change (2 ^ 32)%Z with 4294967296%Z. lia. }
  rewrite /hdr_dec le_word_0 Hn Nat2Z.id. f_equal.
  rewrite wh_map_uint_seq -HnW.
  apply wh_fmap_seq_ext. intros i Hi.
  rewrite /le_word.
  rewrite (wh_take4_at f (W !!! i) (4 * S i)%nat
             ltac:(clear -Hi HnB; unfold LOGBLOCKS in HnB; lia)
             ltac:(intros jj Hjj; exact (Henc i jj Hi Hjj))).
  symmetry. apply wh_uint32.
Qed.

(* ---- the small-literal register facts ---- *)
Lemma wh_sext_n (n : nat) : (n <= 30)%nat ->
  (sign_extend' 64 (mword_of_int (Z.of_nat n) : SailStdpp.Values.mword 32)
   : SailStdpp.Values.mword 64) = mword_of_int (Z.of_nat n).
Proof.
  intro H. do 31 (destruct n as [|n]; [apply bv_eq; vm_compute; reflexivity|]). lia.
Qed.

Lemma wh_slli2 (i : nat) : (i <= 30)%nat ->
  shift_bits_left (mword_of_int (Z.of_nat i) : SailStdpp.Values.mword 64)
    (subrange_vec_dec (mword_of_int 2 : SailStdpp.Values.mword 6) (Z.sub log2_xlen 1) 0)
  = mword_of_int (4 * Z.of_nat i).
Proof.
  intro H. do 31 (destruct i as [|i]; [apply bv_eq; vm_compute; reflexivity|]). lia.
Qed.

Lemma wh_geb_s0 (b : Z) :
  0 <= b < 2 ^ 31 ->
  zopz0zKzJ_s (zero_reg : SailStdpp.Values.mword 64)
              (mword_of_int b : SailStdpp.Values.mword 64) = Z.geb 0 b.
Proof.
  intro Hb. unfold zopz0zKzJ_s.
  assert (Hz : sint (zero_reg : SailStdpp.Values.mword 64) = 0)
    by (vm_compute; reflexivity).
  rewrite Hz.
  rewrite (sint_moi_small b ltac:(change (2^63) with 9223372036854775808; lia)).
  reflexivity.
Qed.

(* ---- the three [struct log] cell addresses the code forms ---- *)
Lemma wh_l_start : add_vec (log_addr : SailStdpp.Values.mword 64)
                     (mword_of_int 24 : SailStdpp.Values.mword 64) = l_start.
Proof. reflexivity. Qed.
Lemma wh_l_dev : add_vec (log_addr : SailStdpp.Values.mword 64)
                     (mword_of_int 36 : SailStdpp.Values.mword 64) = l_dev.
Proof. reflexivity. Qed.
Lemma wh_l_lhn : add_vec (log_addr : SailStdpp.Values.mword 64)
                     (mword_of_int 44 : SailStdpp.Values.mword 64) = lh_n_pa.
Proof. reflexivity. Qed.

(* ---- the sign-extended immediates write_head forms ---- *)
Lemma wh_s0 : sign_extend' 64 (mword_of_int 0 : SailStdpp.Values.mword 12)
              = (mword_of_int 0 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma wh_s24 : sign_extend' 64 (mword_of_int 24 : SailStdpp.Values.mword 12)
               = (mword_of_int 24 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma wh_s36 : sign_extend' 64 (mword_of_int 36 : SailStdpp.Values.mword 12)
               = (mword_of_int 36 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma wh_s44 : sign_extend' 64 (mword_of_int 44 : SailStdpp.Values.mword 12)
               = (mword_of_int 44 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma wh_s88 : sign_extend' 64 (mword_of_int 88 : SailStdpp.Values.mword 12)
               = (mword_of_int 88 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma wh_s92 : sign_extend' 64 (mword_of_int 92 : SailStdpp.Values.mword 12)
               = (mword_of_int 92 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma wh_s4c : sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : SailStdpp.Values.mword 6))
               = (mword_of_int 4 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ===================================================================== *)

Module WriteHeadProof (BR : BREAD) (BW : BWRITE) (BL : BRELSE) : WRITE_HEAD.


Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne := reg_ne_side.

Local Ltac whidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Section WriteHeadDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* ---------------------------------------------------------------- *)
  (*  the payload-less handle, with its bytes in window form            *)
  (* ---------------------------------------------------------------- *)
  Definition wh_hold (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (f : nat -> bv 8) (bsd : list (bv 8)) : iProp Σ :=
    (⌜(k < NBUF)%nat⌝ ∗
     ⌜uint bno ∈ bv_cov V⌝ ∗
     ⌜dev = bv_dev V⌝ ∗
     sleeplocked (snd (bn_slk bn k)) ∗
     sl_pid (buf_lock (bnode k)) ↦₄ pidv ∗
     b_valid (bnode k) ↦₄ (mword_of_int 1 : mword 32) ∗
     b_dev (bnode k) ↦₄{DfracOwn (1/2)} dev ∗
     b_blockno (bnode k) ↦₄{DfracOwn (1/2)} bno ∗
     b_disk (bnode k) ↦₄ (mword_of_int 0 : mword 32) ∗
     bb_bytes (b_data (bnode k)) 1024 f ∗
     disk_block (bv_gd V) (uint bno) bsd)%I.

  Lemma wh_hold_of (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (bs bsd : list (bv 8)) :
    bio_hold0 bn V k pidv dev bno bs bsd -∗
    wh_hold bn V k pidv dev bno (fun j => bs !!! j) bsd.
  Proof.
    rewrite /bio_hold0 /wh_hold /buf_own /bpa.
    iIntros "(%A & %B & %C & H1 & H2 & H3 & H4 & (Hb & Hd & %Hlen & Hby) & H6)".
    iEval (rewrite (bb_bytes_of_list (b_data (bnode k)) bs) Hlen) in "Hby".
    (* NEVER [iFrame] a goal mentioning [bb_bytes]: the framing search walks
       into the 1024-element [seq] big-op and does not come back. *)
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitL "H1"; [iExact "H1"|]. iSplitL "H2"; [iExact "H2"|].
    iSplitL "H3"; [iExact "H3"|]. iSplitL "H4"; [iExact "H4"|].
    iSplitL "Hb"; [iExact "Hb"|]. iSplitL "Hd"; [iExact "Hd"|].
    iSplitL "Hby"; [iExact "Hby"|]. iExact "H6".
  Qed.

  Lemma wh_hold_to (bn : bio_names) (V : bio_view Σ) (k : nat)
      (pidv dev bno : mword 32) (f : nat -> bv 8) (bsd : list (bv 8)) :
    wh_hold bn V k pidv dev bno f bsd -∗
    bio_hold0 bn V k pidv dev bno (f <$> seq 0 1024) bsd.
  Proof.
    rewrite /bio_hold0 /wh_hold /buf_own /bpa.
    iIntros "(%A & %B & %C & H1 & H2 & H3 & H4 & Hb & Hd & Hby & H6)".
    iEval (rewrite bb_bytes_to_list) in "Hby".
    iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
    iSplitL "H1"; [iExact "H1"|]. iSplitL "H2"; [iExact "H2"|].
    iSplitL "H3"; [iExact "H3"|]. iSplitL "H4"; [iExact "H4"|].
    (* [buf_own] is one parenthesised group, so peel it off whole first *)
    iSplitR "H6"; [| iExact "H6"].
    iSplitL "Hb"; [iExact "Hb"|]. iSplitL "Hd"; [iExact "Hd"|].
    iSplitR; [iPureIntro; apply bb_fmap_len|]. iExact "Hby".
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  the payload, split into pieces that survive the write            *)
  (* ---------------------------------------------------------------- *)
  Lemma wh_pay_split (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (dv bno : mword 32)
      (bsl bsd : list (bv 8)) (d : bool) :
    bio_pay bn (fs_view γfs γd dev cov) k dv bno bsl bsd d -∗
    (uint bno ↪[fs_L γfs]{#(1/2)} bsl ∗
     uint bno ↪[fs_dirty γfs]{#(1/2)} d ∗
     (if d then ∃ q : Qp, bref bn k q dv bno else True)).
  Proof.
    rewrite /bio_pay /fs_view /=. destruct d.
    - rewrite /fs_mdirty. iIntros "[[$ $] $]".
    - rewrite /fs_mclean. iIntros "[[$ $] _]"; try done.
  Qed.

  Lemma wh_pay_mk (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (dv bno : mword 32)
      (bs : list (bv 8)) (d : bool) :
    (uint bno ↪[fs_L γfs]{#(1/2)} bs) -∗
    (uint bno ↪[fs_dirty γfs]{#(1/2)} d) -∗
    (if d then ∃ q : Qp, bref bn k q dv bno else True) -∗
    bio_pay bn (fs_view γfs γd dev cov) k dv bno bs bs d.
  Proof.
    rewrite /bio_pay /fs_view /=. destruct d.
    - rewrite /fs_mdirty. iIntros "H1 H2 H3". iFrame.
    - rewrite /fs_mclean. iIntros "H1 H2 _". iFrame; try done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  the continuation, the frame and the register threading            *)
  (* ---------------------------------------------------------------- *)
  Definition wh_cont `{GEN : GenId} `{CID0 : CpuId} 
      (γfs : fs_names) (bn : bio_names) (logstart : Z) (n : nat)
      (W : list (mword 32)) (L : gmap Z (list (bv 8)))
      (pidv : mword 32) (dq : dfrac) (j : nat)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (Q : iProp Σ) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (bs' : list (bv 8)),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) C b -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
        ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) -∗
        ghost_map_auth (fs_L γfs) 1 (<[log_hdr_bno logstart := bs']> L) -∗
        fsblock γfs (log_hdr_bno logstart) bs' -∗
        ⌜hdr_n bs' = Z.of_nat n⌝ -∗
        ⌜hdr_dec bs' = (n, map uint W)⌝ -∗
        bslot bn -∗
        ▷ Q -∗
        WP (Loop : expr riscv_lang))%I.

  (* the four frame slots: ra@24, s0@16, s1@8, s2@0 *)
  Definition wh_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈ (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈ (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈ (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈ (m !!! Regidx Rs2 : mword 64))%I.

  (* what every block knows about its arrival map *)
  Definition wh_regs (m M : regfile) : Prop :=
    M !!! Regidx csp_rs1
      = add_vec (m !!! Regidx csp_rs1 : mword 64)
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
    /\ (forall c : mword 5, is_cs_idx c = true ->
          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
          M !!! Regidx c = (m !!! Regidx c : mword 64)).

End WriteHeadDefs.

(* ===================================================================== *)
(*  THE BLOCKS.  Each carries its own [CID0] binder, so a block whose     *)
(*  predecessor returned on a different hart is applied at the hart it    *)
(*  actually starts on.                                                   *)
(* ===================================================================== *)
Section WriteHeadBlocks.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* ================================================================== *)
  (*  +0x46 .. +0x5c : bwrite, the logged-view move, brelse, epilogue.   *)
  (*  Entered from the loop's exit AND from the [blez] shortcut (n = 0). *)
  (* ================================================================== *)
  Local Lemma wh_tail `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (n : nat) (W : list (mword 32)) (L : gmap Z (list (bv 8)))
      (pidv : mword 32) (dq : dfrac)
      (k : nat) (bno : mword 32) (bsh bs0 bsd0 : list (bv 8)) (d0 : bool)
      (f : nat -> bv 8)
      (m M : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool) (Q : iProp Σ) :
    (K_write_head <= K)%nat ->
    (uint bno < 2147483648)%Z ->
    uint bno = logstart ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    n = length W ->
    (n <= LOGBLOCKS)%nat ->
    (k < NBUF)%nat ->
    (forall jj, (jj < 4)%nat ->
       f jj = nth_byte (mword_of_int (Z.of_nat n) : mword 32) jj) ->
    (* THE COPY LOOP'S OTHER HALF: entry [i'] sits in the word at byte
       offset [4 * S i'].  Together with the line above this is the whole
       on-disk encoding ([wh_hdr_dec]). *)
    (forall i' jj, (i' < n)%nat -> (jj < 4)%nat ->
       f (4 * S i' + jj)%nat = nth_byte (W !!! i') jj) ->
    wh_regs m M ->
    M !!! Regidx Rs1 = bnode k ->
    sie_cap_gpr M (K - 4)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) C b -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.write_head + 0x46) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wh_frame m -∗
    wh_hold bn (fs_view γfs γd dev cov) k pidv dev bno f bsd0 -∗
    (logstart ↪[fs_L γfs]{#(1/2)} bs0) -∗
    (logstart ↪[fs_dirty γfs]{#(1/2)} d0) -∗
    (if d0 then ∃ q : Qp, bref bn k q dev bno else True) -∗
    ghost_map_auth (fs_L γfs) 1 L -∗
    fsblock γfs (log_hdr_bno logstart) bsh -∗
    lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
    ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) -∗
    (∀ bs' : list (bv 8), ⌜length bs' = 1024%nat⌝ -∗ ⌜hdr_n bs' = Z.of_nat n⌝ -∗
       ⌜hdr_dec bs' = (n, map uint W)⌝ -∗
       disk_write_permit gen_id (Some ((1024 * log_hdr_bno logstart)%Z, bs')) Q) -∗
    wh_cont (CID0 := CID0)  γfs bn logstart n W L pidv dq j m K eb C b Q -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hbnolt Hbnou Hj Hgl HnW HnB Hk Hf4 Henc Hregs HMs1.
    pose proof Hregs as (Hsp & Hthr).
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio Hppid #Hprocs
              #Hdevi #Hdgeom #Hdlock Hframe Hhold HpL HpD Hextra HLauth Hfsb
              Hncell HW Hperm Hcont".
    (* LEVEL 0 TIES THE TWO INDICES: write_head never push_off's, so its
       [cpu_own]'s [n] is [0] throughout and [cpu_own_eb_agree] gives
       [eb = b] outright (kept as a hypothesis, not [subst] -- [b] is still
       the index every leaf instruction rule below is stated at); the
       [_ext_transport] guards are spelled at [eb], so this is what lets
       [wp_next_chain] close them off the SAME per-step facts [b]'s
       transports use. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    cbn in Hbm.
    iPoseProof (whi_46 with "Htext") as "Hi46".
    iPoseProof (whi_48 with "Htext") as "Hi48".
    iPoseProof (whi_4c with "Htext") as "Hi4c".
    iPoseProof (whi_4e with "Htext") as "Hi4e".
    (* ===== +0x46 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.write_head + 0x46)) Ra0 Rs1
              M (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (T1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget M Rs1))]> M).
    assert (HT1a0 : T1 !!! Regidx Ra0 = bnode k).
    { rewrite /T1 upd_eq. rgne. rewrite HMs1. apply add_vec_zero_l. }
    assert (HT1s1 : T1 !!! Regidx Rs1 = bnode k)
      by (rewrite /T1 upd_ne; [exact HMs1 | vm_compute; discriminate]).
    assert (HT1sp : T1 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite /T1 upd_ne; [exact Hsp | vm_compute; discriminate]).
    assert (HT1thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              T1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T1 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18). }
    assert (Hpp48 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x46) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x48))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp48) in "Hpc".
    (* ===== +0x48 jal ra,bwrite ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.write_head + 0x48)) Rra
              (mword_of_int 2093456 : mword 21) T1 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi48 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc".
    set (T2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.write_head + 0x48) : mword 64) 4)]> T1).
    assert (Htgtbw : add_vec (mword_of_int (KernelSyms.write_head + 0x48) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093456 : mword 21))
                     = mword_of_int KernelSyms.bwrite)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtbw) in "Hpc".
    assert (HT2a0 : T2 !!! Regidx Ra0 = bnode k)
      by (rewrite /T2 upd_ne; [exact HT1a0 | vm_compute; discriminate]).
    assert (HT2s1 : T2 !!! Regidx Rs1 = bnode k)
      by (rewrite /T2 upd_ne; [exact HT1s1 | vm_compute; discriminate]).
    assert (HT2sp : T2 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    assert (HT2ra : T2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.write_head + 0x48) : mword 64) 4)
      by (rewrite /T2; apply upd_eq).
    assert (HT2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              T2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T2 upd_ne; [| regne]. exact (HT1thr c Hcs N2 N8 N9 N18). }
    iDestruct (wh_hold_to with "Hhold") as "Hhold".
    iDestruct (cpu_own_transport CID0 CID2 0 eb (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID2 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID2 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID2) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbw : (K_bwrite <= K - 4)%nat)
      by (unfold K_bwrite, K_write_head in *; lia).
    (* the header image's [n] field, needed HERE (the permit is deposited at
       the bwrite, not at the return) *)
    assert (Hhn_early : hdr_n (f <$> seq 0 1024) = Z.of_nat n).
    { rewrite (wh_take4 f (mword_of_int (Z.of_nat n) : mword 32) Hf4).
      apply moi32_small.
      unfold LOGBLOCKS in HnB.
      change (2 ^ 32)%Z with 4294967296%Z. lia. }
    assert (Hdec_early : hdr_dec (f <$> seq 0 1024) = (n, map uint W))
      by exact (wh_hdr_dec f n W HnW HnB Hf4 Henc).
    iApply (BW.wp_bwrite_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) k pidv dev bno dq T2 (K - 4)%nat eb C
              (f <$> seq 0 1024) bsd0 b Q
              HKbw Hbnolt eq_refl Hj Hgl Hk HT2a0
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hhold [Hperm] [-]").
    (* THE CALLER'S OWN PERMIT, at the header image this function assembled
       (phase C2b/D1 stage 3).  [Hbnou] is what makes the two spellings of
       the block number agree: the contract states the write's index at
       [log_hdr_bno logstart], the bread/bwrite pair at [uint bno]. *)
    { rewrite Hbnou. iApply ("Hperm" $! (f <$> seq 0 1024)).
      { iPureIntro. rewrite length_fmap length_seq. reflexivity. }
      { iPureIntro. exact Hhn_early. }
      iPureIntro. exact Hdec_early. }
    iIntros (CID3 Hs3 mB) "%Hcs1 Hcg Hcnt Hextc Hextm Hpc Hppid Hhold HQ".
    assert (Hpc4c : ret_pc (T2 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.write_head + 0x4c)).
    { rewrite HT2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc4c) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs1 : mB !!! Regidx Rs1 = bnode k)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs1 ltac:(vm_compute; reflexivity));
          exact HT2s1).
    assert (HmBsp : mB !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HT2sp).
    assert (HmBthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              mB !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs). exact (HT2thr c Hcs N2 N8 N9 N18). }
    (* ---- THE GHOST STEP: the logged view moves at the header's key ---- *)
    iMod (fsblock_update γfs L (log_hdr_bno logstart) bsh (f <$> seq 0 1024) bs0
            with "HLauth Hfsb HpL") as "((%Hbs0 & %Hlk) & HLauth & Hfsb & HpL)".
    (* ---- and the payload is re-paired at the written bytes ---- *)
    iEval (rewrite -Hbnou) in "HpL".
    iEval (rewrite -Hbnou) in "HpD".
    iDestruct (wh_pay_mk bn γfs γd dev cov k dev bno (f <$> seq 0 1024) d0
                 with "HpL HpD Hextra") as "Hpay".
    iAssert (bio_locked bn (fs_view γfs γd dev cov) k pidv dev bno
               (f <$> seq 0 1024) (f <$> seq 0 1024) d0) with "[Hhold Hpay]" as "Hlk".
    { rewrite /bio_locked bio_held_split.
      iSplitL "Hhold"; [iExact "Hhold" | iExact "Hpay"]. }
    (* ===== +0x4c c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.write_head + 0x4c)) Ra0 Rs1
              mB (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4c [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (T3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mB Rs1))]> mB).
    assert (HT3a0 : T3 !!! Regidx Ra0 = bnode k).
    { rewrite /T3 upd_eq. rgne. rewrite HmBs1. apply add_vec_zero_l. }
    assert (HT3sp : T3 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite /T3 upd_ne; [exact HmBsp | vm_compute; discriminate]).
    assert (HT3thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              T3 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T3 upd_ne; [| regne]. exact (HmBthr c Hcs N2 N8 N9 N18). }
    assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.write_head + 0x4c) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x4e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4e) in "Hpc".
    (* ===== +0x4e jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.write_head + 0x4e)) Rra
              (mword_of_int 2093500 : mword 21) T3 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4e [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    set (T4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.write_head + 0x4e) : mword 64) 4)]> T3).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.write_head + 0x4e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093500 : mword 21))
                     = mword_of_int KernelSyms.brelse)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HT4a0 : T4 !!! Regidx Ra0 = bnode k)
      by (rewrite /T4 upd_ne; [exact HT3a0 | vm_compute; discriminate]).
    assert (HT4sp : T4 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite /T4 upd_ne; [exact HT3sp | vm_compute; discriminate]).
    assert (HT4ra : T4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.write_head + 0x4e) : mword 64) 4)
      by (rewrite /T4; apply upd_eq).
    assert (HT4thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              T4 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T4 upd_ne; [| regne]. exact (HT3thr c Hcs N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID3 CID5 0 eb (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* [Hextc]/[Hextm] are not part of brelse's own contract, so brelse's
       internal crossing (CID5 -> CID6) leaves them STRANDED at CID5 here --
       carried this far (CID3 -> CID5) and no further; the transport past
       brelse has to span the WIDER range CID5 -> (the next hart they are
       needed at), not brelse's own CID5 -> CID6. *)
    iDestruct (trap_csrs_ext_transport CID3 CID5 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID3 CID5 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID2) (CIDb := CID5) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbl : (K_brelse <= K - 4)%nat)
      by (unfold K_brelse, K_write_head in *; lia).
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) k pidv dev bno dq
              T4 (K - 4)%nat eb (proc_addr j) C
              (f <$> seq 0 1024) (f <$> seq 0 1024) d0 b
              HKbl Hk HT4a0
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs Hlk [-]").
    iIntros (CID6 Hs6 mR) "%Hcs2 Hcg Hcnt Hpc Hppid Hslot".
    assert (Hpc52 : ret_pc (T4 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.write_head + 0x52)).
    { rewrite HT4ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc52) in "Hpc".
    pose proof Hcs2 as Hcs2_cs.
    assert (HmRsp : mR !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HT4sp).
    assert (HmRthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              mR !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs2_cs c Hcs). exact (HT4thr c Hcs N2 N8 N9 N18). }
    (* ===== EPILOGUE ===== *)
    iPoseProof (whi_52 with "Htext") as "Hi52".
    iPoseProof (whi_54 with "Htext") as "Hi54".
    iPoseProof (whi_56 with "Htext") as "Hi56".
    iPoseProof (whi_58 with "Htext") as "Hi58".
    iPoseProof (whi_5a with "Htext") as "Hi5a".
    iPoseProof (whi_5c with "Htext") as "Hi5c".
    rewrite /wh_frame.
    iDestruct "Hframe" as "(Hr24 & Hr16 & Hr8 & Hr0)".
    assert (Hc1 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hc2 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hc3 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hc4 : add_vec (mR !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HmRsp. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x52 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.write_head + 0x52)) (mword_of_int 3 : mword 6) Rra
              mR (K - 4)%nat (m !!! Regidx Rra : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi52 [Hr24] [-]").
    { iEval (rewrite Hc1). iExact "Hr24". }
    iIntros (CID7 Hs7) "Hcg Hpc Hr24".
    iEval (rewrite Hc1) in "Hr24".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mR).
    assert (HP1sp : P1 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite /P1 upd_ne; [exact HmRsp | vm_compute; discriminate]).
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x52) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x54))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    (* +0x54 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.write_head + 0x54)) (mword_of_int 2 : mword 6) Rs0
              P1 (K - 4)%nat (m !!! Regidx Rs0 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 [Hr16] [-]").
    { iEval (rewrite HP1sp -HmRsp Hc2). iExact "Hr16". }
    iIntros (CID8 Hs8) "Hcg Hpc Hr16".
    iEval (rewrite HP1sp -HmRsp Hc2) in "Hr16".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x54) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x56))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    (* +0x56 c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.write_head + 0x56)) (mword_of_int 1 : mword 6) Rs1
              P2 (K - 4)%nat (m !!! Regidx Rs1 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56 [Hr8] [-]").
    { iEval (rewrite HP2sp -HmRsp Hc3). iExact "Hr8". }
    iIntros (CID9 Hs9) "Hcg Hpc Hr8".
    iEval (rewrite HP2sp -HmRsp Hc3) in "Hr8".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x56) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x58))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58) in "Hpc".
    (* +0x58 c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.write_head + 0x58)) (mword_of_int 0 : mword 6) Rs2
              P3 (K - 4)%nat (m !!! Regidx Rs2 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58 [Hr0] [-]").
    { iEval (rewrite HP3sp -HmRsp Hc4). iExact "Hr0". }
    iIntros (CID10 Hs10) "Hcg Hpc Hr0".
    iEval (rewrite HP3sp -HmRsp Hc4) in "Hr0".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : P4 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite /P4 upd_ne; [exact HP3sp | vm_compute; discriminate]).
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.write_head + 0x58) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x5a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    (* +0x5a c.addi16sp sp,32 : pop the frame *)
    assert (Hwv : add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP4sp. apply frame_cancel_32. }
    assert (Hpop : (P4 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HP4sp. unfold pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own (m !!! Regidx csp_rs1 : mword 64) 4)
      with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iExists _; iExact "Hr8"|].
      iSplitL "Hr0";  [iExists _; iExact "Hr0"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.write_head + 0x5a))
              (mword_of_int 2 : mword 6) P4 (K - 4)%nat 4 b Hpop
              with "Hcg Hpc Hi5a Hframe4 [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (P5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> P4).
    assert (Hnk : ((K - 4) + 4)%nat = K) by (unfold K_write_head in HK; lia).
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.write_head + 0x5a) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x5c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* +0x5c c.ret *)
    assert (HP5ra : P5 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.write_head + 0x5c)) Rra P5 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi5c [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P5 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP5ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== POSTCONDITION ===== *)
    assert (Csp : P5 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite /P5 upd_eq. exact Hwv. }
    assert (Cs0 : P5 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : P5 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_eq. reflexivity. }
    assert (Cs2 : P5 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_eq. reflexivity. }
    assert (Hfin : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              P5 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /P5 upd_ne; [| regne]. rewrite /P4 upd_ne; [| regne].
      rewrite /P3 upd_ne; [| regne]. rewrite /P2 upd_ne; [| regne].
      rewrite /P1 upd_ne; [| regne].
      exact (HmRthr c Hcs N2 N8 N9 N18). }
    assert (Cs3 : P5 !!! Regidx (mword_of_int 19 : mword 5)
                  = (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; whidx).
    assert (Cs4 : P5 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; whidx).
    assert (Cs5 : P5 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; whidx).
    assert (Cs6 : P5 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; whidx).
    assert (Cs7 : P5 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; whidx).
    assert (Cs8 : P5 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; whidx).
    assert (Cs9 : P5 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; whidx).
    assert (Cs10 : P5 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; whidx).
    assert (Cs11 : P5 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; whidx).
    assert (Hhn : hdr_n (f <$> seq 0 1024) = Z.of_nat n).
    { rewrite (wh_take4 f (mword_of_int (Z.of_nat n) : mword 32) Hf4).
      apply moi32_small.
      unfold LOGBLOCKS in HnB.
      change (2 ^ 32)%Z with 4294967296%Z. lia. }
    iDestruct (cpu_own_transport CID6 CID12 0 eb (proc_addr j) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* [Hextc]/[Hextm] were stranded at CID5 by brelse's own crossing
       (CID5 -> CID6): span the whole CID5 -> CID12 range here, not just
       CID6 -> CID12. *)
    iDestruct (trap_csrs_ext_transport CID5 CID12 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID5 CID12 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    rewrite /wh_cont.
    iSpecialize ("Hcont" $! CID12 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P5 (f <$> seq 0 1024) with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid
                     Hncell HW HLauth Hfsb [%] [%] Hslot HQ").
    { unfold callee_saved. repeat split; assumption. }
    { exact Hhn. }
    { exact Hdec_early. }
  Qed.

  (* ================================================================== *)
  (*  +0x3a .. +0x42 : the header-copy do-while.                        *)
  (*    top   +0x3a  lw a3,0(a4)                                        *)
  (*          +0x3c  sw a3,92(a5)                                       *)
  (*    bump  +0x3e / +0x40                                             *)
  (*    back  +0x42  bne a5,a2 -> +0x3a                                 *)
  (*    exit  +0x46  (fall-through, into [wh_tail])                     *)
  (*  A fuel induction on the entries still to copy; the exit test is a  *)
  (*  POINTER compare read back as an index compare.                    *)
  (* ================================================================== *)
  Local Lemma wh_loop `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (n : nat) (W : list (mword 32)) (L : gmap Z (list (bv 8)))
      (pidv : mword 32) (dq : dfrac)
      (kk : nat) (bno : mword 32) (bsh bs0 bsd0 : list (bv 8)) (d0 : bool)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool) (fuel : nat)
      (Q : iProp Σ) :
    (K_write_head <= K)%nat ->
    (uint bno < 2147483648)%Z ->
    uint bno = logstart ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    n = length W ->
    (n <= LOGBLOCKS)%nat ->
    (kk < NBUF)%nat ->
    forall (i : nat) (M : regfile) (f : nat -> bv 8),
    (i < n)%nat ->
    (n - i <= fuel)%nat ->
    (forall jj, (jj < 4)%nat ->
       f jj = nth_byte (mword_of_int (Z.of_nat n) : mword 32) jj) ->
    (* the ENCODING invariant: every entry copied so far is in its word *)
    (forall i' jj, (i' < i)%nat -> (jj < 4)%nat ->
       f (4 * S i' + jj)%nat = nth_byte (W !!! i') jj) ->
    wh_regs m M ->
    M !!! Regidx Rs1 = bnode kk ->
    M !!! Regidx Ra4 = lh_block i ->
    M !!! Regidx Ra5 = pa_add (bnode kk) (4 * i)%nat ->
    M !!! Regidx Ra2 = pa_add (bnode kk) (4 * n)%nat ->
    sie_cap_gpr M (K - 4)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) C b -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.write_head + 0x3a) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    wh_frame m -∗
    wh_hold bn (fs_view γfs γd dev cov) kk pidv dev bno f bsd0 -∗
    (logstart ↪[fs_L γfs]{#(1/2)} bs0) -∗
    (logstart ↪[fs_dirty γfs]{#(1/2)} d0) -∗
    (if d0 then ∃ q : Qp, bref bn kk q dev bno else True) -∗
    ghost_map_auth (fs_L γfs) 1 L -∗
    fsblock γfs (log_hdr_bno logstart) bsh -∗
    lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
    ([∗ list] i0 ↦ w ∈ W, lh_block i0 ↦₄ w) -∗
    (∀ bs' : list (bv 8), ⌜length bs' = 1024%nat⌝ -∗ ⌜hdr_n bs' = Z.of_nat n⌝ -∗
       ⌜hdr_dec bs' = (n, map uint W)⌝ -∗
       disk_write_permit gen_id (Some ((1024 * log_hdr_bno logstart)%Z, bs')) Q) -∗
    wh_cont (CID0 := CID0)  γfs bn logstart n W L pidv dq j m K eb C b Q -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hbnolt Hbnou Hj Hgl HnW HnB Hk.
    (* CID0 is GENERALIZED: the loop body crosses [wp_next]s, so the hart the
       back-edge re-enters at is not the one the block was entered at. *)
    iInduction fuel as [|fuel] "IH" forall (CID0);
      iIntros (i M f Hi Hfuel Hf4 Henc Hregs HMs1 HMa4 HMa5 HMa2);
      [ exfalso; lia |].
    pose proof Hregs as (Hsp & Hthr).
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio Hppid #Hprocs
              #Hdevi #Hdgeom #Hdlock Hframe Hhold HpL HpD Hextra HLauth Hfsb
              Hncell HW Hperm Hcont".
    (* LEVEL 0 TIES THE TWO INDICES, as in [wh_tail]. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    cbn in Hbm.
    iPoseProof (whi_3a with "Htext") as "Hi3a".
    iPoseProof (whi_3c with "Htext") as "Hi3c".
    iPoseProof (whi_3e with "Htext") as "Hi3e".
    iPoseProof (whi_40 with "Htext") as "Hi40".
    iPoseProof (whi_42 with "Htext") as "Hi42".
    (* the entry under copy *)
    destruct (lookup_lt_is_Some_2 W i ltac:(clear -Hi HnW; lia)) as [w Hw].
    iDestruct (big_sepL_lookup_acc _ _ i w Hw with "HW") as "[Hcell Hback]".
    (* ===== +0x3a c.lw a3,0(a4) ===== *)
    assert (Hsrc : add_vec (rget M Ra4) (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = lh_block i).
    { rgne. rewrite HMa4 wh_s0. apply wh_blk_at. }
    iEval (rewrite -Hsrc) in "Hcell".
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.write_head + 0x3a)) Ra3 Ra4
              (mword_of_int 0 : mword 12) M (K - 4)%nat w b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3a Hcell [-]").
    iIntros (CID1 Hs1) "Hcg Hpc Hcell".
    iEval (rewrite Hsrc) in "Hcell".
    iDestruct ("Hback" with "Hcell") as "HW".
    set (S1 := <[Regidx Ra3 := regval_into_reg (sign_extend' 64 w)]> M).
    assert (HS1a3 : S1 !!! Regidx Ra3 = sign_extend' 64 w)
      by (rewrite /S1; apply upd_eq).
    assert (HS1a4 : S1 !!! Regidx Ra4 = lh_block i)
      by (rewrite /S1 upd_ne; [exact HMa4 | vm_compute; discriminate]).
    assert (HS1a5 : S1 !!! Regidx Ra5 = pa_add (bnode kk) (4 * i)%nat)
      by (rewrite /S1 upd_ne; [exact HMa5 | vm_compute; discriminate]).
    assert (HS1a2 : S1 !!! Regidx Ra2 = pa_add (bnode kk) (4 * n)%nat)
      by (rewrite /S1 upd_ne; [exact HMa2 | vm_compute; discriminate]).
    assert (HS1s1 : S1 !!! Regidx Rs1 = bnode kk)
      by (rewrite /S1 upd_ne; [exact HMs1 | vm_compute; discriminate]).
    assert (HS1regs : wh_regs m S1).
    { rewrite /wh_regs. split.
      - rewrite /S1 upd_ne; [exact Hsp | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18.
        rewrite /S1 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18). }
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.write_head + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x3c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3c c.sw a3,92(a5) ===== *)
    assert (Hdst : add_vec (rget S1 Ra5) (sign_extend' 64 (mword_of_int 92 : mword 12))
                   = pa_add (b_data (bnode kk)) (4 * S i)%nat).
    { rgne. rewrite HS1a5 wh_s92. apply wh_dst_addr. }
    assert (Hsum : ((4 * S i) + 4 + (1016 - 4 * i))%nat = 1024%nat)
      by (clear -Hi HnB; unfold LOGBLOCKS in HnB; lia).
    assert (Hal : is_aligned_paddr
                    (Physaddr (pa_add (b_data (bnode kk)) (4 * S i)%nat)) 4 = true)
      by (apply wh_align4; [exact Hk | clear -Hi HnB; unfold LOGBLOCKS in HnB; lia]).
    rewrite /wh_hold.
    iDestruct "Hhold" as
      "(%HA & %HB & %HC & Hslk & Hpid & Hvalid & Hbdev & Hbno & Hbdsk & Hby & Hdisk)".
    iDestruct (bb_word4_acc (b_data (bnode kk)) 1024 (4 * S i)%nat
                 (1016 - 4 * i)%nat f Hsum Hal with "Hby") as "[Hcell Hback2]".
    iEval (rewrite -Hdst) in "Hcell".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.write_head + 0x3c)) Ra3 Ra5
              (mword_of_int 92 : mword 12) S1 (K - 4)%nat
              (bb_mk f (4 * S i)%nat) b
              with "Hcg Hpc Hi3c Hcell [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hcell".
    iEval (rewrite Hdst) in "Hcell".
    assert (Hsv : trunc32 (rget S1 Ra3) = w).
    { rgne. rewrite HS1a3. apply trunc32_sext64. }
    iEval (rewrite Hsv) in "Hcell".
    iDestruct ("Hback2" $! w with "Hcell") as "Hby".
    set (f' := bb_set f (4 * S i)%nat w).
    assert (Hf4' : forall jj, (jj < 4)%nat ->
             f' jj = nth_byte (mword_of_int (Z.of_nat n) : mword 32) jj).
    { intros jj Hjj. rewrite /f' (bb_set_out f (4 * S i)%nat w jj ltac:(left; lia)).
      apply Hf4. exact Hjj. }
    (* the ENCODING invariant, one entry longer: the word just stored IS
       entry [i], and every earlier one is outside the window written *)
    assert (Hwt : W !!! i = w)
      by (rewrite (list_lookup_total_alt W i) Hw; reflexivity).
    assert (Henc' : forall i' jj, (i' < S i)%nat -> (jj < 4)%nat ->
             f' (4 * S i' + jj)%nat = nth_byte (W !!! i') jj).
    { intros i' jj Hi' Hjj. destruct (decide (i' = i)) as [->|Hne].
      - rewrite /f' (bb_set_in f (4 * S i)%nat w (4 * S i + jj)%nat
                       ltac:(lia) ltac:(lia)).
        replace (4 * S i + jj - 4 * S i)%nat with jj by lia.
        rewrite Hwt. reflexivity.
      - rewrite /f' (bb_set_out f (4 * S i)%nat w (4 * S i' + jj)%nat
                       ltac:(left; lia)).
        exact (Henc i' jj ltac:(lia) Hjj). }
    iAssert (wh_hold bn (fs_view γfs γd dev cov) kk pidv dev bno f' bsd0)
      with "[Hslk Hpid Hvalid Hbdev Hbno Hbdsk Hby Hdisk]" as "Hhold".
    { rewrite /wh_hold. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iSplitL "Hslk"; [iExact "Hslk"|]. iSplitL "Hpid"; [iExact "Hpid"|].
      iSplitL "Hvalid"; [iExact "Hvalid"|]. iSplitL "Hbdev"; [iExact "Hbdev"|].
      iSplitL "Hbno"; [iExact "Hbno"|]. iSplitL "Hbdsk"; [iExact "Hbdsk"|].
      iSplitL "Hby"; [iExact "Hby"|]. iExact "Hdisk". }
    assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.write_head + 0x3c) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x3e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3e) in "Hpc".
    (* ===== +0x3e c.addi a4,a4,4 ===== *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.write_head + 0x3e)) Ra4 (mword_of_int 4 : mword 6)
              S1 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi3e [-]").
    iIntros (CID3 Hs3) "Hcg Hpc".
    set (S2 := <[Regidx Ra4 := regval_into_reg
                  (add_vec (rget S1 Ra4)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> S1).
    assert (HS2a4 : S2 !!! Regidx Ra4 = lh_block (S i)).
    { rewrite /S2 upd_eq. rgne. rewrite HS1a4 wh_s4c. apply wh_blk_step. }
    assert (HS2a5 : S2 !!! Regidx Ra5 = pa_add (bnode kk) (4 * i)%nat)
      by (rewrite /S2 upd_ne; [exact HS1a5 | vm_compute; discriminate]).
    assert (HS2a2 : S2 !!! Regidx Ra2 = pa_add (bnode kk) (4 * n)%nat)
      by (rewrite /S2 upd_ne; [exact HS1a2 | vm_compute; discriminate]).
    assert (HS2s1 : S2 !!! Regidx Rs1 = bnode kk)
      by (rewrite /S2 upd_ne; [exact HS1s1 | vm_compute; discriminate]).
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x3e) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x40))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    (* ===== +0x40 c.addi a5,a5,4 ===== *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.write_head + 0x40)) Ra5 (mword_of_int 4 : mword 6)
              S2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi40 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    set (S3 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (rget S2 Ra5)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> S2).
    assert (HS3a5 : S3 !!! Regidx Ra5 = pa_add (bnode kk) (4 * S i)%nat).
    { rewrite /S3 upd_eq. rgne. rewrite HS2a5 wh_s4c. apply wh_cur_step. }
    assert (HS3a4 : S3 !!! Regidx Ra4 = lh_block (S i))
      by (rewrite /S3 upd_ne; [exact HS2a4 | vm_compute; discriminate]).
    assert (HS3a2 : S3 !!! Regidx Ra2 = pa_add (bnode kk) (4 * n)%nat)
      by (rewrite /S3 upd_ne; [exact HS2a2 | vm_compute; discriminate]).
    assert (HS3s1 : S3 !!! Regidx Rs1 = bnode kk)
      by (rewrite /S3 upd_ne; [exact HS2s1 | vm_compute; discriminate]).
    assert (HS3regs : wh_regs m S3).
    { rewrite /wh_regs. split.
      - rewrite /S3 upd_ne; [| vm_compute; discriminate].
        rewrite /S2 upd_ne; [| vm_compute; discriminate].
        rewrite /S1 upd_ne; [exact Hsp | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18.
        rewrite /S3 upd_ne; [| regne].
        rewrite /S2 upd_ne; [| regne].
        rewrite /S1 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18). }
    assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x40) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x42))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp42) in "Hpc".
    (* ===== +0x42 bne a5,a2 ===== *)
    assert (Hb1 : (4 * S i <= 4096)%nat) by (clear -Hi HnB; unfold LOGBLOCKS in HnB; lia).
    assert (Hb2 : (4 * n <= 4096)%nat) by (clear -HnB; unfold LOGBLOCKS in HnB; lia).
    destruct (decide (S i = n)) as [Hdone | Hmore].
    - (* the last entry has been copied: fall through to +0x46 *)
      assert (Hcmp : neq_vec (rget S3 Ra5) (rget S3 Ra2) = false).
      { rgne. rgne. rewrite HS3a5 HS3a2. unfold neq_vec.
        rewrite (wh_ptr_eqb (bnode kk) (4 * S i)%nat (4 * n)%nat Hb1 Hb2).
        replace (Nat.eqb (4 * S i) (4 * n)) with true
          by (symmetry; apply Nat.eqb_eq; clear -Hdone; lia).
        reflexivity. }
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.write_head + 0x42))
                (mword_of_int 8184 : mword 13) Ra2 Ra5 S3 (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp with "Hcg Hpc Hi42 [-]").
      iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x42) : mword 64) 4
                      = mword_of_int (KernelSyms.write_head + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      iDestruct (cpu_own_transport CID0 CID5 0 eb (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID0 CID5 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID0 CID5 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID5) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
      iApply (wh_tail (CID0 := CID5)  γs j γl γu γd γk pd pav pu bn γfs cov logstart
                dev n W L pidv dq kk bno bsh bs0 bsd0 d0 f' m S3 K eb C b Q
                HK Hbnolt Hbnou Hj Hgl HnW HnB Hk Hf4'
                ltac:(intros i' jj Hi' Hjj; exact (Henc' i' jj ltac:(lia) Hjj))
                HS3regs HS3s1
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs
                      Hdevi Hdgeom Hdlock Hframe Hhold HpL HpD Hextra HLauth Hfsb
                      Hncell HW Hperm Hcont").
    - (* more entries: branch back to +0x3a *)
      assert (Hcmp : neq_vec (rget S3 Ra5) (rget S3 Ra2) = true).
      { rgne. rgne. rewrite HS3a5 HS3a2. unfold neq_vec.
        rewrite (wh_ptr_eqb (bnode kk) (4 * S i)%nat (4 * n)%nat Hb1 Hb2).
        replace (Nat.eqb (4 * S i) (4 * n)) with false
          by (symmetry; apply Nat.eqb_neq; clear -Hmore; lia).
        reflexivity. }
      iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.write_head + 0x42))
                (mword_of_int 8184 : mword 13) Ra2 Ra5 S3 (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi42 [-]").
      iNext. iIntros (CID5 Hs5) "Hcg Hpc".
      assert (Htgt3a : add_vec (mword_of_int (KernelSyms.write_head + 0x42) : mword 64)
                         (sign_extend' 64 (mword_of_int 8184 : mword 13))
                       = mword_of_int (KernelSyms.write_head + 0x3a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt3a) in "Hpc".
      assert (Hi' : (S i < n)%nat) by (clear -Hi Hmore; lia).
      assert (Hf' : (n - S i <= fuel)%nat) by (clear -Hi Hfuel Hmore; lia).
      iDestruct (cpu_own_transport CID0 CID5 0 eb (proc_addr j) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID0 CID5 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID0 CID5 eb (proc_addr j)
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (wp_next_shift (b := true) (CIDa := CID0) (CIDb := CID5) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
      iSpecialize ("IH" $! CID5 (S i) S3 f' Hi' Hf' Hf4' Henc' HS3regs HS3s1
                     HS3a4 HS3a5 HS3a2).
      iApply ("IH" with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs Hdevi Hdgeom Hdlock Hframe Hhold HpL HpD
                         Hextra HLauth Hfsb Hncell HW Hperm Hcont").
  Qed.

End WriteHeadBlocks.

(* ===================================================================== *)

Section ProofWriteHead.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_write_head_sconf 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (n : nat) (W : list (mword 32)) (L : gmap Z (list (bv 8)))
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) (Q : iProp Σ)
    : wp_write_head_sconf_body γs j γl γu γd γk pd pav pu bn γfs
                               cov logstart dev n W L pidv dq m K eb C b Q.
  Proof.
    cbv beta delta [wp_write_head_sconf_body].
    intros pcE pj ret_tgt HK Hgeom Hj Hgl Hbatch.
    destruct Hgeom as [Hcovok Hlogsub].
    destruct Hbatch as [HnW HnB].
    unfold K_write_head in HK.
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hfroz Hppid #Hprocs
              #Hdevi #Hdgeom #Hdlock Hncell HW HLauth Hhdr Hslot Hperm Hcont".
    (* LEVEL 0 TIES THE TWO INDICES, as in [wh_tail]. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    cbn in Hbm.
    iDestruct "Hhdr" as (bsh) "Hfsb".
    iDestruct "Hfroz" as "(#Hdevc & #Hstc)".
    (* the header block is covered, and its number is a small positive int *)
    assert (Hhdrcov : logstart ∈ cov).
    { apply Hlogsub. rewrite /log_region_set.
      apply elem_of_union_r. apply elem_of_singleton. reflexivity. }
    destruct (Hcovok logstart Hhdrcov) as [Hls0 Hls1].
    assert (Huint : uint (mword_of_int logstart : mword 32) = logstart).
    { rewrite bb_uint32. apply moi32_small.
      change (2 ^ 32)%Z with 4294967296%Z.
      change (2 ^ 31)%Z with 2147483648%Z in Hls1. lia. }
    assert (Hbnolt : (uint (mword_of_int logstart : mword 32) < 2147483648)%Z).
    { rewrite Huint. change (2 ^ 31)%Z with 2147483648%Z in Hls1. lia. }
    assert (Hcovin : uint (mword_of_int logstart : mword 32)
                     ∈ bv_cov (fs_view γfs γd dev cov))
      by (rewrite Huint; exact Hhdrcov).
    iAssert (wh_cont (CID0 := CID)  γfs bn logstart n W L pidv dq j m K eb C b Q)%I
      with "[Hcont]" as "Hcont"; [rewrite /wh_cont; iExact "Hcont"|].
    iPoseProof (whi_00 with "Htext") as "Hi00".
    iPoseProof (whi_02 with "Htext") as "Hi02".
    iPoseProof (whi_04 with "Htext") as "Hi04".
    iPoseProof (whi_06 with "Htext") as "Hi06".
    iPoseProof (whi_08 with "Htext") as "Hi08".
    iPoseProof (whi_0a with "Htext") as "Hi0a".
    iPoseProof (whi_0c with "Htext") as "Hi0c".
    iPoseProof (whi_10 with "Htext") as "Hi10".
    iPoseProof (whi_14 with "Htext") as "Hi14".
    iPoseProof (whi_18 with "Htext") as "Hi18".
    iPoseProof (whi_1c with "Htext") as "Hi1c".
    (* ===== PROLOGUE ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 b
              ltac:(lia) Hpush with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1 : mword 64)
           (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vr0)  "Hr0".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hr0".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.write_head + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.write_head + 0x02)) (mword_of_int 3 : mword 6) Rra
              R1 (K - 4)%nat vr24 b with "Hcg Hpc Hi02 Hr24 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.write_head + 0x04)) (mword_of_int 2 : mword 6) Rs0
              R1 (K - 4)%nat vr16 b with "Hcg Hpc Hi04 Hr16 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.write_head + 0x06)) (mword_of_int 1 : mword 6) Rs1
              R1 (K - 4)%nat vr8 b with "Hcg Hpc Hi06 Hr8 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.write_head + 0x08)) (mword_of_int 0 : mword 6) Rs2
              R1 (K - 4)%nat vr0 b with "Hcg Hpc Hi08 Hr0 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc Hr0".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.write_head + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* the frame, restated at the entry file *)
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s1 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s2 : (R1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iAssert (wh_frame m) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe".
    { rewrite /wh_frame.
      iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hr24".
      iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hr16".
      iEval (rewrite Hb3; rgne; rewrite HR1s1) in "Hr8".
      iEval (rewrite Hb4; rgne; rewrite HR1s2) in "Hr0".
      iFrame. }
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.write_head + 0x0a)) (Cregidx (mword_of_int 0))
              (mword_of_int 8 : mword 8) Rs0 R1 (K - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.write_head + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c auipc s2,0x1f *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.write_head + 0x0c)) Rs2 (mword_of_int 31 : mword 20)
              R2 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R3 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.write_head + 0x0c) : mword 64)
                     (auipc_off (mword_of_int 31 : mword 20)))]> R2).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x0c) : mword 64) 4
                    = mword_of_int (KernelSyms.write_head + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 addi s2,s2,-1826 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.write_head + 0x10)) Rs2 Rs2
              (mword_of_int 2250 : mword 12) R3 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (R4 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (rget R3 Rs2)
                     (sign_extend' 64 (mword_of_int 2250 : mword 12)))]> R3).
    assert (HR4s2 : R4 !!! Regidx Rs2 = log_addr).
    { rewrite /R4 upd_eq. rgne. rewrite /R3 upd_eq /log_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x10) : mword 64) 4
                    = mword_of_int (KernelSyms.write_head + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    (* +0x14 lw a1,24(s2) : a1 := log.start *)
    assert (Hstart : add_vec (rget R4 Rs2) (sign_extend' 64 (mword_of_int 24 : mword 12))
                     = l_start).
    { rgne. rewrite HR4s2 wh_s24. apply wh_l_start. }
    iEval (rewrite -Hstart) in "Hstc".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.write_head + 0x14)) Ra1 Rs2
              (mword_of_int 24 : mword 12) R4 (K - 4)%nat
              (mword_of_int logstart : mword 32) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 Hstc [-]").
    iIntros (CID9 Hs9) "Hcg Hpc _".
    set (R5 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (mword_of_int logstart : mword 32))]> R4).
    assert (HR5a1 : R5 !!! Regidx Ra1
                    = sign_extend' 64 (mword_of_int logstart : mword 32))
      by (rewrite /R5; apply upd_eq).
    assert (HR5s2 : R5 !!! Regidx Rs2 = log_addr)
      by (rewrite /R5 upd_ne; [exact HR4s2 | vm_compute; discriminate]).
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x14) : mword 64) 4
                    = mword_of_int (KernelSyms.write_head + 0x18))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    (* +0x18 lw a0,36(s2) : a0 := log.dev *)
    assert (Hdvad : add_vec (rget R5 Rs2) (sign_extend' 64 (mword_of_int 36 : mword 12))
                    = l_dev).
    { rgne. rewrite HR5s2 wh_s36. apply wh_l_dev. }
    iEval (rewrite -Hdvad) in "Hdevc".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.write_head + 0x18)) Ra0 Rs2
              (mword_of_int 36 : mword 12) R5 (K - 4)%nat dev b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 Hdevc [-]").
    iIntros (CID10 Hs10) "Hcg Hpc _".
    set (R6 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> R5).
    assert (HR6a0 : R6 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /R6; apply upd_eq).
    assert (HR6a1 : R6 !!! Regidx Ra1
                    = sign_extend' 64 (mword_of_int logstart : mword 32))
      by (rewrite /R6 upd_ne; [exact HR5a1 | vm_compute; discriminate]).
    assert (HR6s2 : R6 !!! Regidx Rs2 = log_addr)
      by (rewrite /R6 upd_ne; [exact HR5s2 | vm_compute; discriminate]).
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.write_head + 0x18) : mword 64) 4
                    = mword_of_int (KernelSyms.write_head + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ===== +0x1c jal ra,bread ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.write_head + 0x1c)) Rra
              (mword_of_int 2093286 : mword 21) R6 (K - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi1c [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (mA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.write_head + 0x1c) : mword 64) 4)]> R6).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.write_head + 0x1c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093286 : mword 21))
                     = mword_of_int KernelSyms.bread)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HmAa0 : mA !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /mA upd_ne; [exact HR6a0 | vm_compute; discriminate]).
    assert (HmAa1 : mA !!! Regidx Ra1
                    = sign_extend' 64 (mword_of_int logstart : mword 32))
      by (rewrite /mA upd_ne; [exact HR6a1 | vm_compute; discriminate]).
    assert (HmAs2 : mA !!! Regidx Rs2 = log_addr)
      by (rewrite /mA upd_ne; [exact HR6s2 | vm_compute; discriminate]).
    assert (HmAra : mA !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.write_head + 0x1c) : mword 64) 4)
      by (rewrite /mA; apply upd_eq).
    assert (HmAsp : mA !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    { rewrite /mA upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [| vm_compute; discriminate].
      exact HspR1. }
    assert (HmAthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              mA !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /mA upd_ne; [| regne].
      rewrite /R6 upd_ne; [| regne].
      rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne].
      rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    iDestruct (cpu_own_transport CID CID11 0 eb pj C b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID CID11 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CID11 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID11) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbr : (K_bread <= K - 4)%nat) by (unfold K_bread; lia).
    iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev (mword_of_int logstart : mword 32) dq
              mA (K - 4)%nat eb C b
              HKbr Hbnolt eq_refl Hcovin eq_refl Hj Hgl HmAa0 HmAa1
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hslot [-]").
    iIntros (CID12 Hs12 mB kk bs0 bsd0 d0) "%Hfacts Hcg Hcnt Hextc Hextm Hpc Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc20 : ret_pc (mA !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.write_head + 0x20)).
    { rewrite HmAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc20) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs2 : mB !!! Regidx Rs2 = log_addr)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HmAs2).
    assert (HmBsp : mB !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
      by (rewrite (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HmAsp).
    assert (HmBthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              mB !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs). exact (HmAthr c Hcs N2 N8 N9 N18). }
    (* ---- the handle is split for the whole body ---- *)
    rewrite /bio_locked bio_held_split.
    iDestruct "Hheld" as "[Hhold Hpay]".
    iDestruct (wh_pay_split with "Hpay") as "(HpL & HpD & Hextra)".
    iEval (rewrite Huint) in "HpL". iEval (rewrite Huint) in "HpD".
    iDestruct (wh_hold_of with "Hhold") as "Hhold".
    (* opened once: [HA] (k < NBUF) is a PURE side condition several
       alignment facts below need, and it only lives inside the handle *)
    iEval (rewrite /wh_hold) in "Hhold".
    iDestruct "Hhold" as
      "(%HA & %HB & %HC & Hslk & Hpid & Hvalid & Hbdev & Hbnoc & Hbdsk & Hby & Hdisk)".
    (* ===== +0x20 c.mv s1,a0 ===== *)
    iPoseProof (whi_20 with "Htext") as "Hi20".
    iPoseProof (whi_22 with "Htext") as "Hi22".
    iPoseProof (whi_26 with "Htext") as "Hi26".
    iPoseProof (whi_28 with "Htext") as "Hi28".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.write_head + 0x20)) Rs1 Ra0
              mB (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi20 [-]").
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (B1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget mB Ra0))]> mB).
    assert (HB1s1 : B1 !!! Regidx Rs1 = bnode kk).
    { rewrite /B1 upd_eq. rgne. rewrite HmBa0. apply add_vec_zero_l. }
    assert (HB1a0 : B1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B1 upd_ne; [exact HmBa0 | vm_compute; discriminate]).
    assert (HB1s2 : B1 !!! Regidx Rs2 = log_addr)
      by (rewrite /B1 upd_ne; [exact HmBs2 | vm_compute; discriminate]).
    assert (HB1regs : wh_regs m B1).
    { rewrite /wh_regs. split.
      - rewrite /B1 upd_ne; [exact HmBsp | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18.
        rewrite /B1 upd_ne; [| regne]. exact (HmBthr c Hcs N2 N8 N9 N18). }
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* ===== +0x22 lw a2,44(s2) : a2 := log.lh.n ===== *)
    assert (Hlhn : add_vec (rget B1 Rs2) (sign_extend' 64 (mword_of_int 44 : mword 12))
                   = lh_n_pa).
    { rgne. rewrite HB1s2 wh_s44. apply wh_l_lhn. }
    iEval (rewrite -Hlhn) in "Hncell".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.write_head + 0x22)) Ra2 Rs2
              (mword_of_int 44 : mword 12) B1 (K - 4)%nat
              (mword_of_int (Z.of_nat n) : mword 32) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 Hncell [-]").
    iIntros (CID14 Hs14) "Hcg Hpc Hncell".
    iEval (rewrite Hlhn) in "Hncell".
    set (B2 := <[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32))]> B1).
    assert (HB2a2 : B2 !!! Regidx Ra2
                    = sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32))
      by (rewrite /B2; apply upd_eq).
    assert (HB2a0 : B2 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B2 upd_ne; [exact HB1a0 | vm_compute; discriminate]).
    assert (HB2s1 : B2 !!! Regidx Rs1 = bnode kk)
      by (rewrite /B2 upd_ne; [exact HB1s1 | vm_compute; discriminate]).
    assert (HB2regs : wh_regs m B2).
    { rewrite /wh_regs. split.
      - rewrite /B2 upd_ne; [| vm_compute; discriminate].
        exact (proj1 HB1regs).
      - intros c Hcs N2 N8 N9 N18.
        rewrite /B2 upd_ne; [| regne]. exact (proj2 HB1regs c Hcs N2 N8 N9 N18). }
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x22) : mword 64) 4
                    = mword_of_int (KernelSyms.write_head + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    (* ===== +0x26 c.sw a2,88(a0) : hb->n := log.lh.n ===== *)
    assert (Hhaddr : add_vec (rget B2 Ra0) (sign_extend' 64 (mword_of_int 88 : mword 12))
                     = pa_add (b_data (bnode kk)) (4 * 0)%nat).
    { rgne. rewrite HB2a0 wh_s88. apply wh_hdr_addr. }
    assert (Hsum0 : ((4 * 0) + 4 + 1020)%nat = 1024%nat) by reflexivity.
    assert (Hal0 : is_aligned_paddr
                     (Physaddr (pa_add (b_data (bnode kk)) (4 * 0)%nat)) 4 = true)
      by (apply wh_align4; [exact HA | apply Nat.le_0_l]).
    iDestruct (bb_word4_acc (b_data (bnode kk)) 1024 (4 * 0)%nat 1020
                 (fun jj => bs0 !!! jj) Hsum0 Hal0 with "Hby") as "[Hcell Hback]".
    iEval (rewrite -Hhaddr) in "Hcell".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.write_head + 0x26)) Ra2 Ra0
              (mword_of_int 88 : mword 12) B2 (K - 4)%nat
              (bb_mk (fun jj => bs0 !!! jj) (4 * 0)%nat) b
              with "Hcg Hpc Hi26 Hcell [-]").
    iIntros (CID15 Hs15) "Hcg Hpc Hcell".
    iEval (rewrite Hhaddr) in "Hcell".
    assert (Hsv0 : trunc32 (rget B2 Ra2) = (mword_of_int (Z.of_nat n) : mword 32)).
    { rgne. rewrite HB2a2. apply trunc32_sext64. }
    iEval (rewrite Hsv0) in "Hcell".
    iDestruct ("Hback" $! (mword_of_int (Z.of_nat n) : mword 32) with "Hcell") as "Hby".
    set (f1 := bb_set (fun jj => bs0 !!! jj) (4 * 0)%nat
                 (mword_of_int (Z.of_nat n) : mword 32)).
    assert (Hf14 : forall jj, (jj < 4)%nat ->
             f1 jj = nth_byte (mword_of_int (Z.of_nat n) : mword 32) jj).
    { intros jj Hjj.
      rewrite /f1 (bb_set_in (fun j0 => bs0 !!! j0) (4 * 0)%nat
                     (mword_of_int (Z.of_nat n) : mword 32) jj ltac:(lia) ltac:(lia)).
      f_equal. lia. }
    iAssert (wh_hold bn (fs_view γfs γd dev cov) kk pidv dev
               (mword_of_int logstart : mword 32) f1 bsd0)
      with "[Hslk Hpid Hvalid Hbdev Hbnoc Hbdsk Hby Hdisk]" as "Hhold".
    { rewrite /wh_hold. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iSplitL "Hslk"; [iExact "Hslk"|]. iSplitL "Hpid"; [iExact "Hpid"|].
      iSplitL "Hvalid"; [iExact "Hvalid"|]. iSplitL "Hbdev"; [iExact "Hbdev"|].
      iSplitL "Hbnoc"; [iExact "Hbnoc"|]. iSplitL "Hbdsk"; [iExact "Hbdsk"|].
      iSplitL "Hby"; [iExact "Hby"|]. iExact "Hdisk". }
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x26) : mword 64) 2
                    = mword_of_int (KernelSyms.write_head + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    (* ===== +0x28 blez a2 ===== *)
    assert (HB2a2v : (rget B2 Ra2 : mword 64) = mword_of_int (Z.of_nat n)).
    { rgne. rewrite HB2a2. apply wh_sext_n. unfold LOGBLOCKS in HnB. lia. }
    assert (Hnb31 : (0 <= Z.of_nat n < 2 ^ 31)%Z).
    { unfold LOGBLOCKS in HnB. change (2 ^ 31)%Z with 2147483648%Z. lia. }
    destruct n as [|n'] eqn:Hncase.
    - (* ---- n = 0: the loop is skipped entirely ---- *)
      assert (Hcmp : zopz0zKzJ_s (zero_reg : mword 64) (rget B2 Ra2) = true).
      { rewrite HB2a2v. rewrite (wh_geb_s0 (Z.of_nat 0%nat) Hnb31). reflexivity. }
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.write_head + 0x28))
                (mword_of_int 30 : mword 13) Ra2 B2 (K - 4)%nat b
                ltac:(vm_compute; discriminate) Hcmp ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi28 [-]").
      iNext. iIntros (CID16 Hs16) "Hcg Hpc".
      assert (Htgt46 : add_vec (mword_of_int (KernelSyms.write_head + 0x28) : mword 64)
                         (sign_extend' 64 (mword_of_int 30 : mword 13))
                       = mword_of_int (KernelSyms.write_head + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt46) in "Hpc".
      iDestruct (cpu_own_transport CID12 CID16 0 eb pj C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID12 CID16 eb pj
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID12 CID16 eb pj
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (wp_next_shift (b := true) (CIDa := CID11) (CIDb := CID16) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
      iApply (wh_tail (CID0 := CID16)  γs j γl γu γd γk pd pav pu bn γfs cov logstart
                dev 0%nat W L pidv dq kk (mword_of_int logstart : mword 32)
                bsh bs0 bsd0 d0 f1 m B2 K eb C b Q
                HK Hbnolt Huint Hj Hgl HnW HnB HA Hf14
                ltac:(intros i' jj Hi' Hjj; exfalso; lia)
                HB2regs HB2s1
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs
                      Hdevi Hdgeom Hdlock Hframe Hhold HpL HpD Hextra HLauth Hfsb
                      Hncell HW Hperm Hcont").
    - (* ---- n > 0: set the cursors up and enter the loop ---- *)
      assert (Hcmp : zopz0zKzJ_s (zero_reg : mword 64) (rget B2 Ra2) = false).
      { rewrite HB2a2v. rewrite (wh_geb_s0 (Z.of_nat (S n')) Hnb31).
        destruct (Z.geb 0 (Z.of_nat (S n'))) eqn:Hgb; [| reflexivity].
        exfalso. rewrite Z.geb_leb in Hgb. apply Z.leb_le in Hgb.
        clear -Hgb. lia. }
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.write_head + 0x28))
                (mword_of_int 30 : mword 13) Ra2 B2 (K - 4)%nat b
                ltac:(vm_compute; discriminate) Hcmp
                with "Hcg Hpc Hi28 [-]").
      iIntros (CID16 Hs16) "Hcg Hpc".
      assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.write_head + 0x28) : mword 64) 4
                      = mword_of_int (KernelSyms.write_head + 0x2c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      iPoseProof (whi_2c with "Htext") as "Hi2c".
      iPoseProof (whi_30 with "Htext") as "Hi30".
      iPoseProof (whi_34 with "Htext") as "Hi34".
      iPoseProof (whi_36 with "Htext") as "Hi36".
      iPoseProof (whi_38 with "Htext") as "Hi38".
      (* +0x2c auipc a4,0x1f *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.write_head + 0x2c)) Ra4
                (mword_of_int 31 : mword 20) B2 (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2c [-]").
      iIntros (CID17 Hs17) "Hcg Hpc".
      set (B3 := <[Regidx Ra4 := regval_into_reg
                    (add_vec (mword_of_int (KernelSyms.write_head + 0x2c) : mword 64)
                       (auipc_off (mword_of_int 31 : mword 20)))]> B2).
      assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x2c) : mword 64) 4
                      = mword_of_int (KernelSyms.write_head + 0x30))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp30) in "Hpc".
      (* +0x30 addi a4,a4,-1810 : a4 := &log.lh.block[0] *)
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.write_head + 0x30)) Ra4 Ra4
                (mword_of_int 2266 : mword 12) B3 (K - 4)%nat b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi30 [-]").
      iIntros (CID18 Hs18) "Hcg Hpc".
      set (B4 := <[Regidx Ra4 := regval_into_reg
                    (add_vec (rget B3 Ra4)
                       (sign_extend' 64 (mword_of_int 2266 : mword 12)))]> B3).
      assert (HB4a4 : B4 !!! Regidx Ra4 = lh_block 0%nat).
      { rewrite /B4 upd_eq. rgne. rewrite /B3 upd_eq.
        rewrite /lh_block /log_pa /log_addr /pa_add /add_vec_int.
        apply bv_eq; vm_compute; reflexivity. }
      assert (HB4a2 : B4 !!! Regidx Ra2
                      = sign_extend' 64 (mword_of_int (Z.of_nat (S n')) : mword 32)).
      { rewrite /B4 upd_ne; [| vm_compute; discriminate].
        rewrite /B3 upd_ne; [| vm_compute; discriminate]. exact HB2a2. }
      assert (HB4a0 : B4 !!! Regidx Ra0 = bnode kk).
      { rewrite /B4 upd_ne; [| vm_compute; discriminate].
        rewrite /B3 upd_ne; [| vm_compute; discriminate]. exact HB2a0. }
      assert (HB4s1 : B4 !!! Regidx Rs1 = bnode kk).
      { rewrite /B4 upd_ne; [| vm_compute; discriminate].
        rewrite /B3 upd_ne; [| vm_compute; discriminate]. exact HB2s1. }
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x30) : mword 64) 4
                      = mword_of_int (KernelSyms.write_head + 0x34))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      (* +0x34 c.mv a5,a0 *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.write_head + 0x34)) Ra5 Ra0
                B4 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi34 [-]").
      iIntros (CID19 Hs19) "Hcg Hpc".
      set (B5 := <[Regidx Ra5 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget B4 Ra0))]> B4).
      assert (HB5a5 : B5 !!! Regidx Ra5 = pa_add (bnode kk) (4 * 0)%nat).
      { rewrite /B5 upd_eq. rgne. rewrite HB4a0.
        rewrite add_vec_zero_l. change (4 * 0)%nat with 0%nat.
        symmetry. apply RiscvExtras.pa_add_0. }
      assert (HB5a2 : B5 !!! Regidx Ra2
                      = sign_extend' 64 (mword_of_int (Z.of_nat (S n')) : mword 32))
        by (rewrite /B5 upd_ne; [exact HB4a2 | vm_compute; discriminate]).
      assert (HB5a0 : B5 !!! Regidx Ra0 = bnode kk)
        by (rewrite /B5 upd_ne; [exact HB4a0 | vm_compute; discriminate]).
      assert (HB5a4 : B5 !!! Regidx Ra4 = lh_block 0%nat)
        by (rewrite /B5 upd_ne; [exact HB4a4 | vm_compute; discriminate]).
      assert (HB5s1 : B5 !!! Regidx Rs1 = bnode kk)
        by (rewrite /B5 upd_ne; [exact HB4s1 | vm_compute; discriminate]).
      assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x34) : mword 64) 2
                      = mword_of_int (KernelSyms.write_head + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      (* +0x36 c.slli a2,a2,2 *)
      iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.write_head + 0x36)) (Regidx Ra2) Ra2
                (mword_of_int 2 : mword 6) B5 (K - 4)%nat b
                eq_refl ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi36 [-]").
      iIntros (CID20 Hs20) "Hcg Hpc".
      set (B6 := <[Regidx Ra2 := regval_into_reg
                    (shift_bits_left (rget B5 Ra2)
                       (subrange_vec_dec (mword_of_int 2 : mword 6)
                          (Z.sub log2_xlen 1) 0))]> B5).
      assert (HB6a2 : B6 !!! Regidx Ra2
                      = mword_of_int (4 * Z.of_nat (S n'))).
      { rewrite /B6 upd_eq. rgne. rewrite HB5a2.
        rewrite (wh_sext_n (S n') ltac:(unfold LOGBLOCKS in HnB; lia)).
        apply wh_slli2. unfold LOGBLOCKS in HnB. lia. }
      assert (HB6a0 : B6 !!! Regidx Ra0 = bnode kk)
        by (rewrite /B6 upd_ne; [exact HB5a0 | vm_compute; discriminate]).
      assert (HB6a4 : B6 !!! Regidx Ra4 = lh_block 0%nat)
        by (rewrite /B6 upd_ne; [exact HB5a4 | vm_compute; discriminate]).
      assert (HB6a5 : B6 !!! Regidx Ra5 = pa_add (bnode kk) (4 * 0)%nat)
        by (rewrite /B6 upd_ne; [exact HB5a5 | vm_compute; discriminate]).
      assert (HB6s1 : B6 !!! Regidx Rs1 = bnode kk)
        by (rewrite /B6 upd_ne; [exact HB5s1 | vm_compute; discriminate]).
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.write_head + 0x36) : mword 64) 2
                      = mword_of_int (KernelSyms.write_head + 0x38))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      (* +0x38 c.add a2,a2,a0 : a2 := buf + 4n *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.write_head + 0x38)) Ra2 Ra0
                B6 (K - 4)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi38 [-]").
      iIntros (CID21 Hs21) "Hcg Hpc".
      set (B7 := <[Regidx Ra2 := regval_into_reg
                    (add_vec (rget B6 Ra2) (rget B6 Ra0))]> B6).
      assert (HB7a2 : B7 !!! Regidx Ra2 = pa_add (bnode kk) (4 * S n')%nat).
      { rewrite /B7 upd_eq. rgne. rgne. rewrite HB6a2 HB6a0.
        assert (Hz : (mword_of_int (4 * Z.of_nat (S n')) : mword 64)
                     = mword_of_int (Z.of_nat (4 * S n'))) by (f_equal; lia).
        rewrite Hz. apply ByteCursor.pa_add_comm. }
      assert (HB7a4 : B7 !!! Regidx Ra4 = lh_block 0%nat)
        by (rewrite /B7 upd_ne; [exact HB6a4 | vm_compute; discriminate]).
      assert (HB7a5 : B7 !!! Regidx Ra5 = pa_add (bnode kk) (4 * 0)%nat)
        by (rewrite /B7 upd_ne; [exact HB6a5 | vm_compute; discriminate]).
      assert (HB7s1 : B7 !!! Regidx Rs1 = bnode kk)
        by (rewrite /B7 upd_ne; [exact HB6s1 | vm_compute; discriminate]).
      assert (HB7regs : wh_regs m B7).
      { rewrite /wh_regs. split.
        - rewrite /B7 upd_ne; [| vm_compute; discriminate].
          rewrite /B6 upd_ne; [| vm_compute; discriminate].
          rewrite /B5 upd_ne; [| vm_compute; discriminate].
          rewrite /B4 upd_ne; [| vm_compute; discriminate].
          rewrite /B3 upd_ne; [| vm_compute; discriminate].
          exact (proj1 HB2regs).
        - intros c Hcs N2 N8 N9 N18.
          rewrite /B7 upd_ne; [| regne].
          rewrite /B6 upd_ne; [| regne].
          rewrite /B5 upd_ne; [| regne].
          rewrite /B4 upd_ne; [| regne].
          rewrite /B3 upd_ne; [| regne].
          exact (proj2 HB2regs c Hcs N2 N8 N9 N18). }
      assert (Hpp3a : add_vec_int (mword_of_int (KernelSyms.write_head + 0x38) : mword 64) 2
                      = mword_of_int (KernelSyms.write_head + 0x3a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3a) in "Hpc".
      iDestruct (cpu_own_transport CID12 CID21 0 eb pj C b ltac:(wp_next_chain)
                   with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID12 CID21 eb pj
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID12 CID21 eb pj
                   ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (wp_next_shift (b := true) (CIDa := CID11) (CIDb := CID21) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
      iApply (wh_loop (CID0 := CID21)  γs j γl γu γd γk pd pav pu bn γfs cov logstart
                dev (S n') W L pidv dq kk (mword_of_int logstart : mword 32)
                bsh bs0 bsd0 d0 m K eb C b (S n') Q
                HK Hbnolt Huint Hj Hgl HnW HnB HA 0%nat B7 f1
                ltac:(lia) ltac:(lia) Hf14
                ltac:(intros i' jj Hi' Hjj; exfalso; lia)
                HB7regs HB7s1 HB7a4 HB7a5 HB7a2
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs
                      Hdevi Hdgeom Hdlock Hframe Hhold HpL HpD Hextra HLauth Hfsb
                      Hncell HW Hperm Hcont").
  Qed.

End ProofWriteHead.

End WriteHeadProof.
