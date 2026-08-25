(* ProofInitlog.v -- initlog over the SIE-agnostic sconf world: THE LOG
   LAYER'S CONSTRUCTOR, in its clean-image (stage-2) form.

     void initlog(int dev, struct superblock *sb) {
       initlock(&log.lock, "log");
       log.start = sb->logstart;
       log.dev   = dev;
       recover_from_log();            // INLINED, and read_head with it
     }

   THE SHAPE OF THE PROOF.  Straight line: five calls (initlock, bread,
   brelse, install_trans, write_head), four stores into [struct log], one
   load out of the buffer's header word, and ONE branch -- the [blez] at
   +0x40, which the clean-image premise [hdr_n bs_hdr = 0] makes TAKEN, so
   the header-copy do-while at +0x44..+0x5a is dead code and never appears
   in the proof at all.

   * SEALING AT A PRE-MINTED NAME.  The "log" spinlock's resource
     ([LogInv.log_res]) does not exist at the initlock call: it holds the
     very [lh] cells that install_trans and write_head are handed a few
     instructions later, and it is indexed by a [log_names] record whose
     first field IS the lock's own ghost name.  This used to force
     [WpLock.newlock_delayed] -- pick the gname right after initlock
     returns, carry its wand to the end.  It no longer does: the contract
     now RECEIVES the four gnames ([LogDefs.log_free_tok γ], minted in the
     era fupd, fs-cfg-boot.md THE PRINCIPLE), so there is nothing to delay.
     The proof carries initlock's two zeroed lock cells to the very END --
     no callee in between touches them, since install_trans and write_head
     take [log_frozen], not [log_ctx] -- and spends them there on
     [WpLockAt.newlock_at], once [log_res] has been assembled at the given
     [γ] out of everything initlog was given.

   * THE FROZEN CELLS ARE PERSISTED BEFORE THE FIRST CALLEE.  log.start and
     log.dev are written at +0x2c / +0x30 and then discarded to
     [DfracDiscarded] ([RiscvPtsto.word4_pointsto_persist]) on the spot --
     which is exactly [LogInv.log_frozen], the context both committer-only
     helpers take (they run with no lock held, and at their call sites there
     is no lock yet).

   * THE HEADER WORD IS READ THROUGH A FOUR-BYTE BRIDGE.  The [c.lw a2,88(a0)]
     at +0x3a reads [buf->data + 0], i.e. the first little-endian word of the
     block -- which is [LogInv.hdr_n] by definition.  [il_hdr_acc] borrows
     that word out of [buf_own]'s byte list and gives it back unchanged (the
     buffer is never written here), so the handle brelse gets is the one
     bread returned, byte for byte.  With [hdr_n bs_hdr = 0] the loaded word
     is 0, which is what kills the copy loop and what makes the
     [install_trans(1)] call legal (its stage-2 premise is
     [recovering = false \/ n = 0]).

   * SLOT ACCOUNTING.  34 = 1 + 33 in, one unit to bread and back from
     brelse, two to install_trans and 2 + |W| = 2 back, one to write_head and
     back: 34 out, split 32 (the batch's pool at n = 0) + 2 (the caller's
     working pair).

   HART-GENERIC PROTOCOL.  Every callee returns through [wp_next true pj (fun
   CID => ...)], so the caller's own continuation is re-anchored at each
   crossing with [WpSconfVc.wp_next_shift] and the [cpu_own] with
   [CpuOwn.cpu_own_transport]. *)
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
(* block 1's park (durable-disk lane C-3a).  EARLY, because this file's
   later imports own the names [FsImg] shadows. *)
Require Import FsImg.
Require Import SbPark.
Require Import KernelDataInv.
Require Import InstrBytes.   (* [pc_is], for the stage-D block lemmas *)
Require Import KernelText.   (* [kernel_text], same *)
Require Import SpecPrintk.  (* the recovery printk's contract *)
Require Import RegFile HartTp WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import DiskPtsto.
Require Import WpLock.
Require Import WpLockAt.   (* [newlock_at]: seal a lock at a GIVEN gname *)
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import ByteCursor.
Require Import ByteBuf.
Require Import FdSlots.
Require Import WpUart.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import CodeInitlog.
Require Import SpecInitlock.
Require Import SpecBread SpecBrelse.
Require Import SpecInstallTrans SpecWriteHead.
Require Import SpecInitlog.
From Kernel Require KernelSyms.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import ProcDefs.  (* [pprivate], [proc_priv_bare] *)
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.

(* ===================================================================== *)
(*  Pure vocabulary.  All of it over plain [Z]/[nat] or closed words, so   *)
(*  no solver ever runs inside the WP context.                            *)
(* ===================================================================== *)

(* ---- the header's [n] field as a WORD: the first little-endian 32-bit
   word of the block, which is what [c.lw a2,88(a0)] loads. ---- *)
Definition il_hdrw (bs : list (bv 8)) : SailStdpp.Values.mword 32 :=
  Z_to_bv 32 (hdr_n bs).

Lemma il_hdrw_zero (bs : list (bv 8)) :
  hdr_n bs = 0 -> il_hdrw bs = (mword_of_int 0 : SailStdpp.Values.mword 32).
Proof.
  intro H. rewrite /il_hdrw H. apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- THE DECODED HEADER, WORD BY WORD (durable-disk stage D1): what the
   copy loop reads at [92 + 4t (a5)] and what it stores into
   [log.lh.block[t]].  [il_W] is the whole write set as the 32-bit words
   the cells end up holding; its [uint] image IS [hdr_dec]'s entry list,
   which is how the general install contract's premises are discharged. ---- *)
Definition il_wordw (bs : list (bv 8)) (k : nat) : SailStdpp.Values.mword 32 :=
  Z_to_bv 32 (le_word bs k).

Definition il_W (bs : list (bv 8)) (nh : nat) : list (SailStdpp.Values.mword 32) :=
  (fun i => il_wordw bs (S i)) <$> seq 0 nh.

Lemma il_W_length (bs : list (bv 8)) (nh : nat) : length (il_W bs nh) = nh.
Proof. rewrite /il_W length_fmap length_seq //. Qed.

Lemma le_word_range (bs : list (bv 8)) (k : nat) :
  0 <= le_word bs k < 2 ^ 32.
Proof.
  rewrite /le_word.
  pose proof (assemble_bytes_bound (take 4 (drop (4 * k) bs))) as [Hlo Hhi].
  split; [exact Hlo|].
  eapply Z.lt_le_trans; [exact Hhi|].
  apply Z.pow_le_mono_r; [lia|]. rewrite length_take. lia.
Qed.

Lemma il_wordw_uint (bs : list (bv 8)) (k : nat) :
  uint (il_wordw bs k) = le_word bs k.
Proof.
  rewrite /il_wordw bb_uint32 Z_to_bv_unsigned.
  apply bv_wrap_small.
  pose proof (le_word_range bs k) as Hr.
  change (2 ^ 32)%Z with 4294967296%Z in Hr.
  assert (Hm : bv_modulus 32 = 4294967296%Z) by (vm_compute; reflexivity).
  rewrite Hm. lia.
Qed.

Lemma il_W_uint (bs : list (bv 8)) :
  map uint (il_W bs (hdr_dec bs).1) = (hdr_dec bs).2.
Proof.
  change (map uint (il_W bs (hdr_dec bs).1))
    with (uint <$> (il_W bs (hdr_dec bs).1)).
  rewrite /il_W -list_fmap_compose.
  apply list_fmap_ext. intros i k Hk. cbn.
  apply il_wordw_uint.
Qed.

(* ---- the copy loop's SOURCE cursor (a5): the buffer pointer plus 4t ---- *)
Definition il_cur (kk t : nat) : SailStdpp.Values.mword 64 :=
  pa_add (bnode kk) (4 * t)%nat.

Lemma il_cur_0 (kk : nat) :
  add_vec (zero_reg : SailStdpp.Values.mword 64) (bnode kk) = il_cur kk 0.
Proof.
  rewrite add_vec_zero_l /il_cur Nat.mul_0_r RiscvExtras.pa_add_0 //.
Qed.

Lemma il_cur_step (kk t : nat) :
  add_vec (il_cur kk t)
    (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : SailStdpp.Values.mword 6)))
  = il_cur kk (S t).
Proof.
  assert (H4 : sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : SailStdpp.Values.mword 6))
               = (mword_of_int (Z.of_nat 4%nat) : SailStdpp.Values.mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite /il_cur H4 pa_add_bump. f_equal. lia.
Qed.

(* the loaded word's address: [92(a5)] is data byte [4 (S t)] *)
Lemma il_cur_addr (kk t : nat) :
  add_vec (il_cur kk t) (sign_extend' 64 (mword_of_int 92 : SailStdpp.Values.mword 12))
  = pa_add (b_data (bnode kk)) (4 * S t)%nat.
Proof.
  assert (H92 : sign_extend' 64 (mword_of_int 92 : SailStdpp.Values.mword 12)
                = (mword_of_int (Z.of_nat 92%nat) : SailStdpp.Values.mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite /il_cur H92 pa_add_bump /b_data pa_add_assoc.
  f_equal. lia.
Qed.

(* two cursors into one buffer agree only at the same index *)
Lemma il_cur_inj (kk t nh : nat) :
  (kk < NBUF)%nat -> (t <= LOGBLOCKS)%nat -> (nh <= LOGBLOCKS)%nat ->
  t <> nh ->
  eq_vec (il_cur kk t) (il_cur kk nh) = false.
Proof.
  intros Hk Ht Hn Hne. rewrite /il_cur pa_add_eqb.
  - apply Nat.eqb_neq. lia.
  - unfold LOGBLOCKS in Ht. lia.
  - unfold LOGBLOCKS in Hn. lia.
Qed.

Lemma il_cur_eq (kk t : nat) :
  (t <= LOGBLOCKS)%nat ->
  eq_vec (il_cur kk t) (il_cur kk t) = true.
Proof.
  intros Ht. rewrite /il_cur pa_add_eqb.
  - apply Nat.eqb_refl.
  - unfold LOGBLOCKS in Ht. lia.
  - unfold LOGBLOCKS in Ht. lia.
Qed.

(* the DESTINATION cursor (a4): [&log.lh.block[t]], stepped by 4 *)
Lemma il_blk_at (t : nat) :
  add_vec (lh_block t : SailStdpp.Values.mword 64)
    (sign_extend' 64 (mword_of_int 0 : SailStdpp.Values.mword 12))
  = (lh_block t : SailStdpp.Values.mword 64).
Proof.
  assert (H0 : sign_extend' 64 (mword_of_int 0 : SailStdpp.Values.mword 12)
               = (mword_of_int (Z.of_nat 0%nat) : SailStdpp.Values.mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite /lh_block H0 pa_add_bump. f_equal. lia.
Qed.

Lemma il_blk_step (t : nat) :
  add_vec (lh_block t : SailStdpp.Values.mword 64)
    (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : SailStdpp.Values.mword 6)))
  = (lh_block (S t) : SailStdpp.Values.mword 64).
Proof.
  assert (H4 : sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : SailStdpp.Values.mword 6))
               = (mword_of_int (Z.of_nat 4%nat) : SailStdpp.Values.mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite /lh_block H4 pa_add_bump. f_equal. lia.
Qed.

(* a4's start: the [auipc/addi] pair at +0x46/+0x4a resolves to
   [&log.lh.block[0]] *)
Lemma il_reloc_blk0 :
  add_vec (add_vec (mword_of_int (KernelSyms.initlog + 0x46) : SailStdpp.Values.mword 64)
                   (auipc_off (mword_of_int 30 : SailStdpp.Values.mword 20)))
          (sign_extend' 64 (mword_of_int 1924 : SailStdpp.Values.mword 12))
  = (lh_block 0 : SailStdpp.Values.mword 64).
Proof.
  rewrite /lh_block /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- the alignment of the buffer's first data word: [bcache]'s geometry,
   then [ByteBuf.bb_align_z] (ProofWriteHead's [wh_align4] at q = 0) ---- *)
Lemma il_align_arith (kk : Z) :
  0 <= kk -> kk < 30 ->
  (2147582488 + 1112 * kk + 88) `mod` 4 = 0
  /\ 0 <= 2147582488 + 1112 * kk + 88
  /\ 2147582488 + 1112 * kk + 88 < 18446744073709551616.
Proof.
  intros H1 H2. split_and!; [| lia | lia].
  replace (2147582488 + 1112 * kk + 88)
    with ((536895644 + 278 * kk) * 4) by lia.
  apply Z_mod_mult.
Qed.

Lemma il_align4k (k mm : nat) : (k < NBUF)%nat -> (mm <= LOGBLOCKS)%nat ->
  is_aligned_paddr (Physaddr (pa_add (b_data (bnode k)) (4 * mm)%nat)) 4 = true.
Proof.
  intros Hk Hm.
  unfold b_data. rewrite pa_add_assoc.
  unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite RiscvExtras.uint_unsigned.
  rewrite ByteCursor.pa_add_unsigned.
  rewrite (bnode_unsigned k Hk).
  unfold buf_base, buf_stride, KernelSyms.bcache.
  assert (Harith : (2147582488 + 1112 * Z.of_nat k + Z.of_nat (88 + 4 * mm))
                     `mod` 4 = 0
                   /\ 0 <= 2147582488 + 1112 * Z.of_nat k + Z.of_nat (88 + 4 * mm)
                   /\ 2147582488 + 1112 * Z.of_nat k + Z.of_nat (88 + 4 * mm)
                        < 18446744073709551616).
  { unfold NBUF in Hk. unfold LOGBLOCKS in Hm.
    split_and!; [| lia | lia].
    replace (2147582488 + 1112 * Z.of_nat k + Z.of_nat (88 + 4 * mm))
      with ((536895644 + 278 * Z.of_nat k + Z.of_nat mm) * 4) by lia.
    apply Z_mod_mult. }
  destruct Harith as (Hm4 & Hlo & Hhi).
  replace (0x80018200 + 24 + 1112 * Z.of_nat k + Z.of_nat (88 + 4 * mm))
    with (2147582488 + 1112 * Z.of_nat k + Z.of_nat (88 + 4 * mm)) by lia.
  apply bb_align_z; assumption.
Qed.

Lemma il_align4 (k : nat) : (k < NBUF)%nat ->
  is_aligned_paddr (Physaddr (b_data (bnode k))) 4 = true.
Proof.
  intros Hk.
  unfold b_data.
  unfold is_aligned_paddr. apply Z.eqb_eq.
  rewrite RiscvExtras.uint_unsigned.
  rewrite ByteCursor.pa_add_unsigned.
  rewrite (bnode_unsigned k Hk).
  unfold buf_base, buf_stride, KernelSyms.bcache.
  destruct (il_align_arith (Z.of_nat k)
              ltac:(lia) ltac:(unfold NBUF in Hk; lia))
    as (Hm & Hlo & Hhi).
  replace (0x80018200 + 24 + 1112 * Z.of_nat k + Z.of_nat 88)
    with (2147582488 + 1112 * Z.of_nat k + 88) by lia.
  apply bb_align_z; assumption.
Qed.

(* ---- the sign-extended immediates initlog forms ---- *)
Lemma il_s20 : sign_extend' 64 (mword_of_int 20 : SailStdpp.Values.mword 12)
               = (mword_of_int 20 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma il_s24 : sign_extend' 64 (mword_of_int 24 : SailStdpp.Values.mword 12)
               = (mword_of_int 24 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma il_s36 : sign_extend' 64 (mword_of_int 36 : SailStdpp.Values.mword 12)
               = (mword_of_int 36 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma il_s44 : sign_extend' 64 (mword_of_int 44 : SailStdpp.Values.mword 12)
               = (mword_of_int 44 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma il_s88 : sign_extend' 64 (mword_of_int 88 : SailStdpp.Values.mword 12)
               = (mword_of_int 88 : SailStdpp.Values.mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- the [struct log] cell addresses the code forms ---- *)
Lemma il_l_start : add_vec (log_addr : SailStdpp.Values.mword 64)
                     (mword_of_int 24 : SailStdpp.Values.mword 64) = l_start.
Proof. reflexivity. Qed.
Lemma il_l_dev : add_vec (log_addr : SailStdpp.Values.mword 64)
                     (mword_of_int 36 : SailStdpp.Values.mword 64) = l_dev.
Proof. reflexivity. Qed.
Lemma il_l_lhn : add_vec (log_addr : SailStdpp.Values.mword 64)
                     (mword_of_int 44 : SailStdpp.Values.mword 64) = lh_n_pa.
Proof. reflexivity. Qed.

Lemma il_hdr_addr (a : SailStdpp.Values.mword 64) :
  add_vec a (mword_of_int 88 : SailStdpp.Values.mword 64) = b_data a.
Proof. reflexivity. Qed.

(* ===================================================================== *)

Module InitlogProof (Initlock : INITLOCK) (Bread : BREAD) (Brelse : BRELSE)
                    (InstallTrans : INSTALL_TRANS) (WriteHead : WRITE_HEAD)
  : INITLOG.


Notation Rra := (mword_of_int 1 : mword 5).
Notation Rs0 := (mword_of_int 8 : mword 5).
Notation Rs1 := (mword_of_int 9 : mword 5).
Notation Rs2 := (mword_of_int 18 : mword 5).
Notation Rs3 := (mword_of_int 19 : mword 5).
Notation Ra0 := (mword_of_int 10 : mword 5).
Notation Ra1 := (mword_of_int 11 : mword 5).
Notation Ra2 := (mword_of_int 12 : mword 5).
Notation Ra3 := (mword_of_int 13 : mword 5).
Notation Ra4 := (mword_of_int 14 : mword 5).
Notation Ra5 := (mword_of_int 15 : mword 5).

Local Ltac regne := reg_ne_side.

Local Ltac ilidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

Section InitlogDefs.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  (* BORROW the block's first word out of its byte list, and give it back.
     The window vocabulary is ByteBuf's ([bb_bytes_of_list] to trade the
     list for a named window, [bb_word4_acc] to borrow the aligned cell at
     offset 0); all this lemma adds is that the word there IS [il_hdrw].
     initlog never WRITES the buffer, so the give-back is at the same word,
     and [ByteBuf.bb_set_mk] -- writing back what was read changes nothing --
     is what says the handle brelse gets is bread's, byte for byte. *)
  Lemma il_hdr_acc (a : Arch.pa) (bs : list (bv 8)) :
    (4 <= length bs)%nat ->
    is_aligned_paddr (Physaddr a) 4 = true ->
    ([∗ list] j ↦ x ∈ bs, pa_add a j ↦ₘ x) -∗
    a ↦₄ il_hdrw bs ∗
    (a ↦₄ il_hdrw bs -∗ ([∗ list] j ↦ x ∈ bs, pa_add a j ↦ₘ x)).
  Proof.
    intros Hlen Hal.
    assert (Ha0 : pa_add a 0%nat = a) by apply RiscvExtras.pa_add_0.
    assert (Hmk : bb_mk (fun j => bs !!! j) 0%nat = il_hdrw bs).
    { rewrite /bb_mk /il_hdrw /hdr_n.
      destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn [length] in Hlen;
        try (exfalso; lia).
      reflexivity. }
    rewrite (bb_bytes_of_list a bs).
    iIntros "Hw".
    iDestruct (bb_word4_acc a (length bs) 0%nat (length bs - 4)%nat
                 (fun j => bs !!! j) ltac:(lia)
                 ltac:(rewrite Ha0; exact Hal) with "Hw") as "[Hc Hback]".
    rewrite Ha0 Hmk.
    iSplitL "Hc"; [iExact "Hc"|].
    iIntros "Hc".
    iDestruct ("Hback" $! (il_hdrw bs) with "Hc") as "Hw".
    (* the opening rewrite already put the give-back's window in [bb_bytes]
       form too, so only the unfolding is left here *)
    rewrite /bb_bytes.
    iApply (big_sepL_mono with "Hw"). intros i jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    rewrite -Hmk (bb_set_mk (fun j => bs !!! j) 0%nat i). reflexivity.
  Qed.

  (* ---- THE COPY LOOP'S WORD ACCESS (durable-disk stage D1): borrow the
     aligned 32-bit word at data offset [4 (S k)] -- [lw a3,92(a5)]'s
     operand -- out of the buffer's byte list, and give it back.  The
     [il_hdr_acc] recipe at a moving offset. ---- *)

  Lemma il_take4 (bs : list (bv 8)) (o : nat) :
    (o + 4 <= length bs)%nat ->
    take 4 (drop o bs)
    = [bs !!! o; bs !!! (o + 1)%nat; bs !!! (o + 2)%nat; bs !!! (o + 3)%nat].
  Proof.
    intros Hle. apply list_eq. intros i.
    destruct (decide (i < 4)%nat) as [Hi | Hi].
    - rewrite lookup_take; [| lia]. rewrite lookup_drop.
      rewrite (list_lookup_lookup_total_lt bs (o + i)%nat); [| lia].
      destruct i as [|[|[|[|i']]]]; try lia; cbn.
      + rewrite Nat.add_0_r //.
      + reflexivity.
      + reflexivity.
      + reflexivity.
    - rewrite lookup_ge_None_2.
      + symmetry. apply lookup_ge_None_2. cbn [length]. lia.
      + rewrite length_take. lia.
  Qed.

  Lemma il_word_mk (bs : list (bv 8)) (k : nat) :
    (4 * k + 4 <= length bs)%nat ->
    bb_mk (fun j => bs !!! j) (4 * k)%nat = il_wordw bs k.
  Proof.
    intros Hle. rewrite /bb_mk /il_wordw /le_word.
    f_equal. f_equal.
    rewrite (il_take4 bs (4 * k)%nat Hle). reflexivity.
  Qed.

  Lemma il_word_acc (a : Arch.pa) (bs : list (bv 8)) (k : nat) :
    (4 * k + 4 <= length bs)%nat ->
    is_aligned_paddr (Physaddr (pa_add a (4 * k)%nat)) 4 = true ->
    ([∗ list] j ↦ x ∈ bs, pa_add a j ↦ₘ x) -∗
    pa_add a (4 * k)%nat ↦₄ il_wordw bs k ∗
    (pa_add a (4 * k)%nat ↦₄ il_wordw bs k -∗
       ([∗ list] j ↦ x ∈ bs, pa_add a j ↦ₘ x)).
  Proof.
    intros Hlen Hal.
    rewrite (bb_bytes_of_list a bs).
    iIntros "Hw".
    iDestruct (bb_word4_acc a (length bs) (4 * k)%nat (length bs - (4 * k) - 4)%nat
                 (fun j => bs !!! j) ltac:(lia) Hal with "Hw") as "[Hc Hback]".
    rewrite (il_word_mk bs k Hlen).
    iSplitL "Hc"; [iExact "Hc"|].
    iIntros "Hc".
    iDestruct ("Hback" $! (il_wordw bs k) with "Hc") as "Hw".
    rewrite /bb_bytes.
    iApply (big_sepL_mono with "Hw"). intros i jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    rewrite -(il_word_mk bs k Hlen) (bb_set_mk (fun j => bs !!! j) (4 * k)%nat i).
    reflexivity.
  Qed.

  (* ---- pull a CONTENTS FUNCTION out of a run of existential slots ---- *)
  Lemma il_sepL_exist {A : Type} (Φ : nat -> A -> list (bv 8) -> iProp Σ)
      (l : list A) :
    ([∗ list] i ↦ x ∈ l, ∃ bs : list (bv 8), Φ i x bs) -∗
    ∃ ys : list (list (bv 8)), ⌜length ys = length l⌝ ∗
      ([∗ list] i ↦ x ∈ l, Φ i x (ys !!! i)).
  Proof.
    iIntros "H".
    iInduction l as [|x l] "IH" forall (Φ).
    - iExists []. iSplitR; [done|]. done.
    - rewrite big_sepL_cons. iDestruct "H" as "[Hx Hl]".
      iDestruct "Hx" as (bs0) "Hx".
      iDestruct ("IH" $! (fun i y bs => Φ (S i) y bs) with "Hl") as (ys) "[%Hlen Hl]".
      iExists (bs0 :: ys). iSplitR.
      { iPureIntro. cbn [length]. lia. }
      rewrite big_sepL_cons. iSplitL "Hx"; [iExact "Hx"|].
      iApply (big_sepL_mono with "Hl"). intros i y Hy. reflexivity.
  Qed.

  (* an INDEX-ONLY big-op transports across any two lists of one length *)
  Lemma il_sepL_reindex {A B : Type} (l1 : list A) (l2 : list B)
      (Φ : nat -> iProp Σ) :
    length l1 = length l2 ->
    ([∗ list] i ↦ _ ∈ l1, Φ i) ⊢ ([∗ list] i ↦ _ ∈ l2, Φ i).
  Proof.
    revert l2 Φ. induction l1 as [|x l1 IH]; intros l2 Φ Hlen.
    - destruct l2; [done | cbn in Hlen; lia].
    - destruct l2 as [|y l2]; [cbn in Hlen; lia|].
      cbn in Hlen. injection Hlen as Hlen.
      rewrite !big_sepL_cons.
      iIntros "[H1 Hrest]". iFrame "H1".
      iApply (IH l2 (fun i => Φ (S i)) Hlen with "Hrest").
  Qed.

  (* over [seq 0 n] the element IS the index *)
  Lemma il_seq_body (n : nat) (Φ : nat -> iProp Σ) :
    ([∗ list] _ ↦ x ∈ seq 0 n, Φ x) ⊣⊢ ([∗ list] k ↦ _ ∈ seq 0 n, Φ k).
  Proof.
    apply big_sepL_proper. intros k x Hk.
    apply lookup_seq in Hk as [-> _]. done.
  Qed.

  (* the logged view's authority reads a client half's content off (the log
     layer holds BOTH at boot, so this costs nothing) *)
  Lemma il_fsb_lookup (γfs : fs_names) (L : gmap Z (list (bv 8)))
      (b : Z) (bs : list (bv 8)) :
    ghost_map_auth (fs_cache γfs) 1 L -∗ fs_chalf γfs b bs -∗ ⌜L !! b = Some bs⌝.
  Proof.
    rewrite /fs_chalf. iIntros "Ha Hb".
    iApply (ghost_map_lookup with "Ha Hb").
  Qed.

  (* ...and the same over a whole family, in one pass: what the recovering
     install needs is EVERY slot's content named in [L] (durable-disk 1a) *)
  Lemma il_fsb_all (γfs : fs_names) (L : gmap Z (list (bv 8)))
      (f : nat -> Z) (ys : nat -> list (bv 8)) (l : list nat) :
    ghost_map_auth (fs_cache γfs) 1 L -∗
    ([∗ list] k ∈ l, fs_chalf γfs (f k) (ys k)) -∗
    ⌜forall k : nat, k ∈ l -> L !! f k = Some (ys k)⌝.
  Proof.
    induction l as [|x l IH].
    - iIntros "Ha Hs". iPureIntro. intros k Hk.
      exfalso. exact (not_elem_of_nil k Hk).
    - iIntros "Ha Hs". rewrite big_sepL_cons.
      iDestruct "Hs" as "[Hx Hs]".
      iDestruct (il_fsb_lookup with "Ha Hx") as %Hlk.
      iDestruct (IH with "Ha Hs") as %Hall.
      iPureIntro. intros k Hk.
      apply elem_of_cons in Hk as [->|Hk]; [exact Hlk | exact (Hall k Hk)].
  Qed.

  (* the 30 header cells, re-formed from the decoded run and the junk tail *)
  Lemma il_cells_join (bs : list (bv 8)) (nh : nat) :
    (nh <= LOGBLOCKS)%nat ->
    ([∗ list] i ↦ w ∈ il_W bs nh, lh_block i ↦₄ w) -∗
    ([∗ list] i ∈ seq nh (LOGBLOCKS - nh), ∃ wj : SailStdpp.Values.mword 32, lh_block i ↦₄ wj) -∗
    ([∗ list] i ∈ seq 0 LOGBLOCKS, ∃ wj : SailStdpp.Values.mword 32, lh_block i ↦₄ wj).
  Proof.
    intros Hnh. iIntros "Hw Hj".
    assert (Hsp : seq 0 LOGBLOCKS = seq 0 nh ++ seq nh (LOGBLOCKS - nh)).
    { replace LOGBLOCKS with (nh + (LOGBLOCKS - nh))%nat at 1 by lia.
      rewrite seq_app. f_equal. }
    rewrite Hsp big_sepL_app.
    iSplitL "Hw".
    - iEval (rewrite (il_seq_body nh (fun x => (∃ wj : SailStdpp.Values.mword 32, lh_block x ↦₄ wj)%I))).
      iApply (il_sepL_reindex (il_W bs nh) (seq 0 nh)
                (fun i => (∃ wj : SailStdpp.Values.mword 32, lh_block i ↦₄ wj)%I)
                ltac:(rewrite il_W_length length_seq; reflexivity)).
      iApply (big_sepL_mono with "Hw"). intros k y Hy.
      iIntros "H". iExists y. iExact "H".
    - iApply (big_sepL_mono with "Hj"). intros k y Hy. done.
  Qed.

  (* an EMPTY indexed big-op is [emp]; naming it keeps the call sites free
     of bracketed spec-pattern goals *)
  Lemma il_bigL_nil {A : Type} (Psi : nat -> A -> iProp Σ) :
    ⊢ ([∗ list] i ↦ x ∈ ([] : list A), Psi i x).
  Proof. first [ done | rewrite big_sepL_nil; done ]. Qed.

  (* the client's own [fs_chalf] half against the handle's machinery half
     pins the bytes bread returned -- for either payload polarity *)
  Lemma il_pay_agree (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (dv bno : mword 32) (z : Z)
      (bs bsl bsd : list (bv 8)) (d : bool) :
    uint bno = z ->
    fs_chalf γfs z bs -∗
    bio_pay bn (fs_view γfs γd dev cov) k dv bno bsl bsd d -∗ ⌜bsl = bs⌝.
  Proof.
    intros <-. rewrite /bio_pay /fs_view /=. destruct d.
    - iIntros "Hc [Hm _]". iApply (fs_chalf_mdirty_agree with "Hc Hm").
    - iIntros "Hc [Hm _]". iApply (fs_chalf_mclean_agree with "Hc Hm").
  Qed.

End InitlogDefs.

(* ===================================================================== *)

(* ===================================================================== *)
(*  The dispatch/copy blocks, in a CID-free section: each lemma binds its  *)
(*  own hart, exactly like ProofInstallTrans's blocks.                     *)
(* ===================================================================== *)
Section InitlogBlocks.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  (* clones of ProofInstallTrans's small arithmetic helpers (a proof file
     may not import a sibling proof file) *)
  Lemma il_sext32 (z : Z) : (0 <= z < 2^31)%Z ->
    (sign_extend' 64 (mword_of_int z : SailStdpp.Values.mword 32) : SailStdpp.Values.mword 64)
    = mword_of_int z.
  Proof.
    intro Hz. apply bv_eq.
    rewrite (sext64_moi32_unsigned z Hz) moi64_unsigned.
    symmetry. apply bvw64_small. lia.
  Qed.

  Lemma il_sint_moi (z : Z) :
    (- 2 ^ 63 <= z < 2 ^ 63)%Z ->
    sint (mword_of_int z : SailStdpp.Values.mword 64) = z.
  Proof.
    intro Hz.
    assert (Hhm : bv_half_modulus 64 = (2 ^ 63)%Z) by reflexivity.
    change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
    rewrite moi64_unsigned bv_swrap_wrap.
    apply bv_swrap_small. rewrite Hhm. lia.
  Qed.

  Lemma il_geb_s0 (b : Z) :
    (0 <= b < 2 ^ 31)%Z ->
    zopz0zKzJ_s (zero_reg : SailStdpp.Values.mword 64)
                (mword_of_int b : SailStdpp.Values.mword 64) = Z.geb 0 b.
  Proof.
    intro Hb. unfold zopz0zKzJ_s.
    assert (Hz : sint (zero_reg : SailStdpp.Values.mword 64) = 0)
      by (vm_compute; reflexivity).
    rewrite Hz (il_sint_moi b ltac:(lia)). reflexivity.
  Qed.

  Lemma il_geb_pos (n : nat) : (0 < n)%nat -> Z.geb 0 (Z.of_nat n) = false.
  Proof. intro H. rewrite Z.geb_leb. apply Z.leb_gt. lia. Qed.

  Lemma il_n_small (n : nat) : (n <= LOGBLOCKS)%nat -> (0 <= Z.of_nat n < 2^31)%Z.
  Proof. rewrite /LOGBLOCKS. lia. Qed.

  (* the loaded [n] word, at its numeral once the decode bound pins it *)
  Lemma il_hdrw_moi (bs : list (bv 8)) (nh : nat) :
    hdr_n bs = Z.of_nat nh -> (nh <= LOGBLOCKS)%nat ->
    il_hdrw bs = (mword_of_int (Z.of_nat nh) : SailStdpp.Values.mword 32).
  Proof.
    intros Hn Hb. rewrite /il_hdrw Hn. apply bv_eq.
    rewrite Z_to_bv_unsigned.
    rewrite bv_wrap_small; [reflexivity|].
    unfold LOGBLOCKS in Hb.
    assert (Hm : bv_modulus 32 = 4294967296%Z) by (vm_compute; reflexivity).
    rewrite Hm. lia.
  Qed.

  (* the [slli a2,a2,2] value: [ofile_slli3]'s recipe at shift 2 *)
  Lemma il_slli2 (z : Z) : 0 <= z -> z * 4 < 18446744073709551616 ->
    shift_bits_left (mword_of_int z : SailStdpp.Values.mword 64)
                    (subrange_vec_dec (mword_of_int 2 : SailStdpp.Values.mword 6)
                       (Z.sub log2_xlen 1) 0)
    = (mword_of_int (z * 4) : SailStdpp.Values.mword 64).
  Proof.
    intros Hz0 Hz. apply bv_eq.
    unfold shift_bits_left, shiftl, with_word, get_word,
           MachineWord.MachineWord.logical_shift_left.
    rewrite bv_shiftl_unsigned.
    replace (bv_unsigned (MachineWord.MachineWord.N_to_word (MachineWord.MachineWord.Z_idx 64)
               (MachineWord.MachineWord.Z_idx (int_of_mword false
                  (subrange_vec_dec (mword_of_int 2 : SailStdpp.Values.mword 6) (Z.sub log2_xlen 1) 0))))) with 2
      by (vm_compute; reflexivity).
    assert (Hzlt : z < 18446744073709551616) by nia.
    rewrite (moi64_small z ltac:(lia)).
    rewrite (moi64_small (z * 4) ltac:(lia)).
    rewrite Z.shiftl_mul_pow2; [| lia].
    rewrite bv_wrap_small; [| unfold bv_modulus; cbn; lia].
    lia.
  Qed.

  (* the decoded write set's [t]-th word *)
  Lemma il_W_lookup (bs : list (bv 8)) (nh t : nat) :
    (t < nh)%nat ->
    il_W bs nh !! t = Some (il_wordw bs (S t)).
  Proof.
    intros Ht. rewrite /il_W list_lookup_fmap.
    rewrite lookup_seq_lt; [| exact Ht]. reflexivity.
  Qed.

  (* ================================================================== *)
  (*  +0x52 .. +0x5a : READ_HEAD'S COPY LOOP (durable-disk stage D1),     *)
  (*  live at a dirty header: word [S t] of the block into                *)
  (*  [log.lh.block[t]], for t = 0 .. nh-1.  No calls, no ghosts -- four  *)
  (*  instructions and the back edge.                                     *)
  (* ================================================================== *)
  Local Lemma il_copy `{GEN : GenId} (fuel : nat)
      (kk nh : nat) (bs_hdr : list (bv 8))
      (pj : SailStdpp.Values.mword 64) (nK : nat) (b : bool) :
    (kk < NBUF)%nat ->
    (nh <= LOGBLOCKS)%nat ->
    length bs_hdr = 1024%nat ->
    forall (CID0 : CpuId) (t : nat) (M : regfile),
    (t < nh)%nat ->
    (nh - t <= fuel)%nat ->
    M !!! Regidx Ra5 = il_cur kk t ->
    M !!! Regidx (mword_of_int 14 : SailStdpp.Values.mword 5) = (lh_block t : SailStdpp.Values.mword 64) ->
    M !!! Regidx Ra2 = il_cur kk nh ->
    M !!! Regidx Ra0 = (bnode kk : SailStdpp.Values.mword 64) ->
    sie_cap_gpr KT1 M nK b pj -∗
    pc_is (mword_of_int (KernelSyms.initlog + 0x52) : SailStdpp.Values.mword 64) -∗
    kernel_text -∗
    ([∗ list] jj ↦ x ∈ bs_hdr, pa_add (b_data (bnode kk)) jj ↦ₘ x) -∗
    ([∗ list] i ↦ w ∈ take t (il_W bs_hdr nh), lh_block i ↦₄ w) -∗
    ([∗ list] i ∈ seq t (LOGBLOCKS - t), ∃ wj : SailStdpp.Values.mword 32, lh_block i ↦₄ wj) -∗
    wp_next b pj (fun (CIDo : CpuId) =>
      ∀ (M' : regfile),
        ⌜forall c : SailStdpp.Values.mword 5, is_cs_idx c = true ->
           M' !!! Regidx c = (M !!! Regidx c : SailStdpp.Values.mword 64)⌝ -∗
        ⌜M' !!! Regidx Ra0 = (bnode kk : SailStdpp.Values.mword 64)⌝ -∗
        sie_cap_gpr KT1 M' nK b pj -∗
        pc_is (mword_of_int (KernelSyms.initlog + 0x5e) : SailStdpp.Values.mword 64) -∗
        ([∗ list] jj ↦ x ∈ bs_hdr, pa_add (b_data (bnode kk)) jj ↦ₘ x) -∗
        ([∗ list] i ↦ w ∈ il_W bs_hdr nh, lh_block i ↦₄ w) -∗
        ([∗ list] i ∈ seq nh (LOGBLOCKS - nh), ∃ wj : SailStdpp.Values.mword 32, lh_block i ↦₄ wj) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkk Hnh Hlen.
    induction fuel as [|fuel IH]; intros CID0 t M Ht Hfuel Ha5 Ha4 Ha2 Ha0.
    { exfalso. lia. }
    iIntros "Hcg Hpc #Htext Hby Hdone Hjunk Hcont".
    (* the junk cell at the cursor *)
    assert (Hjq : seq t (LOGBLOCKS - t) = t :: seq (S t) (LOGBLOCKS - S t)).
    { replace (LOGBLOCKS - t)%nat with (S (LOGBLOCKS - S t))%nat by lia.
      reflexivity. }
    iEval (rewrite Hjq big_sepL_cons) in "Hjunk".
    iDestruct "Hjunk" as "[Hcell Hjunk]".
    iDestruct "Hcell" as (wj) "Hcell".
    (* the word borrowed out of the buffer *)
    iDestruct (il_word_acc (b_data (bnode kk)) bs_hdr (S t)
                 ltac:(unfold LOGBLOCKS in Hnh; lia)
                 (il_align4k kk (S t) Hkk ltac:(lia))
                 with "Hby") as "[Hword Hback]".
    (* ===== +0x52 c.lw a3,92(a5) ===== *)
    assert (Hcaddr : add_vec (rget M Ra5) (sign_extend' 64 (mword_of_int 92 : SailStdpp.Values.mword 12))
                     = pa_add (b_data (bnode kk)) (4 * S t)%nat).
    { rgne. rewrite Ha5. exact (il_cur_addr kk t). }
    iEval (rewrite -Hcaddr) in "Hword".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.initlog + 0x52)) Ra3 Ra5
              (mword_of_int 92 : SailStdpp.Values.mword 12) M nK
              (il_wordw bs_hdr (S t)) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hword").
    { iApply (ili_52 with "Htext"). }
    iIntros (CIDc1 Hsc1) "Hcg Hpc Hword".
    iEval (rewrite Hcaddr) in "Hword".
    iDestruct ("Hback" with "Hword") as "Hby".
    set (E1 := <[Regidx Ra3 := regval_into_reg
                  (sign_extend' 64 (il_wordw bs_hdr (S t)))]> M).
    assert (HE1a3 : E1 !!! Regidx Ra3 = sign_extend' 64 (il_wordw bs_hdr (S t)))
      by (rewrite /E1; apply upd_eq).
    assert (HE1a4 : E1 !!! Regidx (mword_of_int 14 : SailStdpp.Values.mword 5)
                    = (lh_block t : SailStdpp.Values.mword 64))
      by (rewrite /E1 upd_ne; [exact Ha4 | vm_compute; discriminate]).
    assert (HE1a5 : E1 !!! Regidx Ra5 = il_cur kk t)
      by (rewrite /E1 upd_ne; [exact Ha5 | vm_compute; discriminate]).
    assert (HE1a2 : E1 !!! Regidx Ra2 = il_cur kk nh)
      by (rewrite /E1 upd_ne; [exact Ha2 | vm_compute; discriminate]).
    assert (HE1a0 : E1 !!! Regidx Ra0 = (bnode kk : SailStdpp.Values.mword 64))
      by (rewrite /E1 upd_ne; [exact Ha0 | vm_compute; discriminate]).
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x52) : SailStdpp.Values.mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x54))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    (* ===== +0x54 c.sw a3,0(a4) ===== *)
    assert (Hsaddr : add_vec (rget E1 (mword_of_int 14 : SailStdpp.Values.mword 5))
                       (sign_extend' 64 (mword_of_int 0 : SailStdpp.Values.mword 12))
                     = (lh_block t : SailStdpp.Values.mword 64)).
    { rgne. rewrite HE1a4. exact (il_blk_at t). }
    iEval (rewrite -Hsaddr) in "Hcell".
    iApply (wp_csw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.initlog + 0x54))
              Ra3 (mword_of_int 14 : SailStdpp.Values.mword 5)
              (mword_of_int 0 : SailStdpp.Values.mword 12) E1 nK wj b
              with "Hcg Hpc [] Hcell").
    { iApply (ili_54 with "Htext"). }
    iIntros (CIDc2 Hsc2) "Hcg Hpc Hcell".
    iEval (rewrite Hsaddr) in "Hcell".
    assert (Hstv : trunc32 (rget E1 Ra3) = il_wordw bs_hdr (S t)).
    { rgne. rewrite HE1a3. apply trunc32_sext64. }
    iEval (rewrite Hstv) in "Hcell".
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x54) : SailStdpp.Values.mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x56))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    (* ===== +0x56 c.addi a5,a5,4 ===== *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.initlog + 0x56)) Ra5 (mword_of_int 4 : SailStdpp.Values.mword 6)
              E1 nK b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_56 with "Htext"). }
    iIntros (CIDc3 Hsc3) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    assert (Hcurstep : add_vec (E1 !!! Regidx Ra5)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : SailStdpp.Values.mword 6)))
                       = il_cur kk (S t)).
    { rewrite HE1a5. exact (il_cur_step kk t). }
    iEval (rewrite Hcurstep) in "Hcg".
    set (E2 := <[Regidx Ra5 := regval_into_reg (il_cur kk (S t))]> E1).
    assert (HE2a5 : E2 !!! Regidx Ra5 = il_cur kk (S t))
      by (rewrite /E2; apply upd_eq).
    assert (HE2a4 : E2 !!! Regidx (mword_of_int 14 : SailStdpp.Values.mword 5)
                    = (lh_block t : SailStdpp.Values.mword 64))
      by (rewrite /E2 upd_ne; [exact HE1a4 | vm_compute; discriminate]).
    assert (HE2a2 : E2 !!! Regidx Ra2 = il_cur kk nh)
      by (rewrite /E2 upd_ne; [exact HE1a2 | vm_compute; discriminate]).
    assert (HE2a0 : E2 !!! Regidx Ra0 = (bnode kk : SailStdpp.Values.mword 64))
      by (rewrite /E2 upd_ne; [exact HE1a0 | vm_compute; discriminate]).
    assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x56) : SailStdpp.Values.mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x58))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58) in "Hpc".
    (* ===== +0x58 c.addi a4,a4,4 ===== *)
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.initlog + 0x58))
              (mword_of_int 14 : SailStdpp.Values.mword 5) (mword_of_int 4 : SailStdpp.Values.mword 6)
              E2 nK b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_58 with "Htext"). }
    iIntros (CIDc4 Hsc4) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    assert (Hblkstep : add_vec (E2 !!! Regidx (mword_of_int 14 : SailStdpp.Values.mword 5))
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : SailStdpp.Values.mword 6)))
                       = (lh_block (S t) : SailStdpp.Values.mword 64)).
    { rewrite HE2a4. exact (il_blk_step t). }
    iEval (rewrite Hblkstep) in "Hcg".
    set (E3 := <[Regidx (mword_of_int 14 : SailStdpp.Values.mword 5)
                 := regval_into_reg (lh_block (S t) : SailStdpp.Values.mword 64)]> E2).
    assert (HE3a4 : E3 !!! Regidx (mword_of_int 14 : SailStdpp.Values.mword 5)
                    = (lh_block (S t) : SailStdpp.Values.mword 64))
      by (rewrite /E3; apply upd_eq).
    assert (HE3a5 : E3 !!! Regidx Ra5 = il_cur kk (S t))
      by (rewrite /E3 upd_ne; [exact HE2a5 | vm_compute; discriminate]).
    assert (HE3a2 : E3 !!! Regidx Ra2 = il_cur kk nh)
      by (rewrite /E3 upd_ne; [exact HE2a2 | vm_compute; discriminate]).
    assert (HE3a0 : E3 !!! Regidx Ra0 = (bnode kk : SailStdpp.Values.mword 64))
      by (rewrite /E3 upd_ne; [exact HE2a0 | vm_compute; discriminate]).
    assert (HE3cs : forall c : SailStdpp.Values.mword 5, is_cs_idx c = true ->
              E3 !!! Regidx c = (M !!! Regidx c : SailStdpp.Values.mword 64)).
    { intros c Hc.
      assert (Hne : forall r : SailStdpp.Values.mword 5, is_cs_idx r = false -> Regidx c <> Regidx r).
      { intros r Hr. apply not_eq_sym. apply is_cs_idx_true_neq; assumption. }
      rewrite /E3 upd_ne; [| apply Hne; vm_compute; reflexivity].
      rewrite /E2 upd_ne; [| apply Hne; vm_compute; reflexivity].
      rewrite /E1 upd_ne; [| apply Hne; vm_compute; reflexivity].
      reflexivity. }
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.initlog + 0x58) : SailStdpp.Values.mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x5a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    (* the done run grows by the cell just written *)
    iAssert ([∗ list] i ↦ w ∈ take (S t) (il_W bs_hdr nh), lh_block i ↦₄ w)%I
      with "[Hdone Hcell]" as "Hdone".
    { rewrite (take_S_r (il_W bs_hdr nh) t (il_wordw bs_hdr (S t))
                 (il_W_lookup bs_hdr nh t Ht)).
      rewrite big_sepL_app big_sepL_singleton.
      iSplitL "Hdone"; [iExact "Hdone"|].
      rewrite length_take il_W_length Nat.min_l; [| lia].
      rewrite Nat.add_0_r. iExact "Hcell". }
    (* ===== +0x5a bne a5,a2 : the back edge / the exit ===== *)
    destruct (decide (S t = nh)) as [Hend | Hmore].
    - (* ---- the last word: fall through to +0x5e ---- *)
      assert (Hcmp : neq_vec (rget E3 Ra5) (rget E3 Ra2) = false).
      { rgne. rgne. rewrite HE3a5 HE3a2 Hend /neq_vec.
        rewrite (il_cur_eq kk nh Hnh). reflexivity. }
      iApply (wp_bne_fall_s_sconf (mword_of_int (KernelSyms.initlog + 0x5a))
                (mword_of_int 8184 : SailStdpp.Values.mword 13) Ra2 Ra5 E3 nK b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp with "Hcg Hpc []").
      { iApply (ili_5a with "Htext"). }
      iIntros (CIDc5 Hsc5) "Hcg Hpc".
      assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.initlog + 0x5a) : SailStdpp.Values.mword 64) 4
                      = mword_of_int (KernelSyms.initlog + 0x5e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp5e) in "Hpc".
      iSpecialize ("Hcont" $! CIDc5 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! E3 with "[%] [%] Hcg Hpc Hby [Hdone] [Hjunk]").
      + exact HE3cs.
      + exact HE3a0.
      + rewrite Hend (take_ge (il_W bs_hdr nh)); [| rewrite il_W_length; lia].
        iExact "Hdone".
      + rewrite Hend. iExact "Hjunk".
    - (* ---- another word: the branch takes us back to +0x52 ---- *)
      assert (Hcmp : neq_vec (rget E3 Ra5) (rget E3 Ra2) = true).
      { rgne. rgne. rewrite HE3a5 HE3a2 /neq_vec.
        rewrite (il_cur_inj kk (S t) nh Hkk ltac:(lia) Hnh Hmore).
        reflexivity. }
      iApply (wp_bne_taken_s_sconf (mword_of_int (KernelSyms.initlog + 0x5a))
                (mword_of_int 8184 : SailStdpp.Values.mword 13) Ra2 Ra5 E3 nK b
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
      { iApply (ili_5a with "Htext"). }
      iNext. iIntros (CIDc5 Hsc5) "Hcg Hpc".
      assert (Htgt52 : add_vec (mword_of_int (KernelSyms.initlog + 0x5a) : SailStdpp.Values.mword 64)
                         (sign_extend' 64 (mword_of_int 8184 : SailStdpp.Values.mword 13))
                       = mword_of_int (KernelSyms.initlog + 0x52))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt52) in "Hpc".
      iApply (IH CIDc5 (S t) E3 ltac:(lia) ltac:(lia) HE3a5 HE3a4 HE3a2 HE3a0
                with "Hcg Hpc Htext Hby Hdone Hjunk [Hcont]").
      rewrite /wp_next. iIntros (CIDo Hso M') "%HcsX %Ha0X HcgX HpcX HbyX HdoneX HjunkX".
      iSpecialize ("Hcont" $! CIDo with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! M' with "[%] [%] HcgX HpcX HbyX HdoneX HjunkX").
      + intros c Hc. rewrite (HcsX c Hc). exact (HE3cs c Hc).
      + exact Ha0X.
  Qed.

  (* ================================================================== *)
  (*  +0x40 -> +0x5e : THE HEADER DISPATCH (durable-disk stage D1).       *)
  (*  At a clean header the [blez] skips the copy loop; at a dirty one    *)
  (*  the loop runs ([il_copy]).  One CPS block, one continuation: the    *)
  (*  cells arrive holding the decoded write set (empty at nh = 0) and    *)
  (*  the junk tail.                                                      *)
  (* ================================================================== *)
  Local Lemma il_hd `{GEN : GenId} `{CID0 : CpuId}
      (kk nh : nat) (bs_hdr : list (bv 8))
      (pj : SailStdpp.Values.mword 64) (nK : nat) (b : bool)
      (M : regfile) :
    (kk < NBUF)%nat ->
    (nh <= LOGBLOCKS)%nat ->
    nh = (hdr_dec bs_hdr).1 ->
    length bs_hdr = 1024%nat ->
    M !!! Regidx Ra2 = sign_extend' 64 (il_hdrw bs_hdr) ->
    M !!! Regidx Ra0 = (bnode kk : SailStdpp.Values.mword 64) ->
    sie_cap_gpr KT1 M nK b pj -∗
    pc_is (mword_of_int (KernelSyms.initlog + 0x40) : SailStdpp.Values.mword 64) -∗
    kernel_text -∗
    ([∗ list] jj ↦ x ∈ bs_hdr, pa_add (b_data (bnode kk)) jj ↦ₘ x) -∗
    ([∗ list] i ∈ seq 0 LOGBLOCKS, ∃ wj : SailStdpp.Values.mword 32, lh_block i ↦₄ wj) -∗
    wp_next b pj (fun (CIDo : CpuId) =>
      ∀ (M' : regfile),
        ⌜forall c : SailStdpp.Values.mword 5, is_cs_idx c = true ->
           M' !!! Regidx c = (M !!! Regidx c : SailStdpp.Values.mword 64)⌝ -∗
        ⌜M' !!! Regidx Ra0 = (bnode kk : SailStdpp.Values.mword 64)⌝ -∗
        sie_cap_gpr KT1 M' nK b pj -∗
        pc_is (mword_of_int (KernelSyms.initlog + 0x5e) : SailStdpp.Values.mword 64) -∗
        ([∗ list] jj ↦ x ∈ bs_hdr, pa_add (b_data (bnode kk)) jj ↦ₘ x) -∗
        ([∗ list] i ↦ w ∈ il_W bs_hdr nh, lh_block i ↦₄ w) -∗
        ([∗ list] i ∈ seq nh (LOGBLOCKS - nh), ∃ wj : SailStdpp.Values.mword 32, lh_block i ↦₄ wj) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hkk Hnh Hdec Hlen Ha2 Ha0.
    assert (Hhn : hdr_n bs_hdr = Z.of_nat nh)
      by (rewrite Hdec; symmetry; apply hdr_dec_n).
    assert (Ha2m : M !!! Regidx Ra2
                   = (mword_of_int (Z.of_nat nh) : SailStdpp.Values.mword 64)).
    { rewrite Ha2 (il_hdrw_moi bs_hdr nh Hhn Hnh).
      apply il_sext32. exact (il_n_small nh Hnh). }
    iIntros "Hcg Hpc #Htext Hby Hjunk Hcont".
    destruct (decide (nh = 0%nat)) as [Hn0 | Hnpos].
    - (* ---- clean header: the branch skips the loop ---- *)
      assert (Hcmp : zopz0zKzJ_s (zero_reg : SailStdpp.Values.mword 64) (rget M Ra2) = true).
      { rgne. rewrite Ha2m (il_geb_s0 (Z.of_nat nh) (il_n_small nh Hnh)) Hn0.
        reflexivity. }
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.initlog + 0x40))
                (mword_of_int 30 : SailStdpp.Values.mword 13) Ra2 M nK b
                ltac:(vm_compute; discriminate) Hcmp ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (ili_40 with "Htext"). }
      iNext. iIntros (CIDh1 Hsh1) "Hcg Hpc".
      assert (Htgt5e : add_vec (mword_of_int (KernelSyms.initlog + 0x40) : SailStdpp.Values.mword 64)
                         (sign_extend' 64 (mword_of_int 30 : SailStdpp.Values.mword 13))
                       = mword_of_int (KernelSyms.initlog + 0x5e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt5e) in "Hpc".
      iSpecialize ("Hcont" $! CIDh1 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! M with "[%] [%] Hcg Hpc Hby [] [Hjunk]").
      + intros c Hc. reflexivity.
      + exact Ha0.
      + rewrite Hn0 /il_W. iApply il_bigL_nil.
      + rewrite Hn0. iExact "Hjunk".
    - (* ---- dirty header: the setup then the live loop ---- *)
      assert (Hposn : (0 < nh)%nat) by lia.
      assert (Hcmp : zopz0zKzJ_s (zero_reg : SailStdpp.Values.mword 64) (rget M Ra2) = false).
      { rgne. rewrite Ha2m (il_geb_s0 (Z.of_nat nh) (il_n_small nh Hnh)).
        exact (il_geb_pos nh Hposn). }
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.initlog + 0x40))
                (mword_of_int 30 : SailStdpp.Values.mword 13) Ra2 M nK b
                ltac:(vm_compute; discriminate) Hcmp
                with "Hcg Hpc []").
      { iApply (ili_40 with "Htext"). }
      iIntros (CIDh1 Hsh1) "Hcg Hpc".
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x40) : SailStdpp.Values.mword 64) 4
                      = mword_of_int (KernelSyms.initlog + 0x44))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* ===== +0x44 c.mv a5,a0 : the source cursor ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.initlog + 0x44)) Ra5 Ra0
                M nK b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (ili_44 with "Htext"). }
      iIntros (CIDh2 Hsh2) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      assert (Hcur0 : add_vec (zero_reg : SailStdpp.Values.mword 64) (M !!! Regidx Ra0)
                      = il_cur kk 0).
      { rewrite Ha0. exact (il_cur_0 kk). }
      iEval (rewrite Hcur0) in "Hcg".
      set (F1 := <[Regidx Ra5 := regval_into_reg (il_cur kk 0)]> M).
      assert (HF1a5 : F1 !!! Regidx Ra5 = il_cur kk 0)
        by (rewrite /F1; apply upd_eq).
      assert (HF1a2 : F1 !!! Regidx Ra2
                      = (mword_of_int (Z.of_nat nh) : SailStdpp.Values.mword 64))
        by (rewrite /F1 upd_ne; [exact Ha2m | vm_compute; discriminate]).
      assert (HF1a0 : F1 !!! Regidx Ra0 = (bnode kk : SailStdpp.Values.mword 64))
        by (rewrite /F1 upd_ne; [exact Ha0 | vm_compute; discriminate]).
      assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x44) : SailStdpp.Values.mword 64) 2
                      = mword_of_int (KernelSyms.initlog + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp46) in "Hpc".
      (* ===== +0x46 / +0x4a : a4 := &log.lh.block[0] ===== *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.initlog + 0x46))
                (mword_of_int 14 : SailStdpp.Values.mword 5) (mword_of_int 30 : SailStdpp.Values.mword 20)
                F1 nK b ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (ili_46 with "Htext"). }
      iIntros (CIDh3 Hsh3) "Hcg Hpc".
      set (F2 := <[Regidx (mword_of_int 14 : SailStdpp.Values.mword 5)
                   := regval_into_reg
                        (add_vec (mword_of_int (KernelSyms.initlog + 0x46) : SailStdpp.Values.mword 64)
                           (auipc_off (mword_of_int 30 : SailStdpp.Values.mword 20)))]> F1).
      assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.initlog + 0x46) : SailStdpp.Values.mword 64) 4
                      = mword_of_int (KernelSyms.initlog + 0x4a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4a) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.initlog + 0x4a))
                (mword_of_int 14 : SailStdpp.Values.mword 5) (mword_of_int 14 : SailStdpp.Values.mword 5)
                (mword_of_int 1924 : SailStdpp.Values.mword 12) F2 nK b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (ili_4a with "Htext"). }
      iIntros (CIDh4 Hsh4) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (F3 := <[Regidx (mword_of_int 14 : SailStdpp.Values.mword 5)
                   := regval_into_reg
                        (add_vec (F2 !!! Regidx (mword_of_int 14 : SailStdpp.Values.mword 5))
                           (sign_extend' 64 (mword_of_int 1924 : SailStdpp.Values.mword 12)))]> F2).
      assert (HF3a4 : F3 !!! Regidx (mword_of_int 14 : SailStdpp.Values.mword 5)
                      = (lh_block 0 : SailStdpp.Values.mword 64)).
      { rewrite /F3 upd_eq /F2 upd_eq. exact il_reloc_blk0. }
      assert (HF3a5 : F3 !!! Regidx Ra5 = il_cur kk 0).
      { rewrite /F3 upd_ne; [| vm_compute; discriminate].
        rewrite /F2 upd_ne; [exact HF1a5 | vm_compute; discriminate]. }
      assert (HF3a2 : F3 !!! Regidx Ra2
                      = (mword_of_int (Z.of_nat nh) : SailStdpp.Values.mword 64)).
      { rewrite /F3 upd_ne; [| vm_compute; discriminate].
        rewrite /F2 upd_ne; [exact HF1a2 | vm_compute; discriminate]. }
      assert (HF3a0 : F3 !!! Regidx Ra0 = (bnode kk : SailStdpp.Values.mword 64)).
      { rewrite /F3 upd_ne; [| vm_compute; discriminate].
        rewrite /F2 upd_ne; [exact HF1a0 | vm_compute; discriminate]. }
      assert (Hpp4e : add_vec_int (mword_of_int (KernelSyms.initlog + 0x4a) : SailStdpp.Values.mword 64) 4
                      = mword_of_int (KernelSyms.initlog + 0x4e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp4e) in "Hpc".
      (* ===== +0x4e c.slli a2,a2,2 ===== *)
      iApply (wp_cslli_s_sconf (mword_of_int (KernelSyms.initlog + 0x4e))
                (Regidx Ra2) Ra2 (mword_of_int 2 : SailStdpp.Values.mword 6)
                F3 nK b eq_refl
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (ili_4e with "Htext"). }
      iIntros (CIDh5 Hsh5) "Hcg Hpc".
      set (F4 := <[Regidx Ra2 := regval_into_reg
                    (shift_bits_left (F3 !!! Regidx Ra2)
                       (subrange_vec_dec (mword_of_int 2 : SailStdpp.Values.mword 6)
                          (Z.sub log2_xlen 1) 0))]> F3).
      assert (HF4a2 : F4 !!! Regidx Ra2
                      = (mword_of_int (Z.of_nat nh * 4) : SailStdpp.Values.mword 64)).
      { rewrite /F4 upd_eq HF3a2.
        apply il_slli2; [lia | unfold LOGBLOCKS in Hnh; lia]. }
      assert (HF4a0 : F4 !!! Regidx Ra0 = (bnode kk : SailStdpp.Values.mword 64))
        by (rewrite /F4 upd_ne; [exact HF3a0 | vm_compute; discriminate]).
      assert (Hpp50 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x4e) : SailStdpp.Values.mword 64) 2
                      = mword_of_int (KernelSyms.initlog + 0x50))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp50) in "Hpc".
      (* ===== +0x50 c.add a2,a2,a0 : the end pointer ===== *)
      iApply (wp_cadd_s_sconf (mword_of_int (KernelSyms.initlog + 0x50))
                Ra2 Ra0 F4 nK b
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (ili_50 with "Htext"). }
      iIntros (CIDh6 Hsh6) "Hcg Hpc".
      iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
      assert (Hendv : add_vec (F4 !!! Regidx Ra2) (F4 !!! Regidx Ra0)
                      = il_cur kk nh).
      { rewrite HF4a2 HF4a0.
        assert (Hz : (Z.of_nat nh * 4)%Z = Z.of_nat (4 * nh)%nat) by lia.
        rewrite Hz. rewrite pa_add_comm. rewrite /il_cur. f_equal. }
      iEval (rewrite Hendv) in "Hcg".
      set (F5 := <[Regidx Ra2 := regval_into_reg (il_cur kk nh)]> F4).
      assert (HF5a2 : F5 !!! Regidx Ra2 = il_cur kk nh)
        by (rewrite /F5; apply upd_eq).
      assert (HF5a5 : F5 !!! Regidx Ra5 = il_cur kk 0).
      { rewrite /F5 upd_ne; [| vm_compute; discriminate].
        rewrite /F4 upd_ne; [exact HF3a5 | vm_compute; discriminate]. }
      assert (HF5a4 : F5 !!! Regidx (mword_of_int 14 : SailStdpp.Values.mword 5)
                      = (lh_block 0 : SailStdpp.Values.mword 64)).
      { rewrite /F5 upd_ne; [| vm_compute; discriminate].
        rewrite /F4 upd_ne; [exact HF3a4 | vm_compute; discriminate]. }
      assert (HF5a0 : F5 !!! Regidx Ra0 = (bnode kk : SailStdpp.Values.mword 64))
        by (rewrite /F5 upd_ne; [exact HF4a0 | vm_compute; discriminate]).
      assert (HF5cs : forall c : SailStdpp.Values.mword 5, is_cs_idx c = true ->
                F5 !!! Regidx c = (M !!! Regidx c : SailStdpp.Values.mword 64)).
      { intros c Hc.
        assert (Hne : forall r : SailStdpp.Values.mword 5, is_cs_idx r = false -> Regidx c <> Regidx r).
        { intros r Hr. apply not_eq_sym. apply is_cs_idx_true_neq; assumption. }
        rewrite /F5 upd_ne; [| apply Hne; vm_compute; reflexivity].
        rewrite /F4 upd_ne; [| apply Hne; vm_compute; reflexivity].
        rewrite /F3 upd_ne; [| apply Hne; vm_compute; reflexivity].
        rewrite /F2 upd_ne; [| apply Hne; vm_compute; reflexivity].
        rewrite /F1 upd_ne; [| apply Hne; vm_compute; reflexivity].
        reflexivity. }
      assert (Hpp52 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x50) : SailStdpp.Values.mword 64) 2
                      = mword_of_int (KernelSyms.initlog + 0x52))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp52) in "Hpc".
      (* ===== the live loop ===== *)
      iAssert ([∗ list] i ↦ w ∈ take 0 (il_W bs_hdr nh), lh_block i ↦₄ w)%I
        as "Hdone".
      { rewrite take_0. iApply il_bigL_nil. }
      iApply (il_copy nh kk nh bs_hdr pj nK b Hkk Hnh Hlen CIDh6 0%nat F5
                Hposn ltac:(lia) HF5a5 HF5a4 HF5a2 HF5a0
                with "Hcg Hpc Htext Hby Hdone Hjunk [Hcont]").
      rewrite /wp_next. iIntros (CIDo Hso M') "%HcsX %Ha0X HcgX HpcX HbyX HdoneX HjunkX".
      iSpecialize ("Hcont" $! CIDo with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! M' with "[%] [%] HcgX HpcX HbyX HdoneX HjunkX").
      + intros c Hc. rewrite (HcsX c Hc). exact (HF5cs c Hc).
      + exact Ha0X.
  Qed.

End InitlogBlocks.

Section ProofInitlog.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_initlog_sconf 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names)
      (γfs : fs_names) (γpr : gname)
      (cov : gset Z) (logstart : Z) (dev : mword 32) (sb : mword 64)
      (bs_hdr : list (bv 8))
      (Bh : nat -> list (bv 8))
      (M : log_mirror)
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (vlock : mword 32) (vname vcpu : mword 64)
      (v_start v_dev v_nc v_n : mword 32)
      (pidv : mword 32) (dq dqs : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
      (bs_sb : list (bv 8)) (sbrec : fs_sb)
    : wp_initlog_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs γpr
                            cov logstart dev sb bs_hdr Bh M L D
                            vlock vname vcpu v_start v_dev v_nc v_n
                            pidv dq dqs m K eb b lks Vpr bs_sb sbrec.
  Proof.
    cbv beta delta [wp_initlog_sconf_body].
    intros pcE pj ret_tgt c_name c_cpu HK Hgeom Hj Hgl Hbnd Hndup Hin Hpk
           Hma0 Hma1 HDf HLmir Hbelow Hsbok Hsbparse.
    destruct Hgeom as [Hcovok Hlogsub].
    iIntros "Hcg Hcnt Hextc Hclmc #Htext #Hkdata Hpc #Hpenv #Hbio #Hseam
              #Hpenvpk Hhomes #Hcert Hmirf
              Hlfree
              Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hsbf Hlock Hname Hcpu
              Hstc Hdevc Hout Hcmt Hnc Hncell Hblk #Hbrow HLauth HDauth Hcovf Hfsb
              Hslotsfs Hslots Hb1 Hcont".
    (* THE ERA'S MIRROR, BORN TRUE AND IN CUSTODY (durable-disk 1a): the
       half at a NAMED picture and the swap receipt PowerOn's custody hook
       already earned.  There is no boot swap here any more; every write
       below is a value-chained one. *)
    iDestruct "Hmirf" as "[Hmirh #Hswlb]".
    (* the home-set-free form install_trans takes *)
    iAssert (fs_bytes_any γfs) as "#Hbany".
    { rewrite /fs_bytes_any. iExists (fs_home_set cov logstart).
      iExact "Hbrow". }
    (* THE eb-GUARD-TO-b-GUARD BRIDGE.  The complement's transports carry an
       [eb]-indexed guard and every chain fact a straight-line stretch
       produces is [b]-indexed; at level 0 [cpu_own_eb_agree] gives [eb = b]
       outright, so one [rewrite] at each transport is enough.  See
       claude-notes/completed/eb-generic-sweep.md, "Hebf". *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    (* ---- the header block is covered, and its number is a small int ---- *)
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
    (* ---- THE ERA'S PICTURE IS THE LOGGED VIEW AT THE HEADER (1a).  Read
       off here, where the auth and the header's client half are both in
       hand: it is what makes [lm_hdr M logstart] the header initlog is
       about to bread, hence what lets every install permit below name the
       write set the on-disk header records. ---- *)
    iDestruct (il_fsb_lookup with "HLauth Hfsb") as %Hhdrlk.
    assert (Hhdrmir : lm_view M (log_hdr_bno logstart) = bs_hdr).
    { pose proof (HLmir logstart Hhdrcov) as Hm.
      rewrite /log_hdr_bno. rewrite /log_hdr_bno in Hhdrlk.
      rewrite Hhdrlk in Hm. by injection Hm. }
    assert (HMhdr : lm_hdr M logstart = hdr_dec bs_hdr)
      by (rewrite /lm_hdr Hhdrmir //).
    (* every entry the on-disk header names is a covered HOME block, so it
       is neither the header nor a slot -- the side condition every reading
       of the install chain asks for *)
    assert (Hentne : forall (i : nat) (bb : Z),
              (hdr_dec bs_hdr).2 !! i = Some bb -> bb <> log_hdr_bno logstart).
    { intros i bb Hi.
      destruct (Hin bb (elem_of_list_lookup_2 _ _ _ Hi)) as [_ Hout].
      intros ->. exact (Hout (log_hdr_in_region logstart)). }
    assert (Hentslot : forall (i k : nat) (bb : Z),
              (hdr_dec bs_hdr).2 !! i = Some bb -> (k < LOGBLOCKS)%nat ->
              bb <> log_slot_bno logstart k).
    { intros i k bb Hi Hk.
      destruct (Hin bb (elem_of_list_lookup_2 _ _ _ Hi)) as [_ Hout].
      intros ->. exact (Hout (log_slot_in_region logstart k Hk)). }
    assert (HWlen : length ((hdr_dec bs_hdr).2) = (hdr_dec bs_hdr).1)
      by apply hdr_dec_length.
    (* the header's write set is duplicate-free, in the INJECTIVITY form the
       two install chains ([LogDefs.lm_install_hit] on the mirror,
       [SpecInstallTrans.it_rec_L_hit] on the logged view) are stated at *)
    (* [FsCrash]'s [NoDup] is stdpp's; this file's bare one is the
       stdlib inductive.  Convert once. *)
    assert (HndupS : base.NoDup ((hdr_dec bs_hdr).2))
      by (by apply NoDup_ListNoDup).
    assert (HinjWs : forall (i k : nat) (c : Z),
              (hdr_dec bs_hdr).2 !! i = Some c ->
              (hdr_dec bs_hdr).2 !! k = Some c -> i = k).
    { intros i k c H1 H2.
      apply (NoDup_lookup ((hdr_dec bs_hdr).2) i k c);
        [ first [exact Hndup | by apply NoDup_ListNoDup] | exact H1 | exact H2]. }
    assert (Hinjw : forall (i k : nat) (v v' : mword 32),
              il_W bs_hdr ((hdr_dec bs_hdr).1) !! i = Some v ->
              il_W bs_hdr ((hdr_dec bs_hdr).1) !! k = Some v' ->
              uint v = uint v' -> i = k).
    { intros i k v v' H1 H2 Heq.
      apply (HinjWs i k (uint v)).
      - rewrite -(il_W_uint bs_hdr).
        exact (it_map_lookup (il_W bs_hdr ((hdr_dec bs_hdr).1)) i v H1).
      - rewrite -(il_W_uint bs_hdr) Heq.
        exact (it_map_lookup (il_W bs_hdr ((hdr_dec bs_hdr).1)) k v' H2). }
    (* ---- the "log" string literal, out of the data image ---- *)
    assert (Hlogs : forall jj bt, cstring_bytes "log"%string !! jj = Some bt ->
                     KernelData.kernel_data !! (log_name_str + Z.of_nat jj)%Z
                     = Some bt).
    { intros jj bt Hjj.
      do 4 (destruct jj as [|jj];
            [vm_compute in Hjj; injection Hjj as <-; vm_compute; reflexivity |]);
      vm_compute in Hjj; discriminate. }
    iPoseProof (kernel_data_string log_name_str "log"%string
                  (mword_of_int log_name_str : mword 64) eq_refl
                  ltac:(unfold text_end, log_name_str; lia)
                  ltac:(vm_compute; discriminate) Hlogs
                  with "Hkdata") as "#Hstr".
    (* ---- the frame geometry (6 slots; ra@40 s0@32 s1@24 s2@16 s3@8) ---- *)
    pose (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spr := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6)))).
    assert (Hspr6 : spr = pa_stk sp0 6).
    { unfold spr, pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb1 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 5).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec spr (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 6).
    { unfold spr, sp0, pa_stk, add_vec_int. rewrite pa_stk_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* ===== PROLOGUE ===== *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m).
    iApply (wp_caddi16sp_push_s_sconf pcE (mword_of_int 61 : mword 6) m K 6 b
              ltac:(lia) Hspr6 with "Hcg Hpc []").
    { iApply (ili_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 61 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spr)
      by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & _)".
    iDestruct "S1" as (vra0) "Hc1". iDestruct "S2" as (vs00) "Hc2".
    iDestruct "S3" as (vs10) "Hc3". iDestruct "S4" as (vs20) "Hc4".
    iDestruct "S5" as (vs30) "Hc5". iDestruct "S6" as (vs60) "Hc6".
    assert (Hra_v : R1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs0_v : R1 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs1_v : R1 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs2_v : R1 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs3_v : R1 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1a0 : R1 !!! Regidx Ra0 = sign_extend' 64 dev).
    { rewrite /R1 upd_ne; [exact Hma0 | vm_compute; discriminate]. }
    assert (HR1a1 : R1 !!! Regidx Ra1 = sb).
    { rewrite /R1 upd_ne; [exact Hma1 | vm_compute; discriminate]. }
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.initlog + 0x02))
      by (unfold pcE; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,40(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.initlog + 0x02)) (mword_of_int 5 : mword 6) Rra
              R1 (K - 6)%nat vra0 b with "Hcg Hpc [] [Hc1]").
    { iApply (ili_02 with "Htext"). }
    { iEval (rewrite HspR1 Hb1). iExact "Hc1". }
    iIntros (CID2 Hs2) "Hcg Hpc Hc1".
    iEval (rgne) in "Hc1". iEval (rewrite HspR1 Hb1 Hra_v) in "Hc1".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,32(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.initlog + 0x04)) (mword_of_int 4 : mword 6) Rs0
              R1 (K - 6)%nat vs00 b with "Hcg Hpc [] [Hc2]").
    { iApply (ili_04 with "Htext"). }
    { iEval (rewrite HspR1 Hb2). iExact "Hc2". }
    iIntros (CID3 Hs3) "Hcg Hpc Hc2".
    iEval (rgne) in "Hc2". iEval (rewrite HspR1 Hb2 Hs0_v) in "Hc2".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.sdsp s1,24(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.initlog + 0x06)) (mword_of_int 3 : mword 6) Rs1
              R1 (K - 6)%nat vs10 b with "Hcg Hpc [] [Hc3]").
    { iApply (ili_06 with "Htext"). }
    { iEval (rewrite HspR1 Hb3). iExact "Hc3". }
    iIntros (CID4 Hs4) "Hcg Hpc Hc3".
    iEval (rgne) in "Hc3". iEval (rewrite HspR1 Hb3 Hs1_v) in "Hc3".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 c.sdsp s2,16(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.initlog + 0x08)) (mword_of_int 2 : mword 6) Rs2
              R1 (K - 6)%nat vs20 b with "Hcg Hpc [] [Hc4]").
    { iApply (ili_08 with "Htext"). }
    { iEval (rewrite HspR1 Hb4). iExact "Hc4". }
    iIntros (CID5 Hs5) "Hcg Hpc Hc4".
    iEval (rgne) in "Hc4". iEval (rewrite HspR1 Hb4 Hs2_v) in "Hc4".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.initlog + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    (* +0x0a c.sdsp s3,8(sp) *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.initlog + 0x0a)) (mword_of_int 1 : mword 6) Rs3
              R1 (K - 6)%nat vs30 b with "Hcg Hpc [] [Hc5]").
    { iApply (ili_0a with "Htext"). }
    { iEval (rewrite HspR1 Hb5). iExact "Hc5". }
    iIntros (CID6 Hs6) "Hcg Hpc Hc5".
    iEval (rgne) in "Hc5". iEval (rewrite HspR1 Hb5 Hs3_v) in "Hc5".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.initlog + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    (* +0x0c c.addi4spn s0,sp,48 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.initlog + 0x0c)) (Cregidx (mword_of_int 0))
              (mword_of_int 12 : mword 8) Rs0 R1 (K - 6)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_0c with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 12 : mword 8))))]> R1).
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.initlog + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x0e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    (* +0x0e c.mv s1,a0 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.initlog + 0x0e)) Rs1 Ra0
              R2 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_0e with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    set (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R2 Ra0))]> R2).
    assert (HR2a0 : R2 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /R2 upd_ne; [exact HR1a0 | vm_compute; discriminate]).
    assert (HR3s1 : R3 !!! Regidx Rs1 = sign_extend' 64 dev).
    { rewrite /R3 upd_eq. rgne. rewrite HR2a0. apply add_vec_zero_l. }
    assert (HR3a1 : R3 !!! Regidx Ra1 = sb).
    { rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [exact HR1a1 | vm_compute; discriminate]. }
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.mv s3,a1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.initlog + 0x10)) Rs3 Ra1
              R3 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_10 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (R4 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R3 Ra1))]> R3).
    assert (HR4s3 : R4 !!! Regidx Rs3 = sb).
    { rewrite /R4 upd_eq. rgne. rewrite HR3a1. apply add_vec_zero_l. }
    assert (HR4s1 : R4 !!! Regidx Rs1 = sign_extend' 64 dev)
      by (rewrite /R4 upd_ne; [exact HR3s1 | vm_compute; discriminate]).
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x12))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 auipc s2,0x1e *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.initlog + 0x12)) Rs2 (mword_of_int 30 : mword 20)
              R4 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_12 with "Htext"). }
    iIntros (CID10 Hs10) "Hcg Hpc".
    set (R5 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.initlog + 0x12) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> R4).
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x12) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 addi s2,s2,1966 : s2 := &log *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.initlog + 0x16)) Rs2 Rs2
              (mword_of_int 1928 : mword 12) R5 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_16 with "Htext"). }
    iIntros (CID11 Hs11) "Hcg Hpc".
    set (R6 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (rget R5 Rs2)
                     (sign_extend' 64 (mword_of_int 1928 : mword 12)))]> R5).
    assert (HR6s2 : R6 !!! Regidx Rs2 = log_addr).
    { rewrite /R6 upd_eq. rgne. rewrite /R5 upd_eq /log_addr.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.initlog + 0x16) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x1a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a auipc a1,0x4 *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.initlog + 0x1a)) Ra1 (mword_of_int 4 : mword 20)
              R6 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_1a with "Htext"). }
    iIntros (CID12 Hs12) "Hcg Hpc".
    set (R7 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.initlog + 0x1a) : mword 64)
                     (auipc_off (mword_of_int 4 : mword 20)))]> R6).
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.initlog + 0x1a) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e addi a1,a1,-1658 : a1 := "log" *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.initlog + 0x1e)) Ra1 Ra1
              (mword_of_int 2320 : mword 12) R7 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_1e with "Htext"). }
    iIntros (CID13 Hs13) "Hcg Hpc".
    set (R8 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (rget R7 Ra1)
                     (sign_extend' 64 (mword_of_int 2320 : mword 12)))]> R7).
    assert (HR8a1 : R8 !!! Regidx Ra1 = (mword_of_int log_name_str : mword 64)).
    { rewrite /R8 upd_eq. rgne. rewrite /R7 upd_eq /log_name_str.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HR8s2 : R8 !!! Regidx Rs2 = log_addr).
    { rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [exact HR6s2 | vm_compute; discriminate]. }
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x1e) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    (* +0x22 c.mv a0,s2 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.initlog + 0x22)) Ra0 Rs2
              R8 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_22 with "Htext"). }
    iIntros (CID14 Hs14) "Hcg Hpc".
    set (R9 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R8 Rs2))]> R8).
    assert (HR9a0 : R9 !!! Regidx Ra0 = log_addr).
    { rewrite /R9 upd_eq. rgne. rewrite HR8s2. apply add_vec_zero_l. }
    assert (HR9a1 : R9 !!! Regidx Ra1 = (mword_of_int log_name_str : mword 64))
      by (rewrite /R9 upd_ne; [exact HR8a1 | vm_compute; discriminate]).
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    (* ===== +0x24 jal ra,initlock ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.initlog + 0x24)) Rra
              (mword_of_int 2084648 : mword 21) R9 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (ili_24 with "Htext"). }
    iIntros (CID15 Hs15) "Hcg Hpc".
    set (RA := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.initlog + 0x24) : mword 64) 4)]> R9).
    assert (Htgtil : add_vec (mword_of_int (KernelSyms.initlog + 0x24) : mword 64)
                       (sign_extend' 64 (mword_of_int 2084648 : mword 21))
                     = mword_of_int KernelSyms.initlock)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtil) in "Hpc".
    assert (HRAa0 : RA !!! Regidx Ra0 = log_addr)
      by (rewrite /RA upd_ne; [exact HR9a0 | vm_compute; discriminate]).
    assert (HRAa1 : RA !!! Regidx Ra1 = (mword_of_int log_name_str : mword 64))
      by (rewrite /RA upd_ne; [exact HR9a1 | vm_compute; discriminate]).
    assert (HRAra : RA !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.initlog + 0x24) : mword 64) 4)
      by (rewrite /RA; apply upd_eq).
    assert (HRAsp : RA !!! Regidx csp_rs1 = spr).
    { rewrite /RA upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [exact HspR1 | vm_compute; discriminate]. }
    assert (HRAcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              RA !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /RA upd_ne; [| regne]. rewrite /R9 upd_ne; [| regne].
      rewrite /R8 upd_ne; [| regne]. rewrite /R7 upd_ne; [| regne].
      rewrite /R6 upd_ne; [| regne]. rewrite /R5 upd_ne; [| regne].
      rewrite /R4 upd_ne; [| regne]. rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (HRAs1 : RA !!! Regidx Rs1 = sign_extend' 64 dev).
    { rewrite /RA upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [| vm_compute; discriminate].
      rewrite /R4 upd_ne; [exact HR4s1 | vm_compute; discriminate]. }
    assert (HRAs2 : RA !!! Regidx Rs2 = log_addr)
      by (rewrite /RA upd_ne; [| vm_compute; discriminate];
          rewrite /R9 upd_ne; [exact HR8s2 | vm_compute; discriminate]).
    assert (HRAs3 : RA !!! Regidx Rs3 = sb).
    { rewrite /RA upd_ne; [| vm_compute; discriminate].
      rewrite /R9 upd_ne; [| vm_compute; discriminate].
      rewrite /R8 upd_ne; [| vm_compute; discriminate].
      rewrite /R7 upd_ne; [| vm_compute; discriminate].
      rewrite /R6 upd_ne; [| vm_compute; discriminate].
      rewrite /R5 upd_ne; [exact HR4s3 | vm_compute; discriminate]. }
    iApply (Initlock.wp_initlock_sconf KT1 RA vlock vname vcpu "log"%string
              (K - 6)%nat b pj ltac:(lia)
              with "Hcg Htext Hpc [] [Hlock] [Hname] [Hcpu]").
    { iEval (rewrite HRAa1). iExact "Hstr". }
    { iEval (rewrite HRAa0). iExact "Hlock". }
    { iEval (rewrite HRAa0). iExact "Hname". }
    { iEval (rewrite HRAa0). iExact "Hcpu". }
    iIntros (CID16 Hs16 mil) "Hcg Hpc %Hilcs Hlock Hlname Hcpu".
    iEval (rewrite HRAa0) in "Hlock".
    iEval (rewrite HRAa0 HRAa1) in "Hlname".
    iEval (rewrite HRAa0) in "Hcpu".
    assert (Hpcil : ret_pc (RA !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.initlog + 0x28)).
    { rewrite HRAra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcil) in "Hpc".
    pose proof Hilcs as Hilcs_full.
    assert (Hmilsp : mil !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hilcs_full csp_rs1 ltac:(vm_compute; reflexivity));
          exact HRAsp).
    assert (Hmils1 : mil !!! Regidx Rs1 = sign_extend' 64 dev)
      by (rewrite (callee_saved_lookup Hilcs_full Rs1 ltac:(vm_compute; reflexivity));
          exact HRAs1).
    assert (Hmils2 : mil !!! Regidx Rs2 = log_addr)
      by (rewrite (callee_saved_lookup Hilcs_full Rs2 ltac:(vm_compute; reflexivity));
          exact HRAs2).
    assert (Hmils3 : mil !!! Regidx Rs3 = sb)
      by (rewrite (callee_saved_lookup Hilcs_full Rs3 ltac:(vm_compute; reflexivity));
          exact HRAs3).
    assert (Hmilcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              mil !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hilcs_full c Hcs).
      exact (HRAcs c Hcs N2 N8 N9 N18 N19). }
    (* ===== THE NAME FIELD IS SEALED HERE; THE LOCK IS NOT.  The four
       gnames arrived with the contract ([log_free_tok γ], minted in the era
       fupd), so nothing is allocated at this point: the ledger / epoch /
       registry halves are just unpacked for later, and initlock's two
       zeroed lock cells ("Hlock" / "Hcpu") are carried untouched to the
       end, where [newlock_at] seals them onto [ln_lk γ] together with the
       assembled [log_res].  No callee in between wants them: install_trans
       and write_head take [log_frozen], not [log_ctx]. ===== *)
    iApply fupd_wp.
    iMod (lock_name_intro with "Hstr Hlname") as "#Hlnm".
    iModIntro.
    iEval (rewrite /log_free_tok) in "Hlfree".
    iDestruct "Hlfree" as "(Hlkf & Hops & Hepa & Hxa & Htxa)".
    (* ===== +0x28 lw a1,20(s3) : a1 := sb->logstart ===== *)
    assert (Hsbad : add_vec (rget mil Rs3)
                      (sign_extend' 64 (mword_of_int 20 : mword 12))
                    = pa_add sb 20%nat).
    { rgne. rewrite Hmils3 il_s20. reflexivity. }
    iEval (rewrite -Hsbad) in "Hsbf".
    iApply (wp_lw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.initlog + 0x28)) Ra1 Rs3
              (mword_of_int 20 : mword 12) mil (K - 6)%nat
              (mword_of_int logstart : mword 32) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hsbf").
    { iApply (ili_28 with "Htext"). }
    iIntros (CID17 Hs17) "Hcg Hpc Hsbf".
    iEval (rewrite Hsbad) in "Hsbf".
    set (T1 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (mword_of_int logstart : mword 32))]> mil).
    assert (HT1a1 : T1 !!! Regidx Ra1
                    = sign_extend' 64 (mword_of_int logstart : mword 32))
      by (rewrite /T1; apply upd_eq).
    assert (HT1s1 : T1 !!! Regidx Rs1 = sign_extend' 64 dev)
      by (rewrite /T1 upd_ne; [exact Hmils1 | vm_compute; discriminate]).
    assert (HT1s2 : T1 !!! Regidx Rs2 = log_addr)
      by (rewrite /T1 upd_ne; [exact Hmils2 | vm_compute; discriminate]).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = spr)
      by (rewrite /T1 upd_ne; [exact Hmilsp | vm_compute; discriminate]).
    assert (HT1cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              T1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /T1 upd_ne; [| regne]. exact (Hmilcs c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.initlog + 0x28) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp2c) in "Hpc".
    (* ===== +0x2c sw a1,24(s2) : log.start := sb->logstart ===== *)
    assert (Hstad : add_vec (rget T1 Rs2)
                      (sign_extend' 64 (mword_of_int 24 : mword 12)) = l_start).
    { rgne. rewrite HT1s2 il_s24. apply il_l_start. }
    iEval (rewrite -Hstad) in "Hstc".
    iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.initlog + 0x2c)) Ra1 Rs2
              (mword_of_int 24 : mword 12) T1 (K - 6)%nat v_start b
              with "Hcg Hpc [] Hstc").
    { iApply (ili_2c with "Htext"). }
    iIntros (CID18 Hs18) "Hcg Hpc Hstc".
    iEval (rewrite Hstad) in "Hstc".
    assert (Hsv1 : trunc32 (rget T1 Ra1) = (mword_of_int logstart : mword 32)).
    { rgne. rewrite HT1a1. apply trunc32_sext64. }
    iEval (rewrite Hsv1) in "Hstc".
    assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x2c) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x30))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp30) in "Hpc".
    (* ===== +0x30 sw s1,36(s2) : log.dev := dev ===== *)
    assert (Hdvad : add_vec (rget T1 Rs2)
                      (sign_extend' 64 (mword_of_int 36 : mword 12)) = l_dev).
    { rgne. rewrite HT1s2 il_s36. apply il_l_dev. }
    iEval (rewrite -Hdvad) in "Hdevc".
    iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.initlog + 0x30)) Rs1 Rs2
              (mword_of_int 36 : mword 12) T1 (K - 6)%nat v_dev b
              with "Hcg Hpc [] Hdevc").
    { iApply (ili_30 with "Htext"). }
    iIntros (CID19 Hs19) "Hcg Hpc Hdevc".
    iEval (rewrite Hdvad) in "Hdevc".
    assert (Hsv2 : trunc32 (rget T1 Rs1) = dev).
    { rgne. rewrite HT1s1. apply trunc32_sext64. }
    iEval (rewrite Hsv2) in "Hdevc".
    (* ---- FREEZE: the two cells go persistent, giving [log_frozen] ---- *)
    iMod (word4_pointsto_persist with "Hstc") as "#Hstp".
    iMod (word4_pointsto_persist with "Hdevc") as "#Hdvp".
    iAssert (log_frozen logstart dev) as "#Hfroz".
    { rewrite /log_frozen. iSplitL; [iExact "Hdvp" | iExact "Hstp"]. }
    assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x30) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x34))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp34) in "Hpc".
    (* ===== +0x34 c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.initlog + 0x34)) Ra0 Rs1
              T1 (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_34 with "Htext"). }
    iIntros (CID20 Hs20) "Hcg Hpc".
    set (T2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget T1 Rs1))]> T1).
    assert (HT2a0 : T2 !!! Regidx Ra0 = sign_extend' 64 dev).
    { rewrite /T2 upd_eq. rgne. rewrite HT1s1. apply add_vec_zero_l. }
    assert (HT2a1 : T2 !!! Regidx Ra1
                    = sign_extend' 64 (mword_of_int logstart : mword 32))
      by (rewrite /T2 upd_ne; [exact HT1a1 | vm_compute; discriminate]).
    assert (HT2s2 : T2 !!! Regidx Rs2 = log_addr)
      by (rewrite /T2 upd_ne; [exact HT1s2 | vm_compute; discriminate]).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = spr)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    assert (HT2cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              T2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /T2 upd_ne; [| regne]. exact (HT1cs c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x34) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp36) in "Hpc".
    (* ===== +0x36 jal ra,bread ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.initlog + 0x36)) Rra
              (mword_of_int 2092874 : mword 21) T2 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (ili_36 with "Htext"). }
    iIntros (CID21 Hs21) "Hcg Hpc".
    set (T3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.initlog + 0x36) : mword 64) 4)]> T2).
    assert (Htgtbr : add_vec (mword_of_int (KernelSyms.initlog + 0x36) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092874 : mword 21))
                     = mword_of_int KernelSyms.bread)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtbr) in "Hpc".
    assert (HT3a0 : T3 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /T3 upd_ne; [exact HT2a0 | vm_compute; discriminate]).
    assert (HT3a1 : T3 !!! Regidx Ra1
                    = sign_extend' 64 (mword_of_int logstart : mword 32))
      by (rewrite /T3 upd_ne; [exact HT2a1 | vm_compute; discriminate]).
    assert (HT3s2 : T3 !!! Regidx Rs2 = log_addr)
      by (rewrite /T3 upd_ne; [exact HT2s2 | vm_compute; discriminate]).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = spr)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    assert (HT3ra : T3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.initlog + 0x36) : mword 64) 4)
      by (rewrite /T3; apply upd_eq).
    assert (HT3cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              T3 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /T3 upd_ne; [| regne]. exact (HT2cs c Hcs N2 N8 N9 N18 N19). }
    (* one slot unit for the bread; the rest stay put *)
    assert (Hsplit1 : ((LOGBLOCKS + 2) + 2)%nat = (1 + 33)%nat)
      by (unfold LOGBLOCKS; lia).
    iEval (rewrite Hsplit1 bslots_op) in "Hslots".
    iDestruct "Hslots" as "[Hs1u Hslots]".
    iDestruct (cpu_own_transport CID CID21 0 eb pj b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID CID21 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CID21 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclmc") as "Hclmc".
    iDestruct (wp_next_shift (b := true) (CIDa := CID) (CIDb := CID21) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbr : (K_bread <= K - 6)%nat) by (lia).
    iApply (Bread.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev (mword_of_int logstart : mword 32) dq
              T3 (K - 6)%nat eb b
              _ Vpr HKbr Hbnolt eq_refl Hcovin eq_refl Hj Hgl HT3a0 HT3a1
              Hbelow
              with "Hcg Hcnt Hextc Hclmc Htext Hkdata Hpc Hpenv Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hs1u").
    all: try lkbelow.
    iIntros (CID22 Hs22 mB kk bs0 bsd0 d0)
      "%Hfacts Hcg Hcnt Hextc Hclmc Hpc Hppid Hheld".
    destruct Hfacts as [Hcs1 HmBa0].
    assert (Hpc3a : ret_pc (T3 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.initlog + 0x3a)).
    { rewrite HT3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc3a) in "Hpc".
    pose proof Hcs1 as Hcs1_cs.
    assert (HmBs2 : mB !!! Regidx Rs2 = log_addr)
      by (rewrite (callee_saved_lookup Hcs1_cs Rs2 ltac:(vm_compute; reflexivity));
          exact HT3s2).
    assert (HmBsp : mB !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs1_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HT3sp).
    assert (HmBcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              mB !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hcs1_cs c Hcs).
      exact (HT3cs c Hcs N2 N8 N9 N18 N19). }
    (* ---- the handle: its bytes ARE the header block's logical content ---- *)
    rewrite /bio_locked /bio_held.
    iDestruct "Hheld" as
      "(%HA & %HB & %HC & Hslk & Hvalid & Hbdev & Hbown & Hdisk & Hpay)".
    assert (Huintl : uint (mword_of_int logstart : mword 32)
                     = log_hdr_bno logstart)
      by (rewrite /log_hdr_bno; exact Huint).
    iDestruct (il_pay_agree bn γfs γd dev cov kk dev
                 (mword_of_int logstart : mword 32) (log_hdr_bno logstart)
                 bs_hdr bs0 bsd0 d0 Huintl with "Hfsb Hpay") as %->.
    rewrite /buf_own /bpa.
    iDestruct "Hbown" as "(Hbno & Hbdsk & %Hlen & Hby)".
    assert (Hal : is_aligned_paddr (Physaddr (b_data (bnode kk))) 4 = true)
      by (apply il_align4; exact HA).
    assert (Hlen4 : (4 <= length bs_hdr)%nat) by (rewrite Hlen; lia).
    iDestruct (il_hdr_acc (b_data (bnode kk)) bs_hdr Hlen4 Hal with "Hby")
      as "[Hword Hback]".
    (* ===== +0x3a c.lw a2,88(a0) : a2 := lh->n ( = 0 ) ===== *)
    assert (Hhaddr : add_vec (rget mB Ra0)
                       (sign_extend' 64 (mword_of_int 88 : mword 12))
                     = b_data (bnode kk)).
    { rgne. rewrite HmBa0 il_s88. apply il_hdr_addr. }
    iEval (rewrite -Hhaddr) in "Hword".
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.initlog + 0x3a)) Ra2 Ra0
              (mword_of_int 88 : mword 12) mB (K - 6)%nat
              (il_hdrw bs_hdr) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] Hword").
    { iApply (ili_3a with "Htext"). }
    iIntros (CID23 Hs23) "Hcg Hpc Hword".
    iEval (rewrite Hhaddr) in "Hword".
    iDestruct ("Hback" with "Hword") as "Hby".
    set (B1 := <[Regidx Ra2 := regval_into_reg
                  (sign_extend' 64 (il_hdrw bs_hdr))]> mB).
    assert (HB1a2 : B1 !!! Regidx Ra2
                    = sign_extend' 64 (il_hdrw bs_hdr))
      by (rewrite /B1; apply upd_eq).
    assert (HB1a0 : B1 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B1 upd_ne; [exact HmBa0 | vm_compute; discriminate]).
    assert (HB1s2 : B1 !!! Regidx Rs2 = log_addr)
      by (rewrite /B1 upd_ne; [exact HmBs2 | vm_compute; discriminate]).
    assert (HB1sp : B1 !!! Regidx csp_rs1 = spr)
      by (rewrite /B1 upd_ne; [exact HmBsp | vm_compute; discriminate]).
    assert (HB1cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              B1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /B1 upd_ne; [| regne]. exact (HmBcs c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.initlog + 0x3a) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x3c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp3c) in "Hpc".
    (* ===== +0x3c sw a2,44(s2) : log.lh.n := 0 ===== *)
    assert (Hlhad : add_vec (rget B1 Rs2)
                      (sign_extend' 64 (mword_of_int 44 : mword 12)) = lh_n_pa).
    { rgne. rewrite HB1s2 il_s44. apply il_l_lhn. }
    iEval (rewrite -Hlhad) in "Hncell".
    iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.initlog + 0x3c)) Ra2 Rs2
              (mword_of_int 44 : mword 12) B1 (K - 6)%nat v_n b
              with "Hcg Hpc [] Hncell").
    { iApply (ili_3c with "Htext"). }
    iIntros (CID24 Hs24) "Hcg Hpc Hncell".
    iEval (rewrite Hlhad) in "Hncell".
    assert (Hsv3 : trunc32 (rget B1 Ra2) = il_hdrw bs_hdr).
    { rgne. rewrite HB1a2. apply trunc32_sext64. }
    iEval (rewrite Hsv3) in "Hncell".
    assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x3c) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x40))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp40) in "Hpc".
    (* ===== +0x40 -> +0x5e : THE HEADER DISPATCH (stage D1's [il_hd]): the
       clean header skips the copy loop, the dirty one runs it live ===== *)
    iApply (il_hd kk ((hdr_dec bs_hdr).1) bs_hdr pj (K - 6)%nat b B1
              HA Hbnd eq_refl Hlen HB1a2 HB1a0
              with "Hcg Hpc Htext Hby Hblk").
    iIntros (CID25 Hs25 B1x) "%HB1xcs %HB1xa0 Hcg Hpc Hby Hcells Hjunk".
    (* the head's register facts, carried across the dispatch *)
    assert (HB1xsp : B1x !!! Regidx csp_rs1 = spr).
    { rewrite (HB1xcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HB1sp. }
    assert (HB1xcs' : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              B1x !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (HB1xcs c Hcs). exact (HB1cs c Hcs N2 N8 N9 N18 N19). }
    (* rebuild the handle: the buffer was only READ *)
    iAssert (bio_locked bn (fs_view γfs γd dev cov) kk pidv dev
               (mword_of_int logstart : mword 32) bs_hdr bsd0 d0)
      with "[Hslk Hvalid Hbdev Hbno Hbdsk Hby Hdisk Hpay]" as "Hheld".
    { rewrite /bio_locked /bio_held /buf_own /bpa.
      iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iSplitL "Hslk"; [iExact "Hslk"|].
      iSplitL "Hvalid"; [iExact "Hvalid"|]. iSplitL "Hbdev"; [iExact "Hbdev"|].
      iSplitR "Hdisk Hpay".
      { iSplitL "Hbno"; [iExact "Hbno"|]. iSplitL "Hbdsk"; [iExact "Hbdsk"|].
        iSplitR; [iPureIntro; exact Hlen|]. iExact "Hby". }
      iSplitL "Hdisk"; [iExact "Hdisk"|]. iExact "Hpay". }
    (* ===== +0x5e jal ra,brelse ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.initlog + 0x5e)) Rra
              (mword_of_int 2093098 : mword 21) B1x (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (ili_5e with "Htext"). }
    iIntros (CID26 Hs26) "Hcg Hpc".
    set (B2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.initlog + 0x5e) : mword 64) 4)]> B1x).
    assert (Htgtbl : add_vec (mword_of_int (KernelSyms.initlog + 0x5e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093098 : mword 21))
                     = mword_of_int KernelSyms.brelse)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtbl) in "Hpc".
    assert (HB2a0 : B2 !!! Regidx Ra0 = bnode kk)
      by (rewrite /B2 upd_ne; [exact HB1xa0 | vm_compute; discriminate]).
    assert (HB2sp : B2 !!! Regidx csp_rs1 = spr)
      by (rewrite /B2 upd_ne; [exact HB1xsp | vm_compute; discriminate]).
    assert (HB2ra : B2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.initlog + 0x5e) : mword 64) 4)
      by (rewrite /B2; apply upd_eq).
    assert (HB2cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              B2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /B2 upd_ne; [| regne]. exact (HB1xcs' c Hcs N2 N8 N9 N18 N19). }
    iDestruct (cpu_own_transport CID22 CID26 0 eb pj b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID22 CID26 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID22 CID26 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclmc") as "Hclmc".
    iDestruct (wp_next_shift (b := true) (CIDa := CID21) (CIDb := CID26) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKbl : (K_brelse <= K - 6)%nat) by (lia).
    iApply (Brelse.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) kk pidv dev
              (mword_of_int logstart : mword 32) dq B2 (K - 6)%nat eb pj
              bs_hdr bsd0 d0 b _ Vpr HKbl HA HB2a0
              Hbelow
              with "Hcg Hcnt Htext Hpc Hbio Hppid Hprocs Hheld").
    all: try lkbelow.
    iIntros (CID27 Hs27 mR) "%Hcs2 Hcg Hcnt Hpc Hppid Hs1u".
    assert (Hpc62 : ret_pc (B2 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.initlog + 0x62)).
    { rewrite HB2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc62) in "Hpc".
    pose proof Hcs2 as Hcs2_cs.
    assert (HmRsp : mR !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs2_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HB2sp).
    assert (HmRcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              mR !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hcs2_cs c Hcs).
      exact (HB2cs c Hcs N2 N8 N9 N18 N19). }
    (* ===== +0x62 c.li a0,1 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.initlog + 0x62)) Ra0
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              mR (K - 6)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (ili_62 with "Htext"). }
    iIntros (CID28 Hs28) "Hcg Hpc".
    set (C1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 1 : mword 64)]> mR).
    assert (HC1a0 : C1 !!! Regidx Ra0 = (mword_of_int 1 : mword 64))
      by (rewrite /C1; apply upd_eq).
    assert (HC1sp : C1 !!! Regidx csp_rs1 = spr)
      by (rewrite /C1 upd_ne; [exact HmRsp | vm_compute; discriminate]).
    assert (HC1cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              C1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /C1 upd_ne; [| regne]. exact (HmRcs c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x62) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    (* ===== +0x64 jal ra,install_trans ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.initlog + 0x64)) Rra
              (mword_of_int 2096848 : mword 21) C1 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (ili_64 with "Htext"). }
    iIntros (CID29 Hs29) "Hcg Hpc".
    set (C2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.initlog + 0x64) : mword 64) 4)]> C1).
    assert (Htgtit : add_vec (mword_of_int (KernelSyms.initlog + 0x64) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096848 : mword 21))
                     = mword_of_int KernelSyms.install_trans)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtit) in "Hpc".
    assert (HC2a0 : C2 !!! Regidx Ra0 = (mword_of_int 1 : mword 64))
      by (rewrite /C2 upd_ne; [exact HC1a0 | vm_compute; discriminate]).
    assert (HC2sp : C2 !!! Regidx csp_rs1 = spr)
      by (rewrite /C2 upd_ne; [exact HC1sp | vm_compute; discriminate]).
    assert (HC2ra : C2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.initlog + 0x64) : mword 64) 4)
      by (rewrite /C2; apply upd_eq).
    assert (HC2cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              C2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /C2 upd_ne; [| regne]. exact (HC1cs c Hcs N2 N8 N9 N18 N19). }
    (* the two units install_trans wants: the one brelse just returned plus
       one out of the 33 still parked *)
    assert (Hsplit2 : 33%nat = (1 + 32)%nat) by lia.
    iEval (rewrite Hsplit2 bslots_op) in "Hslots".
    iDestruct "Hslots" as "[Hs2u Hpool]".
    iAssert (bslots 2) with "[Hs1u Hs2u]" as "Hs2".
    { rewrite (_ : 2%nat = (1 + 1)%nat); [| lia]. rewrite bslots_op.
      iSplitL "Hs1u"; [iExact "Hs1u" | iExact "Hs2u"]. }
    (* the loaded header word, at its decoded numeral *)
    assert (Hhnd : hdr_n bs_hdr = Z.of_nat ((hdr_dec bs_hdr).1))
      by (symmetry; apply hdr_dec_n).
    iEval (rewrite (il_hdrw_moi bs_hdr ((hdr_dec bs_hdr).1) Hhnd Hbnd)) in "Hncell".
    (* THE SLOT CONTENTS, NAMED: the thirty existential client halves give
       up a contents function; the first [nh] feed the recovering install *)
    iDestruct (il_sepL_exist
                 (fun _ x bs => fs_chalf γfs (log_slot_bno logstart x) bs)
                 (seq 0 LOGBLOCKS) with "Hslotsfs") as (ys) "[%Hyslen Hslotsn]".
    iAssert ([∗ list] k ↦ _ ∈ seq 0 LOGBLOCKS,
               fs_chalf γfs (log_slot_bno logstart k) (ys !!! k))%I
      with "[Hslotsn]" as "Hslotsn".
    { iApply (big_sepL_mono with "Hslotsn"). intros k x Hk.
      apply lookup_seq in Hk as [-> _]. done. }
    (* ...AND THE SLOTS' CONTENTS ARE THE ERA'S PICTURE THERE (durable-disk
       1a).  The boot mint built [L] from the era's disk and the era's
       mirror was born at that same disk, so the bytes the recovering
       install is about to copy into the home blocks are already NAMED in
       the mirror.  That is what turns the closing clear's caught-up premise
       -- home = slot at every entry -- into computation on the chain. *)
    iEval (rewrite -(il_seq_body LOGBLOCKS
             (fun k => fs_chalf γfs (log_slot_bno logstart k) (ys !!! k))))
      in "Hslotsn".
    iDestruct (il_fsb_all γfs L (fun k => log_slot_bno logstart k)
                 (fun k => ys !!! k) (seq 0 LOGBLOCKS)
                 with "HLauth Hslotsn") as %Hyslk.
    iEval (rewrite (il_seq_body LOGBLOCKS
             (fun k => fs_chalf γfs (log_slot_bno logstart k) (ys !!! k))))
      in "Hslotsn".
    assert (Hysmir : forall k : nat, (k < LOGBLOCKS)%nat ->
              ys !!! k = lm_view M (log_slot_bno logstart k)).
    { intros k Hk.
      assert (Hkc : log_slot_bno logstart k ∈ cov)
        by (apply Hlogsub, log_slot_in_region; lia).
      pose proof (HLmir _ Hkc) as H1.
      rewrite (Hyslk k ltac:(apply elem_of_seq; lia)) in H1.
      by injection H1. }
    assert (Hsp30 : seq 0 LOGBLOCKS
                    = seq 0 ((hdr_dec bs_hdr).1)
                      ++ seq ((hdr_dec bs_hdr).1) (LOGBLOCKS - (hdr_dec bs_hdr).1)).
    { replace LOGBLOCKS with ((hdr_dec bs_hdr).1 + (LOGBLOCKS - (hdr_dec bs_hdr).1))%nat at 1
        by lia.
      rewrite seq_app. f_equal. }
    iEval (rewrite Hsp30 big_sepL_app) in "Hslotsn".
    iDestruct "Hslotsn" as "[Hslotfst Hslotrest]".
    iAssert ([∗ list] i ↦ w ∈ il_W bs_hdr ((hdr_dec bs_hdr).1),
               fs_chalf γfs (log_slot_bno logstart i) (ys !!! i))%I
      with "[Hslotfst]" as "Hslotfst".
    { iApply (il_sepL_reindex (seq 0 ((hdr_dec bs_hdr).1))
                (il_W bs_hdr ((hdr_dec bs_hdr).1))
                (fun i => fs_chalf γfs (log_slot_bno logstart i) (ys !!! i))
                ltac:(rewrite il_W_length length_seq; reflexivity)
                with "Hslotfst"). }
    (* the entries' home halves, re-indexed at the write set *)
    iEval (rewrite -(il_W_uint bs_hdr)) in "Hhomes".
    iAssert ([∗ list] i ↦ w ∈ il_W bs_hdr ((hdr_dec bs_hdr).1),
               fsblock (fs_bytes γfs) (uint w) (Bh i))%I with "[Hhomes]" as "Hhomes".
    { iEval (change (map uint ?l) with (uint <$> l)) in "Hhomes".
      iEval (rewrite big_sepL_fmap) in "Hhomes". iExact "Hhomes". }
    (* the per-entry rows the recovering install takes *)
    iAssert ([∗ list] i ↦ w ∈ il_W bs_hdr ((hdr_dec bs_hdr).1),
               fs_chalf γfs (log_slot_bno logstart i) (ys !!! i) ∗
               fsblock (fs_bytes γfs) (uint w) (Bh i))%I
      with "[Hslotfst Hhomes]" as "Hents".
    { rewrite big_sepL_sep. iSplitL "Hslotfst"; [iExact "Hslotfst" | iExact "Hhomes"]. }
    (* the entries are covered home blocks *)
    assert (Hwok' : forall w : mword 32, w ∈ il_W bs_hdr ((hdr_dec bs_hdr).1) ->
              uint w ∈ cov /\ ~ (uint w ∈ log_region_set logstart)).
    { intros w Hw. apply Hin. rewrite -(il_W_uint bs_hdr).
      change (map uint ?l) with (uint <$> l).
      apply elem_of_list_fmap_1. exact Hw. }
    iDestruct (cpu_own_transport CID27 CID29 0 eb pj b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    (* THE COMPLEMENT'S SPAN IS WIDER THAN [cpu_own]'S, because brelse does
       not thread it: its contract never mentions [trap_csrs_ext], so across
       its crossing the pair stays at the hart it was last transported to
       (CID26) while [cpu_own] comes back re-indexed at CID27.  Hop from
       CID26.  claude-notes/completed/eb-generic-sweep.md, "A CALLEE THAT
       DOES NOT THREAD THE COMPLEMENT STRANDS IT". *)
    iDestruct (trap_csrs_ext_transport CID26 CID29 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID26 CID29 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclmc") as "Hclmc".
    iDestruct (wp_next_shift (b := true) (CIDa := CID26) (CIDb := CID29) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKit : (K_install_trans <= K - 6)%nat)
      by (lia).
    (* the empty batch's pure shape, as NAMED facts: a tactic in an argument
       position whose expected type is still an evar diverges
       (claude-notes/durable-notes.md) *)
    assert (Hgeomok : log_geom_ok cov logstart) by (split; assumption).
    assert (Hshapeg : ((hdr_dec bs_hdr).1
                         = length (il_W bs_hdr ((hdr_dec bs_hdr).1))
                       /\ ((hdr_dec bs_hdr).1 <= LOGBLOCKS)%nat)).
    { split; [symmetry; apply il_W_length | exact Hbnd]. }
    assert (Hnodupg : NoDup (map uint (il_W bs_hdr ((hdr_dec bs_hdr).1)))).
    { rewrite (il_W_uint bs_hdr). exact Hndup. }
    assert (HLwg : true = false ->
              forall (i : nat) (w : SailStdpp.Values.mword 32),
                il_W bs_hdr ((hdr_dec bs_hdr).1) !! i = Some w ->
                L !! uint w = Some ((fun k : nat => ys !!! k) i)).
    { intros Hab. discriminate. }
    assert (HDg : true = true ->
              forall w : SailStdpp.Values.mword 32,
                w ∈ il_W bs_hdr ((hdr_dec bs_hdr).1) ->
                D !! uint w = Some false).
    { intros _ w Hw. apply HDf. exact (proj1 (Hwok' w Hw)). }
    assert (Hpkg : true = true -> printk_gen_contract (kt := KT1) γpr γu γd).
    { intros _. exact Hpk. }
    iApply (InstallTrans.wp_install_trans_sconf γs j γl γu γd γk pd pav pu bn γfs γpr
              cov logstart dev true ((hdr_dec bs_hdr).1)
              (il_W bs_hdr ((hdr_dec bs_hdr).1))
              (fun k : nat => ys !!! k) Bh L D pidv dq
              C2 (K - 6)%nat eb b
              (fun i : nat =>
                 log_mirror_half (lm_install M ((hdr_dec bs_hdr).2)
                                    (fun k : nat => ys !!! k) i))
              _ Vpr HKit Hgeomok Hj Hgl
              HC2a0 Hshapeg Hnodupg Hwok' HLwg HDg
              Hbelow Hpkg
              with "Hcg Hcnt Hextc Hclmc Htext Hkdata Hpc Hpenv [] Hbio Hfroz Hppid Hprocs Hdevi Hdgeom Hdlock Hncell Hcells Hbany HLauth HDauth
                    Hents Hs2 [] [Hmirh]").
    all: try lkbelow.
    { iModIntro. iExact "Hpenvpk". }
    (* THE RECOVERING INSTALL'S PERMITS, one generator over the CURSOR-INDEXED
       mirror chain (durable-disk 1a).  Entry [i] overwrites home block
       [Ws[i]] with the slot's content -- which is exactly the STEADY-STATE
       shape [FsCrash.fs_install_v_seq_permit] proves: the on-disk header
       still names the block being overwritten, so recovery re-installs it
       anyway and [fr_D] does not move.  Recovery is a ghost no-op here
       because custody was installed at birth; the era's picture goes in at
       [lm_install ... i] and comes back at [lm_install ... (S i)]. *)
    { iModIntro. iIntros (i w) "%Hwi %Hlen' Hmi".
      iDestruct "Hcert" as "(_ & Hstc2 & Hregc2)".
      assert (Hwsi : (hdr_dec bs_hdr).2 !! i = Some (uint w)).
      { rewrite -(il_W_uint bs_hdr).
        exact (it_map_lookup (il_W bs_hdr ((hdr_dec bs_hdr).1)) i w Hwi). }
      assert (Hilt : (i < length ((hdr_dec bs_hdr).2))%nat)
        by exact (lookup_lt_Some _ _ _ Hwsi).
      assert (Hile : (i <= length ((hdr_dec bs_hdr).2))%nat) by lia.
      assert (Hnei : forall (k : nat) (bb : Z), (k < i)%nat ->
                (hdr_dec bs_hdr).2 !! k = Some bb -> bb <> log_hdr_bno logstart)
        by (intros k bb _ Hk; exact (Hentne k bb Hk)).
      destruct (Hwok' w (elem_of_list_lookup_2 _ _ _ Hwi)) as [Hbcov Hblog].
      assert (HWle : (length ((hdr_dec bs_hdr).2) <= LOGBLOCKS)%nat)
        by (rewrite HWlen; exact Hbnd).
      assert (HMi : lm_hdr (lm_install M ((hdr_dec bs_hdr).2)
                              (fun k : nat => ys !!! k) i) logstart
                    = ((hdr_dec bs_hdr).1, (hdr_dec bs_hdr).2)).
      { rewrite (lm_install_hdr M ((hdr_dec bs_hdr).2)
                   (fun k : nat => ys !!! k) logstart i Hile Hnei) HMhdr.
        apply surjective_pairing. }
      cbn [lm_install].
      rewrite (list_lookup_total_correct ((hdr_dec bs_hdr).2) i (uint w) Hwsi).
      iApply (fs_install_v_seq_permit cov logstart ((hdr_dec bs_hdr).1)
                ((hdr_dec bs_hdr).2) i (uint w)
                (lm_install M ((hdr_dec bs_hdr).2) (fun k : nat => ys !!! k) i)
                (ys !!! i) Hlen' HndupS HWle Hwsi Hbcov Hblog HMi
                with "Hseam Hregc2 Hswlb [Hmi]").
      iNext. iExact "Hmi". }
    { iNext. iExact "Hmirh". }
    iIntros (CID30 Hs30 mI) "%Hcs3 Hcg Hcnt Hextc Hclmc Hpc Hppid
                             Hncell Hcells HLauth HDauth Hents Hs2 HRcust".
    assert (Hpc68 : ret_pc (C2 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.initlog + 0x68)).
    { rewrite HC2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc68) in "Hpc".
    pose proof Hcs3 as Hcs3_cs.
    assert (HmIsp : mI !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs3_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HC2sp).
    assert (HmIcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              mI !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hcs3_cs c Hcs).
      exact (HC2cs c Hcs N2 N8 N9 N18 N19). }
    iAssert (ghost_map_auth (fs_dirty γfs) 1 D) with "[HDauth]" as "HDauth";
      [iExact "HDauth"|].
    iAssert (bslots 2) with "[Hs2]" as "Hs2"; [iExact "Hs2"|].
    (* ===== +0x68 auipc a5,0x1e / +0x6c sw zero,1924(a5) : log.lh.n := 0 ===== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.initlog + 0x68)) Ra5
              (mword_of_int 30 : mword 20) mI (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (ili_68 with "Htext"). }
    iIntros (CID31 Hs31) "Hcg Hpc".
    set (D1 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.initlog + 0x68) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> mI).
    assert (HD1sp : D1 !!! Regidx csp_rs1 = spr)
      by (rewrite /D1 upd_ne; [exact HmIsp | vm_compute; discriminate]).
    assert (HD1cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              D1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /D1 upd_ne; [| regne]. exact (HmIcs c Hcs N2 N8 N9 N18 N19). }
    assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.initlog + 0x68) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x6c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp6c) in "Hpc".
    assert (Hlhad2 : add_vec (rget D1 Ra5)
                       (sign_extend' 64 (mword_of_int 1886 : mword 12)) = lh_n_pa).
    { rgne. rewrite /D1 upd_eq /lh_n_pa /log_pa /log_addr /pa_add /add_vec_int.
      apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hlhad2) in "Hncell".
    iApply (wp_sw_zero_s_sconf (mword_of_int (KernelSyms.initlog + 0x6c)) Ra5
              (mword_of_int 1886 : mword 12) D1 (K - 6)%nat
              (mword_of_int (Z.of_nat ((hdr_dec bs_hdr).1)) : mword 32) b
              with "Hcg Hpc [] Hncell").
    { iApply (ili_6c with "Htext"). }
    iIntros (CID32 Hs32) "Hcg Hpc Hncell".
    iEval (rewrite Hlhad2) in "Hncell".
    (* the install chain's last picture; its later strips on this step
       (the mirror half is timeless) *)
    iDestruct "HRcust" as ">Hmirn".
    (* the cells re-formed for the batch, the homes for the postcondition *)
    iAssert ([∗ list] i ∈ seq 0 LOGBLOCKS,
               ∃ wj : mword 32, lh_block i ↦₄ wj)%I
      with "[Hcells Hjunk]" as "Hblk".
    { iApply (il_cells_join bs_hdr ((hdr_dec bs_hdr).1) Hbnd
                with "Hcells Hjunk"). }
    iEval (rewrite big_sepL_sep) in "Hents".
    iDestruct "Hents" as "[Hslotfst Hhomes]".
    (* the slots, back under their existential for the batch *)
    iAssert ([∗ list] i ∈ seq 0 LOGBLOCKS,
               ∃ bs0 : list (bv 8), fs_chalf γfs (log_slot_bno logstart i) bs0)%I
      with "[Hslotfst Hslotrest]" as "Hslotsfs".
    { iEval (rewrite Hsp30 big_sepL_app).
      iSplitL "Hslotfst".
      - iEval (rewrite (il_seq_body ((hdr_dec bs_hdr).1)
                 (fun x => (∃ bs0 : list (bv 8),
                     fs_chalf γfs (log_slot_bno logstart x) bs0)%I))).
        iApply (il_sepL_reindex (il_W bs_hdr ((hdr_dec bs_hdr).1))
                  (seq 0 ((hdr_dec bs_hdr).1))
                  (fun i => (∃ bs0 : list (bv 8),
                      fs_chalf γfs (log_slot_bno logstart i) bs0)%I)
                  ltac:(rewrite il_W_length length_seq; reflexivity)).
        iApply (big_sepL_mono with "Hslotfst"). intros k y Hy.
        iIntros "H". iExists _. iExact "H".
      - iApply (big_sepL_mono with "Hslotrest"). intros k y Hy.
        apply lookup_seq in Hy as [-> _].
        rewrite length_seq.
        iIntros "H". iExists _. iExact "H". }
    (* the installed home halves, under the postcondition's existential *)
    iAssert ([∗ list] i ↦ bb ∈ (hdr_dec bs_hdr).2,
               ∃ bs0 : list (bv 8), fsblock (fs_bytes γfs) bb bs0)%I
      with "[Hhomes]" as "Hhomesout".
    { iEval (rewrite -(il_W_uint bs_hdr)).
      iEval (change (map uint ?l) with (uint <$> l)).
      iEval (rewrite big_sepL_fmap).
      iApply (big_sepL_mono with "Hhomes"). intros k y Hy.
      iIntros "H". iExists _. iExact "H". }
    assert (Hpp70 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x6c) : mword 64) 4
                    = mword_of_int (KernelSyms.initlog + 0x70))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp70) in "Hpc".
    (* ===== +0x70 jal ra,write_head ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.initlog + 0x70)) Rra
              (mword_of_int 2096742 : mword 21) D1 (K - 6)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc []").
    { iApply (ili_70 with "Htext"). }
    iIntros (CID33 Hs33) "Hcg Hpc".
    set (D2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.initlog + 0x70) : mword 64) 4)]> D1).
    assert (Htgtwh : add_vec (mword_of_int (KernelSyms.initlog + 0x70) : mword 64)
                       (sign_extend' 64 (mword_of_int 2096742 : mword 21))
                     = mword_of_int KernelSyms.write_head)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtwh) in "Hpc".
    assert (HD2sp : D2 !!! Regidx csp_rs1 = spr)
      by (rewrite /D2 upd_ne; [exact HD1sp | vm_compute; discriminate]).
    assert (HD2ra : D2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.initlog + 0x70) : mword 64) 4)
      by (rewrite /D2; apply upd_eq).
    assert (HD2cs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              D2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /D2 upd_ne; [| regne]. exact (HD1cs c Hcs N2 N8 N9 N18 N19). }
    (* one unit for write_head's bread *)
    iEval (rewrite (_ : 2%nat = (1 + 1)%nat); [| lia]) in "Hs2".
    iEval (rewrite bslots_op) in "Hs2".
    iDestruct "Hs2" as "[Hs1u Hs1v]".
    iAssert (lh_n_pa ↦₄ (mword_of_int (Z.of_nat 0%nat) : mword 32))%I
      with "[Hncell]" as "Hncell"; [iExact "Hncell"|].
    iDestruct (cpu_own_transport CID30 CID33 0 eb pj b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID30 CID33 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID30 CID33 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclmc") as "Hclmc".
    iDestruct (wp_next_shift (b := true) (CIDa := CID29) (CIDb := CID33) ltac:(wp_next_chain)
                 with "Hcont") as "Hcont".
    assert (HKwh : (K_write_head <= K - 6)%nat) by (lia).
    assert (Hshape0 : (0%nat = length ([] : list (mword 32))
                       /\ (0 <= LOGBLOCKS)%nat)).
    { split; [reflexivity | unfold LOGBLOCKS; lia]. }
    (* ---- THE INSTALL CHAIN'S END, READ TWICE (durable-disk 1a).  The
       closing clear needs the on-disk header's reading (unchanged: no entry
       is the header) and the CAUGHT-UP fact (every entry's home block now
       holds its slot's content).  Both are computation on the chain plus
       the born-true equation between the era's picture and [L]. ---- *)
    assert (HnnW : ((hdr_dec bs_hdr).1 <= length ((hdr_dec bs_hdr).2))%nat)
      by (rewrite HWlen; lia).
    assert (Hneall : forall (k : nat) (bb : Z), (k < (hdr_dec bs_hdr).1)%nat ->
              (hdr_dec bs_hdr).2 !! k = Some bb -> bb <> log_hdr_bno logstart)
      by (intros k bb _ Hk; exact (Hentne k bb Hk)).
    assert (HMn : lm_hdr (lm_install M ((hdr_dec bs_hdr).2)
                            (fun k : nat => ys !!! k) ((hdr_dec bs_hdr).1))
                    logstart = ((hdr_dec bs_hdr).1, (hdr_dec bs_hdr).2)).
    { rewrite (lm_install_hdr M ((hdr_dec bs_hdr).2) (fun k : nat => ys !!! k)
                 logstart ((hdr_dec bs_hdr).1) HnnW Hneall) HMhdr.
      apply surjective_pairing. }
    assert (Hcaught : forall (jw : nat) (bb : Z),
              (hdr_dec bs_hdr).2 !! jw = Some bb ->
              lm_view (lm_install M ((hdr_dec bs_hdr).2)
                         (fun k : nat => ys !!! k) ((hdr_dec bs_hdr).1)) bb
              = lm_view (lm_install M ((hdr_dec bs_hdr).2)
                           (fun k : nat => ys !!! k) ((hdr_dec bs_hdr).1))
                  (log_slot_bno logstart jw)).
    { intros jw bb Hjw.
      assert (Hjlt : (jw < (hdr_dec bs_hdr).1)%nat)
        by (rewrite -HWlen; exact (lookup_lt_Some _ _ _ Hjw)).
      assert (Hslotne : forall (i : nat) (c : Z),
                (i < (hdr_dec bs_hdr).1)%nat ->
                (hdr_dec bs_hdr).2 !! i = Some c ->
                c <> log_slot_bno logstart jw)
        by (intros i c _ Hi; exact (Hentslot i jw c Hi ltac:(lia))).
      rewrite (lm_install_hit M ((hdr_dec bs_hdr).2) (fun k : nat => ys !!! k)
                 ((hdr_dec bs_hdr).1) jw bb HinjWs HnnW Hjlt Hjw).
      rewrite (lm_install_miss M ((hdr_dec bs_hdr).2) (fun k : nat => ys !!! k)
                 ((hdr_dec bs_hdr).1) (log_slot_bno logstart jw) HnnW Hslotne).
      apply Hysmir. lia. }
    iAssert ([∗ list] i ↦ w ∈ ([] : list (mword 32)), lh_block i ↦₄ w)%I
      as "Hnil3"; [iApply il_bigL_nil|].
    iApply (WriteHead.wp_write_head_sconf γs j γl γu γd γk pd pav pu bn γfs
              cov logstart dev 0%nat ([] : list (mword 32))
              (it_rec_L (il_W bs_hdr ((hdr_dec bs_hdr).1)) (fun k : nat => ys !!! k) L)
              pidv dq
              D2 (K - 6)%nat eb b
              (fun bs' : list (bv 8) =>
                 log_mirror_half (lm_upd
                   (lm_install M ((hdr_dec bs_hdr).2)
                      (fun k : nat => ys !!! k) ((hdr_dec bs_hdr).1))
                   (log_hdr_bno logstart) bs'))%I
              _ Vpr HKwh Hgeomok Hj Hgl Hshape0
              with "Hcg Hcnt Hextc Hclmc Htext Hkdata Hpc Hpenv Hbio Hfroz Hppid Hprocs Hdevi Hdgeom Hdlock Hncell Hnil3 HLauth [Hfsb]
                    Hs1u [Hmirn]").
    all: try lkbelow.
    { iExists bs_hdr. iExact "Hfsb". }
    (* THE BOOT'S FINAL HEADER WRITE (durable-disk 1a): the PRESERVING CLEAR,
       the same one the steady state uses.  [fr_D] does not move -- the
       caught-up premise ("every entry's home block holds its slot's
       content") is computation on the install chain the era just walked,
       and the era's picture is the disk's because it was born so.  There is
       no swap here and nothing re-bases. *)
    { iIntros (bs' Hlen' Hhn' Hdec').
      iDestruct "Hcert" as "(_ & Hstc & Hregc)".
      iApply (fs_clear_keep_seq_permit cov logstart
                (lm_install M ((hdr_dec bs_hdr).2)
                   (fun k : nat => ys !!! k) ((hdr_dec bs_hdr).1))
                (lm_view (lm_install M ((hdr_dec bs_hdr).2)
                   (fun k : nat => ys !!! k) ((hdr_dec bs_hdr).1)))
                ((hdr_dec bs_hdr).1) ((hdr_dec bs_hdr).2) bs'
                Hlen' ltac:(rewrite Hhn'; reflexivity) Hbnd HMn
                (fun c (_ : c <> log_hdr_bno logstart) => eq_refl) Hcaught
                with "Hseam Hregc Hswlb Hmirn"). }
    iIntros (CID34 Hs34 mW bs') "%Hcs4 Hcg Hcnt Hextc Hclmc Hpc Hppid
                                 Hncell _ HLauth Hfsb %Hhn %Hhdec Hs1u HQ".
    assert (Hpc74 : ret_pc (D2 !!! Regidx Rra : mword 64)
                    = mword_of_int (KernelSyms.initlog + 0x74)).
    { rewrite HD2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc74) in "Hpc".
    pose proof Hcs4 as Hcs4_cs.
    assert (HmWsp : mW !!! Regidx csp_rs1 = spr)
      by (rewrite (callee_saved_lookup Hcs4_cs csp_rs1 ltac:(vm_compute; reflexivity));
          exact HD2sp).
    assert (HmWcs : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              mW !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite (callee_saved_lookup Hcs4_cs c Hcs).
      exact (HD2cs c Hcs N2 N8 N9 N18 N19). }
    (* ===== EPILOGUE ===== *)
    (* +0x74 c.ldsp ra,40(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.initlog + 0x74)) (mword_of_int 5 : mword 6) Rra
              mW (K - 6)%nat (m !!! Regidx Rra : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc1]").
    { iApply (ili_74 with "Htext"). }
    { iEval (rewrite HmWsp Hb1). iExact "Hc1". }
    iIntros (CID35 Hs35) "Hcg Hpc Hc1".
    iEval (rewrite HmWsp Hb1) in "Hc1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> mW).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = spr)
      by (rewrite /P1 upd_ne; [exact HmWsp | vm_compute; discriminate]).
    assert (Hpp76 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x74) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x76))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp76) in "Hpc".
    (* +0x76 c.ldsp s0,32(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.initlog + 0x76)) (mword_of_int 4 : mword 6) Rs0
              P1 (K - 6)%nat (m !!! Regidx Rs0 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc2]").
    { iApply (ili_76 with "Htext"). }
    { iEval (rewrite HP1sp Hb2). iExact "Hc2". }
    iIntros (CID36 Hs36) "Hcg Hpc Hc2".
    iEval (rewrite HP1sp Hb2) in "Hc2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = spr)
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hpp78 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x76) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x78))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp78) in "Hpc".
    (* +0x78 c.ldsp s1,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.initlog + 0x78)) (mword_of_int 3 : mword 6) Rs1
              P2 (K - 6)%nat (m !!! Regidx Rs1 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc3]").
    { iApply (ili_78 with "Htext"). }
    { iEval (rewrite HP2sp Hb3). iExact "Hc3". }
    iIntros (CID37 Hs37) "Hcg Hpc Hc3".
    iEval (rewrite HP2sp Hb3) in "Hc3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = spr)
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.initlog + 0x78) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x7a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7a) in "Hpc".
    (* +0x7a c.ldsp s2,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.initlog + 0x7a)) (mword_of_int 2 : mword 6) Rs2
              P3 (K - 6)%nat (m !!! Regidx Rs2 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc4]").
    { iApply (ili_7a with "Htext"). }
    { iEval (rewrite HP3sp Hb4). iExact "Hc4". }
    iIntros (CID38 Hs38) "Hcg Hpc Hc4".
    iEval (rewrite HP3sp Hb4) in "Hc4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : P4 !!! Regidx csp_rs1 = spr)
      by (rewrite /P4 upd_ne; [exact HP3sp | vm_compute; discriminate]).
    assert (Hpp7c : add_vec_int (mword_of_int (KernelSyms.initlog + 0x7a) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x7c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7c) in "Hpc".
    (* +0x7c c.ldsp s3,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.initlog + 0x7c)) (mword_of_int 1 : mword 6) Rs3
              P4 (K - 6)%nat (m !!! Regidx Rs3 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hc5]").
    { iApply (ili_7c with "Htext"). }
    { iEval (rewrite HP4sp Hb5). iExact "Hc5". }
    iIntros (CID39 Hs39) "Hcg Hpc Hc5".
    iEval (rewrite HP4sp Hb5) in "Hc5".
    set (P5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> P4).
    assert (HP5sp : P5 !!! Regidx csp_rs1 = spr)
      by (rewrite /P5 upd_ne; [exact HP4sp | vm_compute; discriminate]).
    assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.initlog + 0x7c) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x7e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7e) in "Hpc".
    (* +0x7e c.addi16sp sp,48 : pop the frame *)
    assert (Hwv : add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))
                  = sp0).
    { rewrite HP5sp. unfold spr, sp0. apply frame_cancel_48. }
    assert (Hpop : (P5 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6)))) 6).
    { rewrite Hwv HP5sp. exact Hspr6. }
    iAssert (stack_own (KTR := KT1) sp0 6) with "[Hc1 Hc2 Hc3 Hc4 Hc5 Hc6]" as "Hframe6".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hc1"; [iExists _; iExact "Hc1"|].
      iSplitL "Hc2"; [iExists _; iExact "Hc2"|].
      iSplitL "Hc3"; [iExists _; iExact "Hc3"|].
      iSplitL "Hc4"; [iExists _; iExact "Hc4"|].
      iSplitL "Hc5"; [iExists _; iExact "Hc5"|].
      iSplitL "Hc6"; [iExists _; iExact "Hc6"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe6".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.initlog + 0x7e))
              (mword_of_int 3 : mword 6) P5 (K - 6)%nat 6 b Hpop
              with "Hcg Hpc [] Hframe6").
    { iApply (ili_7e with "Htext"). }
    iIntros (CID40 Hs40) "Hcg Hpc".
    set (P6 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P5 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 3 : mword 6))))]> P5).
    assert (Hnk : ((K - 6) + 6)%nat = K) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp80 : add_vec_int (mword_of_int (KernelSyms.initlog + 0x7e) : mword 64) 2
                    = mword_of_int (KernelSyms.initlog + 0x80))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp80) in "Hpc".
    (* +0x80 c.ret *)
    assert (HP6ra : P6 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.initlog + 0x80)) Rra P6 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc []").
    { iApply (ili_80 with "Htext"). }
    iIntros (CID41 Hs41) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P6 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP6ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE CALLEE-SAVED LEDGER ===== *)
    assert (Csp : P6 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite /P6 upd_eq. exact Hwv. }
    assert (Cs0 : P6 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_eq. reflexivity. }
    assert (Cs1 : P6 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_eq. reflexivity. }
    assert (Cs2 : P6 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_eq. reflexivity. }
    assert (Cs3 : P6 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
    { rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_eq. reflexivity. }
    assert (Hfin : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
              P6 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18 N19.
      rewrite /P6 upd_ne; [| regne]. rewrite /P5 upd_ne; [| regne].
      rewrite /P4 upd_ne; [| regne]. rewrite /P3 upd_ne; [| regne].
      rewrite /P2 upd_ne; [| regne]. rewrite /P1 upd_ne; [| regne].
      exact (HmWcs c Hcs N2 N8 N9 N18 N19). }
    assert (Cs4 : P6 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs5 : P6 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs6 : P6 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs7 : P6 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs8 : P6 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs9 : P6 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs10 : P6 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    assert (Cs11 : P6 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; ilidx).
    (* ===== THE CONSTRUCTOR'S GHOST STEP: assemble [log_res], seal the
       lock, and hand out [log_ctx]. ===== *)
    assert (Hbd : forall z : Z,
              bool_decide (z ∈ map uint ([] : list (SailStdpp.Values.mword 32)))
              = false).
    { intro z. apply bool_decide_eq_false_2. apply not_elem_of_nil. }
    iApply fupd_wp.
    (* ---- THE CHAIN'S LAST PICTURE, off the clear's permit (durable-disk
       1a).  The mirror half is timeless, so the [▷] the permit channel puts
       on it strips inside this update.  There is no swap receipt to collect
       here any more: custody was installed at birth and [Hswlb] has been in
       hand since the first instruction. *)
    iMod "HQ" as "Hmirc".
    (* the era's picture after the whole boot: the install chain, then the
       clear's header.  Its header reading is the clean one by computation
       on the bytes write_head laid down. *)
    assert (Hmhdr : lm_hdr (lm_upd (lm_install M ((hdr_dec bs_hdr).2)
                              (fun k : nat => ys !!! k) ((hdr_dec bs_hdr).1))
                              (log_hdr_bno logstart) bs') logstart
                    = (0%nat, [])).
    { rewrite /lm_hdr lm_upd_view_eq Hhdec //. }
    iAssert (log_state bn γfs cov logstart 0%nat ∅ ∅)
      with "[Hncell Hblk HLauth HDauth Hcovf Hfsb Hslotsfs Hpool Hmirc]" as "Hbatch".
    { rewrite /log_state.
      iExists ([] : list (mword 32)),
              (<[log_hdr_bno logstart := bs']>
                 (it_rec_L (il_W bs_hdr ((hdr_dec bs_hdr).1))
                    (fun k : nat => ys !!! k) L)), D,
              (lm_upd (lm_install M ((hdr_dec bs_hdr).2)
                         (fun k : nat => ys !!! k) ((hdr_dec bs_hdr).1))
                      (log_hdr_bno logstart) bs').
      iSplitR; [iPureIntro; split; [reflexivity | unfold LOGBLOCKS; lia]|].
      (* the fresh batch has logged nothing: LB = list_to_set [] = empty *)
      iSplitR; [iPureIntro; reflexivity|].
      iSplitR; [iPureIntro; constructor|].
      iSplitR.
      { iPureIntro. intros w Hw. exfalso. exact (not_elem_of_nil w Hw). }
      iSplitL "Hncell"; [iExact "Hncell"|].
      iSplitR; [iApply il_bigL_nil|].
      iSplitL "Hblk"; [iExact "Hblk"|].
      iSplitL "HLauth"; [iExact "HLauth"|].
      iSplitL "HDauth"; [iExact "HDauth"|].
      iSplitL "Hcovf".
      { iApply (big_sepS_mono with "Hcovf"). intros z Hz. rewrite (Hbd z). done. }
      iSplitL "Hfsb"; [iExists bs'; iExact "Hfsb"|].
      iSplitL "Hslotsfs"; [iExact "Hslotsfs"|].
      iSplitL "Hpool"; [iExact "Hpool"|].
      iSplitL "Hmirc"; [iExact "Hmirc"|].
      iSplitR; [iPureIntro; exact Hmhdr|].
      (* ROW (b) AT BOOT, PROVEN (durable-disk 1a) -- one of the two walls
         G1-impl left, and custody at birth is what brings it down.  Outside
         the batch the era's picture of the durable disk IS the logged view,
         and at boot both sides are ONE walk over ONE image: the mint built
         [L] from the era's disk, the mirror was born at that disk, and the
         recovering install moved the two at exactly the same blocks to
         exactly the same bytes.  So the row is arithmetic on the chain. *)
      lazymatch goal with
      | |- environments.envs_entails _ (⌜?P⌝)%I => assert (Hrow0 : P)
      end.
      { intros bb Hbb _.
        rewrite /fs_home_set in Hbb.
        apply elem_of_difference in Hbb as [Hbcov Hbout].
        assert (Hbhdr : bb <> log_hdr_bno logstart)
          by (intros ->; exact (Hbout (log_hdr_in_region logstart))).
        rewrite (lookup_insert_ne _ _ _ _ (not_eq_sym Hbhdr)).
        rewrite (lm_upd_view_ne _ _ _ _ Hbhdr).
        destruct (decide (bb ∈ (hdr_dec bs_hdr).2)) as [Hin'|Hout'].
        - apply elem_of_list_lookup in Hin' as [jj Hjj].
          assert (Hjlt : (jj < (hdr_dec bs_hdr).1)%nat)
            by (rewrite -HWlen; exact (lookup_lt_Some _ _ _ Hjj)).
          assert (Hmapjj : map uint (il_W bs_hdr ((hdr_dec bs_hdr).1)) !! jj
                           = Some bb)
            by (rewrite (il_W_uint bs_hdr); exact Hjj).
          destruct (it_map_lookup_inv _ jj bb Hmapjj) as (w0 & Hw0 & ->).
          rewrite (it_rec_L_hit (il_W bs_hdr ((hdr_dec bs_hdr).1))
                     (fun k : nat => ys !!! k) L jj w0 Hinjw Hw0).
          rewrite (lm_install_hit M ((hdr_dec bs_hdr).2)
                     (fun k : nat => ys !!! k) ((hdr_dec bs_hdr).1) jj
                     (uint w0) HinjWs HnnW Hjlt Hjj).
          reflexivity.
        - assert (Hmiss : forall (i : nat) (w0 : mword 32),
                    il_W bs_hdr ((hdr_dec bs_hdr).1) !! i = Some w0 ->
                    uint w0 <> bb).
          { intros i w0 Hi Heq. apply Hout'. rewrite -(il_W_uint bs_hdr) -Heq.
            exact (elem_of_list_lookup_2 _ i _ (it_map_lookup _ i w0 Hi)). }
          rewrite (it_rec_L_miss (il_W bs_hdr ((hdr_dec bs_hdr).1))
                     (fun k : nat => ys !!! k) L bb Hmiss).
          assert (Hmiss2 : forall (i : nat) (c : Z),
                    (i < (hdr_dec bs_hdr).1)%nat ->
                    (hdr_dec bs_hdr).2 !! i = Some c -> c <> bb).
          { intros i c _ Hi Heq. apply Hout'. subst c.
            exact (elem_of_list_lookup_2 _ i _ Hi). }
          rewrite (lm_install_miss M ((hdr_dec bs_hdr).2)
                     (fun k : nat => ys !!! k) ((hdr_dec bs_hdr).1) bb
                     HnnW Hmiss2).
          exact (HLmir bb Hbcov). }
      iPureIntro. exact Hrow0. }
    iAssert (log_res γ bn γfs cov logstart)
      with "[Hout Hcmt Hnc Hops Hepa Hxa Htxa Hbatch]" as "Hres".
    { rewrite /log_res.
      (* the epoch is ONE at genesis (fs-log.md §G.17): the region's
         "never observed" counter value is zero, and the two must not
         collide.  Both epoch clauses stay vacuous. *)
      iExists 0%nat, false, v_nc, (∅ : gmap nat op_entry), 1%nat,
              (∅ : gset (nat * Z)), (∅ : gmap nat unit).
      iSplitL "Hout"; [iExact "Hout"|].
      iSplitL "Hcmt"; [iExact "Hcmt"|].
      iSplitL "Hnc"; [iExact "Hnc"|].
      iSplitL "Hops"; [iExact "Hops"|].
      iSplitR; [iPureIntro; apply map_size_empty|].
      iSplitR; [iPureIntro; intros i e Hi; rewrite lookup_empty in Hi; discriminate|].
      iSplitR; [iPureIntro; lia|].
      iSplitR; [iPureIntro; discriminate|].
      iSplitL "Hepa"; [iExact "Hepa"|].
      (* GENESIS IS EPOCH ONE, and this is where the ledger's [1 <= E]
         clause is established -- once, at the only place the counter is
         set rather than bumped. *)
      iSplitR; [iPureIntro; lia|].
      iSplitL "Hxa"; [iExact "Hxa"|].
      (* both new clauses are vacuous at genesis: no entry, no registry row *)
      iSplitR; [iPureIntro; intros i e Hi; rewrite lookup_empty in Hi; discriminate|].
      iSplitR; [iPureIntro; intros e' b' Hi;
                exfalso; exact (not_elem_of_empty _ Hi)|].
      (* NO TRANSACTION IS OPEN AT GENESIS (durable-disk lane A): both maps
         are empty, which is the cardinality tie read at zero. *)
      iSplitL "Htxa"; [iExact "Htxa"|].
      iSplitR; [iPureIntro; rewrite !map_size_empty; reflexivity|].
      iExists 0%nat, (∅ : gset Z).
      iSplitR; [iPureIntro; rewrite op_sum_empty; unfold LOGBLOCKS; lia|].
      iSplitR; [iPureIntro; intros i e Hi; rewrite lookup_empty in Hi; discriminate|].
      iSplitR; [iPureIntro; intros b' Hi;
                exfalso; exact (not_elem_of_empty _ Hi)|].
      rewrite op_pending_empty. iExact "Hbatch". }
    (* THE SEAL, AT THE GIVEN NAME.  [newlock_at] is [newlock] over a gname
       the caller already owns the free ghost state of -- the era fupd's
       [lock_ghost_alloc] minted it as [ln_lk γ], so this is a FILL, not a
       mint. *)
    iMod (newlock_at ⊤ (ln_lk γ) log_addr "log"%string
            (log_res γ bn γfs cov logstart)
            with "Hlkf Hlnm Hlock Hcpu Hres") as "#Hislk".
    (* BLOCK 1'S PARK, ALLOCATED (durable-disk lane C-3a).  It is minted
       in the same ghost step as the lock's seal, which is the one place in
       this walk where the run is free and the bundle it belongs to is
       being built. *)
    iMod (sb_park_alloc ⊤ γfs sbrec bs_sb Hsbparse with "Hb1") as "#Hsbp".
    iPoseProof (sb_parked_of_park γfs sbrec Hsbok with "Hsbp")
      as "#Hsbparked".
    iAssert (log_ctx γ bn γfs cov logstart dev)%I as "#Hctx".
    { rewrite /log_ctx.
      iSplitR; [iExact "Hislk"|].
      iSplitR; [iExact "Hdvp"|].
      iSplitR; [iExact "Hstp"|].
      iSplitR; [iExact "Hswlb"|].
      iSplitR; [iExact "Hbrow"|].
      iExact "Hsbparked". }
    iModIntro.
    (* the two units the caller gets back *)
    iAssert (bslots 2) with "[Hs1u Hs1v]" as "Hs2".
    { rewrite (_ : 2%nat = (1 + 1)%nat); [| lia]. rewrite bslots_op.
      iSplitL "Hs1u"; [iExact "Hs1u" | iExact "Hs1v"]. }
    iDestruct (cpu_own_transport CID34 CID41 0 eb pj b ltac:(wp_next_chain)
                 with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID34 CID41 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID34 CID41 eb pj
                 ltac:(rewrite Hbm; wp_next_chain) with "Hclmc") as "Hclmc".
    iSpecialize ("Hcont" $! CID41 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P6 with "[%] Hcg Hcnt Hextc Hclmc Hpc Hppid Hsbf Hs2 Hhomesout Hctx").
    { unfold callee_saved. repeat split; assumption. }
  Qed.

End ProofInitlog.

End InitlogProof.
