(* ProofEndOp.v -- end_op over the SIE-agnostic sconf world.  The batch-commit
   function, and the biggest proof in log.c: [commit] and [write_log] are
   [static] with end_op their only caller, so gcc INLINED both.

     void end_op(void) {
       int do_commit = 0;
       acquire(&log.lock);
       if (log.committing) panic("log.committing");
       log.outstanding -= 1;
       if (log.outstanding == 0) { do_commit = 1; log.committing = 1; }
       else wakeup(&log);
       release(&log.lock);
       if (do_commit) {
         commit();                     // write_log + write_head + install_trans
         acquire(&log.lock);
         log.committing = 0;
         log.ncommit++;
         wakeup(&log);
         release(&log.lock);
       }
     }

   THE SHAPE OF THE PROOF.  Six blocks, each a [Local Lemma] with its own
   [CID0] binder (the hart-generic protocol -- a block whose predecessor
   returned on a different hart is applied at the hart it actually starts on):

     eo_epi    +0x92..+0x9c  the four-register epilogue and the return.
                             Entered from the fast path's release AND from
                             the commit tail's [c.j] at +0x66.
     eo_tail   +0x42..+0x66  re-acquire, committing := 0, ncommit++, wakeup,
                             DEPOSIT the batch, release, [c.j] to the epilogue.
                             Entered from the n = 0 fall-through at +0x3e AND
                             from the commit body's [c.j] at +0x120.
     eo_commit +0x104..+0x120 write_head, install_trans(0), lh.n := 0,
                             write_head, restore s3/s4/s5, join eo_tail.
     eo_loop   +0xb4..+0x100 the inlined write_log copy loop, a fuel
                             induction on the entries still to copy.
     eo_fast   +0x7a..+0x8e  wakeup + release, falling into eo_epi.
     the main lemma          +0x00..+0x3e and +0x9e..+0xb0.

   THE GHOST FLOW.  Under the lock: [log_op_positive] forces out >= 1, which
   with log_res's ⌜cmt = true -> out = 0⌝ forces cmt = false -- that is what
   makes the "log.committing" panic arm at +0x68 DEAD (the [bnez a5] at +0x24
   simply falls through; the three [sd s3/s4/s5] before the panic are never
   executed).  [log_end_step] retires the ledger entry and [op_sum_delete]
   drops the sum by exactly the returned budget, so the sum tie survives at
   the decremented outstanding.

   The commit arm flips committing := 1 and TAKES [log_batch] out linearly --
   the checkout -- so the whole commit body runs with NO lock held and the
   batch in hand, exactly as the C code does.  The copy loop's per-iteration
   ghost step moves the LOG SLOT's logged content to the home block's bytes
   (the batch's own client half plus the handle's payload half plus the
   checked-out authority); the home block is bread and brelse'd UNTOUCHED,
   and its bytes are learned from the AUTHORITY (one [ghost_map_lookup]
   against the payload's half -- there is no client [fsblock] for a home
   block on the committer's side, which is exactly the premise
   install_trans now takes).  That per-iteration fact is what discharges
   install_trans's ⌜forall i w, W !! i = Some w -> L !! uint w = Some (Lw i)⌝:
   later iterations move L only at LOG-REGION keys, and log_batch's own
   conjunct says no entry of W is in the log region.

   SLOT ACCOUNTING, EXACT.  The pool parked in [log_batch] is
   [bslots bn ((LOGBLOCKS - n) + 2)].  The copy loop peels 2 per iteration
   and its two brelses give them back; write_head peels 1 and returns 1;
   install_trans takes 2 and returns [2 + length W]; the second write_head
   peels 1 and returns 1.  Re-forming the batch at n = 0 needs
   (LOGBLOCKS - 0) + 2 = 32, and (32 - n) - 2 + (2 + n) = 32.

   THE RE-ACQUIRE KNOWS committing IS STILL SET without any extra ghost: the
   committer holds [ghost_map_auth (fs_L γfs) 1 L] out of the batch, and
   log_res's cmt = false arm holds one too -- two authorities at fraction 1
   are contradictory ([ghost_map_auth_valid_2]).

   A functor over ACQUIRE / RELEASE / WAKEUP / BREAD / BWRITE / BRELSE /
   MEMMOVE / WRITE_HEAD / INSTALL_TRANS. *)
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
Require Import SchedCtx.
Require Import FdSlots.
Require Import ProcGeom.
Require Import WpLock.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import WpUart.
Require Import ByteCursor.
Require Import DiskPtsto DiskInv.
Require Import BufOwn BcacheInv BioInv.
Require Import FsBlocks LogInv.
Require Import CodeEndOp.
Require Import PanicStub.
Require Import SpecAcquire SpecRelease SpecWakeup.
Require Import SpecBread SpecBwrite SpecBrelse SpecMemmove.
Require Import SpecWriteHead SpecInstallTrans.
Require Import FsCrash.
Require Import SpecEndOp.
From Kernel Require KernelSyms.

Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.


(* ===================================================================== *)
(*  Pure arithmetic, all over plain [Z]/[nat] so no solver ever runs      *)
(*  inside the WP context (the zify-hook rule in durable-notes).          *)
(* ===================================================================== *)

Lemma eo_sext32 (z : Z) : (0 <= z < 2^31)%Z ->
  (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = mword_of_int z.
Proof.
  intro Hz. apply bv_eq.
  rewrite (sext64_moi32_unsigned z Hz) moi64_unsigned.
  symmetry. apply bvw64_small. lia.
Qed.

Lemma eo_uint32 (a : mword 32) : uint a = bv_unsigned a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [ reflexivity | lia ].
Qed.

Lemma eo_uint_moi32 (z : Z) : (0 <= z < 2 ^ 32)%Z ->
  uint (mword_of_int z : mword 32) = z.
Proof. intro Hz. rewrite eo_uint32. apply moi32_small. lia. Qed.

Lemma eo_moi32_add (a b : Z) :
  (0 <= a)%Z -> (0 <= b)%Z -> (a + b < 2^32)%Z ->
  add_vec (mword_of_int a : mword 32) (mword_of_int b : mword 32)
  = (mword_of_int (a + b) : mword 32).
Proof.
  intros Ha Hb Hab. apply bv_eq.
  rewrite add_vec_unsigned.
  change (MachineWord.MachineWord.Z_idx 32) with 32%N.
  rewrite (moi32_small a ltac:(lia)) (moi32_small b ltac:(lia)).
  rewrite moi32_unsigned. reflexivity.
Qed.

Lemma eo_sint_moi (z : Z) :
  (- 2 ^ 63 <= z < 2 ^ 63)%Z -> sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  assert (Hhm : bv_half_modulus 64 = (2 ^ 63)%Z) by reflexivity.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned bv_swrap_wrap.
  apply bv_swrap_small. rewrite Hhm. lia.
Qed.

Lemma eo_lt_lit (x : Z) : (0 < x < 2^31)%Z -> (x < 2147483648)%Z.
Proof. change (2^31)%Z with 2147483648%Z. lia. Qed.

Lemma eo_n_small (n : nat) : (n <= LOGBLOCKS)%nat -> (0 <= Z.of_nat n < 2^31)%Z.
Proof. unfold LOGBLOCKS. intro H. change (2^31)%Z with 2147483648%Z. lia. Qed.

Lemma eo_pow31 : (2^31)%Z = 2147483648%Z. Proof. reflexivity. Qed.

(* the signed compares the two [blt]s read back as *)
Lemma eo_lt_s (a b : Z) :
  (0 <= a < 2^31)%Z -> (0 <= b < 2^31)%Z ->
  zopz0zI_s (mword_of_int a : mword 64) (mword_of_int b : mword 64) = Z.ltb a b.
Proof.
  intros Ha Hb. unfold zopz0zI_s.
  rewrite (eo_sint_moi a ltac:(lia)) (eo_sint_moi b ltac:(lia)). reflexivity.
Qed.

Lemma eo_lt_s0 (b : Z) :
  (0 <= b < 2^31)%Z ->
  zopz0zI_s (zero_reg : mword 64) (mword_of_int b : mword 64) = Z.ltb 0 b.
Proof.
  intro Hb. unfold zopz0zI_s.
  assert (Hz : sint (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz (eo_sint_moi b ltac:(lia)). reflexivity.
Qed.

(* [addw a1,a1,s2] : logstart + tail, both small *)
Lemma eo_addw (a b : Z) :
  (0 <= a)%Z -> (0 <= b)%Z -> (a + b < 2^31)%Z ->
  sign_extend' 64 (add_vec (subrange_vec_dec (mword_of_int a : mword 64) 31 0 : mword 32)
                           (subrange_vec_dec (mword_of_int b : mword 64) 31 0 : mword 32))
  = (mword_of_int (a + b) : mword 64).
Proof.
  intros Ha Hb Hab.
  rewrite -!trunc32_subrange !trunc32_mword_of_int.
  rewrite (eo_moi32_add a b Ha Hb ltac:(lia)).
  apply eo_sext32. lia.
Qed.

(* [c.addiw a1,a1,1] on a small value *)
Lemma eo_addiw1 (z : Z) : (0 <= z)%Z -> (z + 1 < 2^31)%Z ->
  sign_extend' 64 (subrange_vec_dec
     (add_vec (mword_of_int z : mword 64)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
  = (mword_of_int (z + 1) : mword 64).
Proof.
  intros Hz Hb.
  rewrite -trunc32_subrange trunc32_add trunc32_mword_of_int.
  assert (HK : trunc32 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
               = (mword_of_int 1 : mword 32))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite HK (eo_moi32_add z 1 Hz ltac:(lia) ltac:(lia)).
  apply eo_sext32. lia.
Qed.

(* ---- the [struct log] cell addresses the code forms ---- *)
Lemma eo_addr_start :
  add_vec log_addr (sign_extend' 64 (mword_of_int 24 : mword 12)) = l_start.
Proof.
  rewrite /l_start /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.
Lemma eo_addr_out :
  add_vec log_addr (sign_extend' 64 (mword_of_int 28 : mword 12)) = l_out.
Proof.
  rewrite /l_out /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.
Lemma eo_addr_cmt :
  add_vec log_addr (sign_extend' 64 (mword_of_int 32 : mword 12)) = l_cmt.
Proof.
  rewrite /l_cmt /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.
Lemma eo_addr_dev :
  add_vec log_addr (sign_extend' 64 (mword_of_int 36 : mword 12)) = l_dev.
Proof.
  rewrite /l_dev /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.
Lemma eo_addr_nc :
  add_vec log_addr (sign_extend' 64 (mword_of_int 40 : mword 12)) = l_ncommit.
Proof.
  rewrite /l_ncommit /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.
Lemma eo_addr_lhn :
  add_vec log_addr (sign_extend' 64 (mword_of_int 44 : mword 12)) = lh_n_pa.
Proof.
  rewrite /lh_n_pa /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- the auipc/addi relocations ---- *)
Lemma eo_reloc_log_0c :
  add_vec (add_vec (mword_of_int (KernelSyms.end_op + 0x0c) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1736 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma eo_reloc_log_2a :
  add_vec (add_vec (mword_of_int (KernelSyms.end_op + 0x2a) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1706 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma eo_reloc_log_42 :
  add_vec (add_vec (mword_of_int (KernelSyms.end_op + 0x42) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1682 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma eo_reloc_log_7a :
  add_vec (add_vec (mword_of_int (KernelSyms.end_op + 0x7a) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1626 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma eo_reloc_log_86 :
  add_vec (add_vec (mword_of_int (KernelSyms.end_op + 0x86) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1614 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma eo_reloc_blk0 :
  add_vec (add_vec (mword_of_int (KernelSyms.end_op + 0xa4) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1632 : mword 12)) = lh_block 0.
Proof.
  rewrite /lh_block /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma eo_reloc_log_ac :
  add_vec (add_vec (mword_of_int (KernelSyms.end_op + 0xac) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1576 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma eo_reloc_lhn :
  add_vec (add_vec (mword_of_int (KernelSyms.end_op + 0x10e) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1522 : mword 12)) = lh_n_pa.
Proof.
  rewrite /lh_n_pa /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- the lh.block[] cursor ---- *)
Lemma eo_cursor_at (i : nat) :
  add_vec (lh_block i) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lh_block i.
Proof.
  assert (H0 : (sign_extend' 64 (mword_of_int 0 : mword 12) : mword 64)
               = mword_of_int (Z.of_nat 0%nat))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H0 /lh_block pa_add_bump. f_equal. lia.
Qed.

Lemma eo_cursor_step (i : nat) :
  add_vec (lh_block i) (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6)))
  = lh_block (S i).
Proof.
  assert (H4 : (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6)) : mword 64)
               = mword_of_int (Z.of_nat 4%nat))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H4 /lh_block pa_add_bump. f_equal. lia.
Qed.

(* ---- a buffer's data area ---- *)
Lemma eo_data_off (q : mword 64) :
  add_vec q (sign_extend' 64 (mword_of_int 88 : mword 12)) = b_data q.
Proof.
  assert (H88 : (sign_extend' 64 (mword_of_int 88 : mword 12) : mword 64)
                = mword_of_int (Z.of_nat 88%nat))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H88 /b_data /pa_add /add_vec_int. reflexivity.
Qed.

(* ---- the log region's membership facts ---- *)
Lemma eo_slot_in_region (logstart : Z) (i : nat) :
  (i < LOGBLOCKS)%nat -> log_slot_bno logstart i ∈ log_region_set logstart.
Proof.
  intro Hi. rewrite /log_region_set. apply elem_of_union_l.
  apply elem_of_list_to_set. apply elem_of_list_fmap.
  exists i. split; [reflexivity|]. apply elem_of_seq. lia.
Qed.

Lemma eo_hdr_in_region (logstart : Z) :
  log_hdr_bno logstart ∈ log_region_set logstart.
Proof. rewrite /log_region_set. apply elem_of_union_r. apply elem_of_singleton. done. Qed.

(* the block-number arithmetic the two breads need *)
Lemma eo_arith (ls : Z) (t : nat) :
  (0 < ls < 2^31)%Z -> (0 < log_slot_bno ls t < 2^31)%Z ->
  (0 <= ls < 2^31)%Z /\ (0 <= Z.of_nat t < 2^31)%Z /\
  (ls + Z.of_nat t < 2^31)%Z /\ (0 <= ls + Z.of_nat t)%Z /\
  (ls + Z.of_nat t + 1 < 2^31)%Z /\
  (ls + Z.of_nat t + 1 = log_slot_bno ls t)%Z /\
  (0 <= log_slot_bno ls t < 2^32)%Z /\
  (0 <= log_slot_bno ls t < 2^31)%Z.
Proof.
  rewrite /log_slot_bno. intros H1 H2.
  change (2^32)%Z with 4294967296%Z.
  change (2^31)%Z with 2147483648%Z in *.
  rewrite /log_slot_bno in H2. split_and!; lia.
Qed.

(* the fuel induction's arithmetic *)
Lemma eo_fuel_absurd (t n : nat) : (t < n)%nat -> (n - t <= 0)%nat -> False.
Proof. lia. Qed.
Lemma eo_fuel_step (t n fuel : nat) : (n - t <= S fuel)%nat -> (n - S t <= fuel)%nat.
Proof. lia. Qed.
Lemma eo_lt_len (t n : nat) (W : list (mword 32)) :
  (t < n)%nat -> n = length W -> (t < length W)%nat.
Proof. lia. Qed.
Lemma eo_map_lookup (W : list (mword 32)) (i : nat) (w : mword 32) :
  W !! i = Some w -> map uint W !! i = Some (uint w).
Proof.
  intro H. change (map uint W) with (uint <$> W).
  rewrite list_lookup_fmap H. reflexivity.
Qed.

Lemma eo_lookup_elem (W : list (mword 32)) (t : nat) (w : mword 32) :
  W !! t = Some w -> w ∈ W.
Proof. intro H. eapply elem_of_list_lookup_2. exact H. Qed.
Lemma eo_t_lt_lb (t n : nat) : (t < n)%nat -> (n <= LOGBLOCKS)%nat -> (t < LOGBLOCKS)%nat.
Proof. lia. Qed.
Lemma eo_St_small (t n : nat) :
  (t < n)%nat -> (n <= LOGBLOCKS)%nat -> (0 <= Z.of_nat (S t) < 2^31)%Z.
Proof. unfold LOGBLOCKS. intros. change (2^31)%Z with 2147483648%Z. lia. Qed.
Lemma eo_succ_z (t : nat) : (Z.of_nat t + 1)%Z = Z.of_nat (S t).
Proof. lia. Qed.

Lemma eo_neqz0 :
  neq_vec (sign_extend' 64 (mword_of_int 0 : mword 32) : mword 64)
          (zero_reg : mword 64) = false.
Proof. vm_compute; reflexivity. Qed.

Lemma eo_noff0 : (Z.of_nat 0%nat + 1 < 2 ^ 31)%Z.
Proof. change (2^31)%Z with 2147483648%Z. lia. Qed.
Lemma eo_noff1 : (Z.of_nat 1%nat + 1 < 2 ^ 31)%Z.
Proof. change (2^31)%Z with 2147483648%Z. lia. Qed.

(* the K budgets *)
Lemma eo_Kbread (K : nat) : (K_end_op <= K)%nat -> (K_bread <= K - 8)%nat.
Proof. unfold K_end_op, K_bread. lia. Qed.
Lemma eo_Kbwrite (K : nat) : (K_end_op <= K)%nat -> (K_bwrite <= K - 8)%nat.
Proof. unfold K_end_op, K_bwrite. lia. Qed.
Lemma eo_Kbrelse (K : nat) : (K_end_op <= K)%nat -> (K_brelse <= K - 8)%nat.
Proof. unfold K_end_op, K_brelse. lia. Qed.
Lemma eo_Kmm (K : nat) : (K_end_op <= K)%nat -> (2 <= K - 8)%nat.
Proof. unfold K_end_op. lia. Qed.
Lemma eo_Kwh (K : nat) : (K_end_op <= K)%nat -> (K_write_head <= K - 8)%nat.
Proof. unfold K_end_op, K_write_head. lia. Qed.
Lemma eo_Kit (K : nat) : (K_end_op <= K)%nat -> (K_install_trans <= K - 8)%nat.
Proof. unfold K_end_op, K_install_trans. lia. Qed.
Lemma eo_Klk (K : nat) : (K_end_op <= K)%nat -> (10 <= K - 8)%nat.
Proof. unfold K_end_op. lia. Qed.
Lemma eo_Kwk (K : nat) : (K_end_op <= K)%nat -> (18 <= K - 8)%nat.
Proof. unfold K_end_op. lia. Qed.

(* the outstanding cell's small-integer traffic: out is at most 3 *)
Lemma eo_out_sext (out : nat) : (out <= 3)%nat ->
  (sign_extend' 64 (mword_of_int (Z.of_nat out) : mword 32) : mword 64)
  = mword_of_int (Z.of_nat out).
Proof. intro H. apply eo_sext32. change (2^31)%Z with 2147483648%Z. lia. Qed.

Lemma eo_dec (out : nat) : (1 <= out)%nat -> (out <= 3)%nat ->
  (sign_extend' 64
     (subrange_vec_dec
        (add_vec (mword_of_int (Z.of_nat out) : mword 64)
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
   : mword 64) = mword_of_int (Z.of_nat (out - 1)).
Proof.
  intros H1 H2.
  destruct out as [|out]; [lia|].
  do 3 (destruct out as [|out]; [ apply bv_eq; vm_compute; reflexivity |]).
  lia.
Qed.

Lemma eo_dec32 (out : nat) : (1 <= out)%nat -> (out <= 3)%nat ->
  trunc32 (mword_of_int (Z.of_nat (out - 1)) : mword 64)
  = (mword_of_int (Z.of_nat (out - 1)) : mword 32).
Proof.
  intros H1 H2.
  destruct out as [|out]; [lia|].
  do 3 (destruct out as [|out]; [ apply bv_eq; vm_compute; reflexivity |]).
  lia.
Qed.

Lemma eo_neq0 (k : nat) : (k <= 3)%nat ->
  neq_vec (mword_of_int (Z.of_nat k) : mword 64) (zero_reg : mword 64)
  = negb (Nat.eqb k 0).
Proof.
  intro H.
  do 4 (destruct k as [|k]; [ vm_compute; reflexivity |]). lia.
Qed.

Lemma eo_li1 : add_vec (zero_reg : mword 64)
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
               = (mword_of_int 1 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma eo_li1024 : add_vec (zero_reg : mword 64)
                    (sign_extend' 64 (mword_of_int 1024 : mword 12))
                  = (mword_of_int (Z.of_nat 1024%nat) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma eo_trunc1 : trunc32 (mword_of_int 1 : mword 64) = (mword_of_int 1 : mword 32).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma eo_zero32 : (mword_of_int 0 : mword 32) = mword_of_int (Z.of_nat 0%nat).
Proof. reflexivity. Qed.

(* ---- list / big-op bridges ---- *)
Lemma eo_seq_of_list {Σ : gFunctors} {A : Type} (l : list A) (P : nat -> iProp Σ) :
  ([∗ list] i ∈ seq 0 (length l), P i) ⊣⊢ ([∗ list] i ↦ _ ∈ l, P i).
Proof.
  revert P. induction l as [|x l IH]; intro P.
  - by rewrite !big_sepL_nil.
  - cbn [length].
    change (seq 0 (S (length l))) with (0%nat :: seq 1 (length l)).
    rewrite !big_sepL_cons.
    apply bi.sep_proper; [done|].
    rewrite -(fmap_S_seq 0 (length l)) big_sepL_fmap.
    exact (IH (fun i => P (S i))).
Qed.

Lemma eo_seq_split (a b : nat) :
  seq 0 (a + b) = seq 0 a ++ seq a b.
Proof. apply seq_app. Qed.

Lemma eo_seq_cons (a b : nat) : seq a (S b) = a :: seq (S a) b.
Proof. reflexivity. Qed.

(* the two directions memmove's contract needs, applied (not rewritten) *)
Section EoData.
  Context `{!riscvGS Σ}.

  Lemma eo_seq_index (P : nat -> bv 8 -> iProp Σ) (bs : list (bv 8)) :
    ([∗ list] j ↦ x ∈ bs, P j x) ⊣⊢
    ([∗ list] j ∈ seq 0 (length bs), P j (bs !!! j)).
  Proof.
    revert P. induction bs as [|x bs IH]; intro P.
    - by rewrite !big_sepL_nil.
    - cbn [length].
      change (seq 0 (S (length bs))) with (0%nat :: seq 1 (length bs)).
      rewrite !big_sepL_cons.
      apply bi.sep_proper; [done|].
      rewrite -(fmap_S_seq 0 (length bs)) big_sepL_fmap.
      exact (IH (fun i y => P (S i) y)).
  Qed.

  Lemma eo_data_fwd (q : Arch.pa) (bs : list (bv 8)) (len : nat) :
    length bs = len ->
    ([∗ list] j ↦ x ∈ bs, pa_add q j ↦ₘ x) ⊢
    ([∗ list] j ∈ seq 0 len, (pa_add q j) ↦ₘ (bs !!! j)).
  Proof.
    intros <-. rewrite (eo_seq_index (fun i x => (pa_add q i ↦ₘ x)%I) bs).
    iIntros "$".
  Qed.

  Lemma eo_data_back (q : Arch.pa) (bs : list (bv 8)) (len : nat) :
    length bs = len ->
    ([∗ list] j ∈ seq 0 len, (pa_add q j) ↦ₘ (bs !!! j)) ⊢
    ([∗ list] j ↦ x ∈ bs, pa_add q j ↦ₘ x).
  Proof.
    intros <-. rewrite (eo_seq_index (fun i x => (pa_add q i ↦ₘ x)%I) bs).
    iIntros "$".
  Qed.

End EoData.

(* the naming function the loop extends one entry at a time *)
Definition eo_ext (Lw : nat -> list (bv 8)) (t : nat) (bs : list (bv 8))
  : nat -> list (bv 8) :=
  fun i => if Nat.eqb i t then bs else Lw i.

Lemma eo_ext_lt (Lw : nat -> list (bv 8)) (t : nat) (bs : list (bv 8)) (i : nat) :
  (i < t)%nat -> eo_ext Lw t bs i = Lw i.
Proof. intro H. rewrite /eo_ext. destruct (Nat.eqb_spec i t); [lia | reflexivity]. Qed.

Lemma eo_ext_eq (Lw : nat -> list (bv 8)) (t : nat) (bs : list (bv 8)) :
  eo_ext Lw t bs t = bs.
Proof. rewrite /eo_ext. destruct (Nat.eqb_spec t t); [reflexivity | lia]. Qed.

(* ===================================================================== *)

Module EndOpProof (Acq : ACQUIRE) (Rel : RELEASE) (Wk : WAKEUP)
                  (BR : BREAD) (BW : BWRITE) (BL : BRELSE) (Mm : MEMMOVE)
                  (WH : WRITE_HEAD) (IT : INSTALL_TRANS) : END_OP.

Notation Rra  := (mword_of_int 1 : mword 5).
Notation Rs0  := (mword_of_int 8 : mword 5).
Notation Rs1  := (mword_of_int 9 : mword 5).
Notation Ra0  := (mword_of_int 10 : mword 5).
Notation Ra1  := (mword_of_int 11 : mword 5).
Notation Ra2  := (mword_of_int 12 : mword 5).
Notation Ra5  := (mword_of_int 15 : mword 5).
Notation Rs2  := (mword_of_int 18 : mword 5).
Notation Rs3  := (mword_of_int 19 : mword 5).
Notation Rs4  := (mword_of_int 20 : mword 5).
Notation Rs5  := (mword_of_int 21 : mword 5).

Local Ltac regne := reg_ne_side.

Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Local Ltac eoidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

(* ===================================================================== *)
(*  The named pieces: the continuation, the frame, the register           *)
(*  invariants and the batch in its OPENED form.                          *)
(* ===================================================================== *)
Section EndOpDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}.

  (* end_op's own [wp_next] obligation, NAMED and anchored at an explicit
     hart (durable-notes: a whole-function post must not be spelled inline). *)
  Definition eo_cont `{GEN : GenId} `{CID0 : CpuId} 
      (j : nat) (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool) (lks : gset nat) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) C b lks -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        WP (Loop : expr riscv_lang))%I.

  Lemma eo_cont_shift `{GEN : GenId} `{CIDa : CpuId} `{CIDb : CpuId}
       (j : nat) (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool) (lks : gset nat) :
    (* the guard is at the LITERAL [true] now, matching eo_cont's own index *)
    (true = false \/ proc_addr j = zero_reg -> (CIDb : CPU) = (CIDa : CPU)) ->
    eo_cont (CID0 := CIDa)  j pidv dq m K eb C b lks -∗
    eo_cont (CID0 := CIDb)  j pidv dq m K eb C b lks.
  Proof.
    intros Hs. rewrite /eo_cont /wp_next.
    iIntros "H" (CID2 Hs2). iApply "H". iPureIntro.
    intro Hb. specialize (Hs2 Hb). specialize (Hs Hb). congruence.
  Qed.

  (* the frame: 64 bytes = 8 slots.  ra@56, s0@48, s1@40, s2@32 are saved
     UNCONDITIONALLY (slots 1..4); slots 5,6,7 (s3@24, s4@16, s5@8) are
     written only on the two arms that clobber them, and slot 8 (offset 0)
     is never touched at all. *)
  Definition eo_frame4 (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈ (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈ (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈ (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈ (m !!! Regidx Rs2 : mword 64))%I.

  Definition eo_frameJ (m : regfile) : iProp Σ :=
    ((∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈ v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈ v) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈ v))%I.

  Definition eo_frameS (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈ (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈ (m !!! Regidx Rs5 : mword 64) ∗
     (∃ v : mword 64, pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈ v))%I.

  Lemma eo_frameS_J (m : regfile) : eo_frameS m -∗ eo_frameJ m.
  Proof.
    rewrite /eo_frameS /eo_frameJ. iIntros "(H5 & H6 & H7 & H8)".
    iSplitL "H5"; [iExists _; iExact "H5"|].
    iSplitL "H6"; [iExists _; iExact "H6"|].
    iSplitL "H7"; [iExists _; iExact "H7"|]. iExact "H8".
  Qed.

  (* the OPENED batch: log_batch taken apart, with the log-region client
     halves SPLIT at the copy loop's cursor [t] (the prefix is at the
     contents the loop has already written, the suffix is still opaque). *)
  Definition eo_open (bn : bio_names) (γfs : fs_names) (cov : gset Z)
      (logstart : Z) (n : nat) (W : list (mword 32))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (Lw : nat -> list (bv 8)) (t : nat) : iProp Σ :=
    (lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) ∗
     ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) ∗
     ([∗ list] i ∈ seq n (LOGBLOCKS - n),
        ∃ junk : mword 32, lh_block i ↦₄ junk) ∗
     ghost_map_auth (fs_L γfs) 1 L ∗
     ghost_map_auth (fs_dirty γfs) 1 D ∗
     ([∗ set] b ∈ cov,
        b ↪[fs_dirty γfs]{#(1/2)} (bool_decide (b ∈ map uint W))) ∗
     (∃ bsh, fsblock γfs (log_hdr_bno logstart) bsh) ∗
     ([∗ list] i ∈ seq 0 t, fsblock γfs (log_slot_bno logstart i) (Lw i)) ∗
     ([∗ list] i ∈ seq t (LOGBLOCKS - t),
        ∃ bs, fsblock γfs (log_slot_bno logstart i) bs) ∗
     bslots bn ((LOGBLOCKS - n) + 2)%nat)%I.

  Lemma eo_open_of_batch (bn : bio_names) (γfs : fs_names) (cov : gset Z)
      (logstart : Z) (n : nat) (LB : gset Z) :
    log_batch bn γfs cov logstart n LB -∗
    ∃ (W : list (mword 32)) (L : gmap Z (list (bv 8))) (D : gmap Z bool),
      ⌜n = length W /\ (n <= LOGBLOCKS)%nat⌝ ∗
      ⌜NoDup (map uint W)⌝ ∗
      ⌜forall w, w ∈ W -> uint w ∈ cov /\ ~ (uint w ∈ log_region_set logstart)⌝ ∗
      (* the era's mirror half travels OUTSIDE [eo_open]: the commit moves the
         on-disk header away from clean and back, so it cannot ride a bundle
         that is held across [write_head] *)
      log_mirror_clean ∗
      eo_open bn γfs cov logstart n W L D (fun _ => []) 0.
  Proof.
    rewrite /log_batch /eo_open.
    iIntros "H". iDestruct "H" as (W L D)
      "(%Hlen & %HLB & %Hnd & %Hwok & Hncell & HW & Hjunk & HauthL & HauthD & Hcov & Hhdr & Hlogr & Hpool & Hmirc)".
    iExists W, L, D.
    iSplitR; [iPureIntro; exact Hlen|].
    iSplitR; [iPureIntro; exact Hnd|].
    iSplitR; [iPureIntro; exact Hwok|].
    iSplitL "Hmirc"; [iExact "Hmirc"|].
    iSplitL "Hncell"; [iExact "Hncell"|].
    iSplitL "HW"; [iExact "HW"|].
    iSplitL "Hjunk"; [iExact "Hjunk"|].
    iSplitL "HauthL"; [iExact "HauthL"|].
    iSplitL "HauthD"; [iExact "HauthD"|].
    iSplitL "Hcov"; [iExact "Hcov"|].
    iSplitL "Hhdr"; [iExact "Hhdr"|].
    iSplitR; [done|].
    replace (LOGBLOCKS - 0)%nat with LOGBLOCKS by (unfold LOGBLOCKS; lia).
    iSplitL "Hlogr"; [iExact "Hlogr"|]. iExact "Hpool".
  Qed.

  Lemma eo_open_to_batch (bn : bio_names) (γfs : fs_names) (cov : gset Z)
      (logstart : Z) (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (Lw : nat -> list (bv 8)) :
    log_mirror_clean -∗
    eo_open bn γfs cov logstart 0 [] L D Lw 0 -∗
    log_batch bn γfs cov logstart 0 ∅.
  Proof.
    rewrite /log_batch /eo_open.
    iIntros "Hmirc (Hncell & HW & Hjunk & HauthL & HauthD & Hcov & Hhdr & _ & Hlogr & Hpool)".
    iExists [], L, D.
    iSplitR; [iPureIntro; split; [reflexivity | unfold LOGBLOCKS; lia]|].
    (* the emptied batch has logged nothing *)
    iSplitR; [iPureIntro; reflexivity|].
    iSplitR; [iPureIntro; constructor|].
    iSplitR; [iPureIntro; intros w Hw; apply elem_of_nil in Hw; done|].
    iSplitL "Hncell"; [iExact "Hncell"|].
    iSplitL "HW"; [iExact "HW"|].
    iSplitL "Hjunk"; [iExact "Hjunk"|].
    iSplitL "HauthL"; [iExact "HauthL"|].
    iSplitL "HauthD"; [iExact "HauthD"|].
    iSplitL "Hcov"; [iExact "Hcov"|].
    iSplitL "Hhdr"; [iExact "Hhdr"|].
    replace (LOGBLOCKS - 0)%nat with LOGBLOCKS in * by (unfold LOGBLOCKS; lia).
    iSplitL "Hlogr"; [iExact "Hlogr"|].
    iSplitL "Hpool"; [iExact "Hpool"|]. iExact "Hmirc".
  Qed.

  (* ---- the payload's pieces, extracted / re-assembled without a case
     split leaking into the whole-function proof ---- *)

  Lemma eo_pay_split (bn : bio_names) (γfs : fs_names) (γd : disk_names)
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

  Lemma eo_pay_mk (bn : bio_names) (γfs : fs_names) (γd : disk_names)
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

  (* the payload's L-half against the checked-out AUTHORITY: the only way a
     committer can learn a HOME block's bytes (there is no client [fsblock]
     for a home block on this side).  Pure conclusion, so the [iDestruct]
     keeps the payload. *)
  Lemma eo_pay_bs_auth (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (dv bno : mword 32)
      (bsl bsd : list (bv 8)) (d : bool) (L : gmap Z (list (bv 8))) :
    ghost_map_auth (fs_L γfs) 1 L -∗
    bio_pay bn (fs_view γfs γd dev cov) k dv bno bsl bsd d -∗
    ⌜L !! uint bno = Some bsl⌝.
  Proof.
    rewrite /bio_pay /fs_view /=. destruct d.
    - rewrite /fs_mdirty. iIntros "Ha [[Hm _] _]".
      iDestruct (ghost_map_lookup with "Ha Hm") as %Hlk. done.
    - rewrite /fs_mclean. iIntros "Ha [[Hm _] _]".
      iDestruct (ghost_map_lookup with "Ha Hm") as %Hlk. done.
  Qed.

  (* ---- the cov big-op, split along the write set and rejoined all-false ---- *)

  Lemma eo_cov_split (γfs : fs_names) (cov : gset Z) (W : list (mword 32)) :
    NoDup (map uint W) ->
    (forall w, w ∈ W -> uint w ∈ cov) ->
    ([∗ set] b ∈ cov, b ↪[fs_dirty γfs]{#(1/2)} (bool_decide (b ∈ map uint W)))
    -∗ ([∗ list] i ↦ w ∈ W, (uint w) ↪[fs_dirty γfs]{#(1/2)} true) ∗
       ([∗ set] b ∈ cov ∖ list_to_set (map uint W),
          b ↪[fs_dirty γfs]{#(1/2)} false).
  Proof.
    intros Hnd0 Hsub.
    assert (Hnd : base.NoDup (map uint W)) by (apply NoDup_ListNoDup; exact Hnd0).
    assert (Hss : (list_to_set (map uint W) : gset Z) ⊆ cov).
    { intros x Hx. apply elem_of_list_to_set in Hx.
      apply elem_of_list_fmap in Hx as [w [-> Hw]]. exact (Hsub w Hw). }
    assert (Hdisj : (list_to_set (map uint W) : gset Z)
                    ## cov ∖ list_to_set (map uint W)) by set_solver.
    rewrite {1}(union_difference_L (list_to_set (map uint W)) cov Hss).
    rewrite (big_sepS_union _ _ _ Hdisj).
    iIntros "[Hin Hout]".
    iSplitL "Hin".
    - rewrite (big_sepS_list_to_set _ (map uint W) Hnd) big_sepL_fmap.
      iApply (big_sepL_mono with "Hin"). intros i w Hw.
      rewrite bool_decide_eq_true_2; [done|].
      apply elem_of_list_fmap. exists w. split; [reflexivity|].
      eapply elem_of_list_lookup_2. exact Hw.
    - iApply (big_sepS_mono with "Hout"). intros x Hx.
      apply elem_of_difference in Hx as [_ Hx].
      rewrite bool_decide_eq_false_2; [done|].
      intro Hc. apply Hx. by apply elem_of_list_to_set.
  Qed.

  Lemma eo_cov_join (γfs : fs_names) (cov : gset Z) (W : list (mword 32)) :
    NoDup (map uint W) ->
    (forall w, w ∈ W -> uint w ∈ cov) ->
    ([∗ list] i ↦ w ∈ W, (uint w) ↪[fs_dirty γfs]{#(1/2)} false) -∗
    ([∗ set] b ∈ cov ∖ list_to_set (map uint W),
       b ↪[fs_dirty γfs]{#(1/2)} false) -∗
    ([∗ set] b ∈ cov, b ↪[fs_dirty γfs]{#(1/2)}
        (bool_decide (b ∈ map uint (@nil (mword 32))))).
  Proof.
    intros Hnd0 Hsub.
    assert (Hnd : base.NoDup (map uint W)) by (apply NoDup_ListNoDup; exact Hnd0).
    assert (Hss : (list_to_set (map uint W) : gset Z) ⊆ cov).
    { intros x Hx. apply elem_of_list_to_set in Hx.
      apply elem_of_list_fmap in Hx as [w [-> Hw]]. exact (Hsub w Hw). }
    assert (Hdisj : (list_to_set (map uint W) : gset Z)
                    ## cov ∖ list_to_set (map uint W)) by set_solver.
    rewrite {2}(union_difference_L (list_to_set (map uint W)) cov Hss).
    rewrite (big_sepS_union _ _ _ Hdisj).
    iIntros "Hin Hout".
    iSplitL "Hin".
    - rewrite (big_sepS_list_to_set _ (map uint W) Hnd) big_sepL_fmap.
      iApply (big_sepL_mono with "Hin"). intros i w Hw.
      rewrite bool_decide_eq_false_2; [done|].
      intro Hc; apply elem_of_nil in Hc; done.
    - iApply (big_sepS_mono with "Hout"). intros x Hx.
      rewrite bool_decide_eq_false_2; [done|].
      intro Hc; apply elem_of_nil in Hc; done.
  Qed.

  (* what every block knows about its arrival map.  [eo_regs] is the
     mid-function form (the commit arm has s3/s4/s5 in flight); [eo_regsE]
     is the epilogue's, where they are back at the caller's values. *)
  Definition eo_regs (m M : regfile) : Prop :=
    M !!! Regidx csp_rs1
      = add_vec (m !!! Regidx csp_rs1 : mword 64)
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
    /\ (forall c : mword 5, is_cs_idx c = true ->
          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
          c <> Rs3 -> c <> Rs4 -> c <> Rs5 ->
          M !!! Regidx c = (m !!! Regidx c : mword 64)).

  Definition eo_regsE (m M : regfile) : Prop :=
    M !!! Regidx csp_rs1
      = add_vec (m !!! Regidx csp_rs1 : mword 64)
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
    /\ (forall c : mword 5, is_cs_idx c = true ->
          c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
          M !!! Regidx c = (m !!! Regidx c : mword 64)).

  Lemma eo_regsE_regs (m M : regfile) : eo_regsE m M -> eo_regs m M.
  Proof.
    intros [A B]. split; [exact A|]. intros c H1 H2 H3 H4 H5 _ _ _.
    exact (B c H1 H2 H3 H4 H5).
  Qed.

End EndOpDefs.

(* ===================================================================== *)
(*  THE BLOCKS.  Each is a [Local Lemma] with its OWN [CID0] binder, so a  *)
(*  block whose predecessor returned on a different hart is applied at    *)
(*  the hart it actually starts on.                                       *)
(* ===================================================================== *)
Section EndOpBlocks.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}.

  (* ================================================================== *)
  (*  +0x92 .. +0x9c : the four-register epilogue and the return.        *)
  (*  Entered from the fast path's release AND, through the [c.j] at     *)
  (*  +0x66, from the commit tail.  s3/s4/s5 are back at the caller's    *)
  (*  values on BOTH arms -- the commit arm restored them at +0x11a and  *)
  (*  the fast arm never wrote them.                                     *)
  (* ================================================================== *)
  Local Lemma eo_epi `{GEN : GenId} `{CID0 : CpuId} 
      (j : nat) (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool) (lks : gset nat) :
    (K_end_op <= K)%nat ->
    eo_regsE m M ->
    sie_cap_gpr M (K - 8)%nat b (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) C b lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.end_op + 0x92) : mword 64) -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    eo_frame4 m -∗
    eo_frameJ m -∗
    eo_cont (CID0 := CID0)  j pidv dq m K eb C b lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hregs.
    pose proof Hregs as (Hsp & Hthr).
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc Hppid Hframe Hjunk Hcont".
    (* [eo_epi] keeps [b] and [eb] as SEPARATE binders (it is called at
       [b := eb] by every caller, but its own proof must not assume that).
       [cpu_own_eb_agree] at depth 0 derives [eb = b] from the ENTRY [Hcg]/
       [Hcnt] pair, before either name is touched by the register-restore
       leaves below, so it can bridge the [trap_csrs_ext]/[cpu_claim_ext]
       transports (indexed by [eb]) onto the [b]-indexed crossing chain those
       leaves build. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    cbn in Hbm.
    rewrite /eo_frame4 /eo_frameJ.
    iDestruct "Hframe" as "(Hr56 & Hr48 & Hr40 & Hr32)".
    iDestruct "Hjunk" as "(Hg24 & Hg16 & Hg8 & Hg0)".
    iDestruct "Hg24" as (vg24) "Hg24". iDestruct "Hg16" as (vg16) "Hg16".
    iDestruct "Hg8" as (vg8) "Hg8". iDestruct "Hg0" as (vg0) "Hg0".
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { unfold pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hc2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hc3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite Hsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    (* +0x92 c.ldsp ra,56(sp) *)
    iPoseProof (eoi_92 with "Htext") as "Hi92".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x92)) (mword_of_int 7 : mword 6) Rra
              M (K - 8)%nat (m !!! Regidx Rra : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi92 [Hr56]").
    { iEval (rewrite Hc1). iExact "Hr56". }
    iIntros (CID1 Hs1) "Hcg Hpc Hr56".
    iEval (rewrite Hc1) in "Hr56".
    pose (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hpp94 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x92) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x94))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp94) in "Hpc".
    clear Hpp94.
    (* +0x94 c.ldsp s0,48(sp) *)
    iPoseProof (eoi_94 with "Htext") as "Hi94".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x94)) (mword_of_int 6 : mword 6) Rs0
              P1 (K - 8)%nat (m !!! Regidx Rs0 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi94 [Hr48]").
    { iEval (rewrite HP1sp Hc2). iExact "Hr48". }
    iIntros (CID2 Hs2) "Hcg Hpc Hr48".
    iEval (rewrite HP1sp Hc2) in "Hr48".
    pose (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hpp96 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x94) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x96))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp96) in "Hpc".
    clear Hpp96.
    (* +0x96 c.ldsp s1,40(sp) *)
    iPoseProof (eoi_96 with "Htext") as "Hi96".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x96)) (mword_of_int 5 : mword 6) Rs1
              P2 (K - 8)%nat (m !!! Regidx Rs1 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi96 [Hr40]").
    { iEval (rewrite HP2sp Hc3). iExact "Hr40". }
    iIntros (CID3 Hs3) "Hcg Hpc Hr40".
    iEval (rewrite HP2sp Hc3) in "Hr40".
    pose (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hpp98 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x96) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x98))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp98) in "Hpc".
    clear Hpp98.
    (* +0x98 c.ldsp s2,32(sp) *)
    iPoseProof (eoi_98 with "Htext") as "Hi98".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x98)) (mword_of_int 4 : mword 6) Rs2
              P3 (K - 8)%nat (m !!! Regidx Rs2 : mword 64) b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi98 [Hr32]").
    { iEval (rewrite HP3sp Hc4). iExact "Hr32". }
    iIntros (CID4 Hs4) "Hcg Hpc Hr32".
    iEval (rewrite HP3sp Hc4) in "Hr32".
    pose (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : P4 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3sp | vm_compute; discriminate]).
    assert (Hpp9a : add_vec_int (mword_of_int (KernelSyms.end_op + 0x98) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x9a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9a) in "Hpc".
    clear Hpp9a.
    (* +0x9a c.addi16sp sp,64 : pop the eight-slot frame *)
    assert (Hwv : add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP4sp Hsp. apply frame_cancel_64. }
    assert (Hpop : (P4 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))) 8).
    { rewrite Hwv HP4sp Hsp Hpush. reflexivity. }
    iAssert (stack_own (m !!! Regidx csp_rs1 : mword 64) 8)
      with "[Hr56 Hr48 Hr40 Hr32 Hg24 Hg16 Hg8 Hg0]" as "Hstk".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr56"; [iExists _; iExact "Hr56"|].
      iSplitL "Hr48"; [iExists _; iExact "Hr48"|].
      iSplitL "Hr40"; [iExists _; iExact "Hr40"|].
      iSplitL "Hr32"; [iExists _; iExact "Hr32"|].
      iSplitL "Hg24"; [iExists _; iExact "Hg24"|].
      iSplitL "Hg16"; [iExists _; iExact "Hg16"|].
      iSplitL "Hg8";  [iExists _; iExact "Hg8"|].
      iSplitL "Hg0";  [iExists _; iExact "Hg0"|].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iPoseProof (eoi_9a with "Htext") as "Hi9a".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.end_op + 0x9a))
              (mword_of_int 4 : mword 6) P4 (K - 8)%nat 8 b Hpop
              with "Hcg Hpc Hi9a Hstk").
    iIntros (CID5 Hs5) "Hcg Hpc".
    pose (P5 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (P4 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> P4).
    assert (Hnk : ((K - 8) + 8)%nat = K) by (unfold K_end_op in HK; lia).
    iEval (rewrite Hnk) in "Hcg".
    clear Hnk.
    assert (Hpp9c : add_vec_int (mword_of_int (KernelSyms.end_op + 0x9a) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x9c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9c) in "Hpc".
    clear Hpp9c.
    (* +0x9c c.ret *)
    assert (HP5ra : P5 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq. reflexivity. }
    iPoseProof (eoi_9c with "Htext") as "Hi9c".
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.end_op + 0x9c)) Rra P5 K b
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hi9c").
    iIntros (CID6 Hs6) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (P5 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HP5ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    clear Hretf.
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
      rewrite /P1 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18). }
    assert (Cs3 : P5 !!! Regidx (mword_of_int 19 : mword 5)
                  = (m !!! Regidx (mword_of_int 19 : mword 5) : mword 64))
      by (apply Hfin; eoidx).
    assert (Cs4 : P5 !!! Regidx (mword_of_int 20 : mword 5)
                  = (m !!! Regidx (mword_of_int 20 : mword 5) : mword 64))
      by (apply Hfin; eoidx).
    assert (Cs5 : P5 !!! Regidx (mword_of_int 21 : mword 5)
                  = (m !!! Regidx (mword_of_int 21 : mword 5) : mword 64))
      by (apply Hfin; eoidx).
    assert (Cs6 : P5 !!! Regidx (mword_of_int 22 : mword 5)
                  = (m !!! Regidx (mword_of_int 22 : mword 5) : mword 64))
      by (apply Hfin; eoidx).
    assert (Cs7 : P5 !!! Regidx (mword_of_int 23 : mword 5)
                  = (m !!! Regidx (mword_of_int 23 : mword 5) : mword 64))
      by (apply Hfin; eoidx).
    assert (Cs8 : P5 !!! Regidx (mword_of_int 24 : mword 5)
                  = (m !!! Regidx (mword_of_int 24 : mword 5) : mword 64))
      by (apply Hfin; eoidx).
    assert (Cs9 : P5 !!! Regidx (mword_of_int 25 : mword 5)
                  = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64))
      by (apply Hfin; eoidx).
    assert (Cs10 : P5 !!! Regidx (mword_of_int 26 : mword 5)
                  = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64))
      by (apply Hfin; eoidx).
    assert (Cs11 : P5 !!! Regidx (mword_of_int 27 : mword 5)
                  = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64))
      by (apply Hfin; eoidx).
    iDestruct (cpu_own_transport CID0 CID6 0 eb (proc_addr j) C b 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID6 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID6 eb (proc_addr j)
                 ltac:(rewrite Hbm; wp_next_chain) with "Hextm") as "Hextm".
    rewrite /eo_cont.
    iSpecialize ("Hcont" $! CID6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P5 with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid").
    { unfold callee_saved. repeat split; assumption. }
  Qed.


  (* ================================================================== *)
  (*  +0x42 .. +0x66 : re-acquire, committing := 0, ncommit++, wakeup,   *)
  (*  DEPOSIT the batch, release, and [c.j] into the epilogue.           *)
  (*  Entered from the n = 0 fall-through at +0x3e AND, through the      *)
  (*  [c.j] at +0x120, from the commit body -- in both cases holding the *)
  (*  batch re-formed at n = 0.                                          *)
  (* ================================================================== *)
  Local Lemma eo_tail `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (C : iProp Σ) (lks : gset nat) :
    (K_end_op <= K)%nat ->
    eo_regsE m M ->
    (* the order premise: [eo_tail] opens with its OWN re-acquire of "log"
       (rank 3), from the OUTER set [lks] (the lock is not held on entry --
       the first critical section already released it before commit() ran). *)
    locks_below lks (lock_rank "log") ->
    sie_cap_gpr M (K - 8)%nat eb (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) C eb lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.end_op + 0x42) : mword 64) -∗
    panic_wp_any -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    eo_frame4 m -∗
    eo_frameJ m -∗
    log_batch bn γfs cov logstart 0 ∅ -∗
    eo_cont (CID0 := CID0)  j pidv dq m K eb C eb lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hregs Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    pose proof Hregs as (Hsp & Hthr).
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hlctx #Hprocs Hppid
              Hframe Hjunk Hbatch Hcont".
    iDestruct "Hlctx" as "(#Hlock & #Hdevc & #Hstc)".
    iDestruct (procs_inv_len γs with "Hprocs") as %Hlen.
    (* ===== +0x42 auipc s1,0x1e ===== *)
    iPoseProof (eoi_42 with "Htext") as "Hi42".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.end_op + 0x42)) Rs1 (mword_of_int 30 : mword 20)
              M (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi42").
    iIntros (CIDa1 Hsa1) "Hcg Hpc".
    pose (E1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.end_op + 0x42) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> M).
    assert (Hpp46 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x42) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0x46))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp46) in "Hpc".
    clear Hpp46.
    (* ===== +0x46 addi s1,s1,1676 ===== *)
    iPoseProof (eoi_46 with "Htext") as "Hi46".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.end_op + 0x46)) Rs1 Rs1
              (mword_of_int 1682 : mword 12) E1 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi46").
    iIntros (CIDa2 Hsa2) "Hcg Hpc".
    pose (E2 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (E1 !!! Regidx Rs1 : mword 64)
                     (sign_extend' 64 (mword_of_int 1682 : mword 12)))]> E1).
    assert (HE2s1 : E2 !!! Regidx Rs1 = log_addr).
    { rewrite /E2 upd_eq /E1 upd_eq. exact eo_reloc_log_42. }
    assert (HE2sp : E2 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64)).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HE2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              E2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /E2 upd_ne; [| regne]. rewrite /E1 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18). }
    assert (Hpp4a : add_vec_int (mword_of_int (KernelSyms.end_op + 0x46) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0x4a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4a) in "Hpc".
    clear Hpp4a.
    (* ===== +0x4a c.mv a0,s1 ===== *)
    iPoseProof (eoi_4a with "Htext") as "Hi4a".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.end_op + 0x4a)) Ra0 Rs1
              E2 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi4a").
    iIntros (CIDa3 Hsa3) "Hcg Hpc".
    pose (E3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget E2 Rs1))]> E2).
    assert (HE3a0 : E3 !!! Regidx Ra0 = log_addr).
    { rewrite /E3 upd_eq. rgne. rewrite HE2s1. apply add_vec_zero_l. }
    assert (HE3s1 : E3 !!! Regidx Rs1 = log_addr)
      by (rewrite /E3 upd_ne; [exact HE2s1 | vm_compute; discriminate]).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /E3 upd_ne; [exact HE2sp | vm_compute; discriminate]).
    assert (HE3thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              E3 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /E3 upd_ne; [| regne]. exact (HE2thr c Hcs N2 N8 N9 N18). }
    assert (Hpp4c : add_vec_int (mword_of_int (KernelSyms.end_op + 0x4a) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x4c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp4c) in "Hpc".
    clear Hpp4c.
    (* ===== +0x4c jal ra,acquire ===== *)
    iPoseProof (eoi_4c with "Htext") as "Hi4c".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0x4c)) Rra
              (mword_of_int 2084554 : mword 21) E3 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi4c").
    iIntros (CIDa4 Hsa4) "Hcg Hpc".
    pose (E4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0x4c) : mword 64) 4)]> E3).
    assert (Htgt4c : add_vec (mword_of_int (KernelSyms.end_op + 0x4c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2084554 : mword 21))
                     = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt4c) in "Hpc".
    clear Htgt4c.
    assert (HE4a0 : E4 !!! Regidx Ra0 = log_addr)
      by (rewrite /E4 upd_ne; [exact HE3a0 | vm_compute; discriminate]).
    assert (HE4s1 : E4 !!! Regidx Rs1 = log_addr)
      by (rewrite /E4 upd_ne; [exact HE3s1 | vm_compute; discriminate]).
    assert (HE4ra : E4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0x4c) : mword 64) 4)
      by (rewrite /E4; apply upd_eq).
    assert (HE4sp : E4 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /E4 upd_ne; [exact HE3sp | vm_compute; discriminate]).
    assert (HE4thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              E4 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /E4 upd_ne; [| regne]. exact (HE3thr c Hcs N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID0 CIDa4 0 eb (proc_addr j) C eb 
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDa4 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDa4 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CID0) (CIDb := CIDa4)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (Acq.wp_acquire_sconf (ln_lk γ) "log"%string
              (log_res γ bn γfs cov logstart) E4 0%nat eb (proc_addr j) C
              (K - 8)%nat eb lks eo_noff0 ltac:(pose proof (eo_Klk K HK); lia)
              Hbelow
              with "Hcg Hcnt Htext Hpc [Hlock] Hpanic").
    { iEval (rewrite HE4a0). iExact "Hlock". }
    iIntros (CIDb1 Hsb1 ms macq) "%Hmsfacts Hcg Hpc %Hacq Htok HRres Hcnt Hpay".
    assert (Hpc50 : ret_pc (E4 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0x50)).
    { rewrite HE4ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc50) in "Hpc".
    clear Hpc50.
    (* acquire does not itself thread the trap-CSR complement (it does not
       mention it), so it strands Hextc/Hextm at the pre-call hart -- transport
       them across the WIDER span here, not inside acquire's own crossing. *)
    iDestruct (trap_csrs_ext_transport CIDa4 CIDb1 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDa4 CIDb1 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CIDa4) (CIDb := CIDb1)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    pose proof Hacq as Hacq_cs.
    assert (Hqs1 : macq !!! Regidx Rs1 = log_addr).
    { rewrite (callee_saved_lookup Hacq_cs Rs1 ltac:(vm_compute; reflexivity)).
      exact HE4s1. }
    assert (Hqsp : macq !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hacq_cs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HE4sp. }
    assert (Hqthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              macq !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hacq_cs c Hcs). exact (HE4thr c Hcs N2 N8 N9 N18). }
    (* ================= THE CRITICAL SECTION ================= *)
    rewrite /log_res.
    iDestruct "HRres" as (out cmt nc om Ep Xr)
      "(Houtc & Hcmtc & Hncc & Hoauth & %Hsz & %Hbnd & %Hout3 & %Hcmt0 & Hepa & %Hepos & Hxa & %Hlive & %Hcap & Hrest)".
    (* committing IS still set: the committer holds the batch's fs_L
       AUTHORITY, and log_res's cmt = false arm holds one too. *)
    destruct cmt.
    2: { iDestruct "Hrest" as (n0 LB0) "(_ & _ & _ & Hb2)".
         rewrite /log_batch.
         iDestruct "Hbatch" as (W1 L1 D1) "(_ & _ & _ & _ & _ & _ & _ & Ha1 & _)".
         iDestruct "Hb2" as (W2 L2 D2) "(_ & _ & _ & _ & _ & _ & _ & Ha2 & _)".
         iDestruct (ghost_map_auth_valid_2 with "Ha1 Ha2") as %[Hbad _].
         exfalso. by apply (Qp.not_add_le_l 1 1). }
    (* ===== +0x50 sw zero,32(s1) : committing := 0 ===== *)
    assert (Hcmta : add_vec (rget macq Rs1) (sign_extend' 64 (mword_of_int 32 : mword 12))
                    = l_cmt).
    { rgne. rewrite Hqs1. exact eo_addr_cmt. }
    iEval (rewrite -Hcmta) in "Hcmtc".
    iPoseProof (eoi_50 with "Htext") as "Hi50".
    iApply (wp_sw_zero_s_sconf (mword_of_int (KernelSyms.end_op + 0x50)) Rs1
              (mword_of_int 32 : mword 12) macq (trap_res eb + (K - 8))%nat
              (mword_of_int 1 : mword 32) false
              with "Hcg Hpc Hi50 Hcmtc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcmtc".
    iEval (rewrite Hcmta) in "Hcmtc".
    assert (Hpp54 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x50) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0x54))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp54) in "Hpc".
    clear Hpp54.
    (* ===== +0x54 c.lw a5,40(s1) : a5 := log.ncommit ===== *)
    assert (Hnca : add_vec (rget macq Rs1) (sign_extend' 64 (mword_of_int 40 : mword 12))
                   = l_ncommit).
    { rgne. rewrite Hqs1. exact eo_addr_nc. }
    iEval (rewrite -Hnca) in "Hncc".
    iPoseProof (eoi_54 with "Htext") as "Hi54".
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.end_op + 0x54)) Ra5 Rs1
              (mword_of_int 40 : mword 12) macq (trap_res eb + (K - 8))%nat nc false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 Hncc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hncc".
    iEval (rewrite Hnca) in "Hncc".
    pose (F1 := <[Regidx Ra5 := regval_into_reg (sign_extend' 64 nc)]> macq).
    assert (HF1s1 : F1 !!! Regidx Rs1 = log_addr)
      by (rewrite /F1 upd_ne; [exact Hqs1 | vm_compute; discriminate]).
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x54) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x56))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    clear Hpp56.
    (* ===== +0x56 c.addiw a5,a5,1 ===== *)
    iPoseProof (eoi_56 with "Htext") as "Hi56".
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.end_op + 0x56)) Ra5
              (mword_of_int 1 : mword 6) F1 (trap_res eb + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi56").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (F2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (rget F1 Ra5)
                        (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> F1).
    assert (HF2s1 : F2 !!! Regidx Rs1 = log_addr)
      by (rewrite /F2 upd_ne; [exact HF1s1 | vm_compute; discriminate]).
    assert (Hpp58 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x56) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x58))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp58) in "Hpc".
    clear Hpp58.
    (* ===== +0x58 c.sw a5,40(s1) : log.ncommit := a5 ===== *)
    assert (Hnca2 : add_vec (rget F2 Rs1) (sign_extend' 64 (mword_of_int 40 : mword 12))
                    = l_ncommit).
    { rgne. rewrite HF2s1. exact eo_addr_nc. }
    iEval (rewrite -Hnca2) in "Hncc".
    iPoseProof (eoi_58 with "Htext") as "Hi58".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.end_op + 0x58)) Ra5 Rs1
              (mword_of_int 40 : mword 12) F2 (trap_res eb + (K - 8))%nat nc false
              with "Hcg Hpc Hi58 Hncc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hncc".
    iEval (rewrite Hnca2) in "Hncc".
    set (nc' := trunc32 (rget F2 Ra5)).
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.end_op + 0x58) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x5a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    clear Hpp5a.
    (* ===== +0x5a c.mv a0,s1 ===== *)
    iPoseProof (eoi_5a with "Htext") as "Hi5a".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.end_op + 0x5a)) Ra0 Rs1
              F2 (trap_res eb + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (F3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget F2 Rs1))]> F2).
    assert (HF3s1 : F3 !!! Regidx Rs1 = log_addr)
      by (rewrite /F3 upd_ne; [exact HF2s1 | vm_compute; discriminate]).
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.end_op + 0x5a) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x5c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    clear Hpp5c.
    (* ===== +0x5c jal ra,wakeup ===== *)
    iPoseProof (eoi_5c with "Htext") as "Hi5c".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0x5c)) Rra
              (mword_of_int 2089552 : mword 21) F3 (trap_res eb + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (F4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0x5c) : mword 64) 4)]> F3).
    assert (Htgt5c : add_vec (mword_of_int (KernelSyms.end_op + 0x5c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2089552 : mword 21))
                     = mword_of_int KernelSyms.wakeup)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt5c) in "Hpc".
    clear Htgt5c.
    assert (HF4s1 : F4 !!! Regidx Rs1 = log_addr)
      by (rewrite /F4 upd_ne; [exact HF3s1 | vm_compute; discriminate]).
    assert (HF4ra : F4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0x5c) : mword 64) 4)
      by (rewrite /F4; apply upd_eq).
    assert (HwdomF : forall r : regidx, r ∈ dom (rf_to_gmap F4))
      by (intro r; apply rf_to_gmap_dom).
    (* "log" (3) outranks nothing yet held above it, but wakeup's own order
       premise is at "proc" (11): lift [Hbelow] to that rank and push it
       across the "log" singleton this hart is holding right now. *)
    assert (Hlog_lt_proc : (lock_rank "log" < lock_rank "proc")%nat)
      by (vm_compute; lia).
    assert (Hbelow_wk1 : locks_below ({[lock_rank "log"]} ∪ lks) (lock_rank "proc")).
    { apply locks_below_union_singleton; [exact Hlog_lt_proc |].
      apply (locks_below_mono lks (lock_rank "log")); [exact Hbelow | lia]. }
    iApply (Wk.wp_wakeup_sconf F4 γs (proc_addr j) 1%nat
              (trap_res eb + (K - 8))%nat eb C false ({[lock_rank "log"]} ∪ lks)
              ltac:(pose proof (eo_Kwk K HK); lia) HwdomF Hlen eo_noff1
              Hbelow_wk1
              with "Hcg Hcnt Htext Hpc Hpanic Hprocs").
    iApply wp_next_off_intro. iIntros (Mw) "[%Hwcs %Hwdom] Hcg Hcnt Htext2 Hpc".
    iEval (rewrite HF4ra) in "Hpc".
    clear HF4ra.
    assert (Hpp60 : ret_pc (add_vec_int (mword_of_int (KernelSyms.end_op + 0x5c) : mword 64) 4)
                    = (mword_of_int (KernelSyms.end_op + 0x60) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60) in "Hpc".
    clear Hpp60.
    assert (HMws1 : Mw !!! Regidx Rs1 = log_addr).
    { rewrite (callee_saved_lookup Hwcs Rs1 ltac:(vm_compute; reflexivity)).
      exact HF4s1. }
    assert (HMwsp : Mw !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hwcs csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /F4 upd_ne; [| vm_compute; discriminate].
      rewrite /F3 upd_ne; [| vm_compute; discriminate].
      rewrite /F2 upd_ne; [| vm_compute; discriminate].
      rewrite /F1 upd_ne; [| vm_compute; discriminate]. exact Hqsp. }
    assert (HMwthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              Mw !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hwcs c Hcs).
      rewrite /F4 upd_ne; [| regne]. rewrite /F3 upd_ne; [| regne].
      rewrite /F2 upd_ne; [| regne]. rewrite /F1 upd_ne; [| regne].
      exact (Hqthr c Hcs N2 N8 N9 N18). }
    (* ===== +0x60 c.mv a0,s1 ===== *)
    iPoseProof (eoi_60 with "Htext") as "Hi60".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.end_op + 0x60)) Ra0 Rs1
              Mw (trap_res eb + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (G1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget Mw Rs1))]> Mw).
    assert (HG1a0 : G1 !!! Regidx Ra0 = log_addr).
    { rewrite /G1 upd_eq. rgne. rewrite HMws1. apply add_vec_zero_l. }
    assert (HG1sp : G1 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /G1 upd_ne; [exact HMwsp | vm_compute; discriminate]).
    assert (HG1thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              G1 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G1 upd_ne; [| regne]. exact (HMwthr c Hcs N2 N8 N9 N18). }
    assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x60) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x62))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp62) in "Hpc".
    clear Hpp62.
    (* ===== +0x62 jal ra,release ===== *)
    iPoseProof (eoi_62 with "Htext") as "Hi62".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0x62)) Rra
              (mword_of_int 2084668 : mword 21) G1 (trap_res eb + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi62").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (G2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0x62) : mword 64) 4)]> G1).
    assert (Htgt62 : add_vec (mword_of_int (KernelSyms.end_op + 0x62) : mword 64)
                       (sign_extend' 64 (mword_of_int 2084668 : mword 21))
                     = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt62) in "Hpc".
    clear Htgt62.
    assert (HG2a0 : G2 !!! Regidx Ra0 = log_addr)
      by (rewrite /G2 upd_ne; [exact HG1a0 | vm_compute; discriminate]).
    assert (HG2ra : G2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0x62) : mword 64) 4)
      by (rewrite /G2; apply upd_eq).
    assert (HG2sp : G2 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /G2 upd_ne; [exact HG1sp | vm_compute; discriminate]).
    assert (HG2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              G2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G2 upd_ne; [| regne]. exact (HG1thr c Hcs N2 N8 N9 N18). }
    (* ---- the batch goes back in, at n = 0 ---- *)
    assert (Hsum : (0 + op_sum om <= LOGBLOCKS)%nat).
    { pose proof (op_sum_bound om MAXOPBLOCKS Hbnd) as Hb.
      rewrite Hsz in Hb. unfold MAXOPBLOCKS, LOGBLOCKS in *. lia. }
    (* THE BATCH GOES BACK EMPTY, so LB is empty too -- and no surviving op
       may hold a credit against it.  None can: this arm ran with
       committing = 1, which forces out = 0 ([Hcmt0]) and hence om = empty,
       so the credit clause is vacuous.  That is the same fact that makes
       the commit safe in the first place -- no operation is open across
       it, so no operation's already-logged set can outlive the header it
       referred to. *)
    assert (Hommt : om = ∅).
    { apply map_size_empty_iff. rewrite Hsz. exact (Hcmt0 eq_refl). }
    (* ---- THE EPOCH BUMP (fs-log.md §G.2/§G.9 FINDING 4) ----
       THIS is the group extension's one moving part, and it is here rather
       than at the lh-clearing step because here the lock is re-held and the
       batch is going back in.  [Hommt] is what makes it sound: the ledger
       is EMPTY at this point, so the bump cannot falsify any live entry's
       "born in the current epoch" -- there is no live entry.  Every witness
       minted in the batch just committed keeps its old epoch and is thereby
       DEAD: it can no longer equal [S Ep], so [log_use_group] can never
       fire on it again.  Nothing is revoked; the index simply moves on. *)
    iMod (log_epoch_bump γ Ep with "Hepa") as "Hepa".
    iAssert (log_res γ bn γfs cov logstart)
      with "[Houtc Hcmtc Hncc Hoauth Hepa Hxa Hbatch]" as "HRres".
    { rewrite /log_res. iExists out, false, nc', om, (S Ep), Xr.
      iSplitL "Houtc"; [iExact "Houtc"|].
      iSplitL "Hcmtc"; [iExact "Hcmtc"|].
      iSplitL "Hncc"; [iExact "Hncc"|].
      iSplitL "Hoauth"; [iExact "Hoauth"|].
      iSplitR; [iPureIntro; exact Hsz|].
      iSplitR; [iPureIntro; exact Hbnd|].
      iSplitR; [iPureIntro; exact Hout3|].
      iSplitR; [iPureIntro; discriminate|].
      iSplitL "Hepa"; [iExact "Hepa"|].
      iSplitR; [iPureIntro; lia|].
      iSplitL "Hxa"; [iExact "Hxa"|].
      (* vacuous: [Hommt] says there is no live entry to re-date *)
      iSplitR.
      { iPureIntro. intros i e Hi. rewrite Hommt lookup_empty in Hi.
        discriminate. }
      (* the registry still does not run ahead: the cap only went UP *)
      iSplitR.
      { iPureIntro. intros e' b' Hin. pose proof (Hcap e' b' Hin). lia. }
      iExists 0%nat, ∅. iSplitR; [iPureIntro; exact Hsum|].
      iSplitR.
      { iPureIntro. intros i e Hi. rewrite Hommt lookup_empty in Hi.
        discriminate. }
      (* AND THE SELF-INVALIDATION, made concrete: the header went back
         EMPTY, and the clause survives only because no row of the registry
         can carry the NEW epoch -- every row is capped by the old one. *)
      iSplitR.
      { iPureIntro. intros b' Hin. exfalso.
        pose proof (Hcap (S Ep) b' Hin). lia. }
      iExact "Hbatch". }
    iApply (Rel.wp_release_sconf (ln_lk γ) log_addr "log"%string
              (log_res γ bn γfs cov logstart) G2 0%nat eb (proc_addr j) C
              (K - 8)%nat
              ({[lock_rank "log"]} ∪ lks)
              ltac:(rewrite HG2a0; rewrite /log_addr; apply bv_eq; vm_compute; reflexivity)
              ltac:(pose proof (eo_Klk K HK); lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
    { iExact "Hlock". }
    iIntros (CIDc1 Hsc1 mr) "Hcg Hpc %Hrel Hcnt".
    assert (Hsetback : ({[lock_rank "log"]} ∪ lks) ∖ {[lock_rank "log"]} = lks)
      by (apply locks_add_del; assumption).
    iEval (rewrite Hsetback) in "Hcnt".
    assert (Hpc66 : ret_pc (G2 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0x66)).
    { rewrite HG2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc66) in "Hpc".
    clear Hpc66.
    (* release does not itself thread the trap-CSR complement either --
       transport it across this crossing too. *)
    iDestruct (trap_csrs_ext_transport CIDb1 CIDc1 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDb1 CIDc1 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    pose proof Hrel as Hrel_cs.
    assert (Hregs2 : eo_regsE m mr).
    { rewrite /eo_regsE. split.
      - rewrite (callee_saved_lookup Hrel_cs csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite HG2sp. exact Hsp.
      - intros c Hcs N2 N8 N9 N18.
        rewrite (callee_saved_lookup Hrel_cs c Hcs).
        exact (HG2thr c Hcs N2 N8 N9 N18). }
    (* ===== +0x66 c.j -> +0x92 ===== *)
    iPoseProof (eoi_66 with "Htext") as "Hi66".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.end_op + 0x66))
              (sign_extend' 21 (concat_vec (mword_of_int 22 : mword 11) ('b"0")))
              mr (K - 8)%nat eb ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi66").
    iIntros (CIDc2 Hsc2). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt66 : add_vec (mword_of_int (KernelSyms.end_op + 0x66) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 22 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.end_op + 0x92))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt66) in "Hpc".
    clear Htgt66.
    iDestruct (cpu_own_transport CIDc1 CIDc2 0 eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDc1 CIDc2 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDc1 CIDc2 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CIDb1) (CIDb := CIDc2)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (eo_epi (CID0 := CIDc2)  j pidv dq m mr K eb C eb lks HK Hregs2
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hppid Hframe Hjunk Hcont").
  Qed.


  (* ---- the big-op re-indexings the commit tail needs ---- *)

  Lemma eo_seq_join (P : nat -> iProp Σ) (a c : nat) :
    ([∗ list] i ∈ seq 0 a, P i) -∗ ([∗ list] i ∈ seq a c, P i) -∗
    ([∗ list] i ∈ seq 0 (a + c), P i).
  Proof. rewrite seq_app big_sepL_app. iIntros "$ $". Qed.

  Lemma eo_entries_in (γfs : fs_names) (logstart : Z) (W : list (mword 32))
      (Lw : nat -> list (bv 8)) (n : nat) :
    n = length W ->
    ([∗ list] i ∈ seq 0 n, fsblock γfs (log_slot_bno logstart i) (Lw i)) -∗
    ([∗ list] i ↦ w ∈ W, (uint w) ↪[fs_dirty γfs]{#(1/2)} true) -∗
    ([∗ list] i ↦ w ∈ W, fsblock γfs (log_slot_bno logstart i) (Lw i) ∗
                         (uint w) ↪[fs_dirty γfs]{#(1/2)} true).
  Proof.
    intros ->. iIntros "Ha Hb". rewrite big_sepL_sep.
    iSplitL "Ha"; [| iExact "Hb"].
    iEval (rewrite (eo_seq_of_list W
             (fun i => fsblock γfs (log_slot_bno logstart i) (Lw i)))) in "Ha".
    iExact "Ha".
  Qed.

  Lemma eo_entries_out (γfs : fs_names) (logstart : Z) (W : list (mword 32))
      (Lw : nat -> list (bv 8)) (n : nat) :
    n = length W ->
    ([∗ list] i ↦ w ∈ W, fsblock γfs (log_slot_bno logstart i) (Lw i) ∗
                         (uint w) ↪[fs_dirty γfs]{#(1/2)} false) -∗
    ([∗ list] i ∈ seq 0 n, ∃ bs, fsblock γfs (log_slot_bno logstart i) bs) ∗
    ([∗ list] i ↦ w ∈ W, (uint w) ↪[fs_dirty γfs]{#(1/2)} false).
  Proof.
    intros ->. rewrite big_sepL_sep. iIntros "[Ha $]".
    iEval (rewrite (eo_seq_of_list W
             (fun i => ∃ bs, fsblock γfs (log_slot_bno logstart i) bs)%I)).
    iApply (big_sepL_mono with "Ha"). intros i w Hw. iIntros "H". iExists _. iExact "H".
  Qed.

  Lemma eo_cells_junk (W : list (mword 32)) (n : nat) :
    n = length W ->
    ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) -∗
    ([∗ list] i ∈ seq 0 n, ∃ junk : mword 32, lh_block i ↦₄ junk).
  Proof.
    intros ->. iIntros "H".
    iEval (rewrite (eo_seq_of_list W (fun i => ∃ junk : mword 32, lh_block i ↦₄ junk)%I)).
    iApply (big_sepL_mono with "H"). intros i w Hw. iIntros "H". iExists _. iExact "H".
  Qed.

  (* ================================================================== *)
  (*  +0x104 .. +0x120 : write_head, install_trans(0), lh.n := 0,        *)
  (*  write_head, restore s3/s4/s5, and the [c.j] that rejoins the tail.  *)
  (*  Entered by falling out of the copy loop with the cursor at n.       *)
  (* ================================================================== *)
  Local Lemma eo_commit `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (n : nat) (W : list (mword 32)) (Lw : nat -> list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (C : iProp Σ) (lks : gset nat) :
    (K_end_op <= K)%nat ->
    log_geom_ok cov logstart ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (n = length W /\ (n <= LOGBLOCKS)%nat) ->
    NoDup (map uint W) ->
    (forall w, w ∈ W -> uint w ∈ cov /\ ~ (uint w ∈ log_region_set logstart)) ->
    (forall (i : nat) (w : mword 32), W !! i = Some w -> L !! uint w = Some (Lw i)) ->
    eo_regs m M ->
    (* threaded through unchanged to [eo_tail]'s own re-acquire of "log" --
       [eo_commit] itself never touches the lock. *)
    locks_below lks (lock_rank "log") ->
    sie_cap_gpr M (K - 8)%nat eb (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) C eb lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.end_op + 0x104) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    (* the crash seam and the era certificate: what turns this block's
       [bwrite]s into REAL durability fupds (FsCrash's four permits) *)
    fs_crash_seam cov logstart -∗
    era_registered gen_id riscv_eraGS -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    eo_frame4 m -∗
    eo_frameS m -∗
    log_mirror_clean -∗
    eo_open bn γfs cov logstart n W L D Lw n -∗
    eo_cont (CID0 := CID0)  j pidv dq m K eb C eb lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hj Hgl Hshape Hnd Hwok HLw Hregs Hbelow.
    destruct Hshape as [HnW Hn30].
    pose proof Hregs as (Hsp & Hthr).
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlctx #Hseam #Hregc Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hframe HframeS Hmirc
              Hopen Hcont".
    iPoseProof (log_ctx_swap with "Hlctx") as "#Hswlb".
    iPoseProof (log_ctx_frozen with "Hlctx") as "#Hlfz".
    rewrite /eo_open.
    iDestruct "Hopen" as
      "(Hncell & HW & Hjunk & HauthL & HauthD & Hcov & Hhdr & Hdone & Hrest & Hpool)".
    (* ---- the pool: one unit for the first write_head ---- *)
    assert (Hp1 : ((LOGBLOCKS - n) + 2)%nat = (1 + ((LOGBLOCKS - n) + 1))%nat)
      by (unfold LOGBLOCKS in *; lia).
    iEval (rewrite Hp1 (bslots_op bn 1 ((LOGBLOCKS - n) + 1))) in "Hpool".
    iDestruct "Hpool" as "[Hu1 Hpool]".
    (* ===== +0x104 jal ra,write_head ===== *)
    iPoseProof (eoi_104 with "Htext") as "Hi104".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0x104)) Rra
              (mword_of_int 2096324 : mword 21) M (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi104").
    iIntros (CIDa1 Hsa1) "Hcg Hpc".
    pose (A1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0x104) : mword 64) 4)]> M).
    assert (Htgt104 : add_vec (mword_of_int (KernelSyms.end_op + 0x104) : mword 64)
                        (sign_extend' 64 (mword_of_int 2096324 : mword 21))
                      = mword_of_int KernelSyms.write_head)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt104) in "Hpc".
    clear Htgt104.
    assert (HA1ra : A1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0x104) : mword 64) 4)
      by (rewrite /A1; apply upd_eq).
    assert (HA1regs : eo_regs m A1).
    { rewrite /eo_regs. split.
      - rewrite /A1 upd_ne; [exact Hsp | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /A1 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21). }
    iDestruct (cpu_own_transport CID0 CIDa1 0 eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDa1 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDa1 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CID0) (CIDb := CIDa1)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (WH.wp_write_head_sconf γs j γl γu γd γk pd pav pu bn γfs
              cov logstart dev n W L pidv dq A1 (K - 8)%nat eb C eb
              (log_mirror_at (n, map uint W)
               ∗ ∃ Dc : gmap Z (list (bv 8)), fs_receipt_any Dc)%I lks
              ltac:(pose proof (eo_Kwh K HK); lia) Hgeom Hj Hgl (conj HnW Hn30)
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlfz Hppid Hprocs Hdevi Hdgeom Hdlock Hncell HW HauthL Hhdr Hu1
                    [Hmirc]").
    (* THE COMMIT POINT's fupd (phase C2b/D1 stage 4).  The durable state
       jumps to the log's contents over the home map -- computable from the
       PRE-write image, so the fupd needs to know nothing about the disk --
       and the mirror half comes back at the header picture the write just
       laid down, which is what the install fupds below then read. *)
    { iIntros (bs' Hlen' Hhn' Hdec').
      iApply (fs_commit_permit cov logstart (0%nat, []) n (map uint W) bs'
                ltac:(exact Hlen') ltac:(exact Hdec')
                with "Hseam Hregc Hswlb Hmirc"). }
    iIntros (CIDb1 Hsb1 mf1 bs1) "%Hcs1 Hcg Hcnt Hextc Hextm Hpc Hppid
                                  Hncell HW HauthL Hhdr %Hhdrn1 %Hhdec1 Hu1 HQ1".
    (* the mirror half back (the receipt is dropped: nothing in this stage
       consumes a durability receipt -- sys_sync is phase D's) *)
    iDestruct "HQ1" as "[>Hmirc _]".
    assert (Hpc108 : ret_pc (A1 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0x108)).
    { rewrite HA1ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc108) in "Hpc".
    clear Hpc108.
    assert (Hf1regs : eo_regs m mf1).
    { rewrite /eo_regs. split.
      - rewrite (callee_saved_lookup Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact (proj1 HA1regs).
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite (callee_saved_lookup Hcs1 c Hcs).
        exact (proj2 HA1regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    (* ===== +0x108 c.li a0,0 ===== *)
    assert (Hli0 : add_vec (zero_reg : mword 64)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))
                   = (mword_of_int 0 : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iPoseProof (eoi_108 with "Htext") as "Hi108".
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.end_op + 0x108)) Ra0 (mword_of_int 0 : mword 6)
              (mword_of_int 0 : mword 64) mf1 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) Hli0
              with "Hcg Hpc Hi108").
    iIntros (CIDa2 Hsa2) "Hcg Hpc".
    pose (A2 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> mf1).
    assert (HA2a0 : A2 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
      by (rewrite /A2; apply upd_eq).
    assert (HA2regs : eo_regs m A2).
    { rewrite /eo_regs. split.
      - rewrite /A2 upd_ne; [exact (proj1 Hf1regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /A2 upd_ne; [| regne].
        exact (proj2 Hf1regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hpp10a : add_vec_int (mword_of_int (KernelSyms.end_op + 0x108) : mword 64) 2
                     = mword_of_int (KernelSyms.end_op + 0x10a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10a) in "Hpc".
    clear Hpp10a.
    (* ===== +0x10a jal ra,install_trans ===== *)
    iPoseProof (eoi_10a with "Htext") as "Hi10a".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0x10a)) Rra
              (mword_of_int 2096412 : mword 21) A2 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi10a").
    iIntros (CIDa3 Hsa3) "Hcg Hpc".
    pose (A3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0x10a) : mword 64) 4)]> A2).
    assert (Htgt10a : add_vec (mword_of_int (KernelSyms.end_op + 0x10a) : mword 64)
                        (sign_extend' 64 (mword_of_int 2096412 : mword 21))
                      = mword_of_int KernelSyms.install_trans)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt10a) in "Hpc".
    clear Htgt10a.
    assert (HA3a0 : A3 !!! Regidx Ra0 = (mword_of_int 0 : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2a0 | vm_compute; discriminate]).
    assert (HA3ra : A3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0x10a) : mword 64) 4)
      by (rewrite /A3; apply upd_eq).
    assert (HA3regs : eo_regs m A3).
    { rewrite /eo_regs. split.
      - rewrite /A3 upd_ne; [exact (proj1 HA2regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /A3 upd_ne; [| regne].
        exact (proj2 HA2regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    (* ---- the pool: two units for install's two in-flight buffers ---- *)
    assert (Hp2 : ((LOGBLOCKS - n) + 2)%nat = (2 + (LOGBLOCKS - n))%nat)
      by (unfold LOGBLOCKS in *; lia).
    iAssert (bslots bn ((LOGBLOCKS - n) + 2)%nat) with "[Hu1 Hpool]" as "Hpool".
    { rewrite Hp1 (bslots_op bn 1 ((LOGBLOCKS - n) + 1)).
      iSplitL "Hu1"; [iExact "Hu1"|iExact "Hpool"]. }
    iEval (rewrite Hp2 (bslots_op bn 2 (LOGBLOCKS - n))) in "Hpool".
    clear Hp2.
    iDestruct "Hpool" as "[Hu2 Hpool]".
    (* ---- the per-entry bundle install takes ---- *)
    iDestruct (eo_cov_split γfs cov W Hnd
                 ltac:(intros w Hw; exact (proj1 (Hwok w Hw))) with "Hcov")
      as "[Hdirty Hcovrest]".
    iDestruct (eo_entries_in γfs logstart W Lw n HnW with "Hdone Hdirty") as "Hent".
    (* ---- the new L, moved only at the HEADER's key ---- *)
    assert (HLw' : forall (i : nat) (w : mword 32), W !! i = Some w ->
             (<[log_hdr_bno logstart := bs1]> L) !! uint w = Some (Lw i)).
    { intros i w Hw. rewrite lookup_insert_ne.
      - exact (HLw i w Hw).
      - intro Heqk. destruct (Hwok w (eo_lookup_elem W i w Hw)) as [_ Hnl].
        apply Hnl. rewrite -Heqk. apply eo_hdr_in_region. }
    iDestruct (cpu_own_transport CIDb1 CIDa3 0 eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDb1 CIDa3 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDb1 CIDa3 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CIDa1) (CIDb := CIDa3)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (IT.wp_install_trans_sconf γs j γl γu γd γk pd pav pu bn γfs
              cov logstart dev false n W Lw (<[log_hdr_bno logstart := bs1]> L) D
              pidv dq A3 (K - 8)%nat eb C eb (log_mirror_at (n, map uint W)) lks
              ltac:(pose proof (eo_Kit K HK); lia) Hgeom Hj Hgl (or_introl eq_refl) HA3a0
              (conj HnW Hn30) Hnd Hwok HLw'
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlfz Hppid Hprocs Hdevi Hdgeom Hdlock Hncell HW HauthL HauthD Hent Hu2
                    [] [Hmirc]").
    (* THE INSTALL fupds, one per entry, out of one generator: each reads the
       committed header picture out of the mirror half and hands it straight
       back, because recovery re-installs a logged block from its slot no
       matter what the home write put there. *)
    { iModIntro. iIntros (i w bs') "%Hwi %Hlen'".
      iApply (fs_install_permit cov logstart n (map uint W) i (uint w) bs'
                ltac:(exact Hlen')
                ltac:(by apply NoDup_ListNoDup)
                ltac:(rewrite length_map; lia)
                ltac:(exact (eo_map_lookup W i w Hwi))
                ltac:(exact (proj2 (Hwok w (eo_lookup_elem W i w Hwi))))
                with "Hseam Hregc Hswlb"). }
    { iNext. iExact "Hmirc". }
    iIntros (CIDb2 Hsb2 mf2) "%Hcs2 Hcg Hcnt Hextc Hextm Hpc Hppid
                              Hncell HW HauthL HauthD Hent Hu2 >Hmirc".
    assert (Hpc10e : ret_pc (A3 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0x10e)).
    { rewrite HA3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc10e) in "Hpc".
    clear Hpc10e.
    assert (Hf2regs : eo_regs m mf2).
    { rewrite /eo_regs. split.
      - rewrite (callee_saved_lookup Hcs2 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact (proj1 HA3regs).
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite (callee_saved_lookup Hcs2 c Hcs).
        exact (proj2 HA3regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    (* ===== +0x10e auipc a5,0x1e ===== *)
    iPoseProof (eoi_10e with "Htext") as "Hi10e".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.end_op + 0x10e)) Ra5 (mword_of_int 30 : mword 20)
              mf2 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10e").
    iIntros (CIDa4 Hsa4) "Hcg Hpc".
    pose (A4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.end_op + 0x10e) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> mf2).
    assert (HA4a5 : A4 !!! Regidx Ra5
                    = add_vec (mword_of_int (KernelSyms.end_op + 0x10e) : mword 64)
                        (auipc_off (mword_of_int 30 : mword 20)))
      by (rewrite /A4; apply upd_eq).
    assert (HA4regs : eo_regs m A4).
    { rewrite /eo_regs. split.
      - rewrite /A4 upd_ne; [exact (proj1 Hf2regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /A4 upd_ne; [| regne].
        exact (proj2 Hf2regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hpp112 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x10e) : mword 64) 4
                     = mword_of_int (KernelSyms.end_op + 0x112))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp112) in "Hpc".
    clear Hpp112.
    (* ===== +0x112 sw zero,1516(a5) : log.lh.n := 0 ===== *)
    assert (Hlhna : add_vec (rget A4 Ra5) (sign_extend' 64 (mword_of_int 1522 : mword 12))
                    = lh_n_pa).
    { rgne. rewrite HA4a5. exact eo_reloc_lhn. }
    iEval (rewrite -Hlhna) in "Hncell".
    iPoseProof (eoi_112 with "Htext") as "Hi112".
    iApply (wp_sw_zero_s_sconf (mword_of_int (KernelSyms.end_op + 0x112)) Ra5
              (mword_of_int 1522 : mword 12) A4 (K - 8)%nat
              (mword_of_int (Z.of_nat n) : mword 32) eb
              with "Hcg Hpc Hi112 Hncell").
    iIntros (CIDa5 Hsa5) "Hcg Hpc Hncell".
    iEval (rewrite Hlhna) in "Hncell".
    iEval (rewrite eo_zero32) in "Hncell".
    assert (Hpp116 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x112) : mword 64) 4
                     = mword_of_int (KernelSyms.end_op + 0x116))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp116) in "Hpc".
    clear Hpp116.
    (* ===== +0x116 jal ra,write_head (the header is cleared) ===== *)
    iPoseProof (eoi_116 with "Htext") as "Hi116".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0x116)) Rra
              (mword_of_int 2096306 : mword 21) A4 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi116").
    iIntros (CIDa6 Hsa6) "Hcg Hpc".
    pose (A5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0x116) : mword 64) 4)]> A4).
    assert (Htgt116 : add_vec (mword_of_int (KernelSyms.end_op + 0x116) : mword 64)
                        (sign_extend' 64 (mword_of_int 2096306 : mword 21))
                      = mword_of_int KernelSyms.write_head)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt116) in "Hpc".
    clear Htgt116.
    assert (HA5ra : A5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0x116) : mword 64) 4)
      by (rewrite /A5; apply upd_eq).
    assert (HA5regs : eo_regs m A5).
    { rewrite /eo_regs. split.
      - rewrite /A5 upd_ne; [exact (proj1 HA4regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /A5 upd_ne; [| regne].
        exact (proj2 HA4regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    (* ---- one unit out of install's return for the second write_head ---- *)
    assert (Hp3 : (2 + length W)%nat = (1 + (1 + length W))%nat) by lia.
    iEval (rewrite Hp3 (bslots_op bn 1 (1 + length W))) in "Hu2".
    clear Hp3.
    iDestruct "Hu2" as "[Hu3 Hu2]".
    iDestruct (cpu_own_transport CIDb2 CIDa6 0 eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDb2 CIDa6 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDb2 CIDa6 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CIDa3) (CIDb := CIDa6)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    assert (Hshape0 : (0%nat = length (@nil (mword 32)) /\ (0 <= LOGBLOCKS)%nat))
      by (split; [reflexivity | unfold LOGBLOCKS; lia]).
    iApply (WH.wp_write_head_sconf γs j γl γu γd γk pd pav pu bn γfs
              cov logstart dev 0%nat [] (<[log_hdr_bno logstart := bs1]> L) pidv dq
              A5 (K - 8)%nat eb C eb log_mirror_clean lks
              ltac:(pose proof (eo_Kwh K HK); lia) Hgeom Hj Hgl Hshape0
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlfz Hppid Hprocs Hdevi Hdgeom Hdlock Hncell [] HauthL [Hhdr] Hu3
                    [Hmirc]").
    { by iApply big_sepL_nil. }
    { iExists bs1. iExact "Hhdr". }
    (* THE CLEAR's fupd: the on-disk log is emptied, so recovery becomes the
       plain home restriction and the mirror goes back to its clean picture --
       which is the form [log_batch] parks in the lock. *)
    { iIntros (bs' Hlen' Hhn' Hdec').
      iApply (fs_clear_permit cov logstart (n, map uint W) bs'
                ltac:(exact Hlen') ltac:(rewrite Hhn'; reflexivity)
                with "Hseam Hregc Hswlb Hmirc"). }
    iIntros (CIDb3 Hsb3 mf3 bs2) "%Hcs3 Hcg Hcnt Hextc Hextm Hpc Hppid
                                  Hncell _ HauthL Hhdr %Hhdrn2 %Hhdec2 Hu3 >Hmirc".
    assert (Hpc11a : ret_pc (A5 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0x11a)).
    { rewrite HA5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc11a) in "Hpc".
    clear Hpc11a.
    assert (Hf3regs : eo_regs m mf3).
    { rewrite /eo_regs. split.
      - rewrite (callee_saved_lookup Hcs3 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact (proj1 HA5regs).
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite (callee_saved_lookup Hcs3 c Hcs).
        exact (proj2 HA5regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    pose proof Hf3regs as (Hf3sp & Hf3thr).
    (* ===== +0x11a .. +0x11e : restore s3, s4, s5 ===== *)
    rewrite /eo_frameS.
    iDestruct "HframeS" as "(Hg24 & Hg16 & Hg8 & Hg0)".
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { unfold pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    assert (Hc5 : add_vec (mf3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite Hf3sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hc6 : add_vec (mf3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite Hf3sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hc7 : add_vec (mf3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite Hf3sp Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iPoseProof (eoi_11a with "Htext") as "Hi11a".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x11a)) (mword_of_int 3 : mword 6) Rs3
              mf3 (K - 8)%nat (m !!! Regidx Rs3 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi11a [Hg24]").
    { iEval (rewrite Hc5). iExact "Hg24". }
    iIntros (CIDa7 Hsa7) "Hcg Hpc Hg24".
    iEval (rewrite Hc5) in "Hg24".
    pose (B1 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> mf3).
    assert (HB1sp : B1 !!! Regidx csp_rs1 = (mf3 !!! Regidx csp_rs1 : mword 64))
      by (rewrite /B1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hpp11c : add_vec_int (mword_of_int (KernelSyms.end_op + 0x11a) : mword 64) 2
                     = mword_of_int (KernelSyms.end_op + 0x11c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp11c) in "Hpc".
    clear Hpp11c.
    iPoseProof (eoi_11c with "Htext") as "Hi11c".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x11c)) (mword_of_int 2 : mword 6) Rs4
              B1 (K - 8)%nat (m !!! Regidx Rs4 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi11c [Hg16]").
    { iEval (rewrite HB1sp Hc6). iExact "Hg16". }
    iIntros (CIDa8 Hsa8) "Hcg Hpc Hg16".
    iEval (rewrite HB1sp Hc6) in "Hg16".
    pose (B2 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> B1).
    assert (HB2sp : B2 !!! Regidx csp_rs1 = (mf3 !!! Regidx csp_rs1 : mword 64))
      by (rewrite /B2 upd_ne; [exact HB1sp | vm_compute; discriminate]).
    assert (Hpp11e : add_vec_int (mword_of_int (KernelSyms.end_op + 0x11c) : mword 64) 2
                     = mword_of_int (KernelSyms.end_op + 0x11e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp11e) in "Hpc".
    clear Hpp11e.
    iPoseProof (eoi_11e with "Htext") as "Hi11e".
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x11e)) (mword_of_int 1 : mword 6) Rs5
              B2 (K - 8)%nat (m !!! Regidx Rs5 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi11e [Hg8]").
    { iEval (rewrite HB2sp Hc7). iExact "Hg8". }
    iIntros (CIDa9 Hsa9) "Hcg Hpc Hg8".
    iEval (rewrite HB2sp Hc7) in "Hg8".
    pose (B3 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> B2).
    assert (HB3regsE : eo_regsE m B3).
    { rewrite /eo_regsE. split.
      - rewrite /B3 upd_ne; [| vm_compute; discriminate].
        rewrite /B2 upd_ne; [| vm_compute; discriminate].
        rewrite /B1 upd_ne; [| vm_compute; discriminate]. exact Hf3sp.
      - intros c Hcs N2 N8 N9 N18.
        destruct (decide (c = Rs3)) as [->|Nc3].
        { rewrite /B3 upd_ne; [| vm_compute; discriminate].
          rewrite /B2 upd_ne; [| vm_compute; discriminate].
          rewrite /B1 upd_eq. reflexivity. }
        destruct (decide (c = Rs4)) as [->|Nc4].
        { rewrite /B3 upd_ne; [| vm_compute; discriminate].
          rewrite /B2 upd_eq. reflexivity. }
        destruct (decide (c = Rs5)) as [->|Nc5].
        { rewrite /B3 upd_eq. reflexivity. }
        rewrite /B3 upd_ne; [| regne]. rewrite /B2 upd_ne; [| regne].
        rewrite /B1 upd_ne; [| regne].
        exact (Hf3thr c Hcs N2 N8 N9 N18 Nc3 Nc4 Nc5). }
    assert (Hpp120 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x11e) : mword 64) 2
                     = mword_of_int (KernelSyms.end_op + 0x120))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp120) in "Hpc".
    clear Hpp120.
    (* ---- the batch, re-formed at n = 0 ---- *)
    iDestruct (eo_entries_out γfs logstart W Lw n HnW with "Hent") as "[Hdone Hdirty]".
    iDestruct (eo_cov_join γfs cov W Hnd
                 ltac:(intros w Hw; exact (proj1 (Hwok w Hw))) with "Hdirty Hcovrest")
      as "Hcov".
    iDestruct (eo_cells_junk W n HnW with "HW") as "HWj".
    assert (Hsq : LOGBLOCKS = (n + (LOGBLOCKS - n))%nat) by (unfold LOGBLOCKS in *; lia).
    iAssert ([∗ list] i ∈ seq 0 LOGBLOCKS, ∃ junk : mword 32, lh_block i ↦₄ junk)%I
      with "[HWj Hjunk]" as "Hjunk".
    { iEval (rewrite {1}Hsq).
      iApply (eo_seq_join (fun i => ∃ junk : mword 32, lh_block i ↦₄ junk)%I
                n (LOGBLOCKS - n)%nat with "HWj Hjunk"). }
    iAssert ([∗ list] i ∈ seq 0 LOGBLOCKS,
               ∃ bs, fsblock γfs (log_slot_bno logstart i) bs)%I
      with "[Hdone Hrest]" as "Hlogr".
    { iEval (rewrite {1}Hsq).
      iApply (eo_seq_join (fun i => ∃ bs, fsblock γfs (log_slot_bno logstart i) bs)%I
                n (LOGBLOCKS - n)%nat with "Hdone Hrest"). }
    assert (Hp4 : ((LOGBLOCKS - 0) + 2)%nat = ((LOGBLOCKS - n) + (1 + (1 + length W)))%nat)
      by (unfold LOGBLOCKS in *; lia).
    iAssert (bslots bn ((LOGBLOCKS - 0) + 2)%nat) with "[Hpool Hu3 Hu2]" as "Hpool".
    { rewrite Hp4 (bslots_op bn (LOGBLOCKS - n) (1 + (1 + length W))).
      iSplitL "Hpool"; [iExact "Hpool"|].
      rewrite (bslots_op bn 1 (1 + length W)).
      iSplitL "Hu3"; [iExact "Hu3"|iExact "Hu2"]. }
    iAssert (log_batch bn γfs cov logstart 0 ∅)
      with "[Hncell HauthL HauthD Hcov Hhdr Hjunk Hlogr Hpool Hmirc]" as "Hbatch".
    { iApply (eo_open_to_batch bn γfs cov logstart
                (<[log_hdr_bno logstart := bs2]> (<[log_hdr_bno logstart := bs1]> L))
                (dirty_clear D (map uint W)) Lw with "Hmirc").
      rewrite /eo_open.
      iSplitL "Hncell"; [iExact "Hncell"|].
      iSplitR; [by iApply big_sepL_nil|].
      replace (LOGBLOCKS - 0)%nat with LOGBLOCKS by (unfold LOGBLOCKS; lia).
      iSplitL "Hjunk"; [iExact "Hjunk"|].
      iSplitL "HauthL"; [iExact "HauthL"|].
      iSplitL "HauthD"; [iExact "HauthD"|].
      iSplitL "Hcov"; [iExact "Hcov"|].
      iSplitL "Hhdr"; [iExists bs2; iExact "Hhdr"|].
      iSplitR; [done|].
      iSplitL "Hlogr"; [iExact "Hlogr"|]. iExact "Hpool". }
    (* ===== +0x120 c.j -> +0x42 ===== *)
    iPoseProof (eoi_120 with "Htext") as "Hi120".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.end_op + 0x120))
              (sign_extend' 21 (concat_vec (mword_of_int 1937 : mword 11) ('b"0")))
              B3 (K - 8)%nat eb ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi120").
    iIntros (CIDa10 Hsa10). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgt120 : add_vec (mword_of_int (KernelSyms.end_op + 0x120) : mword 64)
                        (sign_extend' 64 (sign_extend' 21
                           (concat_vec (mword_of_int 1937 : mword 11) ('b"0"))))
                      = mword_of_int (KernelSyms.end_op + 0x42))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt120) in "Hpc".
    clear Htgt120.
    iDestruct (cpu_own_transport CIDb3 CIDa10 0 eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDb3 CIDa10 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDb3 CIDa10 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CIDa6) (CIDb := CIDa10)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iDestruct (eo_frameS_J with "[Hg24 Hg16 Hg8 Hg0]") as "Hjunk2".
    { rewrite /eo_frameS. iSplitL "Hg24"; [iExact "Hg24"|].
      iSplitL "Hg16"; [iExact "Hg16"|].
      iSplitL "Hg8"; [iExact "Hg8"|]. iExact "Hg0". }
    iApply (eo_tail (CID0 := CIDa10)  γs j γl bn γ γfs cov logstart dev pidv dq
              m B3 K eb C lks HK HB3regsE Hbelow
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hlctx Hprocs Hppid
                    Hframe Hjunk2 Hbatch Hcont").
  Qed.


  (* ================================================================== *)
  (*  +0xb4 .. +0x100 : the inlined write_log copy loop.                 *)
  (*    top   +0xb4  (entered by falling through from the +0xb0 set-up)  *)
  (*    body  bread(log slot), bread(home), memmove home -> slot,        *)
  (*          bwrite(slot), brelse(home), brelse(slot)                   *)
  (*    bump  +0xf8 s2++ ; +0xfa s5 += 4                                 *)
  (*    back  +0x100 blt s2,a5 -> +0xb4                                  *)
  (*    exit  +0x104 (fall-through, into [eo_commit])                    *)
  (*  The ghost step per iteration moves the LOG SLOT's logged content to *)
  (*  the home block's bytes; the home block itself rides through        *)
  (*  untouched, and its bytes are read off the AUTHORITY.               *)
  (* ================================================================== *)
  Local Lemma eo_loop `{GEN : GenId} 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (n : nat) (W : list (mword 32)) (D : gmap Z bool)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (lks : gset nat) (fuel : nat) :
    (K_end_op <= K)%nat ->
    log_geom_ok cov logstart ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (n = length W /\ (n <= LOGBLOCKS)%nat) ->
    NoDup (map uint W) ->
    (forall w, w ∈ W -> uint w ∈ cov /\ ~ (uint w ∈ log_region_set logstart)) ->
    (* threaded through the whole fuel induction unchanged (no acquire in
       this loop's own body) to [eo_commit] -> [eo_tail]'s re-acquire. *)
    locks_below lks (lock_rank "log") ->
    forall (CID0 : CpuId) (t : nat) (M : regfile) (L : gmap Z (list (bv 8)))
           (Lw : nat -> list (bv 8)),
    (t < n)%nat ->
    (n - t <= fuel)%nat ->
    (forall (i : nat) (w : mword 32), (i < t)%nat -> W !! i = Some w ->
       L !! uint w = Some (Lw i)) ->
    eo_regs m M ->
    M !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64) ->
    M !!! Regidx Rs4 = log_addr ->
    M !!! Regidx Rs5 = (lh_block t : mword 64) ->
    sie_cap_gpr M (K - 8)%nat eb (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) C eb lks -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.end_op + 0xb4) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_ctx γ bn γfs cov logstart dev -∗
    (* the crash seam and the era certificate: what turns this block's
       [bwrite]s into REAL durability fupds (FsCrash's four permits) *)
    fs_crash_seam cov logstart -∗
    era_registered gen_id riscv_eraGS -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    eo_frame4 m -∗
    eo_frameS m -∗
    log_mirror_clean -∗
    eo_open bn γfs cov logstart n W L D Lw t -∗
    eo_cont (CID0 := CID0)  j pidv dq m K eb C eb lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hj Hgl Hshape Hnd Hwok Hbelow.
    destruct Hshape as [HnW Hn30].
    destruct Hgeom as [Hcovok Hlogsub].
    induction fuel as [|fuel IH];
      intros CID0 t M L Lw Ht Hfuel HLw Hregs HMs2 HMs4 HMs5;
      [ exfalso; exact (eo_fuel_absurd t n Ht Hfuel) |].
    pose proof Hregs as (Hsp & Hthr).
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlctx #Hseam #Hregc Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hframe HframeS Hmirc
              Hopen Hcont".
    iPoseProof (log_ctx_swap with "Hlctx") as "#Hswlb".
    iPoseProof (log_ctx_frozen with "Hlctx") as "#Hlfz".
    iDestruct "Hlfz" as "[#Hdevc #Hstc]".
    rewrite /eo_open.
    iDestruct "Hopen" as
      "(Hncell & HW & Hjunk & HauthL & HauthD & Hcov & Hhdr & Hdone & Hrest & Hpool)".
    (* ---- the entry at the cursor, and every bound the two breads need ---- *)
    destruct (lookup_lt_is_Some_2 W t (eo_lt_len t n W Ht HnW)) as [w Hw].
    pose proof (Hwok w (eo_lookup_elem W t w Hw)) as [Hwcov Hwnlog].
    pose proof (Hcovok (uint w) Hwcov) as Hwrange.
    assert (Hslotcov : log_slot_bno logstart t ∈ cov)
      by (apply Hlogsub; apply eo_slot_in_region; exact (eo_t_lt_lb t n Ht Hn30)).
    pose proof (Hcovok _ Hslotcov) as Hslotrange.
    assert (Hhdrcov : log_hdr_bno logstart ∈ cov)
      by (apply Hlogsub; apply eo_hdr_in_region).
    pose proof (Hcovok _ Hhdrcov) as Hlsrange0.
    rewrite /log_hdr_bno in Hlsrange0.
    pose proof (eo_arith logstart t Hlsrange0 Hslotrange)
      as (Har1 & Har2 & Har3 & Har4 & Har5 & Har6 & Har7 & Har8).
    set (bnol := (mword_of_int (log_slot_bno logstart t) : mword 32)).
    assert (Hubnol : uint bnol = log_slot_bno logstart t)
      by (rewrite /bnol; apply eo_uint_moi32; exact Har7).
    (* ---- the instruction facts ---- *)
    iPoseProof (eoi_100 with "Htext") as "Hi100".
    (* ---- the batch pieces this iteration touches ---- *)
    iDestruct (big_sepL_lookup_acc _ W t w Hw with "HW") as "[Hblk Hblkback]".
    assert (Hsq2 : seq t (LOGBLOCKS - t) = t :: seq (S t) (LOGBLOCKS - S t)).
    { assert (Hsq : (LOGBLOCKS - t)%nat = S (LOGBLOCKS - S t)%nat)
        by (unfold LOGBLOCKS in *; lia).
      rewrite Hsq. reflexivity. }
    iEval (rewrite Hsq2) in "Hrest".
    clear Hsq2.
    iDestruct "Hrest" as "[Hslotfb Hrest]".
    iDestruct "Hslotfb" as (bsold) "Hslotfb".
    iEval (rewrite -Hubnol) in "Hslotfb".
    (* the two slot units the two breads spend *)
    assert (Hp1 : ((LOGBLOCKS - n) + 2)%nat = (1 + (1 + (LOGBLOCKS - n)))%nat)
      by (unfold LOGBLOCKS in *; lia).
    iEval (rewrite Hp1 (bslots_op bn 1 (1 + (LOGBLOCKS - n)))) in "Hpool".
    iDestruct "Hpool" as "[Hu1 Hpool]".
    iEval (rewrite (bslots_op bn 1 (LOGBLOCKS - n))) in "Hpool".
    iDestruct "Hpool" as "[Hu2 Hpool]".
    (* ===== +0xb4 lw a1,24(s4) : a1 := log.start ===== *)
    assert (Hastart : add_vec (rget M Rs4) (sign_extend' 64 (mword_of_int 24 : mword 12))
                      = l_start).
    { rgne. rewrite HMs4. exact eo_addr_start. }
    iEval (rewrite -Hastart) in "Hstc".
    iPoseProof (eoi_b4 with "Htext") as "Hib4".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.end_op + 0xb4)) Ra1 Rs4
              (mword_of_int 24 : mword 12) M (K - 8)%nat
              (mword_of_int logstart : mword 32) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib4 Hstc").
    iIntros (CIDa1 Hsa1) "Hcg Hpc _".
    iEval (rewrite Hastart) in "Hstc".
    pose (A1 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (mword_of_int logstart : mword 32))]> M).
    assert (HA1a1 : A1 !!! Regidx Ra1 = (mword_of_int logstart : mword 64))
      by (rewrite /A1 upd_eq; apply eo_sext32; exact Har1).
    assert (HA1s2 : A1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /A1 upd_ne; [exact HMs2 | vm_compute; discriminate]).
    assert (HA1s4 : A1 !!! Regidx Rs4 = log_addr)
      by (rewrite /A1 upd_ne; [exact HMs4 | vm_compute; discriminate]).
    assert (HA1s5 : A1 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /A1 upd_ne; [exact HMs5 | vm_compute; discriminate]).
    assert (Hppb8 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xb4) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0xb8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppb8) in "Hpc".
    clear Hppb8.
    (* ===== +0xb8 addw a1,a1,s2 ===== *)
    assert (Hwvb8 : sign_extend' 64
                      (add_vec (subrange_vec_dec (rget A1 Ra1) 31 0 : mword 32)
                               (subrange_vec_dec (rget A1 Rs2) 31 0 : mword 32))
                    = (mword_of_int (logstart + Z.of_nat t) : mword 64)).
    { rgne. rgne. rewrite HA1a1 HA1s2.
      apply eo_addw; [lia | lia | exact Har3]. }
    iPoseProof (eoi_b8 with "Htext") as "Hib8".
    iApply (wp_addw4_s_sconf (mword_of_int (KernelSyms.end_op + 0xb8)) Ra1 Ra1 Rs2
              A1 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib8").
    iIntros (CIDa2 Hsa2) "Hcg Hpc".
    iEval (rewrite Hwvb8) in "Hcg".
    clear Hwvb8.
    pose (A2 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int (logstart + Z.of_nat t) : mword 64)]> A1).
    assert (HA2a1 : A2 !!! Regidx Ra1 = (mword_of_int (logstart + Z.of_nat t) : mword 64))
      by (rewrite /A2; apply upd_eq).
    assert (HA2s2 : A2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /A2 upd_ne; [exact HA1s2 | vm_compute; discriminate]).
    assert (HA2s4 : A2 !!! Regidx Rs4 = log_addr)
      by (rewrite /A2 upd_ne; [exact HA1s4 | vm_compute; discriminate]).
    assert (HA2s5 : A2 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /A2 upd_ne; [exact HA1s5 | vm_compute; discriminate]).
    assert (Hppbc : add_vec_int (mword_of_int (KernelSyms.end_op + 0xb8) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0xbc))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppbc) in "Hpc".
    clear Hppbc.
    (* ===== +0xbc c.addiw a1,a1,1 : a1 := the log slot's block number ===== *)
    assert (Hwvbc : sign_extend' 64 (subrange_vec_dec
                      (add_vec (rget A2 Ra1)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
                    = (mword_of_int (logstart + Z.of_nat t + 1) : mword 64)).
    { rgne. rewrite HA2a1. apply eo_addiw1; [lia | exact Har5]. }
    iPoseProof (eoi_bc with "Htext") as "Hibc".
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.end_op + 0xbc)) Ra1 (mword_of_int 1 : mword 6)
              A2 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hibc").
    iIntros (CIDa3 Hsa3) "Hcg Hpc".
    iEval (rewrite Hwvbc) in "Hcg".
    clear Hwvbc.
    pose (A3 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int (logstart + Z.of_nat t + 1) : mword 64)]> A2).
    assert (HA3a1 : A3 !!! Regidx Ra1 = sign_extend' 64 bnol).
    { rewrite /A3 upd_eq /bnol (eo_sext32 (log_slot_bno logstart t) Har8).
      rewrite -Har6. reflexivity. }
    assert (HA3s2 : A3 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2s2 | vm_compute; discriminate]).
    assert (HA3s4 : A3 !!! Regidx Rs4 = log_addr)
      by (rewrite /A3 upd_ne; [exact HA2s4 | vm_compute; discriminate]).
    assert (HA3s5 : A3 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2s5 | vm_compute; discriminate]).
    assert (Hppbe : add_vec_int (mword_of_int (KernelSyms.end_op + 0xbc) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0xbe))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppbe) in "Hpc".
    clear Hppbe.
    (* ===== +0xbe lw a0,36(s4) : a0 := log.dev ===== *)
    assert (Hadev : add_vec (rget A3 Rs4) (sign_extend' 64 (mword_of_int 36 : mword 12))
                    = l_dev).
    { rgne. rewrite HA3s4. exact eo_addr_dev. }
    iEval (rewrite -Hadev) in "Hdevc".
    iPoseProof (eoi_be with "Htext") as "Hibe".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.end_op + 0xbe)) Ra0 Rs4
              (mword_of_int 36 : mword 12) A3 (K - 8)%nat dev eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hibe Hdevc").
    iIntros (CIDa4 Hsa4) "Hcg Hpc _".
    iEval (rewrite Hadev) in "Hdevc".
    pose (A4 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> A3).
    assert (HA4a0 : A4 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /A4; apply upd_eq).
    assert (HA4a1 : A4 !!! Regidx Ra1 = sign_extend' 64 bnol)
      by (rewrite /A4 upd_ne; [exact HA3a1 | vm_compute; discriminate]).
    assert (HA4s2 : A4 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /A4 upd_ne; [exact HA3s2 | vm_compute; discriminate]).
    assert (HA4s4 : A4 !!! Regidx Rs4 = log_addr)
      by (rewrite /A4 upd_ne; [exact HA3s4 | vm_compute; discriminate]).
    assert (HA4s5 : A4 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /A4 upd_ne; [exact HA3s5 | vm_compute; discriminate]).
    assert (Hppc2 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xbe) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0xc2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc2) in "Hpc".
    clear Hppc2.
    (* ===== +0xc2 jal ra,bread : "to" = the log slot ===== *)
    iPoseProof (eoi_c2 with "Htext") as "Hic2".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0xc2)) Rra
              (mword_of_int 2092536 : mword 21) A4 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hic2").
    iIntros (CIDa5 Hsa5) "Hcg Hpc".
    pose (A5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0xc2) : mword 64) 4)]> A4).
    assert (Htgtc2 : add_vec (mword_of_int (KernelSyms.end_op + 0xc2) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092536 : mword 21))
                     = mword_of_int KernelSyms.bread)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtc2) in "Hpc".
    clear Htgtc2.
    assert (HA5a0 : A5 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /A5 upd_ne; [exact HA4a0 | vm_compute; discriminate]).
    assert (HA5a1 : A5 !!! Regidx Ra1 = sign_extend' 64 bnol)
      by (rewrite /A5 upd_ne; [exact HA4a1 | vm_compute; discriminate]).
    assert (HA5s2 : A5 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4s2 | vm_compute; discriminate]).
    assert (HA5s4 : A5 !!! Regidx Rs4 = log_addr)
      by (rewrite /A5 upd_ne; [exact HA4s4 | vm_compute; discriminate]).
    assert (HA5s5 : A5 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4s5 | vm_compute; discriminate]).
    assert (HA5ra : A5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0xc2) : mword 64) 4)
      by (rewrite /A5; apply upd_eq).
    assert (HA5regs : eo_regs m A5).
    { rewrite /eo_regs. split.
      - rewrite /A5 upd_ne; [| vm_compute; discriminate].
        rewrite /A4 upd_ne; [| vm_compute; discriminate].
        rewrite /A3 upd_ne; [| vm_compute; discriminate].
        rewrite /A2 upd_ne; [| vm_compute; discriminate].
        rewrite /A1 upd_ne; [exact Hsp | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /A5 upd_ne; [| regne]. rewrite /A4 upd_ne; [| regne].
        rewrite /A3 upd_ne; [| regne]. rewrite /A2 upd_ne; [| regne].
        rewrite /A1 upd_ne; [| regne]. exact (Hthr c Hcs N2 N8 N9 N18 N19 N20 N21). }
    iDestruct (cpu_own_transport CID0 CIDa5 0 eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDa5 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDa5 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CID0) (CIDb := CIDa5)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev bnol dq A5 (K - 8)%nat eb C eb lks
              ltac:(pose proof (eo_Kbread K HK); lia)
              ltac:(rewrite Hubnol; exact (eo_lt_lit _ Hslotrange))
              ltac:(reflexivity) ltac:(rewrite Hubnol; exact Hslotcov) ltac:(reflexivity)
              Hj Hgl HA5a0 HA5a1
              (locks_below_mono lks (lock_rank "log") (lock_rank "bcache") Hbelow ltac:(vm_compute; lia))
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hu1").
    iIntros (CIDb1 Hsb1 mf1 k1 bs1 bsd1 d1) "%Hpair1 Hcg Hcnt Hextc Hextm Hpc Hppid Hlk1".
    destruct Hpair1 as [Hcs1 Hmf1a0].
    assert (Hpcc6 : ret_pc (A5 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0xc6)).
    { rewrite HA5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcc6) in "Hpc".
    clear Hpcc6.
    assert (Hf1s2 : mf1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite (callee_saved_lookup Hcs1 Rs2 ltac:(vm_compute; reflexivity)); exact HA5s2).
    assert (Hf1s4 : mf1 !!! Regidx Rs4 = log_addr)
      by (rewrite (callee_saved_lookup Hcs1 Rs4 ltac:(vm_compute; reflexivity)); exact HA5s4).
    assert (Hf1s5 : mf1 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite (callee_saved_lookup Hcs1 Rs5 ltac:(vm_compute; reflexivity)); exact HA5s5).
    assert (Hf1regs : eo_regs m mf1).
    { rewrite /eo_regs. split.
      - rewrite (callee_saved_lookup Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact (proj1 HA5regs).
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite (callee_saved_lookup Hcs1 c Hcs).
        exact (proj2 HA5regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    iEval (rewrite /bio_locked /bio_held) in "Hlk1".
    iDestruct "Hlk1" as
      "(%Hk1 & %Hcv1 & %Hdv1 & Hslk1 & Hspid1 & Hvld1 & Hbdev1 & Hbuf1 & Hdsk1 & Hpay1)".
    (* ===== +0xc6 c.mv s1,a0 : s1 := the log-slot buffer ===== *)
    iPoseProof (eoi_c6 with "Htext") as "Hic6".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.end_op + 0xc6)) Rs1 Ra0
              mf1 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hic6").
    iIntros (CIDa6 Hsa6) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    pose (B1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mf1 !!! Regidx Ra0))]> mf1).
    assert (HB1s1 : B1 !!! Regidx Rs1 = bnode k1).
    { rewrite /B1 upd_eq add_vec_zero_l. exact Hmf1a0. }
    assert (HB1s2 : B1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /B1 upd_ne; [exact Hf1s2 | vm_compute; discriminate]).
    assert (HB1s4 : B1 !!! Regidx Rs4 = log_addr)
      by (rewrite /B1 upd_ne; [exact Hf1s4 | vm_compute; discriminate]).
    assert (HB1s5 : B1 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /B1 upd_ne; [exact Hf1s5 | vm_compute; discriminate]).
    assert (HB1regs : eo_regs m B1).
    { rewrite /eo_regs. split.
      - rewrite /B1 upd_ne; [exact (proj1 Hf1regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /B1 upd_ne; [| regne].
        exact (proj2 Hf1regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppc8 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xc6) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0xc8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc8) in "Hpc".
    clear Hppc8.
    (* ===== +0xc8 lw a1,0(s5) : a1 := log.lh.block[tail] ===== *)
    assert (Hacur : add_vec (rget B1 Rs5) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = lh_block t).
    { rgne. rewrite HB1s5. exact (eo_cursor_at t). }
    iEval (rewrite -Hacur) in "Hblk".
    iPoseProof (eoi_c8 with "Htext") as "Hic8".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.end_op + 0xc8)) Ra1 Rs5
              (mword_of_int 0 : mword 12) B1 (K - 8)%nat w eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hic8 Hblk").
    iIntros (CIDa7 Hsa7) "Hcg Hpc Hblk".
    iEval (rewrite Hacur) in "Hblk".
    pose (B2 := <[Regidx Ra1 := regval_into_reg (sign_extend' 64 w)]> B1).
    assert (HB2a1 : B2 !!! Regidx Ra1 = sign_extend' 64 w)
      by (rewrite /B2; apply upd_eq).
    assert (HB2s1 : B2 !!! Regidx Rs1 = bnode k1)
      by (rewrite /B2 upd_ne; [exact HB1s1 | vm_compute; discriminate]).
    assert (HB2s2 : B2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /B2 upd_ne; [exact HB1s2 | vm_compute; discriminate]).
    assert (HB2s4 : B2 !!! Regidx Rs4 = log_addr)
      by (rewrite /B2 upd_ne; [exact HB1s4 | vm_compute; discriminate]).
    assert (HB2s5 : B2 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /B2 upd_ne; [exact HB1s5 | vm_compute; discriminate]).
    assert (HB2regs : eo_regs m B2).
    { rewrite /eo_regs. split.
      - rewrite /B2 upd_ne; [exact (proj1 HB1regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /B2 upd_ne; [| regne].
        exact (proj2 HB1regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppcc : add_vec_int (mword_of_int (KernelSyms.end_op + 0xc8) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0xcc))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppcc) in "Hpc".
    clear Hppcc.
    (* ===== +0xcc lw a0,36(s4) : a0 := log.dev ===== *)
    assert (Hadev2 : add_vec (rget B2 Rs4) (sign_extend' 64 (mword_of_int 36 : mword 12))
                     = l_dev).
    { rgne. rewrite HB2s4. exact eo_addr_dev. }
    iEval (rewrite -Hadev2) in "Hdevc".
    iPoseProof (eoi_cc with "Htext") as "Hicc".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.end_op + 0xcc)) Ra0 Rs4
              (mword_of_int 36 : mword 12) B2 (K - 8)%nat dev eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hicc Hdevc").
    iIntros (CIDa8 Hsa8) "Hcg Hpc _".
    iEval (rewrite Hadev2) in "Hdevc".
    pose (B3 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> B2).
    assert (HB3a0 : B3 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /B3; apply upd_eq).
    assert (HB3a1 : B3 !!! Regidx Ra1 = sign_extend' 64 w)
      by (rewrite /B3 upd_ne; [exact HB2a1 | vm_compute; discriminate]).
    assert (HB3s1 : B3 !!! Regidx Rs1 = bnode k1)
      by (rewrite /B3 upd_ne; [exact HB2s1 | vm_compute; discriminate]).
    assert (HB3s2 : B3 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2s2 | vm_compute; discriminate]).
    assert (HB3s4 : B3 !!! Regidx Rs4 = log_addr)
      by (rewrite /B3 upd_ne; [exact HB2s4 | vm_compute; discriminate]).
    assert (HB3s5 : B3 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2s5 | vm_compute; discriminate]).
    assert (HB3regs : eo_regs m B3).
    { rewrite /eo_regs. split.
      - rewrite /B3 upd_ne; [exact (proj1 HB2regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /B3 upd_ne; [| regne].
        exact (proj2 HB2regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppd0 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xcc) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0xd0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppd0) in "Hpc".
    clear Hppd0.
    (* ===== +0xd0 jal ra,bread : "from" = the home block ===== *)
    iPoseProof (eoi_d0 with "Htext") as "Hid0".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0xd0)) Rra
              (mword_of_int 2092522 : mword 21) B3 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hid0").
    iIntros (CIDa9 Hsa9) "Hcg Hpc".
    pose (B4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0xd0) : mword 64) 4)]> B3).
    assert (Htgtd0 : add_vec (mword_of_int (KernelSyms.end_op + 0xd0) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092522 : mword 21))
                     = mword_of_int KernelSyms.bread)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtd0) in "Hpc".
    clear Htgtd0.
    assert (HB4a0 : B4 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /B4 upd_ne; [exact HB3a0 | vm_compute; discriminate]).
    assert (HB4a1 : B4 !!! Regidx Ra1 = sign_extend' 64 w)
      by (rewrite /B4 upd_ne; [exact HB3a1 | vm_compute; discriminate]).
    assert (HB4s1 : B4 !!! Regidx Rs1 = bnode k1)
      by (rewrite /B4 upd_ne; [exact HB3s1 | vm_compute; discriminate]).
    assert (HB4s2 : B4 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /B4 upd_ne; [exact HB3s2 | vm_compute; discriminate]).
    assert (HB4s4 : B4 !!! Regidx Rs4 = log_addr)
      by (rewrite /B4 upd_ne; [exact HB3s4 | vm_compute; discriminate]).
    assert (HB4s5 : B4 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /B4 upd_ne; [exact HB3s5 | vm_compute; discriminate]).
    assert (HB4ra : B4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0xd0) : mword 64) 4)
      by (rewrite /B4; apply upd_eq).
    assert (HB4regs : eo_regs m B4).
    { rewrite /eo_regs. split.
      - rewrite /B4 upd_ne; [exact (proj1 HB3regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /B4 upd_ne; [| regne].
        exact (proj2 HB3regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    iDestruct (cpu_own_transport CIDb1 CIDa9 0 eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDb1 CIDa9 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDb1 CIDa9 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CIDa5) (CIDb := CIDa9)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (BR.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev w dq B4 (K - 8)%nat eb C eb lks
              ltac:(pose proof (eo_Kbread K HK); lia)
              ltac:(exact (eo_lt_lit _ Hwrange))
              ltac:(reflexivity) ltac:(exact Hwcov) ltac:(reflexivity)
              Hj Hgl HB4a0 HB4a1
              (locks_below_mono lks (lock_rank "log") (lock_rank "bcache") Hbelow ltac:(vm_compute; lia))
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hu2").
    iIntros (CIDb2 Hsb2 mf2 k2 bs2 bsd2 d2) "%Hpair2 Hcg Hcnt Hextc Hextm Hpc Hppid Hlk2".
    destruct Hpair2 as [Hcs2 Hmf2a0].
    assert (Hpcd4 : ret_pc (B4 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0xd4)).
    { rewrite HB4ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcd4) in "Hpc".
    clear Hpcd4.
    assert (Hf2s1 : mf2 !!! Regidx Rs1 = bnode k1)
      by (rewrite (callee_saved_lookup Hcs2 Rs1 ltac:(vm_compute; reflexivity)); exact HB4s1).
    assert (Hf2s2 : mf2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite (callee_saved_lookup Hcs2 Rs2 ltac:(vm_compute; reflexivity)); exact HB4s2).
    assert (Hf2s4 : mf2 !!! Regidx Rs4 = log_addr)
      by (rewrite (callee_saved_lookup Hcs2 Rs4 ltac:(vm_compute; reflexivity)); exact HB4s4).
    assert (Hf2s5 : mf2 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite (callee_saved_lookup Hcs2 Rs5 ltac:(vm_compute; reflexivity)); exact HB4s5).
    assert (Hf2regs : eo_regs m mf2).
    { rewrite /eo_regs. split.
      - rewrite (callee_saved_lookup Hcs2 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact (proj1 HB4regs).
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite (callee_saved_lookup Hcs2 c Hcs).
        exact (proj2 HB4regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    iEval (rewrite /bio_locked /bio_held) in "Hlk2".
    iDestruct "Hlk2" as
      "(%Hk2 & %Hcv2 & %Hdv2 & Hslk2 & Hspid2 & Hvld2 & Hbdev2 & Hbuf2 & Hdsk2 & Hpay2)".
    (* THE HOME BLOCK'S BYTES, off the checked-out AUTHORITY *)
    iDestruct (eo_pay_bs_auth with "HauthL Hpay2") as %Hlkhome.
    (* ===== +0xd4 c.mv s3,a0 : s3 := the home buffer ===== *)
    iPoseProof (eoi_d4 with "Htext") as "Hid4".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.end_op + 0xd4)) Rs3 Ra0
              mf2 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hid4").
    iIntros (CIDa10 Hsa10) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    pose (G1 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mf2 !!! Regidx Ra0))]> mf2).
    assert (HG1s3 : G1 !!! Regidx Rs3 = bnode k2).
    { rewrite /G1 upd_eq add_vec_zero_l. exact Hmf2a0. }
    assert (HG1a0 : G1 !!! Regidx Ra0 = bnode k2)
      by (rewrite /G1 upd_ne; [exact Hmf2a0 | vm_compute; discriminate]).
    assert (HG1s1 : G1 !!! Regidx Rs1 = bnode k1)
      by (rewrite /G1 upd_ne; [exact Hf2s1 | vm_compute; discriminate]).
    assert (HG1s2 : G1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /G1 upd_ne; [exact Hf2s2 | vm_compute; discriminate]).
    assert (HG1s4 : G1 !!! Regidx Rs4 = log_addr)
      by (rewrite /G1 upd_ne; [exact Hf2s4 | vm_compute; discriminate]).
    assert (HG1s5 : G1 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /G1 upd_ne; [exact Hf2s5 | vm_compute; discriminate]).
    assert (HG1regs : eo_regs m G1).
    { rewrite /eo_regs. split.
      - rewrite /G1 upd_ne; [exact (proj1 Hf2regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /G1 upd_ne; [| regne].
        exact (proj2 Hf2regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppd6 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xd4) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0xd6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppd6) in "Hpc".
    clear Hppd6.
    (* ===== +0xd6 li a2,1024 ===== *)
    iPoseProof (eoi_d6 with "Htext") as "Hid6".
    iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.end_op + 0xd6)) Ra2 (mword_of_int 1024 : mword 12)
              (mword_of_int (Z.of_nat 1024%nat) : mword 64) G1 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) eo_li1024
              with "Hcg Hpc Hid6").
    iIntros (CIDa11 Hsa11) "Hcg Hpc".
    pose (G2 := <[Regidx Ra2 := regval_into_reg
                  (mword_of_int (Z.of_nat 1024%nat) : mword 64)]> G1).
    assert (HG2a2 : G2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 1024%nat) : mword 64))
      by (rewrite /G2; apply upd_eq).
    assert (HG2a0 : G2 !!! Regidx Ra0 = bnode k2)
      by (rewrite /G2 upd_ne; [exact HG1a0 | vm_compute; discriminate]).
    assert (HG2s1 : G2 !!! Regidx Rs1 = bnode k1)
      by (rewrite /G2 upd_ne; [exact HG1s1 | vm_compute; discriminate]).
    assert (HG2s3 : G2 !!! Regidx Rs3 = bnode k2)
      by (rewrite /G2 upd_ne; [exact HG1s3 | vm_compute; discriminate]).
    assert (HG2s2 : G2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /G2 upd_ne; [exact HG1s2 | vm_compute; discriminate]).
    assert (HG2s4 : G2 !!! Regidx Rs4 = log_addr)
      by (rewrite /G2 upd_ne; [exact HG1s4 | vm_compute; discriminate]).
    assert (HG2s5 : G2 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /G2 upd_ne; [exact HG1s5 | vm_compute; discriminate]).
    assert (HG2regs : eo_regs m G2).
    { rewrite /eo_regs. split.
      - rewrite /G2 upd_ne; [exact (proj1 HG1regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /G2 upd_ne; [| regne].
        exact (proj2 HG1regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppda : add_vec_int (mword_of_int (KernelSyms.end_op + 0xd6) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0xda))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppda) in "Hpc".
    clear Hppda.
    (* ===== +0xda addi a1,a0,88 : a1 := from->data ===== *)
    iPoseProof (eoi_da with "Htext") as "Hida".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.end_op + 0xda)) Ra1 Ra0
              (mword_of_int 88 : mword 12) G2 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hida").
    iIntros (CIDa12 Hsa12) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    pose (G3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (G2 !!! Regidx Ra0 : mword 64)
                     (sign_extend' 64 (mword_of_int 88 : mword 12)))]> G2).
    assert (HG3a1 : G3 !!! Regidx Ra1 = b_data (bpa k2)).
    { rewrite /G3 upd_eq HG2a0. rewrite /bpa. exact (eo_data_off (bnode k2)). }
    assert (HG3a2 : G3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 1024%nat) : mword 64))
      by (rewrite /G3 upd_ne; [exact HG2a2 | vm_compute; discriminate]).
    assert (HG3s1 : G3 !!! Regidx Rs1 = bnode k1)
      by (rewrite /G3 upd_ne; [exact HG2s1 | vm_compute; discriminate]).
    assert (HG3s3 : G3 !!! Regidx Rs3 = bnode k2)
      by (rewrite /G3 upd_ne; [exact HG2s3 | vm_compute; discriminate]).
    assert (HG3s2 : G3 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /G3 upd_ne; [exact HG2s2 | vm_compute; discriminate]).
    assert (HG3s4 : G3 !!! Regidx Rs4 = log_addr)
      by (rewrite /G3 upd_ne; [exact HG2s4 | vm_compute; discriminate]).
    assert (HG3s5 : G3 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /G3 upd_ne; [exact HG2s5 | vm_compute; discriminate]).
    assert (HG3regs : eo_regs m G3).
    { rewrite /eo_regs. split.
      - rewrite /G3 upd_ne; [exact (proj1 HG2regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /G3 upd_ne; [| regne].
        exact (proj2 HG2regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppde : add_vec_int (mword_of_int (KernelSyms.end_op + 0xda) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0xde))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppde) in "Hpc".
    clear Hppde.
    (* ===== +0xde addi a0,s1,88 : a0 := to->data ===== *)
    iPoseProof (eoi_de with "Htext") as "Hide".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.end_op + 0xde)) Ra0 Rs1
              (mword_of_int 88 : mword 12) G3 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hide").
    iIntros (CIDa13 Hsa13) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    pose (G4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (G3 !!! Regidx Rs1 : mword 64)
                     (sign_extend' 64 (mword_of_int 88 : mword 12)))]> G3).
    assert (HG4a0 : G4 !!! Regidx Ra0 = b_data (bpa k1)).
    { rewrite /G4 upd_eq HG3s1. rewrite /bpa. exact (eo_data_off (bnode k1)). }
    assert (HG4a1 : G4 !!! Regidx Ra1 = b_data (bpa k2))
      by (rewrite /G4 upd_ne; [exact HG3a1 | vm_compute; discriminate]).
    assert (HG4a2 : G4 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 1024%nat) : mword 64))
      by (rewrite /G4 upd_ne; [exact HG3a2 | vm_compute; discriminate]).
    assert (HG4s1 : G4 !!! Regidx Rs1 = bnode k1)
      by (rewrite /G4 upd_ne; [exact HG3s1 | vm_compute; discriminate]).
    assert (HG4s3 : G4 !!! Regidx Rs3 = bnode k2)
      by (rewrite /G4 upd_ne; [exact HG3s3 | vm_compute; discriminate]).
    assert (HG4s2 : G4 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /G4 upd_ne; [exact HG3s2 | vm_compute; discriminate]).
    assert (HG4s4 : G4 !!! Regidx Rs4 = log_addr)
      by (rewrite /G4 upd_ne; [exact HG3s4 | vm_compute; discriminate]).
    assert (HG4s5 : G4 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /G4 upd_ne; [exact HG3s5 | vm_compute; discriminate]).
    assert (HG4regs : eo_regs m G4).
    { rewrite /eo_regs. split.
      - rewrite /G4 upd_ne; [exact (proj1 HG3regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /G4 upd_ne; [| regne].
        exact (proj2 HG3regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppe2 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xde) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0xe2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppe2) in "Hpc".
    clear Hppe2.
    (* ===== +0xe2 jal ra,memmove : the log slot gets the home bytes ===== *)
    iPoseProof (eoi_e2 with "Htext") as "Hie2".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0xe2)) Rra
              (mword_of_int 2084692 : mword 21) G4 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hie2").
    iIntros (CIDa14 Hsa14) "Hcg Hpc".
    pose (G5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0xe2) : mword 64) 4)]> G4).
    assert (Htgte2 : add_vec (mword_of_int (KernelSyms.end_op + 0xe2) : mword 64)
                       (sign_extend' 64 (mword_of_int 2084692 : mword 21))
                     = mword_of_int KernelSyms.memmove)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgte2) in "Hpc".
    clear Htgte2.
    assert (HG5a0 : G5 !!! Regidx Ra0 = b_data (bpa k1))
      by (rewrite /G5 upd_ne; [exact HG4a0 | vm_compute; discriminate]).
    assert (HG5a1 : G5 !!! Regidx Ra1 = b_data (bpa k2))
      by (rewrite /G5 upd_ne; [exact HG4a1 | vm_compute; discriminate]).
    assert (HG5a2 : G5 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 1024%nat) : mword 64))
      by (rewrite /G5 upd_ne; [exact HG4a2 | vm_compute; discriminate]).
    assert (HG5s1 : G5 !!! Regidx Rs1 = bnode k1)
      by (rewrite /G5 upd_ne; [exact HG4s1 | vm_compute; discriminate]).
    assert (HG5s3 : G5 !!! Regidx Rs3 = bnode k2)
      by (rewrite /G5 upd_ne; [exact HG4s3 | vm_compute; discriminate]).
    assert (HG5s2 : G5 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /G5 upd_ne; [exact HG4s2 | vm_compute; discriminate]).
    assert (HG5s4 : G5 !!! Regidx Rs4 = log_addr)
      by (rewrite /G5 upd_ne; [exact HG4s4 | vm_compute; discriminate]).
    assert (HG5s5 : G5 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /G5 upd_ne; [exact HG4s5 | vm_compute; discriminate]).
    assert (HG5ra : G5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0xe2) : mword 64) 4)
      by (rewrite /G5; apply upd_eq).
    assert (HG5regs : eo_regs m G5).
    { rewrite /eo_regs. split.
      - rewrite /G5 upd_ne; [exact (proj1 HG4regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /G5 upd_ne; [| regne].
        exact (proj2 HG4regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    iDestruct "Hbuf1" as "(Hbno1 & Hbdsk1 & %Hlen1 & Hdata1)".
    iDestruct "Hbuf2" as "(Hbno2 & Hbdsk2 & %Hlen2 & Hdata2)".
    iDestruct (eo_data_fwd (b_data (bpa k1)) bs1 1024%nat Hlen1 with "Hdata1") as "Hdata1".
    iDestruct (eo_data_fwd (b_data (bpa k2)) bs2 1024%nat Hlen2 with "Hdata2") as "Hdata2".
    iEval (rewrite -HG5a1) in "Hdata2".
    iEval (rewrite -HG5a0) in "Hdata1".
    iApply (Mm.wp_memmove_sconf G5 (K - 8)%nat 1024%nat
              (fun i => bs2 !!! i) (fun i => bs1 !!! i) eb (proc_addr j)
              ltac:(pose proof (eo_Kmm K HK); lia) ltac:(vm_compute; reflexivity) HG5a2
              with "Hcg Htext Hpc Hdata2 Hdata1").
    iIntros (CIDa15 Hsa15 mf3) "Hcg Hpc Hdata2 Hdata1 %Hmf3a0 %Hcs3".
    iEval (rewrite HG5a1) in "Hdata2".
    iEval (rewrite HG5a0) in "Hdata1".
    iDestruct (eo_data_back (b_data (bpa k2)) bs2 1024%nat Hlen2 with "Hdata2") as "Hdata2".
    iDestruct (eo_data_back (b_data (bpa k1)) bs2 1024%nat Hlen2 with "Hdata1") as "Hdata1".
    assert (Hpce6 : ret_pc (G5 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0xe6)).
    { rewrite HG5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpce6) in "Hpc".
    clear Hpce6.
    assert (Hf3s1 : mf3 !!! Regidx Rs1 = bnode k1)
      by (rewrite (callee_saved_lookup Hcs3 Rs1 ltac:(vm_compute; reflexivity)); exact HG5s1).
    assert (Hf3s3 : mf3 !!! Regidx Rs3 = bnode k2)
      by (rewrite (callee_saved_lookup Hcs3 Rs3 ltac:(vm_compute; reflexivity)); exact HG5s3).
    assert (Hf3s2 : mf3 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite (callee_saved_lookup Hcs3 Rs2 ltac:(vm_compute; reflexivity)); exact HG5s2).
    assert (Hf3s4 : mf3 !!! Regidx Rs4 = log_addr)
      by (rewrite (callee_saved_lookup Hcs3 Rs4 ltac:(vm_compute; reflexivity)); exact HG5s4).
    assert (Hf3s5 : mf3 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite (callee_saved_lookup Hcs3 Rs5 ltac:(vm_compute; reflexivity)); exact HG5s5).
    assert (Hf3regs : eo_regs m mf3).
    { rewrite /eo_regs. split.
      - rewrite (callee_saved_lookup Hcs3 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact (proj1 HG5regs).
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite (callee_saved_lookup Hcs3 c Hcs).
        exact (proj2 HG5regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    (* the HOME handle goes back together, untouched *)
    iAssert (bio_locked bn (fs_view γfs γd dev cov) k2 pidv dev w bs2 bsd2 d2)
      with "[Hslk2 Hspid2 Hvld2 Hbdev2 Hbno2 Hbdsk2 Hdata2 Hdsk2 Hpay2]" as "Hlk2".
    { rewrite /bio_locked /bio_held.
      iSplitR; [iPureIntro; exact Hk2|]. iSplitR; [iPureIntro; exact Hcv2|].
      iSplitR; [iPureIntro; exact Hdv2|].
      iSplitL "Hslk2"; [iExact "Hslk2"|]. iSplitL "Hspid2"; [iExact "Hspid2"|].
      iSplitL "Hvld2"; [iExact "Hvld2"|]. iSplitL "Hbdev2"; [iExact "Hbdev2"|].
      iSplitR "Hdsk2 Hpay2".
      { rewrite /buf_own. iSplitL "Hbno2"; [iExact "Hbno2"|].
        iSplitL "Hbdsk2"; [iExact "Hbdsk2"|].
        iSplitR; [iPureIntro; exact Hlen2|]. iExact "Hdata2". }
      iSplitL "Hdsk2"; [iExact "Hdsk2"|]. iExact "Hpay2". }
    (* ===== +0xe6 c.mv a0,s1 ===== *)
    iPoseProof (eoi_e6 with "Htext") as "Hie6".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.end_op + 0xe6)) Ra0 Rs1
              mf3 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hie6").
    iIntros (CIDa16 Hsa16) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    pose (H1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mf3 !!! Regidx Rs1))]> mf3).
    assert (HH1a0 : H1 !!! Regidx Ra0 = bnode k1).
    { rewrite /H1 upd_eq add_vec_zero_l. exact Hf3s1. }
    assert (HH1s1 : H1 !!! Regidx Rs1 = bnode k1)
      by (rewrite /H1 upd_ne; [exact Hf3s1 | vm_compute; discriminate]).
    assert (HH1s3 : H1 !!! Regidx Rs3 = bnode k2)
      by (rewrite /H1 upd_ne; [exact Hf3s3 | vm_compute; discriminate]).
    assert (HH1s2 : H1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /H1 upd_ne; [exact Hf3s2 | vm_compute; discriminate]).
    assert (HH1s4 : H1 !!! Regidx Rs4 = log_addr)
      by (rewrite /H1 upd_ne; [exact Hf3s4 | vm_compute; discriminate]).
    assert (HH1s5 : H1 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /H1 upd_ne; [exact Hf3s5 | vm_compute; discriminate]).
    assert (HH1regs : eo_regs m H1).
    { rewrite /eo_regs. split.
      - rewrite /H1 upd_ne; [exact (proj1 Hf3regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /H1 upd_ne; [| regne].
        exact (proj2 Hf3regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppe8 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xe6) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0xe8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppe8) in "Hpc".
    clear Hppe8.
    (* ===== +0xe8 jal ra,bwrite : the log slot's disk cell moves ===== *)
    iPoseProof (eoi_e8 with "Htext") as "Hie8".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0xe8)) Rra
              (mword_of_int 2092712 : mword 21) H1 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hie8").
    iIntros (CIDa17 Hsa17) "Hcg Hpc".
    pose (H2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0xe8) : mword 64) 4)]> H1).
    assert (Htgte8 : add_vec (mword_of_int (KernelSyms.end_op + 0xe8) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092712 : mword 21))
                     = mword_of_int KernelSyms.bwrite)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgte8) in "Hpc".
    clear Htgte8.
    assert (HH2a0 : H2 !!! Regidx Ra0 = bnode k1)
      by (rewrite /H2 upd_ne; [exact HH1a0 | vm_compute; discriminate]).
    assert (HH2s1 : H2 !!! Regidx Rs1 = bnode k1)
      by (rewrite /H2 upd_ne; [exact HH1s1 | vm_compute; discriminate]).
    assert (HH2s3 : H2 !!! Regidx Rs3 = bnode k2)
      by (rewrite /H2 upd_ne; [exact HH1s3 | vm_compute; discriminate]).
    assert (HH2s2 : H2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /H2 upd_ne; [exact HH1s2 | vm_compute; discriminate]).
    assert (HH2s4 : H2 !!! Regidx Rs4 = log_addr)
      by (rewrite /H2 upd_ne; [exact HH1s4 | vm_compute; discriminate]).
    assert (HH2s5 : H2 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /H2 upd_ne; [exact HH1s5 | vm_compute; discriminate]).
    assert (HH2ra : H2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0xe8) : mword 64) 4)
      by (rewrite /H2; apply upd_eq).
    assert (HH2regs : eo_regs m H2).
    { rewrite /eo_regs. split.
      - rewrite /H2 upd_ne; [exact (proj1 HH1regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /H2 upd_ne; [| regne].
        exact (proj2 HH1regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    iAssert (bio_hold0 bn (fs_view γfs γd dev cov) k1 pidv dev bnol bs2 bsd1)
      with "[Hslk1 Hspid1 Hvld1 Hbdev1 Hbno1 Hbdsk1 Hdata1 Hdsk1]" as "Hhold".
    { rewrite /bio_hold0.
      iSplitR; [iPureIntro; exact Hk1|]. iSplitR; [iPureIntro; exact Hcv1|].
      iSplitR; [iPureIntro; exact Hdv1|].
      iSplitL "Hslk1"; [iExact "Hslk1"|]. iSplitL "Hspid1"; [iExact "Hspid1"|].
      iSplitL "Hvld1"; [iExact "Hvld1"|]. iSplitL "Hbdev1"; [iExact "Hbdev1"|].
      iSplitR "Hdsk1"; [| iExact "Hdsk1"].
      rewrite /buf_own. iSplitL "Hbno1"; [iExact "Hbno1"|].
      iSplitL "Hbdsk1"; [iExact "Hbdsk1"|].
      iSplitR; [iPureIntro; exact Hlen2|]. iExact "Hdata1". }
    iDestruct (cpu_own_transport CIDb2 CIDa17 0 eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDb2 CIDa17 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDb2 CIDa17 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CIDa9) (CIDb := CIDa17)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (BW.wp_bwrite_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) k1 pidv dev bnol dq H2 (K - 8)%nat eb C
              bs2 bsd1 eb log_mirror_clean lks
              ltac:(pose proof (eo_Kbwrite K HK); lia)
              ltac:(rewrite Hubnol; exact (eo_lt_lit _ Hslotrange))
              ltac:(reflexivity) Hj Hgl Hk1 HH2a0
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs
                    Hdevi Hdgeom Hdlock Hhold [Hmirc]").
    (* THE LOG-FILL fupd (phase C2b/D1 stage 4): with the ON-DISK header
       still clean -- which is what the mirror half in hand says, and what
       makes the batch's [log_mirror_clean] the right thing to park in the
       lock -- recovery does not look at the slots at all, so this write is
       invisible to the durable state. *)
    { rewrite Hubnol.
      iApply (fs_logfill_permit cov logstart t bs2 Hlen2
                ltac:(exact (eo_t_lt_lb t n Ht Hn30))
                with "Hseam Hregc Hswlb Hmirc"). }
    iIntros (CIDb3 Hsb3 mf4) "%Hcs4 Hcg Hcnt Hextc Hextm Hpc Hppid Hhold >Hmirc".
    assert (Hpcec : ret_pc (H2 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0xec)).
    { rewrite HH2ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcec) in "Hpc".
    clear Hpcec.
    assert (Hf4s1 : mf4 !!! Regidx Rs1 = bnode k1)
      by (rewrite (callee_saved_lookup Hcs4 Rs1 ltac:(vm_compute; reflexivity)); exact HH2s1).
    assert (Hf4s3 : mf4 !!! Regidx Rs3 = bnode k2)
      by (rewrite (callee_saved_lookup Hcs4 Rs3 ltac:(vm_compute; reflexivity)); exact HH2s3).
    assert (Hf4s2 : mf4 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite (callee_saved_lookup Hcs4 Rs2 ltac:(vm_compute; reflexivity)); exact HH2s2).
    assert (Hf4s4 : mf4 !!! Regidx Rs4 = log_addr)
      by (rewrite (callee_saved_lookup Hcs4 Rs4 ltac:(vm_compute; reflexivity)); exact HH2s4).
    assert (Hf4s5 : mf4 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite (callee_saved_lookup Hcs4 Rs5 ltac:(vm_compute; reflexivity)); exact HH2s5).
    assert (Hf4regs : eo_regs m mf4).
    { rewrite /eo_regs. split.
      - rewrite (callee_saved_lookup Hcs4 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact (proj1 HH2regs).
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite (callee_saved_lookup Hcs4 c Hcs).
        exact (proj2 HH2regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    (* ---- THE GHOST STEP: the log slot's logged content := the home bytes ---- *)
    iDestruct (eo_pay_split with "Hpay1") as "(HpL1 & HpD1 & Hextra1)".
    iMod (fsblock_update γfs L (uint bnol) bsold bs2 bs1
            with "HauthL Hslotfb HpL1") as "((%Hbs1 & %Hlkslot) & HauthL & Hslotfb & HpL1)".
    iDestruct (eo_pay_mk bn γfs γd dev cov k1 dev bnol bs2 d1
                 with "HpL1 HpD1 Hextra1") as "Hpay1".
    iAssert (bio_locked bn (fs_view γfs γd dev cov) k1 pidv dev bnol bs2 bs2 d1)
      with "[Hhold Hpay1]" as "Hlk1".
    { rewrite /bio_locked bio_held_split.
      iSplitL "Hhold"; [iExact "Hhold" | iExact "Hpay1"]. }
    (* ===== +0xec c.mv a0,s3 ; +0xee jal brelse (the home block) ===== *)
    iPoseProof (eoi_ec with "Htext") as "Hiec".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.end_op + 0xec)) Ra0 Rs3
              mf4 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiec").
    iIntros (CIDa18 Hsa18) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    pose (H3 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mf4 !!! Regidx Rs3))]> mf4).
    assert (HH3a0 : H3 !!! Regidx Ra0 = bnode k2).
    { rewrite /H3 upd_eq add_vec_zero_l. exact Hf4s3. }
    assert (HH3s1 : H3 !!! Regidx Rs1 = bnode k1)
      by (rewrite /H3 upd_ne; [exact Hf4s1 | vm_compute; discriminate]).
    assert (HH3s2 : H3 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /H3 upd_ne; [exact Hf4s2 | vm_compute; discriminate]).
    assert (HH3s4 : H3 !!! Regidx Rs4 = log_addr)
      by (rewrite /H3 upd_ne; [exact Hf4s4 | vm_compute; discriminate]).
    assert (HH3s5 : H3 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /H3 upd_ne; [exact Hf4s5 | vm_compute; discriminate]).
    assert (HH3regs : eo_regs m H3).
    { rewrite /eo_regs. split.
      - rewrite /H3 upd_ne; [exact (proj1 Hf4regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /H3 upd_ne; [| regne].
        exact (proj2 Hf4regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppee : add_vec_int (mword_of_int (KernelSyms.end_op + 0xec) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0xee))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppee) in "Hpc".
    clear Hppee.
    iPoseProof (eoi_ee with "Htext") as "Hiee".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0xee)) Rra
              (mword_of_int 2092756 : mword 21) H3 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hiee").
    iIntros (CIDa19 Hsa19) "Hcg Hpc".
    pose (H4 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0xee) : mword 64) 4)]> H3).
    assert (Htgtee : add_vec (mword_of_int (KernelSyms.end_op + 0xee) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092756 : mword 21))
                     = mword_of_int KernelSyms.brelse)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtee) in "Hpc".
    clear Htgtee.
    assert (HH4a0 : H4 !!! Regidx Ra0 = bnode k2)
      by (rewrite /H4 upd_ne; [exact HH3a0 | vm_compute; discriminate]).
    assert (HH4s1 : H4 !!! Regidx Rs1 = bnode k1)
      by (rewrite /H4 upd_ne; [exact HH3s1 | vm_compute; discriminate]).
    assert (HH4s2 : H4 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /H4 upd_ne; [exact HH3s2 | vm_compute; discriminate]).
    assert (HH4s4 : H4 !!! Regidx Rs4 = log_addr)
      by (rewrite /H4 upd_ne; [exact HH3s4 | vm_compute; discriminate]).
    assert (HH4s5 : H4 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /H4 upd_ne; [exact HH3s5 | vm_compute; discriminate]).
    assert (HH4ra : H4 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0xee) : mword 64) 4)
      by (rewrite /H4; apply upd_eq).
    assert (HH4regs : eo_regs m H4).
    { rewrite /eo_regs. split.
      - rewrite /H4 upd_ne; [exact (proj1 HH3regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /H4 upd_ne; [| regne].
        exact (proj2 HH3regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    iDestruct (cpu_own_transport CIDb3 CIDa19 0 eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDb3 CIDa19 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDb3 CIDa19 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CIDa17) (CIDb := CIDa19)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) k2 pidv dev w dq
              H4 (K - 8)%nat eb (proc_addr j) C bs2 bsd2 d2 eb lks
              ltac:(pose proof (eo_Kbrelse K HK); lia) Hk2 HH4a0
              (locks_below_mono lks (lock_rank "log") (lock_rank "bcache") Hbelow ltac:(vm_compute; lia))
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs Hlk2").
    iIntros (CIDb4 Hsb4 mf5) "%Hcs5 Hcg Hcnt Hpc Hppid Hu2".
    assert (Hpcf2 : ret_pc (H4 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0xf2)).
    { rewrite HH4ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcf2) in "Hpc".
    clear Hpcf2.
    assert (Hf5s1 : mf5 !!! Regidx Rs1 = bnode k1)
      by (rewrite (callee_saved_lookup Hcs5 Rs1 ltac:(vm_compute; reflexivity)); exact HH4s1).
    assert (Hf5s2 : mf5 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite (callee_saved_lookup Hcs5 Rs2 ltac:(vm_compute; reflexivity)); exact HH4s2).
    assert (Hf5s4 : mf5 !!! Regidx Rs4 = log_addr)
      by (rewrite (callee_saved_lookup Hcs5 Rs4 ltac:(vm_compute; reflexivity)); exact HH4s4).
    assert (Hf5s5 : mf5 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite (callee_saved_lookup Hcs5 Rs5 ltac:(vm_compute; reflexivity)); exact HH4s5).
    assert (Hf5regs : eo_regs m mf5).
    { rewrite /eo_regs. split.
      - rewrite (callee_saved_lookup Hcs5 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact (proj1 HH4regs).
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite (callee_saved_lookup Hcs5 c Hcs).
        exact (proj2 HH4regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    (* ===== +0xf2 c.mv a0,s1 ; +0xf4 jal brelse (the log slot) ===== *)
    iPoseProof (eoi_f2 with "Htext") as "Hif2".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.end_op + 0xf2)) Ra0 Rs1
              mf5 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hif2").
    iIntros (CIDa20 Hsa20) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    pose (H5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mf5 !!! Regidx Rs1))]> mf5).
    assert (HH5a0 : H5 !!! Regidx Ra0 = bnode k1).
    { rewrite /H5 upd_eq add_vec_zero_l. exact Hf5s1. }
    assert (HH5s2 : H5 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /H5 upd_ne; [exact Hf5s2 | vm_compute; discriminate]).
    assert (HH5s4 : H5 !!! Regidx Rs4 = log_addr)
      by (rewrite /H5 upd_ne; [exact Hf5s4 | vm_compute; discriminate]).
    assert (HH5s5 : H5 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /H5 upd_ne; [exact Hf5s5 | vm_compute; discriminate]).
    assert (HH5regs : eo_regs m H5).
    { rewrite /eo_regs. split.
      - rewrite /H5 upd_ne; [exact (proj1 Hf5regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /H5 upd_ne; [| regne].
        exact (proj2 Hf5regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppf4 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xf2) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0xf4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppf4) in "Hpc".
    clear Hppf4.
    iPoseProof (eoi_f4 with "Htext") as "Hif4".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0xf4)) Rra
              (mword_of_int 2092750 : mword 21) H5 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hif4").
    iIntros (CIDa21 Hsa21) "Hcg Hpc".
    pose (H6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0xf4) : mword 64) 4)]> H5).
    assert (Htgtf4 : add_vec (mword_of_int (KernelSyms.end_op + 0xf4) : mword 64)
                       (sign_extend' 64 (mword_of_int 2092750 : mword 21))
                     = mword_of_int KernelSyms.brelse)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtf4) in "Hpc".
    clear Htgtf4.
    assert (HH6a0 : H6 !!! Regidx Ra0 = bnode k1)
      by (rewrite /H6 upd_ne; [exact HH5a0 | vm_compute; discriminate]).
    assert (HH6s2 : H6 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite /H6 upd_ne; [exact HH5s2 | vm_compute; discriminate]).
    assert (HH6s4 : H6 !!! Regidx Rs4 = log_addr)
      by (rewrite /H6 upd_ne; [exact HH5s4 | vm_compute; discriminate]).
    assert (HH6s5 : H6 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /H6 upd_ne; [exact HH5s5 | vm_compute; discriminate]).
    assert (HH6ra : H6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0xf4) : mword 64) 4)
      by (rewrite /H6; apply upd_eq).
    assert (HH6regs : eo_regs m H6).
    { rewrite /eo_regs. split.
      - rewrite /H6 upd_ne; [exact (proj1 HH5regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /H6 upd_ne; [| regne].
        exact (proj2 HH5regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    iDestruct (cpu_own_transport CIDb4 CIDa21 0 eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    (* brelse does not thread the trap-CSR complement (it does not mention
       it), so it stranded Hextc/Hextm at [CIDa19], its OWN entry hart, not
       at [CIDb4] where its own continuation landed -- transport across the
       WIDER span, same as [Hcont] just below. *)
    iDestruct (trap_csrs_ext_transport CIDa19 CIDa21 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDa19 CIDa21 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CIDa19) (CIDb := CIDa21)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (BL.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) k1 pidv dev bnol dq
              H6 (K - 8)%nat eb (proc_addr j) C bs2 bs2 d1 eb lks
              ltac:(pose proof (eo_Kbrelse K HK); lia) Hk1 HH6a0
              (locks_below_mono lks (lock_rank "log") (lock_rank "bcache") Hbelow ltac:(vm_compute; lia))
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs Hlk1").
    iIntros (CIDb5 Hsb5 mf6) "%Hcs6 Hcg Hcnt Hpc Hppid Hu1".
    assert (Hpcf8 : ret_pc (H6 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0xf8)).
    { rewrite HH6ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcf8) in "Hpc".
    clear Hpcf8.
    assert (Hf6s2 : mf6 !!! Regidx Rs2 = (mword_of_int (Z.of_nat t) : mword 64))
      by (rewrite (callee_saved_lookup Hcs6 Rs2 ltac:(vm_compute; reflexivity)); exact HH6s2).
    assert (Hf6s4 : mf6 !!! Regidx Rs4 = log_addr)
      by (rewrite (callee_saved_lookup Hcs6 Rs4 ltac:(vm_compute; reflexivity)); exact HH6s4).
    assert (Hf6s5 : mf6 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite (callee_saved_lookup Hcs6 Rs5 ltac:(vm_compute; reflexivity)); exact HH6s5).
    assert (Hf6regs : eo_regs m mf6).
    { rewrite /eo_regs. split.
      - rewrite (callee_saved_lookup Hcs6 csp_rs1 ltac:(vm_compute; reflexivity)).
        exact (proj1 HH6regs).
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite (callee_saved_lookup Hcs6 c Hcs).
        exact (proj2 HH6regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    (* ===== +0xf8 c.addiw s2,s2,1 ===== *)
    assert (Hwvf8 : sign_extend' 64 (subrange_vec_dec
                      (add_vec (rget mf6 Rs2)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
                    = (mword_of_int (Z.of_nat t + 1) : mword 64)).
    { rgne. rewrite Hf6s2. apply eo_addiw1; [lia|].
      pose proof (eo_St_small t n Ht Hn30) as Hsm. lia. }
    iPoseProof (eoi_f8 with "Htext") as "Hif8".
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.end_op + 0xf8)) Rs2 (mword_of_int 1 : mword 6)
              mf6 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hif8").
    iIntros (CIDa22 Hsa22) "Hcg Hpc".
    iEval (rewrite Hwvf8) in "Hcg".
    clear Hwvf8.
    pose (J1 := <[Regidx Rs2 := regval_into_reg
                  (mword_of_int (Z.of_nat t + 1) : mword 64)]> mf6).
    assert (HJ1s2 : J1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (S t)) : mword 64)).
    { rewrite /J1 upd_eq. rewrite eo_succ_z. reflexivity. }
    assert (HJ1s4 : J1 !!! Regidx Rs4 = log_addr)
      by (rewrite /J1 upd_ne; [exact Hf6s4 | vm_compute; discriminate]).
    assert (HJ1s5 : J1 !!! Regidx Rs5 = (lh_block t : mword 64))
      by (rewrite /J1 upd_ne; [exact Hf6s5 | vm_compute; discriminate]).
    assert (HJ1regs : eo_regs m J1).
    { rewrite /eo_regs. split.
      - rewrite /J1 upd_ne; [exact (proj1 Hf6regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /J1 upd_ne; [| regne].
        exact (proj2 Hf6regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppfa : add_vec_int (mword_of_int (KernelSyms.end_op + 0xf8) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0xfa))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppfa) in "Hpc".
    clear Hppfa.
    (* ===== +0xfa c.addi s5,s5,4 ===== *)
    iPoseProof (eoi_fa with "Htext") as "Hifa".
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.end_op + 0xfa)) Rs5 (mword_of_int 4 : mword 6)
              J1 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hifa").
    iIntros (CIDa23 Hsa23) "Hcg Hpc".
    pose (J2 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (rget J1 Rs5)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))))]> J1).
    assert (HJ2s5 : J2 !!! Regidx Rs5 = (lh_block (S t) : mword 64)).
    { rewrite /J2 upd_eq. rgne. rewrite HJ1s5. exact (eo_cursor_step t). }
    assert (HJ2s2 : J2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (S t)) : mword 64))
      by (rewrite /J2 upd_ne; [exact HJ1s2 | vm_compute; discriminate]).
    assert (HJ2s4 : J2 !!! Regidx Rs4 = log_addr)
      by (rewrite /J2 upd_ne; [exact HJ1s4 | vm_compute; discriminate]).
    assert (HJ2regs : eo_regs m J2).
    { rewrite /eo_regs. split.
      - rewrite /J2 upd_ne; [exact (proj1 HJ1regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /J2 upd_ne; [| regne].
        exact (proj2 HJ1regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hppfc : add_vec_int (mword_of_int (KernelSyms.end_op + 0xfa) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0xfc))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppfc) in "Hpc".
    clear Hppfc.
    (* ===== +0xfc lw a5,44(s4) : a5 := log.lh.n ===== *)
    assert (Halhn : add_vec (rget J2 Rs4) (sign_extend' 64 (mword_of_int 44 : mword 12))
                    = lh_n_pa).
    { rgne. rewrite HJ2s4. exact eo_addr_lhn. }
    iEval (rewrite -Halhn) in "Hncell".
    iPoseProof (eoi_fc with "Htext") as "Hifc".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.end_op + 0xfc)) Ra5 Rs4
              (mword_of_int 44 : mword 12) J2 (K - 8)%nat
              (mword_of_int (Z.of_nat n) : mword 32) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hifc Hncell").
    iIntros (CIDa24 Hsa24) "Hcg Hpc Hncell".
    iEval (rewrite Halhn) in "Hncell".
    pose (J3 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32))]> J2).
    assert (HJ3a5 : J3 !!! Regidx Ra5 = (mword_of_int (Z.of_nat n) : mword 64))
      by (rewrite /J3 upd_eq; apply eo_sext32; exact (eo_n_small n Hn30)).
    assert (HJ3s2 : J3 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (S t)) : mword 64))
      by (rewrite /J3 upd_ne; [exact HJ2s2 | vm_compute; discriminate]).
    assert (HJ3s4 : J3 !!! Regidx Rs4 = log_addr)
      by (rewrite /J3 upd_ne; [exact HJ2s4 | vm_compute; discriminate]).
    assert (HJ3s5 : J3 !!! Regidx Rs5 = (lh_block (S t) : mword 64))
      by (rewrite /J3 upd_ne; [exact HJ2s5 | vm_compute; discriminate]).
    assert (HJ3regs : eo_regs m J3).
    { rewrite /eo_regs. split.
      - rewrite /J3 upd_ne; [exact (proj1 HJ2regs) | vm_compute; discriminate].
      - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
        rewrite /J3 upd_ne; [| regne].
        exact (proj2 HJ2regs c Hcs N2 N8 N9 N18 N19 N20 N21). }
    assert (Hpp100 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xfc) : mword 64) 4
                     = mword_of_int (KernelSyms.end_op + 0x100))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp100) in "Hpc".
    clear Hpp100.
    (* ---- the batch, re-formed at the bumped cursor ---- *)
    iDestruct ("Hblkback" with "Hblk") as "HW".
    set (Lw' := eo_ext Lw t bs2).
    assert (HLw' : forall (i : nat) (v : mword 32), (i < S t)%nat -> W !! i = Some v ->
             (<[uint bnol := bs2]> L) !! uint v = Some (Lw' i)).
    { intros i v Hi Hv.
      assert (Hne : uint bnol <> uint v).
      { rewrite Hubnol. intro Hbad.
        destruct (Hwok v (eo_lookup_elem W i v Hv)) as [_ Hnl].
        apply Hnl. rewrite -Hbad. apply eo_slot_in_region.
        exact (eo_t_lt_lb t n Ht Hn30). }
      rewrite lookup_insert_ne; [| exact Hne].
      destruct (decide (i = t)) as [->|Hit].
      - rewrite Hv in Hw. injection Hw as <-.
        rewrite /Lw' eo_ext_eq. exact Hlkhome.
      - assert (Hit2 : (i < t)%nat) by lia.
        rewrite /Lw' (eo_ext_lt Lw t bs2 i Hit2). exact (HLw i v Hit2 Hv). }
    assert (Hseq : seq 0 (S t) = seq 0 t ++ [t]) by (rewrite seq_S; reflexivity).
    iAssert ([∗ list] i ∈ seq 0 (S t),
               fsblock γfs (log_slot_bno logstart i) (Lw' i))%I
      with "[Hdone Hslotfb]" as "Hdone".
    { rewrite Hseq big_sepL_app. iSplitL "Hdone".
      - iApply (big_sepL_mono with "Hdone"). intros i x Hx.
        apply lookup_seq in Hx as [-> Hlt].
        rewrite Nat.add_0_l /Lw' (eo_ext_lt Lw t bs2 i Hlt). done.
      - rewrite big_sepL_singleton /Lw' eo_ext_eq.
        iEval (rewrite Hubnol) in "Hslotfb". iExact "Hslotfb". }
    iAssert (bslots bn ((LOGBLOCKS - n) + 2)%nat) with "[Hu1 Hu2 Hpool]" as "Hpool".
    { rewrite Hp1 (bslots_op bn 1 (1 + (LOGBLOCKS - n))).
      iSplitL "Hu1"; [iExact "Hu1"|].
      rewrite (bslots_op bn 1 (LOGBLOCKS - n)).
      iSplitL "Hu2"; [iExact "Hu2"|iExact "Hpool"]. }
    iAssert (eo_open bn γfs cov logstart n W (<[uint bnol := bs2]> L) D Lw' (S t))
      with "[Hncell HW Hjunk HauthL HauthD Hcov Hhdr Hdone Hrest Hpool]" as "Hopen".
    { rewrite /eo_open.
      iSplitL "Hncell"; [iExact "Hncell"|].
      iSplitL "HW"; [iExact "HW"|].
      iSplitL "Hjunk"; [iExact "Hjunk"|].
      iSplitL "HauthL"; [iExact "HauthL"|].
      iSplitL "HauthD"; [iExact "HauthD"|].
      iSplitL "Hcov"; [iExact "Hcov"|].
      iSplitL "Hhdr"; [iExact "Hhdr"|].
      iSplitL "Hdone"; [iExact "Hdone"|].
      iSplitL "Hrest"; [iExact "Hrest"|]. iExact "Hpool". }
    (* ===== +0x100 blt s2,a5 -> +0xb4 ===== *)
    destruct (decide (S t < n)%nat) as [Hlt|Hge].
    - (* the back edge is TAKEN *)
      assert (Hcmp : zopz0zI_s (rget J3 Rs2) (rget J3 Ra5) = true).
      { rgne. rgne. rewrite HJ3s2 HJ3a5.
        rewrite (eo_lt_s (Z.of_nat (S t)) (Z.of_nat n)
                   (eo_St_small t n Ht Hn30) (eo_n_small n Hn30)).
        apply Z.ltb_lt. lia. }
      iApply (wp_blt_taken_s_sconf (mword_of_int (KernelSyms.end_op + 0x100))
                (mword_of_int 8116 : mword 13) Ra5 Rs2 J3 (K - 8)%nat eb
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi100").
      iApply bi.later_intro. iIntros (CIDa25 Hsa25) "Hcg Hpc".
      assert (Htgt100 : add_vec (mword_of_int (KernelSyms.end_op + 0x100) : mword 64)
                          (sign_extend' 64 (mword_of_int 8116 : mword 13))
                        = mword_of_int (KernelSyms.end_op + 0xb4))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt100) in "Hpc".
      clear Htgt100.
      iDestruct (cpu_own_transport CIDb5 CIDa25 0 eb (proc_addr j) C eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      (* the second [brelse] also strands Hextc/Hextm at ITS entry hart
         [CIDa21], not at its own exit [CIDb5] -- same wider-span fix. *)
      iDestruct (trap_csrs_ext_transport CIDa21 CIDa25 eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDa21 CIDa25 eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (eo_cont_shift (CIDa := CIDa21) (CIDb := CIDa25)  j pidv dq m K eb C eb lks
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (IH CIDa25 (S t) J3 (<[uint bnol := bs2]> L) Lw' Hlt
                (eo_fuel_step t n fuel Hfuel) HLw' HJ3regs HJ3s2 HJ3s4 HJ3s5
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hseam Hregc Hppid Hprocs Hdevi Hdgeom Hdlock Hframe HframeS Hmirc
                      Hopen Hcont").
    - (* the loop is done: S t = n, and the commit tail follows *)
      assert (Htn : S t = n) by lia.
      assert (Hcmp : zopz0zI_s (rget J3 Rs2) (rget J3 Ra5) = false).
      { rgne. rgne. rewrite HJ3s2 HJ3a5.
        rewrite (eo_lt_s (Z.of_nat (S t)) (Z.of_nat n)
                   (eo_St_small t n Ht Hn30) (eo_n_small n Hn30)).
        apply Z.ltb_ge. lia. }
      iApply (wp_blt_fall_s_sconf (mword_of_int (KernelSyms.end_op + 0x100))
                (mword_of_int 8116 : mword 13) Ra5 Rs2 J3 (K - 8)%nat eb
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp with "Hcg Hpc Hi100").
      iIntros (CIDa25 Hsa25) "Hcg Hpc".
      assert (Hpp104 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x100) : mword 64) 4
                       = mword_of_int (KernelSyms.end_op + 0x104))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp104) in "Hpc".
      clear Hpp104.
      iDestruct (cpu_own_transport CIDb5 CIDa25 0 eb (proc_addr j) C eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      (* the second [brelse] also strands Hextc/Hextm at ITS entry hart
         [CIDa21], not at its own exit [CIDb5] -- same wider-span fix. *)
      iDestruct (trap_csrs_ext_transport CIDa21 CIDa25 eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDa21 CIDa25 eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (eo_cont_shift (CIDa := CIDa21) (CIDb := CIDa25)  j pidv dq m K eb C eb lks
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      rewrite Htn in HLw'.
      iEval (rewrite Htn) in "Hopen".
      iApply (eo_commit (CID0 := CIDa25)  γs j γl γu γd γk pd pav pu bn γ γfs
                cov logstart dev n W Lw' (<[uint bnol := bs2]> L) D pidv dq m J3 K eb C lks
                HK (conj Hcovok Hlogsub) Hj Hgl (conj HnW Hn30) Hnd Hwok
                ltac:(intros i v Hv; apply (HLw' i v);
                      [ apply lookup_lt_Some in Hv; lia | exact Hv ])
                HJ3regs Hbelow
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hseam Hregc Hppid Hprocs Hdevi Hdgeom Hdlock Hframe HframeS Hmirc
                      Hopen Hcont").
  Qed.


  (* ================================================================== *)
  (*  +0x7a .. +0x8e : the FAST path -- wakeup(&log) with the lock still  *)
  (*  held, then release, falling straight into the epilogue at +0x92.    *)
  (* ================================================================== *)
  Local Lemma eo_fast `{GEN : GenId} `{CID0 : CpuId} 
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names) (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (C : iProp Σ) (lks : gset nat) :
    (K_end_op <= K)%nat ->
    eo_regsE m M ->
    (* THE OUTER/INNER TRAP (claude-notes sweep, point 5): [eo_fast]'s own
       [lks] binder is the OUTER set -- it matches [eo_cont]/[Hcont] below
       VERBATIM, unchanged, because [eo_fast]'s caller splices its own final
       continuation straight through.  But [eo_fast] is entered from the
       C's "else { wakeup(&log); }" arm, i.e. WHILE STILL HOLDING "log", so
       the ENTRY [cpu_own] must read the INNER set
       [{[lock_rank "log"]} ∪ lks], not bare [lks] -- the interior release
       (below) is what brings it back down to bare [lks] for [Hcont]. *)
    locks_below lks (lock_rank "log") ->
    sie_cap_gpr M (trap_res eb + (K - 8))%nat false (proc_addr j) -∗
    cpu_own 1 eb (proc_addr j) C false ({[lock_rank "log"]} ∪ lks) -∗
    arm_pay 0 eb (proc_addr j) -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.end_op + 0x7a) : mword 64) -∗
    panic_wp_any -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    eo_frame4 m -∗
    eo_frameJ m -∗
    eo_cont (CID0 := CID0)  j pidv dq m K eb C eb lks -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hregs Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    pose proof Hregs as (Hsp & Hthr).
    iIntros "Hcg Hcnt Hpay Hextc Hextm Htok HRres #Htext Hpc #Hpanic #Hlctx #Hprocs Hppid Hframe Hjunk Hcont".
    iDestruct "Hlctx" as "(#Hlock & #Hdevc & #Hstc)".
    iDestruct (procs_inv_len γs with "Hprocs") as %Hlen.
    (* ===== +0x7a / +0x7e : a0 := &log ===== *)
    iPoseProof (eoi_7a with "Htext") as "Hi7a".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.end_op + 0x7a)) Ra0 (mword_of_int 30 : mword 20)
              M (trap_res eb + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (E1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.end_op + 0x7a) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> M).
    assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.end_op + 0x7a) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0x7e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7e) in "Hpc".
    clear Hpp7e.
    iPoseProof (eoi_7e with "Htext") as "Hi7e".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.end_op + 0x7e)) Ra0 Ra0
              (mword_of_int 1626 : mword 12) E1 (trap_res eb + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi7e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (E2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (E1 !!! Regidx Ra0 : mword 64)
                     (sign_extend' 64 (mword_of_int 1626 : mword 12)))]> E1).
    assert (HE2a0 : E2 !!! Regidx Ra0 = log_addr).
    { rewrite /E2 upd_eq /E1 upd_eq. exact eo_reloc_log_7a. }
    assert (HE2sp : E2 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64)).
    { rewrite /E2 upd_ne; [| vm_compute; discriminate].
      rewrite /E1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HE2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              E2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /E2 upd_ne; [| regne]. rewrite /E1 upd_ne; [| regne].
      exact (Hthr c Hcs N2 N8 N9 N18). }
    assert (Hpp82 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x7e) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0x82))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp82) in "Hpc".
    clear Hpp82.
    (* ===== +0x82 jal ra,wakeup ===== *)
    iPoseProof (eoi_82 with "Htext") as "Hi82".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0x82)) Rra
              (mword_of_int 2089514 : mword 21) E2 (trap_res eb + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi82").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (E3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0x82) : mword 64) 4)]> E2).
    assert (Htgt82 : add_vec (mword_of_int (KernelSyms.end_op + 0x82) : mword 64)
                       (sign_extend' 64 (mword_of_int 2089514 : mword 21))
                     = mword_of_int KernelSyms.wakeup)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt82) in "Hpc".
    clear Htgt82.
    assert (HE3ra : E3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0x82) : mword 64) 4)
      by (rewrite /E3; apply upd_eq).
    assert (HE3sp : E3 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /E3 upd_ne; [exact HE2sp | vm_compute; discriminate]).
    assert (HE3thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              E3 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /E3 upd_ne; [| regne]. exact (HE2thr c Hcs N2 N8 N9 N18). }
    assert (HwdomE : forall r : regidx, r ∈ dom (rf_to_gmap E3))
      by (intro r; apply rf_to_gmap_dom).
    (* same lift as [eo_tail]'s wakeup call: "log" (3) held, "proc" (11) is
       wakeup's own order premise. *)
    assert (Hlog_lt_proc : (lock_rank "log" < lock_rank "proc")%nat)
      by (vm_compute; lia).
    assert (Hbelow_wk2 : locks_below ({[lock_rank "log"]} ∪ lks) (lock_rank "proc")).
    { apply locks_below_union_singleton; [exact Hlog_lt_proc |].
      apply (locks_below_mono lks (lock_rank "log")); [exact Hbelow | lia]. }
    iApply (Wk.wp_wakeup_sconf E3 γs (proc_addr j) 1%nat
              (trap_res eb + (K - 8))%nat eb C false ({[lock_rank "log"]} ∪ lks)
              ltac:(pose proof (eo_Kwk K HK); lia) HwdomE Hlen eo_noff1
              Hbelow_wk2
              with "Hcg Hcnt Htext Hpc Hpanic Hprocs").
    iApply wp_next_off_intro. iIntros (Mw) "[%Hwcs %Hwdom] Hcg Hcnt Htext2 Hpc".
    iEval (rewrite HE3ra) in "Hpc".
    clear HE3ra.
    assert (Hpp86 : ret_pc (add_vec_int (mword_of_int (KernelSyms.end_op + 0x82) : mword 64) 4)
                    = (mword_of_int (KernelSyms.end_op + 0x86) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp86) in "Hpc".
    clear Hpp86.
    assert (HMwsp : Mw !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64)).
    { rewrite (callee_saved_lookup Hwcs csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HE3sp. }
    assert (HMwthr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              Mw !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite (callee_saved_lookup Hwcs c Hcs). exact (HE3thr c Hcs N2 N8 N9 N18). }
    (* ===== +0x86 / +0x8a : a0 := &log ===== *)
    iPoseProof (eoi_86 with "Htext") as "Hi86".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.end_op + 0x86)) Ra0 (mword_of_int 30 : mword 20)
              Mw (trap_res eb + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi86").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (G1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.end_op + 0x86) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> Mw).
    assert (Hpp8a : add_vec_int (mword_of_int (KernelSyms.end_op + 0x86) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0x8a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8a) in "Hpc".
    clear Hpp8a.
    iPoseProof (eoi_8a with "Htext") as "Hi8a".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.end_op + 0x8a)) Ra0 Ra0
              (mword_of_int 1614 : mword 12) G1 (trap_res eb + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi8a").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (G2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (G1 !!! Regidx Ra0 : mword 64)
                     (sign_extend' 64 (mword_of_int 1614 : mword 12)))]> G1).
    assert (HG2a0 : G2 !!! Regidx Ra0 = log_addr).
    { rewrite /G2 upd_eq /G1 upd_eq. exact eo_reloc_log_86. }
    assert (HG2sp : G2 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64)).
    { rewrite /G2 upd_ne; [| vm_compute; discriminate].
      rewrite /G1 upd_ne; [exact HMwsp | vm_compute; discriminate]. }
    assert (HG2thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              G2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G2 upd_ne; [| regne]. rewrite /G1 upd_ne; [| regne].
      exact (HMwthr c Hcs N2 N8 N9 N18). }
    assert (Hpp8e : add_vec_int (mword_of_int (KernelSyms.end_op + 0x8a) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0x8e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8e) in "Hpc".
    clear Hpp8e.
    (* ===== +0x8e jal ra,release ===== *)
    iPoseProof (eoi_8e with "Htext") as "Hi8e".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0x8e)) Rra
              (mword_of_int 2084624 : mword 21) G2 (trap_res eb + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi8e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (G3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0x8e) : mword 64) 4)]> G2).
    assert (Htgt8e : add_vec (mword_of_int (KernelSyms.end_op + 0x8e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2084624 : mword 21))
                     = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt8e) in "Hpc".
    clear Htgt8e.
    assert (HG3a0 : G3 !!! Regidx Ra0 = log_addr)
      by (rewrite /G3 upd_ne; [exact HG2a0 | vm_compute; discriminate]).
    assert (HG3ra : G3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0x8e) : mword 64) 4)
      by (rewrite /G3; apply upd_eq).
    assert (HG3sp : G3 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /G3 upd_ne; [exact HG2sp | vm_compute; discriminate]).
    assert (HG3thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              G3 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /G3 upd_ne; [| regne]. exact (HG2thr c Hcs N2 N8 N9 N18). }
    iApply (Rel.wp_release_sconf (ln_lk γ) log_addr "log"%string
              (log_res γ bn γfs cov logstart) G3 0%nat eb (proc_addr j) C
              (K - 8)%nat
              ({[lock_rank "log"]} ∪ lks)
              ltac:(rewrite HG3a0; rewrite /log_addr; apply bv_eq; vm_compute; reflexivity)
              ltac:(pose proof (eo_Klk K HK); lia)
              with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
    { iExact "Hlock". }
    iIntros (CIDc1 Hsc1 mr) "Hcg Hpc %Hrel Hcnt".
    assert (Hsetback : ({[lock_rank "log"]} ∪ lks) ∖ {[lock_rank "log"]} = lks)
      by (apply locks_add_del; assumption).
    iEval (rewrite Hsetback) in "Hcnt".
    assert (Hpc92 : ret_pc (G3 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0x92)).
    { rewrite HG3ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc92) in "Hpc".
    clear Hpc92.
    assert (Hregs2 : eo_regsE m mr).
    { rewrite /eo_regsE. split.
      - rewrite (callee_saved_lookup Hrel csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite HG3sp. exact Hsp.
      - intros c Hcs N2 N8 N9 N18.
        rewrite (callee_saved_lookup Hrel c Hcs). exact (HG3thr c Hcs N2 N8 N9 N18). }
    iDestruct (trap_csrs_ext_transport CID0 CIDc1 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDc1 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CID0) (CIDb := CIDc1)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (eo_epi (CID0 := CIDc1)  j pidv dq m mr K eb C eb lks HK Hregs2
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hppid Hframe Hjunk Hcont").
  Qed.

End EndOpBlocks.

(* ===================================================================== *)

Section ProofEndOp.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_end_op_sconf 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (u : nat)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) (lks : gset nat)
    : wp_end_op_sconf_body γs j γl γu γd γk pd pav pu bn γ γfs
                           cov logstart dev u pidv dq m K eb C b lks.
  Proof.
    cbv beta zeta delta [wp_end_op_sconf_body].
    intros HK Hgeom Hj Hgl Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    pose proof Hgeom as [Hcovok Hlogsub].
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlctx #Hseam #Hcert Hppid #Hprocs #Hdevi #Hdgeom #Hdlock Hop Hcont".
    iDestruct "Hcert" as "(_ & _ & #Hregc)".
    (* [b] and [eb] AGREE at depth 0 -- [CpuOwn.cpu_own_eb_agree], the general
       (index-free) fact, not [cpu_own_forces_on] which needed [eb = true].
       Per durable-notes: do NOT [subst b] -- keep the name, rewrite the
       entry bundle into [eb]-form once, and never touch [b] again; every
       level-0 stretch below is genuinely at [eb] (that is what this equation
       says), while the depth-1 critical section is unconditionally [false]
       regardless of [eb]. *)
    (* [b] and [eb] AGREE at depth 0, and here the honest move is to ELIMINATE
       [b]: the rest of this proof is written at [eb] throughout, and
       [iEval (rewrite ...)] does not fire on the entry bundle anyway (the
       occurrences sit under [wp_next]'s binder in [Hcont], and did not fire on
       [Hcg]/[Hcnt] either).  [subst b] is safe HERE because this file spells
       [eb], not [b], in its tactic arguments -- the opposite of ProofBalloc /
       ProofBmap, where [b] is named in dozens of leaf calls and substituting
       it would erase a name they still spell. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbm.
    cbn in Hbm. subst b.
    iDestruct "Hlctx" as "(#Hlock & #Hdevc & #Hstc & #Hswlb)".
    iAssert (log_ctx γ bn γfs cov logstart dev) as "#Hlctx".
    { rewrite /log_ctx. iSplitR; [iExact "Hlock"|]. iSplitR; [iExact "Hdevc"|].
      iSplitR; [iExact "Hstc" | iExact "Hswlb"]. }
    iAssert (eo_cont (CID0 := CID)  j pidv dq m K eb C eb lks)%I
      with "[Hcont]" as "Hcont"; [rewrite /eo_cont; iExact "Hcont"|].
    (* ===== PROLOGUE: the eight-slot frame ===== *)
    pose (R1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m).
    assert (Hpush : add_vec (m !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { unfold pa_stk, add_vec_int. apply f_equal.
      apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (eoi_00 with "Htext") as "Hi00".
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int KernelSyms.end_op : mword 64)
              (mword_of_int 60 : mword 6) m K 8 eb
              ltac:(unfold K_end_op in HK; lia) Hpush with "Hcg Hpc Hi00").
    iIntros (CID1 Hs1) "Hcg Hstk Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1 : mword 64)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))
      by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hstk".
    iDestruct "Hstk" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & _)".
    iDestruct "S1" as (v1) "Hr56". iDestruct "S2" as (v2) "Hr48".
    iDestruct "S3" as (v3) "Hr40". iDestruct "S4" as (v4) "Hr32".
    iDestruct "S5" as (v5) "Hg24". iDestruct "S6" as (v6) "Hg16".
    iDestruct "S7" as (v7) "Hg8".  iDestruct "S8" as (v8) "Hg0".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr56". iEval (rewrite -Hb2) in "Hr48".
    iEval (rewrite -Hb3) in "Hr40". iEval (rewrite -Hb4) in "Hr32".
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.end_op : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    clear Hpp02.
    iPoseProof (eoi_02 with "Htext") as "Hi02".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x02)) (mword_of_int 7 : mword 6) Rra
              R1 (K - 8)%nat v1 eb with "Hcg Hpc Hi02 Hr56").
    iIntros (CID2 Hs2) "Hcg Hpc Hr56".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    clear Hpp04.
    iPoseProof (eoi_04 with "Htext") as "Hi04".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x04)) (mword_of_int 6 : mword 6) Rs0
              R1 (K - 8)%nat v2 eb with "Hcg Hpc Hi04 Hr48").
    iIntros (CID3 Hs3) "Hcg Hpc Hr48".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    clear Hpp06.
    iPoseProof (eoi_06 with "Htext") as "Hi06".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x06)) (mword_of_int 5 : mword 6) Rs1
              R1 (K - 8)%nat v3 eb with "Hcg Hpc Hi06 Hr40").
    iIntros (CID4 Hs4) "Hcg Hpc Hr40".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    clear Hpp08.
    iPoseProof (eoi_08 with "Htext") as "Hi08".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x08)) (mword_of_int 4 : mword 6) Rs2
              R1 (K - 8)%nat v4 eb with "Hcg Hpc Hi08 Hr32").
    iIntros (CID5 Hs5) "Hcg Hpc Hr32".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.end_op + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    clear Hpp0a.
    assert (HR1ra : (R1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s0 : (R1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s1 : (R1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (HR1s2 : (R1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]).
    iAssert (eo_frame4 m) with "[Hr56 Hr48 Hr40 Hr32]" as "Hframe".
    { rewrite /eo_frame4.
      iEval (rewrite Hb1; rgne; rewrite HR1ra) in "Hr56".
      clear HR1ra.
      iEval (rewrite Hb2; rgne; rewrite HR1s0) in "Hr48".
      clear HR1s0.
      iEval (rewrite Hb3; rgne; rewrite HR1s1) in "Hr40".
      clear HR1s1.
      iEval (rewrite Hb4; rgne; rewrite HR1s2) in "Hr32".
      clear HR1s2.
      iSplitL "Hr56"; [iExact "Hr56"|]. iSplitL "Hr48"; [iExact "Hr48"|].
      iSplitL "Hr40"; [iExact "Hr40"|]. iExact "Hr32". }
    (* the three lazily-saved slots and the untouched one *)
    assert (Hb5 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec (R1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite HspR1 Hpush. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iAssert (eo_frameJ m) with "[Hg24 Hg16 Hg8 Hg0]" as "Hjunk".
    { rewrite /eo_frameJ.
      iSplitL "Hg24"; [iExists v5; iExact "Hg24"|].
      iSplitL "Hg16"; [iExists v6; iExact "Hg16"|].
      iSplitL "Hg8";  [iExists v7; iExact "Hg8"|].
      iExists v8; iExact "Hg0". }
    (* ===== +0x0a c.addi4spn s0,sp,64 ===== *)
    iPoseProof (eoi_0a with "Htext") as "Hi0a".
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.end_op + 0x0a)) (Cregidx (mword_of_int 0))
              (mword_of_int 16 : mword 8) Rs0 R1 (K - 8)%nat eb
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a").
    iIntros (CID6 Hs6) "Hcg Hpc".
    pose (R2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (R1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 16 : mword 8))))]> R1).
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.end_op + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    clear Hpp0c.
    (* ===== +0x0c / +0x10 : s1 := &log ===== *)
    iPoseProof (eoi_0c with "Htext") as "Hi0c".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.end_op + 0x0c)) Rs1 (mword_of_int 30 : mword 20)
              R2 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c").
    iIntros (CID7 Hs7) "Hcg Hpc".
    pose (R3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (mword_of_int (KernelSyms.end_op + 0x0c) : mword 64)
                     (auipc_off (mword_of_int 30 : mword 20)))]> R2).
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x0c) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    clear Hpp10.
    iPoseProof (eoi_10 with "Htext") as "Hi10".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.end_op + 0x10)) Rs1 Rs1
              (mword_of_int 1736 : mword 12) R3 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi10").
    iIntros (CID8 Hs8) "Hcg Hpc".
    pose (R4 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (R3 !!! Regidx Rs1 : mword 64)
                     (sign_extend' 64 (mword_of_int 1736 : mword 12)))]> R3).
    assert (HR4s1 : R4 !!! Regidx Rs1 = log_addr).
    { rewrite /R4 upd_eq /R3 upd_eq. exact eo_reloc_log_0c. }
    assert (HR4sp : R4 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))).
    { rewrite /R4 upd_ne; [| vm_compute; discriminate].
      rewrite /R3 upd_ne; [| vm_compute; discriminate].
      rewrite /R2 upd_ne; [exact HspR1 | vm_compute; discriminate]. }
    assert (HR4thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              R4 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R4 upd_ne; [| regne]. rewrite /R3 upd_ne; [| regne].
      rewrite /R2 upd_ne; [| regne]. rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x10) : mword 64) 4
                    = mword_of_int (KernelSyms.end_op + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    clear Hpp14.
    (* ===== +0x14 c.mv a0,s1 ; +0x16 jal acquire ===== *)
    iPoseProof (eoi_14 with "Htext") as "Hi14".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.end_op + 0x14)) Ra0 Rs1
              R4 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14").
    iIntros (CID9 Hs9) "Hcg Hpc".
    pose (R5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget R4 Rs1))]> R4).
    assert (HR5a0 : R5 !!! Regidx Ra0 = log_addr).
    { rewrite /R5 upd_eq. rgne. rewrite HR4s1. apply add_vec_zero_l. }
    assert (HR5s1 : R5 !!! Regidx Rs1 = log_addr)
      by (rewrite /R5 upd_ne; [exact HR4s1 | vm_compute; discriminate]).
    assert (HR5sp : R5 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))
      by (rewrite /R5 upd_ne; [exact HR4sp | vm_compute; discriminate]).
    assert (HR5thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              R5 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R5 upd_ne; [| regne]. exact (HR4thr c Hcs N2 N8 N9 N18). }
    assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x14) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x16))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    clear Hpp16.
    iPoseProof (eoi_16 with "Htext") as "Hi16".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0x16)) Rra
              (mword_of_int 2084608 : mword 21) R5 (K - 8)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi16").
    iIntros (CID10 Hs10) "Hcg Hpc".
    pose (R6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.end_op + 0x16) : mword 64) 4)]> R5).
    assert (Htgt16 : add_vec (mword_of_int (KernelSyms.end_op + 0x16) : mword 64)
                       (sign_extend' 64 (mword_of_int 2084608 : mword 21))
                     = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt16) in "Hpc".
    clear Htgt16.
    assert (HR6a0 : R6 !!! Regidx Ra0 = log_addr)
      by (rewrite /R6 upd_ne; [exact HR5a0 | vm_compute; discriminate]).
    assert (HR6s1 : R6 !!! Regidx Rs1 = log_addr)
      by (rewrite /R6 upd_ne; [exact HR5s1 | vm_compute; discriminate]).
    assert (HR6ra : R6 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.end_op + 0x16) : mword 64) 4)
      by (rewrite /R6; apply upd_eq).
    assert (HR6sp : R6 !!! Regidx csp_rs1
                    = add_vec (m !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))
      by (rewrite /R6 upd_ne; [exact HR5sp | vm_compute; discriminate]).
    assert (HR6thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              R6 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /R6 upd_ne; [| regne]. exact (HR5thr c Hcs N2 N8 N9 N18). }
    iDestruct (cpu_own_transport CID CID10 0 eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID CID10 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CID10 eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CID) (CIDb := CID10)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    iApply (Acq.wp_acquire_sconf (ln_lk γ) "log"%string
              (log_res γ bn γfs cov logstart) R6 0%nat eb (proc_addr j) C
              (K - 8)%nat eb lks eo_noff0 ltac:(pose proof (eo_Klk K HK); lia)
              Hbelow
              with "Hcg Hcnt Htext Hpc [Hlock] Hpanic").
    { iEval (rewrite HR6a0). iExact "Hlock". }
    iIntros (CIDq Hsq ms macq) "%Hmsfacts Hcg Hpc %Hacq Htok HRres Hcnt Hpay".
    assert (Hpc1a : ret_pc (R6 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0x1a)).
    { rewrite HR6ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc1a) in "Hpc".
    clear Hpc1a.
    (* acquire does not itself thread the trap-CSR complement -- transport it
       across this crossing too, not just [Hcnt]. *)
    iDestruct (trap_csrs_ext_transport CID10 CIDq eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID10 CIDq eb (proc_addr j)
                 ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (eo_cont_shift (CIDa := CID10) (CIDb := CIDq)  j pidv dq m K eb C eb lks
                 ltac:(wp_next_chain) with "Hcont") as "Hcont".
    assert (Hqs1 : macq !!! Regidx Rs1 = log_addr)
      by (rewrite (callee_saved_lookup Hacq Rs1 ltac:(vm_compute; reflexivity)); exact HR6s1).
    assert (HqregsE : eo_regsE m macq).
    { rewrite /eo_regsE. split.
      - rewrite (callee_saved_lookup Hacq csp_rs1 ltac:(vm_compute; reflexivity)).
        exact HR6sp.
      - intros c Hcs N2 N8 N9 N18.
        rewrite (callee_saved_lookup Hacq c Hcs). exact (HR6thr c Hcs N2 N8 N9 N18). }
    (* ================= THE ACCOUNTING CRITICAL SECTION ================= *)
    rewrite /log_res.
    iDestruct "HRres" as (out cmt nc om Ep Xr)
      "(Houtc & Hcmtc & Hncc & Hoauth & %Hsz & %Hbnd & %Hout3 & %Hcmt0 & Hepa & %Hepos & Hxa & %Hlive & %Hcap & Hrest)".
    iDestruct (log_op_positive with "Hoauth Hop") as %Hpos.
    (* the "log.committing" PANIC IS DEAD: an op token forces out >= 1, and
       log_res's own conjunct then refutes committing. *)
    destruct cmt.
    { exfalso. specialize (Hcmt0 eq_refl). lia. }
    iDestruct "Hrest" as (nl LB) "(%Hsum & %Hsub & %Hreg & Hbatch)".
    iMod (log_end_step with "Hoauth Hop") as (i0 Sb0 e00) "(%Hi0 & Hoauth)".
    assert (Hszd : size (delete i0 om) = (out - 1)%nat).
    { rewrite map_size_delete Hi0 Hsz. symmetry. apply Nat.sub_1_r. }
    assert (Hbndd : forall i e, delete i0 om !! i = Some e -> (e.1.1 <= MAXOPBLOCKS)%nat).
    { intros i e Hv. apply (Hbnd i e). rewrite lookup_delete_Some in Hv.
      exact (proj2 Hv). }
    (* DELETING an entry only shrinks the map, so every surviving op's
       credit clause is the one it already had *)
    assert (Hsubd : forall i e, delete i0 om !! i = Some e -> e.1.2 ⊆ LB).
    { intros i e Hv. apply (Hsub i e). rewrite lookup_delete_Some in Hv.
      exact (proj2 Hv). }
    (* ...and so is its birth epoch: retiring an op cannot re-date another *)
    assert (Hlived : forall i e, delete i0 om !! i = Some e -> e.2 = Ep).
    { intros i e Hv. apply (Hlive i e). rewrite lookup_delete_Some in Hv.
      exact (proj2 Hv). }
    assert (Hsumd : (nl + op_sum (delete i0 om) <= LOGBLOCKS)%nat).
    { pose proof (op_sum_delete om i0 (u, Sb0, e00) Hi0) as Hd. cbn in Hd. lia. }
    assert (Hout3d : ((out - 1) <= 3)%nat) by lia.
    assert (Hout1 : (1 <= out)%nat) by lia.
    iPoseProof (eoi_26 with "Htext") as "Hi26".
    (* ===== +0x1a c.lw a5,28(s1) : a5 := log.outstanding ===== *)
    assert (Houta : add_vec (rget macq Rs1) (sign_extend' 64 (mword_of_int 28 : mword 12))
                    = l_out).
    { rgne. rewrite Hqs1. exact eo_addr_out. }
    iEval (rewrite -Houta) in "Houtc".
    iPoseProof (eoi_1a with "Htext") as "Hi1a".
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.end_op + 0x1a)) Ra5 Rs1
              (mword_of_int 28 : mword 12) macq (trap_res eb + (K - 8))%nat
              (mword_of_int (Z.of_nat out) : mword 32) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1a Houtc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Houtc".
    iEval (rewrite Houta) in "Houtc".
    pose (T1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat out) : mword 32))]> macq).
    assert (HT1a5 : T1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat out) : mword 64))
      by (rewrite /T1 upd_eq; exact (eo_out_sext out Hout3)).
    assert (HT1s1 : T1 !!! Regidx Rs1 = log_addr)
      by (rewrite /T1 upd_ne; [exact Hqs1 | vm_compute; discriminate]).
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.end_op + 0x1a) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    clear Hpp1c.
    (* ===== +0x1c c.addiw a5,a5,-1 ===== *)
    assert (Hwv1c : sign_extend' 64 (subrange_vec_dec
                      (add_vec (rget T1 Ra5)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0)
                    = (mword_of_int (Z.of_nat (out - 1)) : mword 64)).
    { rgne. rewrite HT1a5. exact (eo_dec out Hout1 Hout3). }
    iPoseProof (eoi_1c with "Htext") as "Hi1c".
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.end_op + 0x1c)) Ra5
              (mword_of_int 63 : mword 6) T1 (trap_res eb + (K - 8))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hwv1c) in "Hcg".
    clear Hwv1c.
    pose (T2 := <[Regidx Ra5 := regval_into_reg
                  (mword_of_int (Z.of_nat (out - 1)) : mword 64)]> T1).
    assert (HT2a5 : T2 !!! Regidx Ra5 = (mword_of_int (Z.of_nat (out - 1)) : mword 64))
      by (rewrite /T2; apply upd_eq).
    assert (HT2s1 : T2 !!! Regidx Rs1 = log_addr)
      by (rewrite /T2 upd_ne; [exact HT1s1 | vm_compute; discriminate]).
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.end_op + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x1e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    clear Hpp1e.
    (* ===== +0x1e c.mv s2,a5 ===== *)
    iPoseProof (eoi_1e with "Htext") as "Hi1e".
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.end_op + 0x1e)) Rs2 Ra5
              T2 (trap_res eb + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1e").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    pose (T3 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (rget T2 Ra5))]> T2).
    assert (HT3s2 : T3 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (out - 1)) : mword 64)).
    { rewrite /T3 upd_eq. rgne. rewrite HT2a5. apply add_vec_zero_l. }
    assert (HT3a5 : T3 !!! Regidx Ra5 = (mword_of_int (Z.of_nat (out - 1)) : mword 64))
      by (rewrite /T3 upd_ne; [exact HT2a5 | vm_compute; discriminate]).
    assert (HT3s1 : T3 !!! Regidx Rs1 = log_addr)
      by (rewrite /T3 upd_ne; [exact HT2s1 | vm_compute; discriminate]).
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    clear Hpp20.
    (* ===== +0x20 c.sw a5,28(s1) : log.outstanding := out - 1 ===== *)
    assert (Houta2 : add_vec (rget T3 Rs1) (sign_extend' 64 (mword_of_int 28 : mword 12))
                     = l_out).
    { rgne. rewrite HT3s1. exact eo_addr_out. }
    iEval (rewrite -Houta2) in "Houtc".
    iPoseProof (eoi_20 with "Htext") as "Hi20".
    iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.end_op + 0x20)) Ra5 Rs1
              (mword_of_int 28 : mword 12) T3 (trap_res eb + (K - 8))%nat
              (mword_of_int (Z.of_nat out) : mword 32) false
              with "Hcg Hpc Hi20 Houtc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Houtc".
    iEval (rewrite Houta2) in "Houtc".
    assert (Hsv20 : trunc32 (rget T3 Ra5) = (mword_of_int (Z.of_nat (out - 1)) : mword 32)).
    { rgne. rewrite HT3a5. exact (eo_dec32 out Hout1 Hout3). }
    iEval (rewrite Hsv20) in "Houtc".
    clear Hsv20.
    assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x20) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    clear Hpp22.
    (* ===== +0x22 c.lw a5,32(s1) : a5 := log.committing (= 0) ===== *)
    assert (Hcmta : add_vec (rget T3 Rs1) (sign_extend' 64 (mword_of_int 32 : mword 12))
                    = l_cmt).
    { rgne. rewrite HT3s1. exact eo_addr_cmt. }
    iEval (rewrite -Hcmta) in "Hcmtc".
    iPoseProof (eoi_22 with "Htext") as "Hi22".
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.end_op + 0x22)) Ra5 Rs1
              (mword_of_int 32 : mword 12) T3 (trap_res eb + (K - 8))%nat
              (mword_of_int 0 : mword 32) false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi22 Hcmtc").
    iApply wp_next_off_intro. iIntros "Hcg Hpc Hcmtc".
    iEval (rewrite Hcmta) in "Hcmtc".
    pose (T4 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int 0 : mword 32))]> T3).
    assert (HT4a5 : T4 !!! Regidx Ra5 = sign_extend' 64 (mword_of_int 0 : mword 32))
      by (rewrite /T4; apply upd_eq).
    assert (HT4s2 : T4 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (out - 1)) : mword 64))
      by (rewrite /T4 upd_ne; [exact HT3s2 | vm_compute; discriminate]).
    assert (HT4s1 : T4 !!! Regidx Rs1 = log_addr)
      by (rewrite /T4 upd_ne; [exact HT3s1 | vm_compute; discriminate]).
    assert (HT4sp : T4 !!! Regidx csp_rs1 = (macq !!! Regidx csp_rs1 : mword 64)).
    { rewrite /T4 upd_ne; [| vm_compute; discriminate].
      rewrite /T3 upd_ne; [| vm_compute; discriminate].
      rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HT4thr : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
              T4 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs N2 N8 N9 N18.
      rewrite /T4 upd_ne; [| regne]. rewrite /T3 upd_ne; [| regne].
      rewrite /T2 upd_ne; [| regne]. rewrite /T1 upd_ne; [| regne].
      exact (proj2 HqregsE c Hcs N2 N8 N9 N18). }
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x22) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x24))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    clear Hpp24.
    (* ===== +0x24 c.bnez a5 -> +0x68 : the panic arm, NOT taken ===== *)
    assert (Hnz24 : neq_vec (rget T4 Ra5) (zero_reg : mword 64) = false).
    { rgne. rewrite HT4a5. exact eo_neqz0. }
    iPoseProof (eoi_24 with "Htext") as "Hi24".
    iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.end_op + 0x24))
              (mword_of_int 34 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              T4 (trap_res eb + (K - 8))%nat false ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate) Hnz24 with "Hcg Hpc Hi24").
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x24) : mword 64) 2
                    = mword_of_int (KernelSyms.end_op + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp26) in "Hpc".
    clear Hpp26.
    (* ===== +0x26 bnez s2 -> +0x7a : the two arms ===== *)
    destruct (decide ((out - 1)%nat = 0%nat)) as [Hzero|Hnzero].
    - (* ---- THE COMMIT ARM: outstanding hit zero ---- *)
      assert (Hnz26 : neq_vec (rget T4 Rs2) (zero_reg : mword 64) = false).
      { rgne. rewrite HT4s2 (eo_neq0 (out - 1)%nat Hout3d) Hzero. reflexivity. }
      iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KernelSyms.end_op + 0x26))
                (mword_of_int 84 : mword 13) Rs2 T4 (trap_res eb + (K - 8))%nat false
                ltac:(vm_compute; discriminate) Hnz26 with "Hcg Hpc Hi26").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.end_op + 0x26) : mword 64) 4
                      = mword_of_int (KernelSyms.end_op + 0x2a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      clear Hpp2a.
      iPoseProof (eoi_3e with "Htext") as "Hi3e".
      (* ===== +0x2a / +0x2e : s1 := &log (again) ===== *)
      iPoseProof (eoi_2a with "Htext") as "Hi2a".
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.end_op + 0x2a)) Rs1 (mword_of_int 30 : mword 20)
                T4 (trap_res eb + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2a").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      pose (U1 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (mword_of_int (KernelSyms.end_op + 0x2a) : mword 64)
                       (auipc_off (mword_of_int 30 : mword 20)))]> T4).
      assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.end_op + 0x2a) : mword 64) 4
                      = mword_of_int (KernelSyms.end_op + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      clear Hpp2e.
      iPoseProof (eoi_2e with "Htext") as "Hi2e".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.end_op + 0x2e)) Rs1 Rs1
                (mword_of_int 1706 : mword 12) U1 (trap_res eb + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi2e").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      pose (U2 := <[Regidx Rs1 := regval_into_reg
                    (add_vec (U1 !!! Regidx Rs1 : mword 64)
                       (sign_extend' 64 (mword_of_int 1706 : mword 12)))]> U1).
      assert (HU2s1 : U2 !!! Regidx Rs1 = log_addr).
      { rewrite /U2 upd_eq /U1 upd_eq. exact eo_reloc_log_2a. }
      assert (HU2s2 : U2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (out - 1)) : mword 64)).
      { rewrite /U2 upd_ne; [| vm_compute; discriminate].
        rewrite /U1 upd_ne; [exact HT4s2 | vm_compute; discriminate]. }
      assert (HU2sp : U2 !!! Regidx csp_rs1 = (macq !!! Regidx csp_rs1 : mword 64)).
      { rewrite /U2 upd_ne; [| vm_compute; discriminate].
        rewrite /U1 upd_ne; [exact HT4sp | vm_compute; discriminate]. }
      assert (HU2thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
                U2 !!! Regidx c = (m !!! Regidx c : mword 64)).
      { intros c Hcs N2 N8 N9 N18.
        rewrite /U2 upd_ne; [| regne]. rewrite /U1 upd_ne; [| regne].
        exact (HT4thr c Hcs N2 N8 N9 N18). }
      assert (Hpp32 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x2e) : mword 64) 4
                      = mword_of_int (KernelSyms.end_op + 0x32))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp32) in "Hpc".
      clear Hpp32.
      (* ===== +0x32 c.li a5,1 ; +0x34 c.sw a5,32(s1) : committing := 1 ===== *)
      iPoseProof (eoi_32 with "Htext") as "Hi32".
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.end_op + 0x32)) Ra5 (mword_of_int 1 : mword 6)
                (mword_of_int 1 : mword 64) U2 (trap_res eb + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok) eo_li1
                with "Hcg Hpc Hi32").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      pose (U3 := <[Regidx Ra5 := regval_into_reg (mword_of_int 1 : mword 64)]> U2).
      assert (HU3a5 : U3 !!! Regidx Ra5 = (mword_of_int 1 : mword 64))
        by (rewrite /U3; apply upd_eq).
      assert (HU3s1 : U3 !!! Regidx Rs1 = log_addr)
        by (rewrite /U3 upd_ne; [exact HU2s1 | vm_compute; discriminate]).
      assert (HU3s2 : U3 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (out - 1)) : mword 64))
        by (rewrite /U3 upd_ne; [exact HU2s2 | vm_compute; discriminate]).
      assert (HU3sp : U3 !!! Regidx csp_rs1 = (macq !!! Regidx csp_rs1 : mword 64))
        by (rewrite /U3 upd_ne; [exact HU2sp | vm_compute; discriminate]).
      assert (HU3thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
                U3 !!! Regidx c = (m !!! Regidx c : mword 64)).
      { intros c Hcs N2 N8 N9 N18.
        rewrite /U3 upd_ne; [| regne]. exact (HU2thr c Hcs N2 N8 N9 N18). }
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x32) : mword 64) 2
                      = mword_of_int (KernelSyms.end_op + 0x34))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      clear Hpp34.
      assert (Hcmta2 : add_vec (rget U3 Rs1) (sign_extend' 64 (mword_of_int 32 : mword 12))
                       = l_cmt).
      { rgne. rewrite HU3s1. exact eo_addr_cmt. }
      iEval (rewrite -Hcmta2) in "Hcmtc".
      iPoseProof (eoi_34 with "Htext") as "Hi34".
      iApply (wp_csw_s_sconf (mword_of_int (KernelSyms.end_op + 0x34)) Ra5 Rs1
                (mword_of_int 32 : mword 12) U3 (trap_res eb + (K - 8))%nat
                (mword_of_int 0 : mword 32) false
                with "Hcg Hpc Hi34 Hcmtc").
      iApply wp_next_off_intro. iIntros "Hcg Hpc Hcmtc".
      iEval (rewrite Hcmta2) in "Hcmtc".
      assert (Hsv34 : trunc32 (rget U3 Ra5) = (mword_of_int 1 : mword 32)).
      { rgne. rewrite HU3a5. exact eo_trunc1. }
      iEval (rewrite Hsv34) in "Hcmtc".
      clear Hsv34.
      (* ---- the batch is CHECKED OUT and log_res re-closed at cmt = true ---- *)
      iAssert (log_res γ bn γfs cov logstart)
        with "[Houtc Hcmtc Hncc Hoauth Hepa Hxa]" as "HRres".
      { rewrite /log_res. iExists (out - 1)%nat, true, nc, (delete i0 om), Ep, Xr.
        iSplitL "Houtc"; [iExact "Houtc"|].
        iSplitL "Hcmtc"; [iExact "Hcmtc"|].
        iSplitL "Hncc"; [iExact "Hncc"|].
        iSplitL "Hoauth"; [iExact "Hoauth"|].
        iSplitR; [iPureIntro; exact Hszd|].
        iSplitR; [iPureIntro; exact Hbndd|].
        iSplitR; [iPureIntro; exact Hout3d|].
        iSplitR; [iPureIntro; intros _; exact Hzero|].
        (* the batch is checked out but the EPOCH does not move here -- the
           bump belongs to the re-deposit, where om is provably empty *)
        iSplitL "Hepa"; [iExact "Hepa"|].
        iSplitR; [iPureIntro; exact Hepos|].
        iSplitL "Hxa"; [iExact "Hxa"|].
        iSplitR; [iPureIntro; exact Hlived|].
        iSplitR; [iPureIntro; exact Hcap|]. done. }
      assert (Hpp36 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x34) : mword 64) 2
                      = mword_of_int (KernelSyms.end_op + 0x36))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp36) in "Hpc".
      clear Hpp36.
      (* ===== +0x36 c.mv a0,s1 ; +0x38 jal release ===== *)
      iPoseProof (eoi_36 with "Htext") as "Hi36".
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.end_op + 0x36)) Ra0 Rs1
                U3 (trap_res eb + (K - 8))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi36").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      pose (U4 := <[Regidx Ra0 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (rget U3 Rs1))]> U3).
      assert (HU4a0 : U4 !!! Regidx Ra0 = log_addr).
      { rewrite /U4 upd_eq. rgne. rewrite HU3s1. apply add_vec_zero_l. }
      assert (HU4s1 : U4 !!! Regidx Rs1 = log_addr)
        by (rewrite /U4 upd_ne; [exact HU3s1 | vm_compute; discriminate]).
      assert (HU4s2 : U4 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (out - 1)) : mword 64))
        by (rewrite /U4 upd_ne; [exact HU3s2 | vm_compute; discriminate]).
      assert (HU4sp : U4 !!! Regidx csp_rs1 = (macq !!! Regidx csp_rs1 : mword 64))
        by (rewrite /U4 upd_ne; [exact HU3sp | vm_compute; discriminate]).
      assert (HU4thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
                U4 !!! Regidx c = (m !!! Regidx c : mword 64)).
      { intros c Hcs N2 N8 N9 N18.
        rewrite /U4 upd_ne; [| regne]. exact (HU3thr c Hcs N2 N8 N9 N18). }
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x36) : mword 64) 2
                      = mword_of_int (KernelSyms.end_op + 0x38))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      clear Hpp38.
      iPoseProof (eoi_38 with "Htext") as "Hi38".
      iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.end_op + 0x38)) Rra
                (mword_of_int 2084710 : mword 21) U4 (trap_res eb + (K - 8))%nat false
                ltac:(vm_compute; discriminate) ltac:(rdok)
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi38").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      pose (U5 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KernelSyms.end_op + 0x38) : mword 64) 4)]> U4).
      assert (Htgt38 : add_vec (mword_of_int (KernelSyms.end_op + 0x38) : mword 64)
                         (sign_extend' 64 (mword_of_int 2084710 : mword 21))
                       = mword_of_int KernelSyms.release)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt38) in "Hpc".
      clear Htgt38.
      assert (HU5a0 : U5 !!! Regidx Ra0 = log_addr)
        by (rewrite /U5 upd_ne; [exact HU4a0 | vm_compute; discriminate]).
      assert (HU5ra : U5 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KernelSyms.end_op + 0x38) : mword 64) 4)
        by (rewrite /U5; apply upd_eq).
      assert (HU5s1 : U5 !!! Regidx Rs1 = log_addr)
        by (rewrite /U5 upd_ne; [exact HU4s1 | vm_compute; discriminate]).
      assert (HU5s2 : U5 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (out - 1)) : mword 64))
        by (rewrite /U5 upd_ne; [exact HU4s2 | vm_compute; discriminate]).
      assert (HU5sp : U5 !!! Regidx csp_rs1 = (macq !!! Regidx csp_rs1 : mword 64))
        by (rewrite /U5 upd_ne; [exact HU4sp | vm_compute; discriminate]).
      assert (HU5thr : forall c : mword 5, is_cs_idx c = true ->
                c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 ->
                U5 !!! Regidx c = (m !!! Regidx c : mword 64)).
      { intros c Hcs N2 N8 N9 N18.
        rewrite /U5 upd_ne; [| regne]. exact (HU4thr c Hcs N2 N8 N9 N18). }
      iApply (Rel.wp_release_sconf (ln_lk γ) log_addr "log"%string
                (log_res γ bn γfs cov logstart) U5 0%nat eb (proc_addr j) C (K - 8)%nat
                ({[lock_rank "log"]} ∪ lks)
                ltac:(rewrite HU5a0; rewrite /log_addr; apply bv_eq; vm_compute; reflexivity)
                ltac:(pose proof (eo_Klk K HK); lia)
                with "Hcg Htext Hpc [Hlock] Htok HRres Hcnt Hpay").
      { iExact "Hlock". }
      iIntros (CIDr Hsr mr) "Hcg Hpc %Hrel Hcnt".
      assert (Hsetback : ({[lock_rank "log"]} ∪ lks) ∖ {[lock_rank "log"]} = lks)
        by (apply locks_add_del; assumption).
      iEval (rewrite Hsetback) in "Hcnt".
      assert (Hpc3c : ret_pc (U5 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.end_op + 0x3c)).
      { rewrite HU5ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc3c) in "Hpc".
      clear Hpc3c.
      (* release does not itself thread the trap-CSR complement either. *)
      iDestruct (trap_csrs_ext_transport CIDq CIDr eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDq CIDr eb (proc_addr j)
                   ltac:(wp_next_chain) with "Hextm") as "Hextm".
      assert (Hrs1 : mr !!! Regidx Rs1 = log_addr)
        by (rewrite (callee_saved_lookup Hrel Rs1 ltac:(vm_compute; reflexivity)); exact HU5s1).
      assert (Hrs2 : mr !!! Regidx Rs2 = (mword_of_int (Z.of_nat (out - 1)) : mword 64))
        by (rewrite (callee_saved_lookup Hrel Rs2 ltac:(vm_compute; reflexivity)); exact HU5s2).
      assert (HrregsE : eo_regsE m mr).
      { rewrite /eo_regsE. split.
        - rewrite (callee_saved_lookup Hrel csp_rs1 ltac:(vm_compute; reflexivity)).
          rewrite HU5sp. exact (proj1 HqregsE).
        - intros c Hcs N2 N8 N9 N18.
          rewrite (callee_saved_lookup Hrel c Hcs). exact (HU5thr c Hcs N2 N8 N9 N18). }
      iDestruct (eo_cont_shift (CIDa := CIDq) (CIDb := CIDr)  j pidv dq m K eb C eb lks
                   ltac:(wp_next_chain) with "Hcont") as "Hcont".
      (* ---- the batch, opened for the commit body ---- *)
      iDestruct (eo_open_of_batch with "Hbatch") as (W L D)
        "(%Hshape & %Hnd & %Hwok & Hmirc & Hopen)".
      pose proof Hshape as [HnW Hn30].
      rewrite /eo_open.
      iDestruct "Hopen" as
        "(Hncell & HW & Hjnk & HauthL & HauthD & Hcov & Hhdr & Hdone & Hrest & Hpool)".
      (* ===== +0x3c c.lw a5,44(s1) : a5 := log.lh.n ===== *)
      assert (Hlhna : add_vec (rget mr Rs1) (sign_extend' 64 (mword_of_int 44 : mword 12))
                      = lh_n_pa).
      { rgne. rewrite Hrs1. exact eo_addr_lhn. }
      iEval (rewrite -Hlhna) in "Hncell".
      iPoseProof (eoi_3c with "Htext") as "Hi3c".
      iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.end_op + 0x3c)) Ra5 Rs1
                (mword_of_int 44 : mword 12) mr (K - 8)%nat
                (mword_of_int (Z.of_nat nl) : mword 32) eb
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3c Hncell").
      iIntros (CIDs1 Hss1) "Hcg Hpc Hncell".
      iEval (rewrite Hlhna) in "Hncell".
      pose (V1 := <[Regidx Ra5 := regval_into_reg
                    (sign_extend' 64 (mword_of_int (Z.of_nat nl) : mword 32))]> mr).
      assert (HV1a5 : V1 !!! Regidx Ra5 = (mword_of_int (Z.of_nat nl) : mword 64))
        by (rewrite /V1 upd_eq; apply eo_sext32; exact (eo_n_small nl Hn30)).
      assert (HV1s2 : V1 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (out - 1)) : mword 64))
        by (rewrite /V1 upd_ne; [exact Hrs2 | vm_compute; discriminate]).
      assert (HV1regsE : eo_regsE m V1).
      { rewrite /eo_regsE. split.
        - rewrite /V1 upd_ne; [exact (proj1 HrregsE) | vm_compute; discriminate].
        - intros c Hcs N2 N8 N9 N18.
          rewrite /V1 upd_ne; [| regne]. exact (proj2 HrregsE c Hcs N2 N8 N9 N18). }
      assert (Hpp3e : add_vec_int (mword_of_int (KernelSyms.end_op + 0x3c) : mword 64) 2
                      = mword_of_int (KernelSyms.end_op + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3e) in "Hpc".
      clear Hpp3e.
      iAssert (eo_open bn γfs cov logstart nl W L D (fun _ => []) 0)
        with "[Hncell HW Hjnk HauthL HauthD Hcov Hhdr Hdone Hrest Hpool]" as "Hopen".
      { rewrite /eo_open.
        iSplitL "Hncell"; [iExact "Hncell"|]. iSplitL "HW"; [iExact "HW"|].
        iSplitL "Hjnk"; [iExact "Hjnk"|]. iSplitL "HauthL"; [iExact "HauthL"|].
        iSplitL "HauthD"; [iExact "HauthD"|]. iSplitL "Hcov"; [iExact "Hcov"|].
        iSplitL "Hhdr"; [iExact "Hhdr"|]. iSplitL "Hdone"; [iExact "Hdone"|].
        iSplitL "Hrest"; [iExact "Hrest"|]. iExact "Hpool". }
      (* ===== +0x3e bgtz a5 -> +0x9e ===== *)
      destruct (decide (nl = 0%nat)) as [Hn0|Hnpos].
      + (* n = 0: the whole commit body is skipped *)
        assert (Hcmp : zopz0zI_s (zero_reg : mword 64) (rget V1 Ra5) = false).
        { rgne. rewrite HV1a5 (eo_lt_s0 (Z.of_nat nl) (eo_n_small nl Hn30)).
          apply Z.ltb_ge. lia. }
        iApply (wp_bgtz_fall_s_sconf (mword_of_int (KernelSyms.end_op + 0x3e))
                  (mword_of_int 96 : mword 13) Ra5 V1 (K - 8)%nat eb
                  ltac:(vm_compute; discriminate) Hcmp with "Hcg Hpc Hi3e").
        iIntros (CIDs2 Hss2) "Hcg Hpc".
        assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x3e) : mword 64) 4
                        = mword_of_int (KernelSyms.end_op + 0x42))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp42) in "Hpc".
        clear Hpp42.
        assert (HW0 : W = []).
        { apply nil_length_inv. lia. }
        subst W. subst nl.
        iDestruct (cpu_own_transport CIDr CIDs2 0 eb (proc_addr j) C eb
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CIDr CIDs2 eb (proc_addr j)
                     ltac:(wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CIDr CIDs2 eb (proc_addr j)
                     ltac:(wp_next_chain) with "Hextm") as "Hextm".
        iDestruct (eo_cont_shift (CIDa := CIDr) (CIDb := CIDs2)  j pidv dq m K eb C eb lks
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iDestruct (eo_open_to_batch with "Hmirc Hopen") as "Hbatch".
        iApply (eo_tail (CID0 := CIDs2)  γs j γl bn γ γfs cov logstart dev pidv dq
                  m V1 K eb C lks HK HV1regsE Hbelow
                  with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hlctx Hprocs Hppid
                        Hframe Hjunk Hbatch Hcont").
      + (* n > 0: save s3/s4/s5, set up the cursors, and run the copy loop *)
        assert (Hcmp : zopz0zI_s (zero_reg : mword 64) (rget V1 Ra5) = true).
        { rgne. rewrite HV1a5 (eo_lt_s0 (Z.of_nat nl) (eo_n_small nl Hn30)).
          apply Z.ltb_lt. lia. }
        iApply (wp_bgtz_taken_s_sconf (mword_of_int (KernelSyms.end_op + 0x3e))
                  (mword_of_int 96 : mword 13) Ra5 V1 (K - 8)%nat eb
                  ltac:(vm_compute; discriminate) Hcmp ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi3e").
        iApply bi.later_intro. iIntros (CIDs2 Hss2) "Hcg Hpc".
        assert (Htgt3e : add_vec (mword_of_int (KernelSyms.end_op + 0x3e) : mword 64)
                           (sign_extend' 64 (mword_of_int 96 : mword 13))
                         = mword_of_int (KernelSyms.end_op + 0x9e))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt3e) in "Hpc".
        clear Htgt3e.
        pose proof HV1regsE as (HV1sp & HV1thr).
        assert (Hpush2 : add_vec (m !!! Regidx csp_rs1 : mword 64)
                           (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)))
                         = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
        { unfold pa_stk, add_vec_int. apply f_equal.
          apply bv_eq; vm_compute; reflexivity. }
        assert (Hd5 : add_vec (V1 !!! Regidx csp_rs1 : mword 64)
                        (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                      = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
        { rewrite HV1sp Hpush2. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
          f_equal; try (apply bv_eq; vm_compute; reflexivity). }
        assert (Hd6 : add_vec (V1 !!! Regidx csp_rs1 : mword 64)
                        (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                      = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
        { rewrite HV1sp Hpush2. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
          f_equal; try (apply bv_eq; vm_compute; reflexivity). }
        assert (Hd7 : add_vec (V1 !!! Regidx csp_rs1 : mword 64)
                        (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                      = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
        { rewrite HV1sp Hpush2. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
          f_equal; try (apply bv_eq; vm_compute; reflexivity). }
        rewrite /eo_frameJ.
        iDestruct "Hjunk" as "(Hg24 & Hg16 & Hg8 & Hg0)".
        iDestruct "Hg24" as (u5) "Hg24". iDestruct "Hg16" as (u6) "Hg16".
        iDestruct "Hg8" as (u7) "Hg8".
        iEval (rewrite -Hd5) in "Hg24". iEval (rewrite -Hd6) in "Hg16".
        iEval (rewrite -Hd7) in "Hg8".
        (* ===== +0x9e / +0xa0 / +0xa2 : the lazy saves ===== *)
        iPoseProof (eoi_9e with "Htext") as "Hi9e".
        iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.end_op + 0x9e)) (mword_of_int 3 : mword 6) Rs3
                  V1 (K - 8)%nat u5 eb with "Hcg Hpc Hi9e Hg24").
        iIntros (CIDs3 Hss3) "Hcg Hpc Hg24".
        iEval (rewrite Hd5) in "Hg24".
        assert (Hppa0 : add_vec_int (mword_of_int (KernelSyms.end_op + 0x9e) : mword 64) 2
                        = mword_of_int (KernelSyms.end_op + 0xa0))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppa0) in "Hpc".
        clear Hppa0.
        iPoseProof (eoi_a0 with "Htext") as "Hia0".
        iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.end_op + 0xa0)) (mword_of_int 2 : mword 6) Rs4
                  V1 (K - 8)%nat u6 eb with "Hcg Hpc Hia0 Hg16").
        iIntros (CIDs4 Hss4) "Hcg Hpc Hg16".
        iEval (rewrite Hd6) in "Hg16".
        assert (Hppa2 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xa0) : mword 64) 2
                        = mword_of_int (KernelSyms.end_op + 0xa2))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppa2) in "Hpc".
        clear Hppa2.
        iPoseProof (eoi_a2 with "Htext") as "Hia2".
        iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.end_op + 0xa2)) (mword_of_int 1 : mword 6) Rs5
                  V1 (K - 8)%nat u7 eb with "Hcg Hpc Hia2 Hg8").
        iIntros (CIDs5 Hss5) "Hcg Hpc Hg8".
        iEval (rewrite Hd7) in "Hg8".
        assert (Hs3v : (V1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
          by (apply HV1thr; eoidx).
        assert (Hs4v : (V1 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
          by (apply HV1thr; eoidx).
        assert (Hs5v : (V1 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64))
          by (apply HV1thr; eoidx).
        iAssert (eo_frameS m) with "[Hg24 Hg16 Hg8 Hg0]" as "HframeS".
        { rewrite /eo_frameS.
          iEval (rgne; rewrite Hs3v) in "Hg24".
          clear Hs3v.
          iEval (rgne; rewrite Hs4v) in "Hg16".
          clear Hs4v.
          iEval (rgne; rewrite Hs5v) in "Hg8".
          clear Hs5v.
          iSplitL "Hg24"; [iExact "Hg24"|]. iSplitL "Hg16"; [iExact "Hg16"|].
          iSplitL "Hg8"; [iExact "Hg8"|]. iExact "Hg0". }
        assert (Hppa4 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xa2) : mword 64) 2
                        = mword_of_int (KernelSyms.end_op + 0xa4))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppa4) in "Hpc".
        clear Hppa4.
        (* ===== +0xa4 / +0xa8 : s5 := &log.lh.block[0] ===== *)
        iPoseProof (eoi_a4 with "Htext") as "Hia4".
        iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.end_op + 0xa4)) Rs5 (mword_of_int 30 : mword 20)
                  V1 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hia4").
        iIntros (CIDs6 Hss6) "Hcg Hpc".
        pose (Y1 := <[Regidx Rs5 := regval_into_reg
                      (add_vec (mword_of_int (KernelSyms.end_op + 0xa4) : mword 64)
                         (auipc_off (mword_of_int 30 : mword 20)))]> V1).
        assert (Hppa8 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xa4) : mword 64) 4
                        = mword_of_int (KernelSyms.end_op + 0xa8))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppa8) in "Hpc".
        clear Hppa8.
        iPoseProof (eoi_a8 with "Htext") as "Hia8".
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.end_op + 0xa8)) Rs5 Rs5
                  (mword_of_int 1632 : mword 12) Y1 (K - 8)%nat eb
                  ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hia8").
        iIntros (CIDs7 Hss7) "Hcg Hpc".
        pose (Y2 := <[Regidx Rs5 := regval_into_reg
                      (add_vec (Y1 !!! Regidx Rs5 : mword 64)
                         (sign_extend' 64 (mword_of_int 1632 : mword 12)))]> Y1).
        assert (HY2s5 : Y2 !!! Regidx Rs5 = (lh_block 0 : mword 64)).
        { rewrite /Y2 upd_eq /Y1 upd_eq. exact eo_reloc_blk0. }
        assert (HY2s2 : Y2 !!! Regidx Rs2 = (mword_of_int (Z.of_nat (out - 1)) : mword 64)).
        { rewrite /Y2 upd_ne; [| vm_compute; discriminate].
          rewrite /Y1 upd_ne; [exact HV1s2 | vm_compute; discriminate]. }
        assert (Hppac : add_vec_int (mword_of_int (KernelSyms.end_op + 0xa8) : mword 64) 4
                        = mword_of_int (KernelSyms.end_op + 0xac))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppac) in "Hpc".
        clear Hppac.
        (* ===== +0xac / +0xb0 : s4 := &log ===== *)
        iPoseProof (eoi_ac with "Htext") as "Hiac".
        iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.end_op + 0xac)) Rs4 (mword_of_int 30 : mword 20)
                  Y2 (K - 8)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hiac").
        iIntros (CIDs8 Hss8) "Hcg Hpc".
        pose (Y3 := <[Regidx Rs4 := regval_into_reg
                      (add_vec (mword_of_int (KernelSyms.end_op + 0xac) : mword 64)
                         (auipc_off (mword_of_int 30 : mword 20)))]> Y2).
        assert (Hppb0 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xac) : mword 64) 4
                        = mword_of_int (KernelSyms.end_op + 0xb0))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppb0) in "Hpc".
        clear Hppb0.
        iPoseProof (eoi_b0 with "Htext") as "Hib0".
        iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.end_op + 0xb0)) Rs4 Rs4
                  (mword_of_int 1576 : mword 12) Y3 (K - 8)%nat eb
                  ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hib0").
        iIntros (CIDs9 Hss9) "Hcg Hpc".
        pose (Y4 := <[Regidx Rs4 := regval_into_reg
                      (add_vec (Y3 !!! Regidx Rs4 : mword 64)
                         (sign_extend' 64 (mword_of_int 1576 : mword 12)))]> Y3).
        assert (HY4s4 : Y4 !!! Regidx Rs4 = log_addr).
        { rewrite /Y4 upd_eq /Y3 upd_eq. exact eo_reloc_log_ac. }
        assert (HY4s5 : Y4 !!! Regidx Rs5 = (lh_block 0 : mword 64))
          by (rewrite /Y4 upd_ne; [exact HY2s5 | vm_compute; discriminate]).
        assert (HY4s2 : Y4 !!! Regidx Rs2 = (mword_of_int (Z.of_nat 0%nat) : mword 64)).
        { rewrite /Y4 upd_ne; [| vm_compute; discriminate].
          rewrite /Y3 upd_ne; [| vm_compute; discriminate].
          rewrite HY2s2 Hzero. reflexivity. }
        assert (HY4regs : eo_regs m Y4).
        { rewrite /eo_regs. split.
          - rewrite /Y4 upd_ne; [| vm_compute; discriminate].
            rewrite /Y3 upd_ne; [| vm_compute; discriminate].
            rewrite /Y2 upd_ne; [| vm_compute; discriminate].
            rewrite /Y1 upd_ne; [exact HV1sp | vm_compute; discriminate].
          - intros c Hcs N2 N8 N9 N18 N19 N20 N21.
            rewrite /Y4 upd_ne; [| regne]. rewrite /Y3 upd_ne; [| regne].
            rewrite /Y2 upd_ne; [| regne]. rewrite /Y1 upd_ne; [| regne].
            exact (HV1thr c Hcs N2 N8 N9 N18). }
        assert (Hppb4 : add_vec_int (mword_of_int (KernelSyms.end_op + 0xb0) : mword 64) 4
                        = mword_of_int (KernelSyms.end_op + 0xb4))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hppb4) in "Hpc".
        clear Hppb4.
        iDestruct (cpu_own_transport CIDr CIDs9 0 eb (proc_addr j) C eb
                     ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
        iDestruct (trap_csrs_ext_transport CIDr CIDs9 eb (proc_addr j)
                     ltac:(wp_next_chain) with "Hextc") as "Hextc".
        iDestruct (cpu_claim_ext_transport CIDr CIDs9 eb (proc_addr j)
                     ltac:(wp_next_chain) with "Hextm") as "Hextm".
        iDestruct (eo_cont_shift (CIDa := CIDr) (CIDb := CIDs9)  j pidv dq m K eb C eb lks
                     ltac:(wp_next_chain) with "Hcont") as "Hcont".
        iApply (eo_loop γs j γl γu γd γk pd pav pu bn γ γfs cov logstart dev
                  nl W D pidv dq m K eb C lks nl
                  HK Hgeom Hj Hgl (conj HnW Hn30) Hnd Hwok Hbelow
                  CIDs9 0%nat Y4 L (fun _ => []) ltac:(lia) ltac:(lia)
                  ltac:(intros i v Hi Hv; lia) HY4regs HY4s2 HY4s4 HY4s5
                  with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlctx Hseam Hregc Hppid Hprocs Hdevi Hdgeom Hdlock Hframe HframeS Hmirc
                        Hopen Hcont").
    - (* ---- THE FAST PATH: other operations are still open ---- *)
      assert (Hnz26 : neq_vec (rget T4 Rs2) (zero_reg : mword 64) = true).
      { rgne. rewrite HT4s2 (eo_neq0 (out - 1)%nat Hout3d).
        destruct (out - 1)%nat; [contradiction | reflexivity]. }
      (* the batch goes straight back in, at the decremented outstanding *)
      iAssert (log_res γ bn γfs cov logstart)
        with "[Houtc Hcmtc Hncc Hoauth Hepa Hxa Hbatch]" as "HRres".
      { rewrite /log_res. iExists (out - 1)%nat, false, nc, (delete i0 om), Ep, Xr.
        iSplitL "Houtc"; [iExact "Houtc"|].
        iSplitL "Hcmtc"; [iExact "Hcmtc"|].
        iSplitL "Hncc"; [iExact "Hncc"|].
        iSplitL "Hoauth"; [iExact "Hoauth"|].
        iSplitR; [iPureIntro; exact Hszd|].
        iSplitR; [iPureIntro; exact Hbndd|].
        iSplitR; [iPureIntro; exact Hout3d|].
        iSplitR; [iPureIntro; discriminate|].
        (* THE FAST PATH DOES NOT COMMIT, so the epoch stands: the other
           open ops' entries and every witness they hold stay live. *)
        iSplitL "Hepa"; [iExact "Hepa"|].
        iSplitR; [iPureIntro; exact Hepos|].
        iSplitL "Hxa"; [iExact "Hxa"|].
        iSplitR; [iPureIntro; exact Hlived|].
        iSplitR; [iPureIntro; exact Hcap|].
        iExists nl, LB. iSplitR; [iPureIntro; exact Hsumd|].
        iSplitR; [iPureIntro; exact Hsubd|].
        iSplitR; [iPureIntro; exact Hreg|]. iExact "Hbatch". }
      assert (HT4regsE : eo_regsE m T4).
      { rewrite /eo_regsE. split.
        - rewrite HT4sp. exact (proj1 HqregsE).
        - exact HT4thr. }
      iApply (wp_bnez_x0_taken_s_sconf (mword_of_int (KernelSyms.end_op + 0x26))
                (mword_of_int 84 : mword 13) Rs2 T4 (trap_res eb + (K - 8))%nat false
                ltac:(vm_compute; discriminate) Hnz26
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi26").
      iApply bi.later_intro. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htgt26 : add_vec (mword_of_int (KernelSyms.end_op + 0x26) : mword 64)
                         (sign_extend' 64 (mword_of_int 84 : mword 13))
                       = mword_of_int (KernelSyms.end_op + 0x7a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt26) in "Hpc".
      clear Htgt26.
      iApply (eo_fast (CID0 := CIDq)  γs j γl bn γ γfs cov logstart dev pidv dq
                m T4 K eb C lks HK HT4regsE Hbelow
                with "Hcg Hcnt Hpay Hextc Hextm Htok HRres Htext Hpc Hpanic Hlctx Hprocs Hppid Hframe Hjunk Hcont").
  Qed.

End ProofEndOp.

End EndOpProof.
