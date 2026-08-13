(* ProofInstallTrans.v -- install_trans over the SIE-agnostic sconf world.

     static void install_trans(int recovering) {
       for (int tail = 0; tail < log.lh.n; tail++) {
         struct buf *lbuf = bread(log.dev, log.start + tail + 1);
         struct buf *dbuf = bread(log.dev, log.lh.block[tail]);
         memmove(dbuf->data, lbuf->data, BSIZE);
         bwrite(dbuf);
         if (recovering == 0) bunpin(dbuf);
         brelse(lbuf);
         brelse(dbuf);
       }
     }

   THE SHAPE (CodeInstallTrans.v has the byte-exact disassembly).  gcc
   hoisted the [log.lh.n] test AHEAD of the prologue, so there are two
   return sites and the frame exists only on the loop path:

     it_epi    +0xb2..+0xc8   the ten-register epilogue and the return
     it_loop   +0x6c..+0xb0   the loop, by induction on the remaining
                              iterations; entry (and back edge) at +0x6c
     wp_..._sconf +0x00..+0x44  the pre-frame [blez] (whose taken arm is the
                              BARE [c.ret] at +0xca), the prologue, the six
                              register set-ups and the [c.j] into the loop

   THE STAGE-2 PREMISE [recovering = false \/ n = 0] splits exactly along
   that test: at n = 0 the function returns from +0xca having done
   nothing (W = [], every big-op empty, [dirty_clear D [] = D]), and every
   other instance has recovering = false, i.e. s6 = 0 -- which is what
   makes the printk block at +0x46 and the bunpin-skip at +0xa6 dead code
   on this path (both [bnez s6] fall through).  So printk is NOT a functor
   argument of this proof.

   THE PER-ITERATION GHOST STEP.  The loop invariant carries the write set
   SPLIT AT THE CURSOR: the entries before [tail] are already installed
   (their dirty halves at false), the rest still pending (at true), and the
   dirty authority sits at [dirty_clear D (map uint (take tail W))].  One
   iteration:

     1. bread(log slot) -- the handle's payload L-half against the batch's
        [fsblock (log_slot_bno logstart tail) (Lw tail)] pins its bytes to
        [Lw tail].  Its dirty flag is NOT needed: brelse takes either.
     2. bread(home) -- the payload's DIRTY half against the caller's half
        at true forces d = true (so the payload parks the pin's [bref]),
        and its L-half against the AUTHORITY ([it_pay_bs_auth], one
        [ghost_map_lookup]) pins the bytes to [L !! uint w], which the
        spec's pure premise identifies with [Lw tail].  There is no client
        [fsblock] for a home block on the committer's side -- see
        SpecInstallTrans.v's header.
     3. memmove copies [Lw tail] onto [Lw tail]: the destination bytes are
        unchanged AS A VALUE, which is what keeps the handle [bio_locked].
     4. [bio_held_split] + bwrite: the disk cell moves to [Lw tail].
     5. [FsBlocks.fs_dirty_flip] flips both halves true -> false, the
        [bref] falls out of the dirty arm, and the payload re-forms CLEAN
        (its ⌜bsd = bsl⌝ tie now holds -- disk = bytes = Lw tail).
     6. bunpin spends the [bref] and returns the slot unit: THAT is the
        [+1] per entry in the postcondition's [bslots bn (2 + length W)].
     7. brelse, brelse -- both handles are [bio_locked].

   A functor over BREAD / BWRITE / BUNPIN / BRELSE / MEMMOVE. *)
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
Require Import CodeInstallTrans.
Require Import SpecPanic.
Require Import SpecBread SpecBwrite SpecBunpin SpecBrelse SpecMemmove.
Require Import SpecInstallTrans.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* a whole-function WP goal is enormous; keep a failing tactic's error
   printable (claude-notes/durable-notes.md) *)
Set Printing Depth 40.


(* ===================================================================== *)
(*  Pure arithmetic, all over plain [Z]/[nat] so no solver ever runs      *)
(*  inside the WP context (the zify-hook rule in durable-notes).          *)
(* ===================================================================== *)

Lemma it_sext32 (z : Z) : (0 <= z < 2^31)%Z ->
  (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = mword_of_int z.
Proof.
  intro Hz. apply bv_eq.
  rewrite (sext64_moi32_unsigned z Hz) moi64_unsigned.
  symmetry. apply bvw64_small. lia.
Qed.

Lemma it_moi32_add (a b : Z) :
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

(* [addw rd,rd,rs2] at two small nonnegative literals *)
Lemma it_addw (a b : Z) :
  (0 <= a)%Z -> (0 <= b)%Z -> (a + b < 2^31)%Z ->
  sign_extend' 64 (add_vec (subrange_vec_dec (mword_of_int a : mword 64) 31 0 : mword 32)
                           (subrange_vec_dec (mword_of_int b : mword 64) 31 0 : mword 32))
  = (mword_of_int (a + b) : mword 64).
Proof.
  intros Ha Hb Hab.
  rewrite -!trunc32_subrange !trunc32_mword_of_int.
  rewrite (it_moi32_add a b Ha Hb ltac:(lia)).
  apply it_sext32. lia.
Qed.

(* [c.addiw rd,rd,1] at a small nonnegative literal *)
Lemma it_addiw (z : Z) : (0 <= z)%Z -> (z + 1 < 2^31)%Z ->
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
  rewrite HK (it_moi32_add z 1 Hz ltac:(lia) ltac:(lia)).
  apply it_sext32. lia.
Qed.

Lemma it_sint_moi (z : Z) :
  (- 2 ^ 63 <= z < 2 ^ 63)%Z -> sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  assert (Hhm : bv_half_modulus 64 = (2 ^ 63)%Z) by reflexivity.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned bv_swrap_wrap.
  apply bv_swrap_small. rewrite Hhm. lia.
Qed.

(* the two signed compares: [blez a5] at +0x08 and [bge s3,a5] at +0x68 *)
Lemma it_geb_s0 (b : Z) :
  (0 <= b < 2 ^ 31)%Z ->
  zopz0zKzJ_s (zero_reg : mword 64) (mword_of_int b : mword 64) = Z.geb 0 b.
Proof.
  intro Hb. unfold zopz0zKzJ_s.
  assert (Hz : sint (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite Hz (it_sint_moi b ltac:(lia)). reflexivity.
Qed.

Lemma it_geb_s (a b : Z) :
  (0 <= a < 2 ^ 31)%Z -> (0 <= b < 2 ^ 31)%Z ->
  zopz0zKzJ_s (mword_of_int a : mword 64) (mword_of_int b : mword 64) = Z.geb a b.
Proof.
  intros Ha Hb. unfold zopz0zKzJ_s.
  rewrite (it_sint_moi a ltac:(lia)) (it_sint_moi b ltac:(lia)). reflexivity.
Qed.

Lemma it_uint32 (a : mword 32) : uint a = bv_unsigned a.
Proof.
  pose proof (bv_unsigned_in_range _ a) as Hr.
  unfold uint, get_word, MachineWord.MachineWord.word_to_N.
  rewrite Z2N.id; [ reflexivity | lia ].
Qed.

Lemma it_uint_moi32 (z : Z) : (0 <= z < 2 ^ 32)%Z ->
  uint (mword_of_int z : mword 32) = z.
Proof. intro Hz. rewrite it_uint32. apply moi32_small. lia. Qed.

(* the [c.li]/[li] constants the set-up block forms *)
Lemma it_li0 : add_vec (zero_reg : mword 64)
                 (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))
               = (mword_of_int (Z.of_nat 0) : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma it_li1024 : add_vec (zero_reg : mword 64)
                    (sign_extend' 64 (mword_of_int 1024 : mword 12))
                  = (mword_of_int 1024 : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ---- the struct-log cell addresses the loop forms off s4 = &log ---- *)

Lemma it_addr_start : add_vec log_addr (sign_extend' 64 (mword_of_int 24 : mword 12)) = l_start.
Proof.
  rewrite /l_start /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma it_addr_dev : add_vec log_addr (sign_extend' 64 (mword_of_int 36 : mword 12)) = l_dev.
Proof.
  rewrite /l_dev /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma it_addr_lhn : add_vec log_addr (sign_extend' 64 (mword_of_int 44 : mword 12)) = lh_n_pa.
Proof.
  rewrite /lh_n_pa /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* the pre-frame load's own relocation: &log.lh.n off the +0x00 auipc *)
Lemma it_reloc_lhn :
  add_vec (add_vec (mword_of_int (KernelSyms.install_trans + 0x00) : mword 64)
                   (auipc_off (mword_of_int 31 : mword 20)))
          (sign_extend' 64 (mword_of_int 2276 : mword 12)) = lh_n_pa.
Proof.
  rewrite /lh_n_pa /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* s5's initial value: &log.lh.block[0] *)
Lemma it_reloc_blk0 :
  add_vec (add_vec (mword_of_int (KernelSyms.install_trans + 0x26) : mword 64)
                   (auipc_off (mword_of_int 31 : mword 20)))
          (sign_extend' 64 (mword_of_int 2242 : mword 12)) = lh_block 0.
Proof.
  rewrite /lh_block /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* s4's value: &log *)
Lemma it_reloc_log :
  add_vec (add_vec (mword_of_int (KernelSyms.install_trans + 0x38) : mword 64)
                   (auipc_off (mword_of_int 31 : mword 20)))
          (sign_extend' 64 (mword_of_int 2176 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

(* the cursor: [0(s5)] is &lh.block[i] itself, and [addi s5,s5,4] steps it *)
Lemma it_cursor_at (i : nat) :
  add_vec (lh_block i) (sign_extend' 64 (mword_of_int 0 : mword 12)) = lh_block i.
Proof.
  assert (H0 : sign_extend' 64 (mword_of_int 0 : mword 12)
               = (mword_of_int (Z.of_nat 0%nat) : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite /lh_block H0 pa_add_bump. f_equal. lia.
Qed.

Lemma it_cursor_step (i : nat) :
  add_vec (lh_block i) (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6)))
  = lh_block (S i).
Proof.
  assert (H4 : sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6))
               = (mword_of_int (Z.of_nat 4%nat) : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite /lh_block H4 pa_add_bump. f_equal. lia.
Qed.

(* [b->data] off the buffer pointer: the two memmove arguments *)
Lemma it_data_off (q : mword 64) :
  add_vec q (sign_extend' 64 (mword_of_int 88 : mword 12)) = b_data q.
Proof.
  assert (H88 : sign_extend' 64 (mword_of_int 88 : mword 12)
                = (mword_of_int (Z.of_nat 88%nat) : mword 64))
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite /b_data H88.
  assert (H0 : q = pa_add q 0%nat).
  { rewrite /pa_add /add_vec_int. apply bv_eq.
    rewrite add_vec_unsigned. cbn [Z.of_nat].
    change (bv_unsigned (mword_of_int 0 : mword 64)) with 0%Z.
    rewrite Z.add_0_r. symmetry. apply bv_wrap_small.
    apply bv_unsigned_in_range. }
  rewrite {1}H0 pa_add_bump. f_equal.
Qed.

(* ---- the log region, and the write set's bookkeeping ---- *)

Lemma it_slot_in_region (logstart : Z) (i : nat) :
  (i < LOGBLOCKS)%nat -> log_slot_bno logstart i ∈ log_region_set logstart.
Proof.
  intro Hi. rewrite /log_region_set. apply elem_of_union. left.
  apply elem_of_list_to_set. apply elem_of_list_fmap.
  exists i. split; [reflexivity|]. apply elem_of_seq. lia.
Qed.

Lemma it_hdr_in_region (logstart : Z) :
  log_hdr_bno logstart ∈ log_region_set logstart.
Proof.
  rewrite /log_region_set. apply elem_of_union. right.
  apply elem_of_singleton. reflexivity.
Qed.

(* the dirty authority's step: one more installed entry *)
Lemma it_dc_cons (D : gmap Z bool) (w : Z) (ws : list Z) :
  dirty_clear D (w :: ws) = <[w := false]> (dirty_clear D ws).
Proof. reflexivity. Qed.

Lemma it_dirty_snoc (D : gmap Z bool) (ws : list Z) (z : Z) :
  ~ (z ∈ ws) ->
  dirty_clear D (ws ++ [z]) = <[z := false]> (dirty_clear D ws).
Proof.
  induction ws as [|w ws IH]; intro Hz.
  - reflexivity.
  - rewrite -app_comm_cons !it_dc_cons.
    rewrite (IH ltac:(intro Hin; apply Hz; exact (elem_of_list_further _ _ _ Hin))).
    apply insert_commute. intro Heq. apply Hz.
    apply elem_of_cons. left. by rewrite Heq.
Qed.

(* NoDup gives the freshness the step needs *)
Lemma it_nodup_take (W : list (mword 32)) (t : nat) (w : mword 32) :
  NoDup (map uint W) -> W !! t = Some w ->
  ~ (uint w ∈ map uint (take t W)).
Proof.
  intros Hnd Hw Hin.
  assert (Hsplit : map uint W
                   = (map uint (take t W) ++ uint w :: map uint (drop (S t) W))%list).
  { rewrite -{1}(take_drop_middle W t w Hw). apply map_app. }
  rewrite Hsplit in Hnd.
  apply NoDup_remove_2 in Hnd. apply Hnd.
  apply in_or_app. left. by apply elem_of_list_In.
Qed.

Lemma it_map_take_S (W : list (mword 32)) (t : nat) (w : mword 32) :
  W !! t = Some w ->
  map uint (take (S t) W) = (map uint (take t W) ++ [uint w])%list.
Proof. intro Hw. rewrite (take_S_r W t w Hw) map_app. reflexivity. Qed.

Lemma it_lookup_elem (W : list (mword 32)) (t : nat) (w : mword 32) :
  W !! t = Some w -> w ∈ W.
Proof. intro Hw. apply elem_of_list_lookup. by exists t. Qed.


Lemma it_n_small (n : nat) : (n <= LOGBLOCKS)%nat -> (0 <= Z.of_nat n < 2^31)%Z.
Proof. rewrite /LOGBLOCKS. lia. Qed.

Lemma it_t_small (t n : nat) :
  (t < n)%nat -> (n <= LOGBLOCKS)%nat -> (0 <= Z.of_nat t < 2^31)%Z.
Proof. rewrite /LOGBLOCKS. lia. Qed.

Lemma it_pos (n : nat) : n <> 0%nat -> (0 < n)%nat.
Proof. lia. Qed.

Lemma it_fuel0 (n : nat) : (n - 0 <= n)%nat.
Proof. lia. Qed.

Lemma it_geb_pos (n : nat) : (0 < n)%nat -> Z.geb 0 (Z.of_nat n) = false.
Proof. intro H. rewrite Z.geb_leb. apply Z.leb_gt. lia. Qed.

Lemma it_len0 (n : nat) (W : list (mword 32)) : n = length W -> n = 0%nat -> W = [].
Proof. intros H1 H2. apply nil_length_inv. rewrite -H1. exact H2. Qed.




(* the frame base: sp after [c.addi16sp sp,-80] *)
Definition it_spr (m : regfile) : mword 64 :=
  add_vec (m !!! Regidx csp_rs1 : mword 64)
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))).

Lemma it_push (m : regfile) :
  it_spr m = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10.
Proof.
  rewrite /it_spr. unfold pa_stk, add_vec_int. apply f_equal.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* ---- the loop's bookkeeping arithmetic, all mword-FREE ---- *)

Lemma it_fuel_absurd (t n : nat) : (t < n)%nat -> (n - t <= 0)%nat -> False.
Proof. lia. Qed.

Lemma it_fuel_step (t n fuel : nat) : (n - t <= S fuel)%nat -> (n - S t <= fuel)%nat.
Proof. lia. Qed.

Lemma it_lt_len (t n : nat) (W : list (mword 32)) :
  (t < n)%nat -> n = length W -> (t < length W)%nat.
Proof. lia. Qed.

Lemma it_lt_len_le (t n : nat) (W : list (mword 32)) :
  (t < n)%nat -> n = length W -> (t <= length W)%nat.
Proof. lia. Qed.

Lemma it_t_lt_lb (t n : nat) : (t < n)%nat -> (n <= LOGBLOCKS)%nat -> (t < LOGBLOCKS)%nat.
Proof. rewrite /LOGBLOCKS. lia. Qed.

Lemma it_take_len (W : list (mword 32)) (t : nat) :
  (t <= length W)%nat -> length (take t W) = t.
Proof. intro H. rewrite length_take. lia. Qed.

Lemma it_take_all (W : list (mword 32)) (n : nat) : n = length W -> take n W = W.
Proof. intros ->. apply take_ge. lia. Qed.

Lemma it_len_eq (W : list (mword 32)) (n : nat) :
  n = length W -> (2 + length W)%nat = (2 + n)%nat.
Proof. lia. Qed.

Lemma it_lt_lit (x : Z) : (0 < x < 2^31)%Z -> (x < 2147483648)%Z.
Proof. lia. Qed.

Lemma it_noff0 : (Z.of_nat 0%nat + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma it_St_small (t n : nat) :
  (t < n)%nat -> (n <= LOGBLOCKS)%nat -> (0 <= Z.of_nat (S t) < 2^31)%Z.
Proof. rewrite /LOGBLOCKS. lia. Qed.

Lemma it_t1_small (t n : nat) :
  (t < n)%nat -> (n <= LOGBLOCKS)%nat -> (Z.of_nat t + 1 < 2^31)%Z.
Proof. rewrite /LOGBLOCKS. lia. Qed.

Lemma it_succ_moi (t : nat) :
  (mword_of_int (Z.of_nat t + 1) : mword 64) = mword_of_int (Z.of_nat (S t)).
Proof. f_equal. lia. Qed.

Lemma it_geb_eq (t n : nat) :
  S t = n -> Z.geb (Z.of_nat (S t)) (Z.of_nat n) = true.
Proof. intro H. rewrite Z.geb_leb. apply Z.leb_le. lia. Qed.

Lemma it_geb_ne (t n : nat) :
  (t < n)%nat -> S t <> n -> Z.geb (Z.of_nat (S t)) (Z.of_nat n) = false.
Proof. intros H1 H2. rewrite Z.geb_leb. apply Z.leb_gt. lia. Qed.

Lemma it_more (t n : nat) : (t < n)%nat -> S t <> n -> (S t < n)%nat.
Proof. lia. Qed.

(* the two breads' block numbers, and every bound their arithmetic needs *)
Lemma it_arith (ls : Z) (t : nat) :
  (0 < ls < 2^31)%Z -> (0 < log_slot_bno ls t < 2^31)%Z ->
  (0 <= ls < 2^31)%Z /\ (0 <= Z.of_nat t)%Z /\ (0 <= ls)%Z /\
  (0 <= ls + Z.of_nat t)%Z /\ (ls + Z.of_nat t < 2^31)%Z /\
  (ls + Z.of_nat t + 1 < 2^31)%Z /\
  ((ls + Z.of_nat t + 1)%Z = log_slot_bno ls t) /\
  (0 <= log_slot_bno ls t < 2^32)%Z /\
  (0 <= log_slot_bno ls t < 2^31)%Z.
Proof. rewrite /log_slot_bno. lia. Qed.

(* the stack budget: the ten-slot frame, then each callee's own depth *)
Lemma it_Kbread (K : nat) : (K_install_trans <= K)%nat -> (K_bread <= K - 10)%nat.
Proof. rewrite /K_install_trans /K_bread. lia. Qed.
Lemma it_Kbwrite (K : nat) : (K_install_trans <= K)%nat -> (K_bwrite <= K - 10)%nat.
Proof. rewrite /K_install_trans /K_bwrite. lia. Qed.
Lemma it_Kbrelse (K : nat) : (K_install_trans <= K)%nat -> (K_brelse <= K - 10)%nat.
Proof. rewrite /K_install_trans /K_brelse. lia. Qed.
Lemma it_Kbunpin (K : nat) : (K_install_trans <= K)%nat -> (14 <= K - 10)%nat.
Proof. rewrite /K_install_trans. lia. Qed.
Lemma it_Kmm (K : nat) : (K_install_trans <= K)%nat -> (2 <= K - 10)%nat.
Proof. rewrite /K_install_trans. lia. Qed.

(* the dirty authority's step *)
Lemma it_dirty_flip_step (D : gmap Z bool) (W : list (mword 32)) (t : nat) (w : mword 32) :
  NoDup (map uint W) -> W !! t = Some w ->
  <[uint w := false]> (dirty_clear D (map uint (take t W)))
  = dirty_clear D (map uint (take (S t) W)).
Proof.
  intros Hnd Hw.
  rewrite (it_map_take_S W t w Hw)
          (it_dirty_snoc D (map uint (take t W)) (uint w) (it_nodup_take W t w Hnd Hw)).
  reflexivity.
Qed.

(* the loop's register invariant *)
Definition it_lregs (m M : regfile) (t : nat) : Prop :=
  M !!! Regidx csp_rs1 = it_spr m /\
  M !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int (Z.of_nat t) : mword 64) /\
  M !!! Regidx (mword_of_int 20 : mword 5) = log_addr /\
  M !!! Regidx (mword_of_int 21 : mword 5) = (lh_block t : mword 64) /\
  M !!! Regidx (mword_of_int 22 : mword 5) = (mword_of_int 0 : mword 64) /\
  M !!! Regidx (mword_of_int 23 : mword 5) = (mword_of_int 1024 : mword 64) /\
  M !!! Regidx (mword_of_int 25 : mword 5) = (m !!! Regidx (mword_of_int 25 : mword 5) : mword 64) /\
  M !!! Regidx (mword_of_int 26 : mword 5) = (m !!! Regidx (mword_of_int 26 : mword 5) : mword 64) /\
  M !!! Regidx (mword_of_int 27 : mword 5) = (m !!! Regidx (mword_of_int 27 : mword 5) : mword 64).

Lemma it_lregs_upd (m M : regfile) (t : nat) (r : mword 5) (v : mword 64) :
  is_cs_idx r = false -> it_lregs m M t -> it_lregs m (<[Regidx r := v]> M) t.
Proof.
  intros Hr (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  assert (Hne : forall c : mword 5, is_cs_idx c = true -> Regidx c <> Regidx r).
  { intros c Hc. apply not_eq_sym. apply is_cs_idx_true_neq; assumption. }
  rewrite /it_lregs. split_and!;
    (rewrite upd_ne; [ assumption | apply Hne; vm_compute; reflexivity ]).
Qed.

Lemma it_lregs_upd_s1 (m M : regfile) (t : nat) (v : mword 64) :
  it_lregs m M t -> it_lregs m (<[Regidx (mword_of_int 9 : mword 5) := v]> M) t.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  rewrite /it_lregs. split_and!;
    (rewrite upd_ne; [ assumption | vm_compute; discriminate ]).
Qed.

Lemma it_lregs_upd_s2 (m M : regfile) (t : nat) (v : mword 64) :
  it_lregs m M t -> it_lregs m (<[Regidx (mword_of_int 18 : mword 5) := v]> M) t.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  rewrite /it_lregs. split_and!;
    (rewrite upd_ne; [ assumption | vm_compute; discriminate ]).
Qed.

Lemma it_lregs_cs (m M1 M2 : regfile) (t : nat) :
  callee_saved M1 M2 -> it_lregs m M1 t -> it_lregs m M2 t.
Proof.
  intros Hcs (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  unfold callee_saved in Hcs.
  destruct Hcs as (C2 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27).
  rewrite /it_lregs. split_and!; congruence.
Qed.

(* ===================================================================== *)

Module InstallTransProof (Bread : BREAD) (Bwrite : BWRITE) (Bunpin : BUNPIN)
                         (Brelse : BRELSE) (Mm : MEMMOVE) : INSTALL_TRANS.

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
Notation Rs6  := (mword_of_int 22 : mword 5).
Notation Rs7  := (mword_of_int 23 : mword 5).
Notation Rs8  := (mword_of_int 24 : mword 5).
Notation Rs9  := (mword_of_int 25 : mword 5).
Notation Rs10 := (mword_of_int 26 : mword 5).
Notation Rs11 := (mword_of_int 27 : mword 5).

Local Ltac regne := reg_ne_side.

Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

(* ===================================================================== *)
(*  The named pieces: the continuation, the frame, the register           *)
(*  invariant and the two big-op splits the loop carries.                 *)
(* ===================================================================== *)
Section InstallTransDefs.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* install_trans's own [wp_next] obligation, NAMED and anchored at an
     explicit hart (durable-notes: a whole-function post must not be
     spelled inline). *)
  Definition it_cont `{GEN : GenId} `{CID0 : CpuId} 
      (j : nat) (bn : bio_names) (γfs : fs_names) (logstart : Z)
      (n : nat) (W : list (mword 32)) (Lw : nat -> list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (R : iProp Σ) : iProp Σ :=
    wp_next true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜callee_saved m mf⌝ -∗
        sie_cap_gpr mf K b (proc_addr j) -∗
        cpu_own 0 eb (proc_addr j) C b -∗
        trap_csrs_ext eb -∗
        cpu_claim_ext eb (proc_addr j) -∗
        pc_is (ret_pc (m !!! Regidx Rra)) -∗
        p_pid (proc_addr j) ↦₄{dq} pidv -∗
        lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
        ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) -∗
        ghost_map_auth (fs_L γfs) 1 L -∗
        ghost_map_auth (fs_dirty γfs) 1 (dirty_clear D (map uint W)) -∗
        ([∗ list] i ↦ w ∈ W,
           fsblock γfs (log_slot_bno logstart i) (Lw i) ∗
           (uint w) ↪[fs_dirty γfs]{#(1/2)} false) -∗
        bslots bn (2 + length W) -∗
        ▷ R -∗
        WP (Loop : expr riscv_lang))%I.

  Lemma it_cont_shift `{GEN : GenId} `{CIDa : CpuId} `{CIDb : CpuId}
      
      (j : nat) (bn : bio_names) (γfs : fs_names) (logstart : Z)
      (n : nat) (W : list (mword 32)) (Lw : nat -> list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (R : iProp Σ) :
    (* the guard is at the LITERAL [true] now, matching it_cont's own index *)
    (true = false \/ proc_addr j = zero_reg -> (CIDb : CPU) = (CIDa : CPU)) ->
    it_cont (CID0 := CIDa)  j bn γfs logstart n W Lw L D pidv dq m K eb C b R -∗
    it_cont (CID0 := CIDb)  j bn γfs logstart n W Lw L D pidv dq m K eb C b R.
  Proof.
    intros Hs. rewrite /it_cont /wp_next.
    iIntros "H" (CID2 Hs2). iApply "H". iPureIntro.
    intro Hb. specialize (Hs2 Hb). specialize (Hs Hb). congruence.
  Qed.

  (* the ten saved slots (ra, s0..s8): every one is written *)
  Definition it_frame (m : regfile) : iProp Σ :=
    (pa_stk (m !!! Regidx csp_rs1 : mword 64) 1 ↦₈ (m !!! Regidx Rra : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 2 ↦₈ (m !!! Regidx Rs0 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 3 ↦₈ (m !!! Regidx Rs1 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 4 ↦₈ (m !!! Regidx Rs2 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 5 ↦₈ (m !!! Regidx Rs3 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 6 ↦₈ (m !!! Regidx Rs4 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 7 ↦₈ (m !!! Regidx Rs5 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 8 ↦₈ (m !!! Regidx Rs6 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 9 ↦₈ (m !!! Regidx Rs7 : mword 64) ∗
     pa_stk (m !!! Regidx csp_rs1 : mword 64) 10 ↦₈ (m !!! Regidx Rs8 : mword 64))%I.

  (* what the caller still owns when the loop is done / at the epilogue *)
  Definition it_out (bn : bio_names) (γfs : fs_names) (logstart : Z)
      (n : nat) (W : list (mword 32)) (Lw : nat -> list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool) : iProp Σ :=
    (lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) ∗
     ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) ∗
     ghost_map_auth (fs_L γfs) 1 L ∗
     ghost_map_auth (fs_dirty γfs) 1 (dirty_clear D (map uint W)) ∗
     ([∗ list] i ↦ w ∈ W,
        fsblock γfs (log_slot_bno logstart i) (Lw i) ∗
        (uint w) ↪[fs_dirty γfs]{#(1/2)} false) ∗
     bslots bn (2 + length W))%I.

  (* the payload's two agreements, both with a PURE conclusion so the
     [iDestruct] keeps the payload itself (durable-notes) *)
  Lemma it_pay_bs (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (dv bno : mword 32)
      (bsl bsd bs0 : list (bv 8)) (d : bool) :
    fsblock γfs (uint bno) bs0 -∗
    bio_pay bn (fs_view γfs γd dev cov) k dv bno bsl bsd d -∗ ⌜bsl = bs0⌝.
  Proof.
    rewrite /bio_pay /fs_view /=. destruct d.
    - rewrite /fs_mdirty. iIntros "Hc [[Hm _] _]".
      iDestruct (ghost_map_elem_agree with "Hm Hc") as %Heq. done.
    - rewrite /fs_mclean. iIntros "Hc [[Hm _] _]".
      iDestruct (ghost_map_elem_agree with "Hm Hc") as %Heq. done.
  Qed.

  (* THE COMMITTER'S OWN WITNESS.  A home block's client [fsblock] is
     unobtainable on this side (SpecInstallTrans.v's header), so its bytes
     are read out of the AUTHORITY install_trans holds instead.  Pure
     conclusion, so the payload survives the [iDestruct]. *)
  Lemma it_pay_bs_auth (bn : bio_names) (γfs : fs_names) (γd : disk_names)
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

  Lemma it_pay_d (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (dv bno : mword 32)
      (bsl bsd : list (bv 8)) (d db : bool) :
    (uint bno) ↪[fs_dirty γfs]{#(1/2)} db -∗
    bio_pay bn (fs_view γfs γd dev cov) k dv bno bsl bsd d -∗ ⌜d = db⌝.
  Proof.
    rewrite /bio_pay /fs_view /=. destruct d.
    - rewrite /fs_mdirty. iIntros "Hc [[_ Hm] _]".
      iDestruct (ghost_map_elem_agree with "Hm Hc") as %Heq. done.
    - rewrite /fs_mclean. iIntros "Hc [[_ Hm] _]".
      iDestruct (ghost_map_elem_agree with "Hm Hc") as %Heq. done.
  Qed.

  (* the DIRTY payload taken apart: the L-half, the dirty half and the pin *)
  Lemma it_pay_open (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (dv bno : mword 32)
      (bsl bsd : list (bv 8)) :
    bio_pay bn (fs_view γfs γd dev cov) k dv bno bsl bsd true -∗
    ((uint bno) ↪[fs_L γfs]{#(1/2)} bsl ∗
     (uint bno) ↪[fs_dirty γfs]{#(1/2)} true ∗
     (∃ q : Qp, bref bn k q dv bno)).
  Proof. rewrite /bio_pay /fs_view /= /fs_mdirty. iIntros "[[$ $] $]". Qed.

  (* ... and re-formed CLEAN, once the write has made disk = bytes *)
  Lemma it_pay_clean (bn : bio_names) (γfs : fs_names) (γd : disk_names)
      (dev : mword 32) (cov : gset Z) (k : nat) (dv bno : mword 32)
      (bsl : list (bv 8)) :
    (uint bno) ↪[fs_L γfs]{#(1/2)} bsl -∗
    (uint bno) ↪[fs_dirty γfs]{#(1/2)} false -∗
    bio_pay bn (fs_view γfs γd dev cov) k dv bno bsl bsl false.
  Proof.
    rewrite /bio_pay /fs_view /= /fs_mclean.
    iIntros "H1 H2". iFrame. done.
  Qed.

  (* a buffer's bytes, re-indexed as the FUNCTION memmove's contract takes *)
  Lemma it_seq_index (P : nat -> bv 8 -> iProp Σ) (bs : list (bv 8)) :
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

  (* the pending suffix, re-indexed at the next cursor: [t + S i] and
     [S t + i] are equal but NOT convertible (plus recurses on the left). *)
  Lemma it_rest_shift (γfs : fs_names) (logstart : Z) (Lw : nat -> list (bv 8))
      (t : nat) (l : list (mword 32)) :
    ([∗ list] i ↦ v ∈ l,
       fsblock γfs (log_slot_bno logstart ((t + S i)%nat)) (Lw ((t + S i)%nat)) ∗
       (uint v) ↪[fs_dirty γfs]{#(1/2)} true)
    ⊢ ([∗ list] i ↦ v ∈ l,
       fsblock γfs (log_slot_bno logstart ((S t + i)%nat)) (Lw ((S t + i)%nat)) ∗
       (uint v) ↪[fs_dirty γfs]{#(1/2)} true).
  Proof.
    apply big_sepL_mono. intros k y _.
    assert (Hk : (t + S k)%nat = (S t + k)%nat) by lia.
    rewrite Hk. done.
  Qed.

  (* the two directions memmove's contract needs, applied (not rewritten):
     both sides carry beta-redexes, which unification sees through and
     ssreflect's [rewrite] does not. *)
  Lemma it_data_fwd (q : Arch.pa) (bs : list (bv 8)) (len : nat) :
    length bs = len ->
    ([∗ list] j ↦ x ∈ bs, pa_add q j ↦ₘ x) ⊢
    ([∗ list] j ∈ seq 0 len, (pa_add q j) ↦ₘ (bs !!! j)).
  Proof.
    intros <-. rewrite (it_seq_index (fun i x => (pa_add q i ↦ₘ x)%I) bs).
    iIntros "$".
  Qed.

  Lemma it_data_back (q : Arch.pa) (bs : list (bv 8)) (len : nat) :
    length bs = len ->
    ([∗ list] j ∈ seq 0 len, (pa_add q j) ↦ₘ (bs !!! j)) ⊢
    ([∗ list] j ↦ x ∈ bs, pa_add q j ↦ₘ x).
  Proof.
    intros <-. rewrite (it_seq_index (fun i x => (pa_add q i ↦ₘ x)%I) bs).
    iIntros "$".
  Qed.

End InstallTransDefs.

(* ===================================================================== *)
(*  The blocks.                                                          *)
(* ===================================================================== *)
Section InstallTransBlocks.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.

  (* ================================================================== *)
  (*  +0xb2 .. +0xc8 : restore ra/s0..s8, pop the 80-byte frame, return. *)
  (* ================================================================== *)
  Local Lemma it_epi `{GEN : GenId} `{CID0 : CpuId} 
      (j : nat) (bn : bio_names) (γfs : fs_names) (logstart : Z)
      (n : nat) (W : list (mword 32)) (Lw : nat -> list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (pidv : mword 32) (dq : dfrac)
      (m M : regfile) (K : nat) (eb : bool) (C : iProp Σ) (R : iProp Σ) :
    (K_install_trans <= K)%nat ->
    M !!! Regidx csp_rs1 = it_spr m ->
    M !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64) ->
    M !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64) ->
    M !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64) ->
    sie_cap_gpr M (K - 10)%nat eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.install_trans + 0xb2) : mword 64) -∗
    it_frame m -∗
    cpu_own 0 eb (proc_addr j) C eb -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    it_out bn γfs logstart n W Lw L D -∗
    ▷ R -∗
    it_cont (CID0 := CID0)  j bn γfs logstart n W Lw L D pidv dq m K eb C eb R -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hs9 Hs10 Hs11.
    iIntros "Hcg #Htext Hpc Hframe Hcnt Hextc Hextm Hppid Hout HR Hcont".
    iPoseProof (iti_b2 with "Htext") as "Hib2".
    iPoseProof (iti_b4 with "Htext") as "Hib4".
    iPoseProof (iti_b6 with "Htext") as "Hib6".
    iPoseProof (iti_b8 with "Htext") as "Hib8".
    iPoseProof (iti_ba with "Htext") as "Hiba".
    iPoseProof (iti_bc with "Htext") as "Hibc".
    iPoseProof (iti_be with "Htext") as "Hibe".
    iPoseProof (iti_c0 with "Htext") as "Hic0".
    iPoseProof (iti_c2 with "Htext") as "Hic2".
    iPoseProof (iti_c4 with "Htext") as "Hic4".
    iPoseProof (iti_c6 with "Htext") as "Hic6".
    iPoseProof (iti_c8 with "Htext") as "Hic8".
    rewrite /it_frame.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9 & Hf10)".
    (* the ten saved-slot addresses in the [c.ldsp] leaf's spelling *)
    assert (Hb1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
    { rewrite Hsp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
    { rewrite Hsp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
    { rewrite Hsp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
    { rewrite Hsp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb5 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
    { rewrite Hsp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb6 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
    { rewrite Hsp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb7 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
    { rewrite Hsp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb8 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
    { rewrite Hsp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb9 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 9).
    { rewrite Hsp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb10 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                  = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
    { rewrite Hsp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hf1".   iEval (rewrite -Hb2) in "Hf2".
    iEval (rewrite -Hb3) in "Hf3".   iEval (rewrite -Hb4) in "Hf4".
    iEval (rewrite -Hb5) in "Hf5".   iEval (rewrite -Hb6) in "Hf6".
    iEval (rewrite -Hb7) in "Hf7".   iEval (rewrite -Hb8) in "Hf8".
    iEval (rewrite -Hb9) in "Hf9".   iEval (rewrite -Hb10) in "Hf10".
    (* ===== +0xb2 : ld ra,72(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0xb2)) (mword_of_int 9 : mword 6) Rra
              M (K - 10)%nat (m !!! Regidx Rra : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib2 Hf1 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc Hf1".
    set (P1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HP1sp : P1 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P1 upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hppb4 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xb2) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xb4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppb4) in "Hpc".
    (* ===== +0xb4 : ld s0,64(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0xb4)) (mword_of_int 8 : mword 6) Rs0
              P1 (K - 10)%nat (m !!! Regidx Rs0 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib4 [Hf2] [-]").
    { iEval (rewrite HP1sp). iExact "Hf2". }
    iIntros (CID2 Hs2) "Hcg Hpc Hf2".
    set (P2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> P1).
    assert (HP2sp : P2 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P2 upd_ne; [exact HP1sp | vm_compute; discriminate]).
    assert (Hppb6 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xb4) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xb6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppb6) in "Hpc".
    (* ===== +0xb6 : ld s1,56(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0xb6)) (mword_of_int 7 : mword 6) Rs1
              P2 (K - 10)%nat (m !!! Regidx Rs1 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib6 [Hf3] [-]").
    { iEval (rewrite HP2sp). iExact "Hf3". }
    iIntros (CID3 Hs3) "Hcg Hpc Hf3".
    set (P3 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> P2).
    assert (HP3sp : P3 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P3 upd_ne; [exact HP2sp | vm_compute; discriminate]).
    assert (Hppb8 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xb6) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xb8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppb8) in "Hpc".
    (* ===== +0xb8 : ld s2,48(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0xb8)) (mword_of_int 6 : mword 6) Rs2
              P3 (K - 10)%nat (m !!! Regidx Rs2 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hib8 [Hf4] [-]").
    { iEval (rewrite HP3sp). iExact "Hf4". }
    iIntros (CID4 Hs4) "Hcg Hpc Hf4".
    set (P4 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> P3).
    assert (HP4sp : P4 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3sp | vm_compute; discriminate]).
    assert (Hppba : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xb8) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xba))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppba) in "Hpc".
    (* ===== +0xba : ld s3,40(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0xba)) (mword_of_int 5 : mword 6) Rs3
              P4 (K - 10)%nat (m !!! Regidx Rs3 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiba [Hf5] [-]").
    { iEval (rewrite HP4sp). iExact "Hf5". }
    iIntros (CID5 Hs5) "Hcg Hpc Hf5".
    set (P5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> P4).
    assert (HP5sp : P5 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4sp | vm_compute; discriminate]).
    assert (Hppbc : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xba) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xbc))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppbc) in "Hpc".
    (* ===== +0xbc : ld s4,32(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0xbc)) (mword_of_int 4 : mword 6) Rs4
              P5 (K - 10)%nat (m !!! Regidx Rs4 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hibc [Hf6] [-]").
    { iEval (rewrite HP5sp). iExact "Hf6". }
    iIntros (CID6 Hs6) "Hcg Hpc Hf6".
    set (P6 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> P5).
    assert (HP6sp : P6 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P6 upd_ne; [exact HP5sp | vm_compute; discriminate]).
    assert (Hppbe : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xbc) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xbe))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppbe) in "Hpc".
    (* ===== +0xbe : ld s5,24(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0xbe)) (mword_of_int 3 : mword 6) Rs5
              P6 (K - 10)%nat (m !!! Regidx Rs5 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hibe [Hf7] [-]").
    { iEval (rewrite HP6sp). iExact "Hf7". }
    iIntros (CID7 Hs7) "Hcg Hpc Hf7".
    set (P7 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> P6).
    assert (HP7sp : P7 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P7 upd_ne; [exact HP6sp | vm_compute; discriminate]).
    assert (Hppc0 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xbe) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xc0))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc0) in "Hpc".
    (* ===== +0xc0 : ld s6,16(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0xc0)) (mword_of_int 2 : mword 6) Rs6
              P7 (K - 10)%nat (m !!! Regidx Rs6 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hic0 [Hf8] [-]").
    { iEval (rewrite HP7sp). iExact "Hf8". }
    iIntros (CID8 Hs8) "Hcg Hpc Hf8".
    set (P8 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> P7).
    assert (HP8sp : P8 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P8 upd_ne; [exact HP7sp | vm_compute; discriminate]).
    assert (Hppc2 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xc0) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xc2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc2) in "Hpc".
    (* ===== +0xc2 : ld s7,8(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0xc2)) (mword_of_int 1 : mword 6) Rs7
              P8 (K - 10)%nat (m !!! Regidx Rs7 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hic2 [Hf9] [-]").
    { iEval (rewrite HP8sp). iExact "Hf9". }
    iIntros (CID9 Hs9') "Hcg Hpc Hf9".
    set (P9 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7 : mword 64)]> P8).
    assert (HP9sp : P9 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P9 upd_ne; [exact HP8sp | vm_compute; discriminate]).
    assert (Hppc4 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xc2) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xc4))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc4) in "Hpc".
    (* ===== +0xc4 : ld s8,0(sp) ===== *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0xc4)) (mword_of_int 0 : mword 6) Rs8
              P9 (K - 10)%nat (m !!! Regidx Rs8 : mword 64) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hic4 [Hf10] [-]").
    { iEval (rewrite HP9sp). iExact "Hf10". }
    iIntros (CID10 Hs10') "Hcg Hpc Hf10".
    set (P10 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8 : mword 64)]> P9).
    assert (HP10sp : P10 !!! Regidx csp_rs1 = (M !!! Regidx csp_rs1 : mword 64))
      by (rewrite /P10 upd_ne; [exact HP9sp | vm_compute; discriminate]).
    assert (Hppc6 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xc4) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xc6))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc6) in "Hpc".
    (* ===== +0xc6 : c.addi16sp sp,80 -- the pop ===== *)
    assert (Hwv : add_vec (P10 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))
                  = (m !!! Regidx csp_rs1 : mword 64)).
    { rewrite HP10sp Hsp /it_spr. apply frame_cancel_80. }
    assert (Hpop : P10 !!! Regidx csp_rs1
                   = pa_stk (add_vec (P10 !!! Regidx csp_rs1 : mword 64)
                               (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6)))) 10).
    { rewrite Hwv HP10sp Hsp. exact (it_push m). }
    iAssert (stack_own (m !!! Regidx csp_rs1 : mword 64) 10)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10]" as "Hstk".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hf1"; [iEval (rewrite -Hb1); iExists _; iExact "Hf1"|].
      iSplitL "Hf2"; [iEval (rewrite -Hb2 -HP1sp); iExists _; iExact "Hf2"|].
      iSplitL "Hf3"; [iEval (rewrite -Hb3 -HP2sp); iExists _; iExact "Hf3"|].
      iSplitL "Hf4"; [iEval (rewrite -Hb4 -HP3sp); iExists _; iExact "Hf4"|].
      iSplitL "Hf5"; [iEval (rewrite -Hb5 -HP4sp); iExists _; iExact "Hf5"|].
      iSplitL "Hf6"; [iEval (rewrite -Hb6 -HP5sp); iExists _; iExact "Hf6"|].
      iSplitL "Hf7"; [iEval (rewrite -Hb7 -HP6sp); iExists _; iExact "Hf7"|].
      iSplitL "Hf8"; [iEval (rewrite -Hb8 -HP7sp); iExists _; iExact "Hf8"|].
      iSplitL "Hf9"; [iEval (rewrite -Hb9 -HP8sp); iExists _; iExact "Hf9"|].
      iSplitL "Hf10"; [iEval (rewrite -Hb10 -HP9sp); iExists _; iExact "Hf10"|].
      done. }
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.install_trans + 0xc6)) (mword_of_int 5 : mword 6)
              P10 (K - 10)%nat 10 eb Hpop with "Hcg Hpc Hic6 Hstk [-]").
    iIntros (CID11 Hs11') "Hcg Hpc".
    assert (Hnk : ((K - 10) + 10)%nat = K) by (unfold K_install_trans in HK; lia).
    iEval (rewrite Hnk) in "Hcg".
    set (P11 := <[Regidx csp_rs1 := regval_into_reg
                   (add_vec (P10 !!! Regidx csp_rs1 : mword 64)
                      (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> P10).
    change (<[Regidx csp_rs1 := regval_into_reg
      (add_vec (P10 !!! Regidx csp_rs1 : mword 64)
         (sign_extend' 64 (caddi16sp_imm (mword_of_int 5 : mword 6))))]> P10) with P11.
    assert (Hppc8 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xc6) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xc8))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppc8) in "Hpc".
    (* ===== +0xc8 : c.ret ===== *)
    assert (HP11ra : P11 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /P11 upd_ne; [| vm_compute; discriminate].
      rewrite /P10 upd_ne; [| vm_compute; discriminate].
      rewrite /P9 upd_ne; [| vm_compute; discriminate].
      rewrite /P8 upd_ne; [| vm_compute; discriminate].
      rewrite /P7 upd_ne; [| vm_compute; discriminate].
      rewrite /P6 upd_ne; [| vm_compute; discriminate].
      rewrite /P5 upd_ne; [| vm_compute; discriminate].
      rewrite /P4 upd_ne; [| vm_compute; discriminate].
      rewrite /P3 upd_ne; [| vm_compute; discriminate].
      rewrite /P2 upd_ne; [| vm_compute; discriminate].
      rewrite /P1 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.install_trans + 0xc8)) Rra P11 K eb
              ltac:(vm_compute; discriminate) with "Hcg Hpc Hic8 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    assert (Hretf : ret_pc (rget P11 Rra) = ret_pc (m !!! Regidx Rra : mword 64)).
    { rewrite rget_ne; [ by rewrite HP11ra
                       | intro Hq; injection Hq as Hq2; vm_compute in Hq2; congruence ]. }
    iEval (rewrite Hretf) in "Hpc".
    (* the callee-saved obligation *)
    assert (Hcs : callee_saved m P11).
    { unfold callee_saved.
      assert (Hc2 : P11 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
        by (rewrite /P11 upd_eq; exact Hwv).
      assert (Hc8 : P11 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
      { rewrite /P11 upd_ne; [| vm_compute; discriminate].
        rewrite /P10 upd_ne; [| vm_compute; discriminate].
        rewrite /P9 upd_ne; [| vm_compute; discriminate].
        rewrite /P8 upd_ne; [| vm_compute; discriminate].
        rewrite /P7 upd_ne; [| vm_compute; discriminate].
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_ne; [| vm_compute; discriminate].
        rewrite /P2 upd_eq. reflexivity. }
      assert (Hc9 : P11 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
      { rewrite /P11 upd_ne; [| vm_compute; discriminate].
        rewrite /P10 upd_ne; [| vm_compute; discriminate].
        rewrite /P9 upd_ne; [| vm_compute; discriminate].
        rewrite /P8 upd_ne; [| vm_compute; discriminate].
        rewrite /P7 upd_ne; [| vm_compute; discriminate].
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_ne; [| vm_compute; discriminate].
        rewrite /P3 upd_eq. reflexivity. }
      assert (Hc18 : P11 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
      { rewrite /P11 upd_ne; [| vm_compute; discriminate].
        rewrite /P10 upd_ne; [| vm_compute; discriminate].
        rewrite /P9 upd_ne; [| vm_compute; discriminate].
        rewrite /P8 upd_ne; [| vm_compute; discriminate].
        rewrite /P7 upd_ne; [| vm_compute; discriminate].
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_ne; [| vm_compute; discriminate].
        rewrite /P4 upd_eq. reflexivity. }
      assert (Hc19 : P11 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
      { rewrite /P11 upd_ne; [| vm_compute; discriminate].
        rewrite /P10 upd_ne; [| vm_compute; discriminate].
        rewrite /P9 upd_ne; [| vm_compute; discriminate].
        rewrite /P8 upd_ne; [| vm_compute; discriminate].
        rewrite /P7 upd_ne; [| vm_compute; discriminate].
        rewrite /P6 upd_ne; [| vm_compute; discriminate].
        rewrite /P5 upd_eq. reflexivity. }
      assert (Hc20 : P11 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
      { rewrite /P11 upd_ne; [| vm_compute; discriminate].
        rewrite /P10 upd_ne; [| vm_compute; discriminate].
        rewrite /P9 upd_ne; [| vm_compute; discriminate].
        rewrite /P8 upd_ne; [| vm_compute; discriminate].
        rewrite /P7 upd_ne; [| vm_compute; discriminate].
        rewrite /P6 upd_eq. reflexivity. }
      assert (Hc21 : P11 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
      { rewrite /P11 upd_ne; [| vm_compute; discriminate].
        rewrite /P10 upd_ne; [| vm_compute; discriminate].
        rewrite /P9 upd_ne; [| vm_compute; discriminate].
        rewrite /P8 upd_ne; [| vm_compute; discriminate].
        rewrite /P7 upd_eq. reflexivity. }
      assert (Hc22 : P11 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
      { rewrite /P11 upd_ne; [| vm_compute; discriminate].
        rewrite /P10 upd_ne; [| vm_compute; discriminate].
        rewrite /P9 upd_ne; [| vm_compute; discriminate].
        rewrite /P8 upd_eq. reflexivity. }
      assert (Hc23 : P11 !!! Regidx Rs7 = (m !!! Regidx Rs7 : mword 64)).
      { rewrite /P11 upd_ne; [| vm_compute; discriminate].
        rewrite /P10 upd_ne; [| vm_compute; discriminate].
        rewrite /P9 upd_eq. reflexivity. }
      assert (Hc24 : P11 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64)).
      { rewrite /P11 upd_ne; [| vm_compute; discriminate].
        rewrite /P10 upd_eq. reflexivity. }
      assert (Hthr : forall c : mword 5, is_cs_idx c = true ->
                       c <> csp_rs1 -> c <> Rs0 -> c <> Rs1 -> c <> Rs2 -> c <> Rs3 ->
                       c <> Rs4 -> c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
                       P11 !!! Regidx c = (M !!! Regidx c : mword 64)).
      { intros c Hcs2 N2 N8 N9 N18 N19 N20 N21 N22 N23 N24.
        rewrite /P11 upd_ne; [| regne].
        rewrite /P10 upd_ne; [| regne].
        rewrite /P9 upd_ne; [| regne].
        rewrite /P8 upd_ne; [| regne].
        rewrite /P7 upd_ne; [| regne].
        rewrite /P6 upd_ne; [| regne].
        rewrite /P5 upd_ne; [| regne].
        rewrite /P4 upd_ne; [| regne].
        rewrite /P3 upd_ne; [| regne].
        rewrite /P2 upd_ne; [| regne].
        rewrite /P1 upd_ne; [reflexivity | regne]. }
      assert (Hc25 : P11 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64)).
      { rewrite (Hthr Rs9 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact Hs9. }
      assert (Hc26 : P11 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64)).
      { rewrite (Hthr Rs10 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact Hs10. }
      assert (Hc27 : P11 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64)).
      { rewrite (Hthr Rs11 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact Hs11. }
      split_and!; assumption. }
    rewrite /it_out.
    iDestruct "Hout" as "(Hncell & Hblks & HauthL & HauthD & Hents & Hslots)".
    iDestruct (cpu_own_transport CID0 CID12 0%nat eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID12 eb (proc_addr j) ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID12 eb (proc_addr j) ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iDestruct (it_cont_shift (CIDa := CID0) (CIDb := CID12)  j bn γfs logstart n W Lw L D
                 pidv dq m K eb C eb R ltac:(wp_next_chain) with "Hcont") as "Hcont".
    rewrite /it_cont.
    iSpecialize ("Hcont" $! CID12 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! P11 with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hncell Hblks
                                 HauthL HauthD Hents Hslots HR").
    exact Hcs.
  Qed.

  (* ================================================================== *)
  (*  +0x6c .. +0xb0 (with +0x54..+0x68): ONE iteration of the install   *)
  (*  loop, by induction on the iterations still to run.  Entry and back *)
  (*  edge are both +0x6c; the exit is the [bge s3,a5] at +0x68.         *)
  (* ================================================================== *)
  Local Lemma it_loop `{GEN : GenId} (fuel : nat) 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (n : nat) (W : list (mword 32)) (Lw : nat -> list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (R : iProp Σ) :
    (K_install_trans <= K)%nat ->
    log_geom_ok cov logstart ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (n = length W /\ (n <= LOGBLOCKS)%nat) ->
    NoDup (map uint W) ->
    (forall w, w ∈ W -> uint w ∈ cov /\ ~ (uint w ∈ log_region_set logstart)) ->
    (forall (i : nat) (w : mword 32), W !! i = Some w -> L !! uint w = Some (Lw i)) ->
    forall (CID0 : CpuId) (t : nat) (M : regfile),
    (t < n)%nat ->
    (n - t <= fuel)%nat ->
    it_lregs m M t ->
    sie_cap_gpr M (K - 10)%nat eb (proc_addr j) -∗
    cpu_own 0 eb (proc_addr j) C eb -∗
    trap_csrs_ext eb -∗
    cpu_claim_ext eb (proc_addr j) -∗
    kernel_text -∗
    pc_is (mword_of_int (KernelSyms.install_trans + 0x6c) : mword 64) -∗
    panic_wp_any -∗
    bio_ctx bn (fs_view γfs γd dev cov) -∗
    log_frozen logstart dev -∗
    p_pid (proc_addr j) ↦₄{dq} pidv -∗
    procs_inv γs -∗
    dev_inv γu γd -∗
    disk_geom γd pd pav pu -∗
    is_lock γk d_lock "virtio_disk"%string (disk_res γd pd pav pu) -∗
    it_frame m -∗
    lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
    ([∗ list] i ↦ w ∈ W, lh_block i ↦₄ w) -∗
    ghost_map_auth (fs_L γfs) 1 L -∗
    ghost_map_auth (fs_dirty γfs) 1 (dirty_clear D (map uint (take t W))) -∗
    ([∗ list] i ↦ w ∈ take t W,
       fsblock γfs (log_slot_bno logstart i) (Lw i) ∗
       (uint w) ↪[fs_dirty γfs]{#(1/2)} false) -∗
    ([∗ list] i ↦ w ∈ drop t W,
       fsblock γfs (log_slot_bno logstart ((t + i)%nat)) (Lw ((t + i)%nat)) ∗
       (uint w) ↪[fs_dirty γfs]{#(1/2)} true) -∗
    bslots bn (2 + t) -∗
    (* the per-entry crash permits, and the resource they thread *)
    □ (∀ (i : nat) (w : mword 32) (bs' : list (bv 8)),
         ⌜W !! i = Some w⌝ -∗ ⌜length bs' = 1024%nat⌝ -∗ ▷ R -∗
         disk_write_permit gen_id (Some ((1024 * uint w)%Z, bs')) R) -∗
    ▷ R -∗
    it_cont (CID0 := CID0)  j bn γfs logstart n W Lw L D pidv dq m K eb C eb R -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hgeom Hj Hgl Hshape Hnd Hwok HLw.
    destruct Hshape as [HnW Hn30].
    destruct Hgeom as [Hcovok Hlogsub].
    induction fuel as [|fuel IH]; intros CID0 t M Ht Hfuel Hregs.
    { exfalso. exact (it_fuel_absurd t n Ht Hfuel). }
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlfz Hppid #Hprocs".
    iIntros "#Hdev #Hgeo #Hdlock Hframe Hncell Hblks HauthL HauthD Hdone Hrest Hslots".
    iIntros "#Hperm HR Hcont".
    pose proof Hregs as (HMsp & HMs3 & HMs4 & HMs5 & HMs6 & HMs7 & HMs9 & HMs10 & HMs11).
    iDestruct "Hlfz" as "[#Hdevc #Hstc]".
    (* ---- the entry at the cursor, and every bound its two breads need ---- *)
    destruct (lookup_lt_is_Some_2 W t (it_lt_len t n W Ht HnW)) as [w Hw].
    pose proof (Hwok w (it_lookup_elem W t w Hw)) as [Hwcov Hwnlog].
    pose proof (Hcovok (uint w) Hwcov) as Hwrange.
    assert (Hslotcov : log_slot_bno logstart t ∈ cov)
      by (apply Hlogsub; apply it_slot_in_region; exact (it_t_lt_lb t n Ht Hn30)).
    pose proof (Hcovok _ Hslotcov) as Hslotrange.
    assert (Hhdrcov : log_hdr_bno logstart ∈ cov)
      by (apply Hlogsub; apply it_hdr_in_region).
    pose proof (Hcovok _ Hhdrcov) as Hlsrange0.
    rewrite /log_hdr_bno in Hlsrange0.
    pose proof (it_arith logstart t Hlsrange0 Hslotrange)
      as (Har1 & Har2 & Har3 & Har4 & Har5 & Har6 & Har7 & Har8 & Har9).
    set (bnol := (mword_of_int (log_slot_bno logstart t) : mword 32)).
    assert (Hubnol : uint bnol = log_slot_bno logstart t)
      by (rewrite /bnol; apply it_uint_moi32; exact Har8).
    (* ---- the instruction facts ---- *)
    iPoseProof (iti_6c with "Htext") as "Hi6c".
    iPoseProof (iti_70 with "Htext") as "Hi70".
    iPoseProof (iti_74 with "Htext") as "Hi74".
    iPoseProof (iti_78 with "Htext") as "Hi78".
    iPoseProof (iti_7a with "Htext") as "Hi7a".
    iPoseProof (iti_7e with "Htext") as "Hi7e".
    iPoseProof (iti_82 with "Htext") as "Hi82".
    iPoseProof (iti_84 with "Htext") as "Hi84".
    iPoseProof (iti_88 with "Htext") as "Hi88".
    iPoseProof (iti_8c with "Htext") as "Hi8c".
    iPoseProof (iti_90 with "Htext") as "Hi90".
    iPoseProof (iti_92 with "Htext") as "Hi92".
    iPoseProof (iti_94 with "Htext") as "Hi94".
    iPoseProof (iti_98 with "Htext") as "Hi98".
    iPoseProof (iti_9c with "Htext") as "Hi9c".
    iPoseProof (iti_a0 with "Htext") as "Hia0".
    iPoseProof (iti_a2 with "Htext") as "Hia2".
    iPoseProof (iti_a6 with "Htext") as "Hia6".
    iPoseProof (iti_aa with "Htext") as "Hiaa".
    iPoseProof (iti_ac with "Htext") as "Hiac".
    iPoseProof (iti_b0 with "Htext") as "Hib0".
    iPoseProof (iti_54 with "Htext") as "Hi54".
    iPoseProof (iti_56 with "Htext") as "Hi56".
    iPoseProof (iti_5a with "Htext") as "Hi5a".
    iPoseProof (iti_5c with "Htext") as "Hi5c".
    iPoseProof (iti_60 with "Htext") as "Hi60".
    iPoseProof (iti_62 with "Htext") as "Hi62".
    iPoseProof (iti_64 with "Htext") as "Hi64".
    iPoseProof (iti_68 with "Htext") as "Hi68".
    (* ---- the batch pieces this iteration touches ---- *)
    iDestruct (big_sepL_lookup_acc _ W t w Hw with "Hblks") as "[Hblk Hblkback]".
    iEval (rewrite (drop_S W w t Hw)) in "Hrest".
    iDestruct "Hrest" as "[Hent Hrest]".
    iEval (rewrite Nat.add_0_r) in "Hent".
    iDestruct "Hent" as "(Hfblog & Hdirty)".
    iEval (rewrite -Hubnol) in "Hfblog".
    (* the two slot units the two breads spend *)
    assert (Hsl1 : (2 + t)%nat = (1 + (1 + t))%nat) by reflexivity.
    iEval (rewrite Hsl1 (bslots_op bn 1 (1 + t))) in "Hslots".
    iDestruct "Hslots" as "[Hu1 Hslots]".
    iEval (rewrite (bslots_op bn 1 t)) in "Hslots".
    iDestruct "Hslots" as "[Hu2 Hslots]".
    (* ===== +0x6c bnez s6 : NOT taken (recovering = 0) ===== *)
    assert (Hnz6c : neq_vec (rget M Rs6) (zero_reg : mword 64) = false).
    { rgne. rewrite HMs6. vm_compute. reflexivity. }
    iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KernelSyms.install_trans + 0x6c))
              (mword_of_int 8154 : mword 13) Rs6 M (K - 10)%nat eb
              ltac:(vm_compute; discriminate) Hnz6c with "Hcg Hpc Hi6c [-]").
    iIntros (CIDa1 Hsa1) "Hcg Hpc".
    assert (Hpp70 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x6c) : mword 64) 4
                    = mword_of_int (KernelSyms.install_trans + 0x70))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp70) in "Hpc".
    (* ===== +0x70 lw a1,24(s4) : a1 := log.start ===== *)
    assert (Hastart : add_vec (rget M Rs4) (sign_extend' 64 (mword_of_int 24 : mword 12))
                      = l_start).
    { rgne. rewrite HMs4. exact it_addr_start. }
    iEval (rewrite -Hastart) in "Hstc".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.install_trans + 0x70)) Ra1 Rs4 (mword_of_int 24 : mword 12)
              M (K - 10)%nat (mword_of_int logstart : mword 32) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi70 Hstc [-]").
    iIntros (CIDa2 Hsa2) "Hcg Hpc Hstc2".
    iEval (rewrite Hastart) in "Hstc".
    set (A1 := <[Regidx Ra1 := regval_into_reg
                  (sign_extend' 64 (mword_of_int logstart : mword 32))]> M).
    assert (HA1a1 : A1 !!! Regidx Ra1 = (mword_of_int logstart : mword 64))
      by (rewrite /A1 upd_eq; apply it_sext32; exact Har1).
    assert (HA1regs : it_lregs m A1 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact Hregs]).
    pose proof HA1regs as (_ & HA1s3 & HA1s4 & HA1s5 & HA1s6 & HA1s7 & _ & _ & _).
    assert (Hpp74 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x70) : mword 64) 4
                    = mword_of_int (KernelSyms.install_trans + 0x74))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp74) in "Hpc".
    (* ===== +0x74 addw a1,a1,s3 : a1 := log.start + tail ===== *)
    assert (Hwv74 : sign_extend' 64
                      (add_vec (subrange_vec_dec (rget A1 Ra1) 31 0 : mword 32)
                               (subrange_vec_dec (rget A1 Rs3) 31 0 : mword 32))
                    = (mword_of_int (logstart + Z.of_nat t) : mword 64)).
    { rgne. rgne. rewrite HA1a1 HA1s3.
      apply it_addw; [exact Har3 | exact Har2 | exact Har5]. }
    iApply (wp_addw4_s_sconf (mword_of_int (KernelSyms.install_trans + 0x74)) Ra1 Ra1 Rs3 A1 (K - 10)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi74 [-]").
    iIntros (CIDa3 Hsa3) "Hcg Hpc".
    iEval (rewrite Hwv74) in "Hcg".
    set (A2 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int (logstart + Z.of_nat t) : mword 64)]> A1).
    assert (HA2a1 : A2 !!! Regidx Ra1 = (mword_of_int (logstart + Z.of_nat t) : mword 64))
      by (rewrite /A2 upd_eq; reflexivity).
    assert (HA2regs : it_lregs m A2 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HA1regs]).
    assert (Hpp78 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x74) : mword 64) 4
                    = mword_of_int (KernelSyms.install_trans + 0x78))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp78) in "Hpc".
    (* ===== +0x78 c.addiw a1,a1,1 : a1 := the log slot's block number ===== *)
    assert (Hwv78 : sign_extend' 64 (subrange_vec_dec
                      (add_vec (rget A2 Ra1)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
                    = (mword_of_int (logstart + Z.of_nat t + 1) : mword 64)).
    { rgne. rewrite HA2a1. apply it_addiw; [exact Har4 | exact Har6]. }
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.install_trans + 0x78)) Ra1 (mword_of_int 1 : mword 6)
              A2 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi78 [-]").
    iIntros (CIDa4 Hsa4) "Hcg Hpc".
    iEval (rewrite Hwv78) in "Hcg".
    set (A3 := <[Regidx Ra1 := regval_into_reg
                  (mword_of_int (logstart + Z.of_nat t + 1) : mword 64)]> A2).
    assert (HA3a1 : A3 !!! Regidx Ra1 = sign_extend' 64 bnol).
    { rewrite /A3 upd_eq /bnol (it_sext32 (log_slot_bno logstart t) Har9).
      rewrite -Har7. reflexivity. }
    assert (HA3regs : it_lregs m A3 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HA2regs]).
    pose proof HA3regs as (_ & _ & HA3s4 & HA3s5 & _ & _ & _ & _ & _).
    assert (Hpp7a : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x78) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0x7a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7a) in "Hpc".
    (* ===== +0x7a lw a0,36(s4) : a0 := log.dev ===== *)
    assert (Hadev : add_vec (rget A3 Rs4) (sign_extend' 64 (mword_of_int 36 : mword 12))
                    = l_dev).
    { rgne. rewrite HA3s4. exact it_addr_dev. }
    iEval (rewrite -Hadev) in "Hdevc".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.install_trans + 0x7a)) Ra0 Rs4 (mword_of_int 36 : mword 12)
              A3 (K - 10)%nat dev eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi7a Hdevc [-]").
    iIntros (CIDa5 Hsa5) "Hcg Hpc Hdevc2".
    iEval (rewrite Hadev) in "Hdevc".
    set (A4 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> A3).
    assert (HA4a0 : A4 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /A4 upd_eq; reflexivity).
    assert (HA4a1 : A4 !!! Regidx Ra1 = sign_extend' 64 bnol)
      by (rewrite /A4 upd_ne; [exact HA3a1 | vm_compute; discriminate]).
    assert (HA4regs : it_lregs m A4 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HA3regs]).
    assert (Hpp7e : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x7a) : mword 64) 4
                    = mword_of_int (KernelSyms.install_trans + 0x7e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp7e) in "Hpc".
    (* ===== +0x7e jal ra,bread : lbuf = bread(dev, log slot) ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.install_trans + 0x7e)) Rra (mword_of_int 2093078 : mword 21)
              A4 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi7e [-]").
    iIntros (CIDa6 Hsa6) "Hcg Hpc".
    set (A5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.install_trans + 0x7e) : mword 64) 4)]> A4).
    assert (Htgt7e : add_vec (mword_of_int (KernelSyms.install_trans + 0x7e) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093078 : mword 21))
                     = mword_of_int KernelSyms.bread)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt7e) in "Hpc".
    assert (HA5a0 : A5 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /A5 upd_ne; [exact HA4a0 | vm_compute; discriminate]).
    assert (HA5a1 : A5 !!! Regidx Ra1 = sign_extend' 64 bnol)
      by (rewrite /A5 upd_ne; [exact HA4a1 | vm_compute; discriminate]).
    assert (HA5ra : A5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.install_trans + 0x7e) : mword 64) 4)
      by (rewrite /A5; apply upd_eq).
    assert (HA5regs : it_lregs m A5 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HA4regs]).
    iDestruct (cpu_own_transport CID0 CIDa6 0%nat eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDa6 eb (proc_addr j) ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDa6 eb (proc_addr j) ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iApply (Bread.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev bnol dq A5 (K - 10)%nat eb C eb
              (it_Kbread K HK)
              ltac:(rewrite Hubnol; exact (it_lt_lit _ Hslotrange))
              ltac:(reflexivity) ltac:(rewrite Hubnol; exact Hslotcov) ltac:(reflexivity)
              Hj Hgl HA5a0 HA5a1
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs
                    Hdev Hgeo Hdlock Hu1 [-]").
    iIntros (CIDb1 Hsb1 mf1 k1 bs1 bsd1 d1) "%Hpair1 Hcg Hcnt Hextc Hextm Hpc Hppid Hlk1".
    destruct Hpair1 as [Hcs1 Hmf1a0].
    assert (Hpc82 : ret_pc (A5 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.install_trans + 0x82)).
    { rewrite HA5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc82) in "Hpc".
    assert (Hmf1regs : it_lregs m mf1 t) by exact (it_lregs_cs m A5 mf1 t Hcs1 HA5regs).
    (* the log slot's bytes ARE the logged content: the payload's L-half
       against the batch's own client half *)
    iEval (rewrite /bio_locked /bio_held) in "Hlk1".
    iDestruct "Hlk1" as "(%Hk1 & %Hcv1 & %Hdv1 & Hslk1 & Hspid1 & Hvld1 & Hbdev1 & Hbuf1 & Hdsk1 & Hpay1)".
    iDestruct (it_pay_bs with "Hfblog Hpay1") as %Hbs1. subst bs1.
    (* ===== +0x82 c.mv s2,a0 : s2 := lbuf ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.install_trans + 0x82)) Rs2 Ra0
              mf1 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi82 [-]").
    iIntros (CIDa7 Hsa7) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A6 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mf1 !!! Regidx Ra0))]> mf1).
    assert (HA6s2 : A6 !!! Regidx Rs2 = bnode k1).
    { rewrite /A6 upd_eq add_vec_zero_l. exact Hmf1a0. }
    assert (HA6regs : it_lregs m A6 t)
      by (apply it_lregs_upd_s2; exact Hmf1regs).
    pose proof HA6regs as (_ & _ & HA6s4 & HA6s5 & _ & _ & _ & _ & _).
    assert (Hpp84 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x82) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0x84))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp84) in "Hpc".
    (* ===== +0x84 lw a1,0(s5) : a1 := log.lh.block[tail] ===== *)
    assert (Hacur : add_vec (rget A6 Rs5) (sign_extend' 64 (mword_of_int 0 : mword 12))
                    = lh_block t).
    { rgne. rewrite HA6s5. exact (it_cursor_at t). }
    iEval (rewrite -Hacur) in "Hblk".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.install_trans + 0x84)) Ra1 Rs5 (mword_of_int 0 : mword 12)
              A6 (K - 10)%nat w eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi84 Hblk [-]").
    iIntros (CIDa8 Hsa8) "Hcg Hpc Hblk".
    iEval (rewrite Hacur) in "Hblk".
    set (A7 := <[Regidx Ra1 := regval_into_reg (sign_extend' 64 w)]> A6).
    assert (HA7a1 : A7 !!! Regidx Ra1 = sign_extend' 64 w)
      by (rewrite /A7 upd_eq; reflexivity).
    assert (HA7s2 : A7 !!! Regidx Rs2 = bnode k1)
      by (rewrite /A7 upd_ne; [exact HA6s2 | vm_compute; discriminate]).
    assert (HA7regs : it_lregs m A7 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HA6regs]).
    pose proof HA7regs as (_ & _ & HA7s4 & _ & _ & _ & _ & _ & _).
    assert (Hpp88 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x84) : mword 64) 4
                    = mword_of_int (KernelSyms.install_trans + 0x88))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp88) in "Hpc".
    (* ===== +0x88 lw a0,36(s4) : a0 := log.dev ===== *)
    assert (Hadev2 : add_vec (rget A7 Rs4) (sign_extend' 64 (mword_of_int 36 : mword 12))
                     = l_dev).
    { rgne. rewrite HA7s4. exact it_addr_dev. }
    iEval (rewrite -Hadev2) in "Hdevc".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.install_trans + 0x88)) Ra0 Rs4 (mword_of_int 36 : mword 12)
              A7 (K - 10)%nat dev eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi88 Hdevc [-]").
    iIntros (CIDa9 Hsa9) "Hcg Hpc Hdevc3".
    iEval (rewrite Hadev2) in "Hdevc".
    set (A8 := <[Regidx Ra0 := regval_into_reg (sign_extend' 64 dev)]> A7).
    assert (HA8a0 : A8 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /A8 upd_eq; reflexivity).
    assert (HA8a1 : A8 !!! Regidx Ra1 = sign_extend' 64 w)
      by (rewrite /A8 upd_ne; [exact HA7a1 | vm_compute; discriminate]).
    assert (HA8s2 : A8 !!! Regidx Rs2 = bnode k1)
      by (rewrite /A8 upd_ne; [exact HA7s2 | vm_compute; discriminate]).
    assert (HA8regs : it_lregs m A8 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HA7regs]).
    assert (Hpp8c : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x88) : mword 64) 4
                    = mword_of_int (KernelSyms.install_trans + 0x8c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp8c) in "Hpc".
    (* ===== +0x8c jal ra,bread : dbuf = bread(dev, W[tail]) ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.install_trans + 0x8c)) Rra (mword_of_int 2093064 : mword 21)
              A8 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi8c [-]").
    iIntros (CIDa10 Hsa10) "Hcg Hpc".
    set (A9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.install_trans + 0x8c) : mword 64) 4)]> A8).
    assert (Htgt8c : add_vec (mword_of_int (KernelSyms.install_trans + 0x8c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093064 : mword 21))
                     = mword_of_int KernelSyms.bread)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt8c) in "Hpc".
    assert (HA9a0 : A9 !!! Regidx Ra0 = sign_extend' 64 dev)
      by (rewrite /A9 upd_ne; [exact HA8a0 | vm_compute; discriminate]).
    assert (HA9a1 : A9 !!! Regidx Ra1 = sign_extend' 64 w)
      by (rewrite /A9 upd_ne; [exact HA8a1 | vm_compute; discriminate]).
    assert (HA9s2 : A9 !!! Regidx Rs2 = bnode k1)
      by (rewrite /A9 upd_ne; [exact HA8s2 | vm_compute; discriminate]).
    assert (HA9ra : A9 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.install_trans + 0x8c) : mword 64) 4)
      by (rewrite /A9; apply upd_eq).
    assert (HA9regs : it_lregs m A9 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HA8regs]).
    iDestruct (cpu_own_transport CIDb1 CIDa10 0%nat eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDb1 CIDa10 eb (proc_addr j) ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDb1 CIDa10 eb (proc_addr j) ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iApply (Bread.wp_bread_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) pidv dev w dq A9 (K - 10)%nat eb C eb
              (it_Kbread K HK)
              ltac:(exact (it_lt_lit _ Hwrange))
              ltac:(reflexivity) ltac:(exact Hwcov) ltac:(reflexivity)
              Hj Hgl HA9a0 HA9a1
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs
                    Hdev Hgeo Hdlock Hu2 [-]").
    iIntros (CIDb2 Hsb2 mf2 k2 bs2 bsd2 d2) "%Hpair2 Hcg Hcnt Hextc Hextm Hpc Hppid Hlk2".
    destruct Hpair2 as [Hcs2 Hmf2a0].
    assert (Hpc90 : ret_pc (A9 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.install_trans + 0x90)).
    { rewrite HA9ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc90) in "Hpc".
    assert (Hmf2regs : it_lregs m mf2 t) by exact (it_lregs_cs m A9 mf2 t Hcs2 HA9regs).
    assert (Hmf2s2 : mf2 !!! Regidx Rs2 = bnode k1).
    { rewrite (callee_saved_lookup Hcs2 Rs2 ltac:(vm_compute; reflexivity)). exact HA9s2. }
    (* the home block arrives DIRTY (its dirty half agrees with the batch's,
       which is at true), and its bytes are the logged content *)
    iEval (rewrite /bio_locked /bio_held) in "Hlk2".
    iDestruct "Hlk2" as "(%Hk2 & %Hcv2 & %Hdv2 & Hslk2 & Hspid2 & Hvld2 & Hbdev2 & Hbuf2 & Hdsk2 & Hpay2)".
    iDestruct (it_pay_d with "Hdirty Hpay2") as %Hd2. subst d2.
    iDestruct (it_pay_bs_auth with "HauthL Hpay2") as %Hlk2.
    assert (Hbs2 : bs2 = Lw t).
    { pose proof (HLw t w Hw) as Hlw2. rewrite Hlk2 in Hlw2.
      injection Hlw2 as Hlw3. exact Hlw3. }
    subst bs2.
    (* ===== +0x90 c.mv s1,a0 : s1 := dbuf ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.install_trans + 0x90)) Rs1 Ra0
              mf2 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi90 [-]").
    iIntros (CIDa11 Hsa11) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mf2 !!! Regidx Ra0))]> mf2).
    assert (HB1s1 : B1 !!! Regidx Rs1 = bnode k2).
    { rewrite /B1 upd_eq add_vec_zero_l. exact Hmf2a0. }
    assert (HB1s2 : B1 !!! Regidx Rs2 = bnode k1)
      by (rewrite /B1 upd_ne; [exact Hmf2s2 | vm_compute; discriminate]).
    assert (HB1a0 : B1 !!! Regidx Ra0 = bnode k2)
      by (rewrite /B1 upd_ne; [exact Hmf2a0 | vm_compute; discriminate]).
    assert (HB1regs : it_lregs m B1 t) by (apply it_lregs_upd_s1; exact Hmf2regs).
    pose proof HB1regs as (_ & _ & _ & _ & _ & HB1s7 & _ & _ & _).
    assert (Hpp92 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x90) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0x92))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp92) in "Hpc".
    (* ===== +0x92 c.mv a2,s7 : a2 := BSIZE ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.install_trans + 0x92)) Ra2 Rs7
              B1 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi92 [-]").
    iIntros (CIDa12 Hsa12) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B2 := <[Regidx Ra2 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (B1 !!! Regidx Rs7))]> B1).
    assert (HB2a2 : B2 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 1024%nat) : mword 64)).
    { rewrite /B2 upd_eq add_vec_zero_l HB1s7.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HB2s1 : B2 !!! Regidx Rs1 = bnode k2)
      by (rewrite /B2 upd_ne; [exact HB1s1 | vm_compute; discriminate]).
    assert (HB2s2 : B2 !!! Regidx Rs2 = bnode k1)
      by (rewrite /B2 upd_ne; [exact HB1s2 | vm_compute; discriminate]).
    assert (HB2a0 : B2 !!! Regidx Ra0 = bnode k2)
      by (rewrite /B2 upd_ne; [exact HB1a0 | vm_compute; discriminate]).
    assert (HB2regs : it_lregs m B2 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HB1regs]).
    assert (Hpp94 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x92) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0x94))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp94) in "Hpc".
    (* ===== +0x94 addi a1,s2,88 : a1 := lbuf->data ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.install_trans + 0x94)) Ra1 Rs2
              (mword_of_int 88 : mword 12) B2 (K - 10)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi94 [-]").
    iIntros (CIDa13 Hsa13) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (B2 !!! Regidx Rs2 : mword 64)
                     (sign_extend' 64 (mword_of_int 88 : mword 12)))]> B2).
    assert (HB3a1 : B3 !!! Regidx Ra1 = b_data (bpa k1)).
    { rewrite /B3 upd_eq HB2s2. rewrite /bpa. exact (it_data_off (bnode k1)). }
    assert (HB3a2 : B3 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 1024%nat) : mword 64))
      by (rewrite /B3 upd_ne; [exact HB2a2 | vm_compute; discriminate]).
    assert (HB3s1 : B3 !!! Regidx Rs1 = bnode k2)
      by (rewrite /B3 upd_ne; [exact HB2s1 | vm_compute; discriminate]).
    assert (HB3a0 : B3 !!! Regidx Ra0 = bnode k2)
      by (rewrite /B3 upd_ne; [exact HB2a0 | vm_compute; discriminate]).
    assert (HB3regs : it_lregs m B3 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HB2regs]).
    assert (Hpp98 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x94) : mword 64) 4
                    = mword_of_int (KernelSyms.install_trans + 0x98))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp98) in "Hpc".
    (* ===== +0x98 addi a0,a0,88 : a0 := dbuf->data ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.install_trans + 0x98)) Ra0 Ra0
              (mword_of_int 88 : mword 12) B3 (K - 10)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) with "Hcg Hpc Hi98 [-]").
    iIntros (CIDa14 Hsa14) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (B3 !!! Regidx Ra0 : mword 64)
                     (sign_extend' 64 (mword_of_int 88 : mword 12)))]> B3).
    assert (HB4a0 : B4 !!! Regidx Ra0 = b_data (bpa k2)).
    { rewrite /B4 upd_eq HB3a0. rewrite /bpa. exact (it_data_off (bnode k2)). }
    assert (HB4a1 : B4 !!! Regidx Ra1 = b_data (bpa k1))
      by (rewrite /B4 upd_ne; [exact HB3a1 | vm_compute; discriminate]).
    assert (HB4a2 : B4 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 1024%nat) : mword 64))
      by (rewrite /B4 upd_ne; [exact HB3a2 | vm_compute; discriminate]).
    assert (HB4s1 : B4 !!! Regidx Rs1 = bnode k2)
      by (rewrite /B4 upd_ne; [exact HB3s1 | vm_compute; discriminate]).
    assert (HB4regs : it_lregs m B4 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HB3regs]).
    assert (Hpp9c : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x98) : mword 64) 4
                    = mword_of_int (KernelSyms.install_trans + 0x9c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp9c) in "Hpc".
    (* ===== +0x9c jal ra,memmove ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.install_trans + 0x9c)) Rra (mword_of_int 2085236 : mword 21)
              B4 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi9c [-]").
    iIntros (CIDa15 Hsa15) "Hcg Hpc".
    set (B5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.install_trans + 0x9c) : mword 64) 4)]> B4).
    assert (Htgt9c : add_vec (mword_of_int (KernelSyms.install_trans + 0x9c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2085236 : mword 21))
                     = mword_of_int KernelSyms.memmove)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt9c) in "Hpc".
    assert (HB5a0 : B5 !!! Regidx Ra0 = b_data (bpa k2))
      by (rewrite /B5 upd_ne; [exact HB4a0 | vm_compute; discriminate]).
    assert (HB5a1 : B5 !!! Regidx Ra1 = b_data (bpa k1))
      by (rewrite /B5 upd_ne; [exact HB4a1 | vm_compute; discriminate]).
    assert (HB5a2 : B5 !!! Regidx Ra2 = (mword_of_int (Z.of_nat 1024%nat) : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a2 | vm_compute; discriminate]).
    assert (HB5s1 : B5 !!! Regidx Rs1 = bnode k2)
      by (rewrite /B5 upd_ne; [exact HB4s1 | vm_compute; discriminate]).
    assert (HB5ra : B5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.install_trans + 0x9c) : mword 64) 4)
      by (rewrite /B5; apply upd_eq).
    assert (HB5regs : it_lregs m B5 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HB4regs]).
    (* the two buffers' bytes, at the FUNCTION index memmove's contract uses *)
    iDestruct "Hbuf1" as "(Hbno1 & Hbdsk1 & %Hlen1 & Hdata1)".
    iDestruct "Hbuf2" as "(Hbno2 & Hbdsk2 & %Hlen2 & Hdata2)".
    iDestruct (it_data_fwd (b_data (bpa k1)) (Lw t) 1024%nat Hlen1 with "Hdata1") as "Hdata1".
    iDestruct (it_data_fwd (b_data (bpa k2)) (Lw t) 1024%nat Hlen2 with "Hdata2") as "Hdata2".
    iEval (rewrite -HB5a1) in "Hdata1".
    iEval (rewrite -HB5a0) in "Hdata2".
    iApply (Mm.wp_memmove_sconf B5 (K - 10)%nat 1024%nat
              (fun i => (Lw t) !!! i) (fun i => (Lw t) !!! i) eb (proc_addr j)
              (it_Kmm K HK)
              ltac:(vm_compute; reflexivity) HB5a2
              with "Hcg Htext Hpc Hdata1 Hdata2 [-]").
    iIntros (CIDa16 Hsa16 mf3) "Hcg Hpc Hdata1 Hdata2 %Hmf3a0 %Hcs3".
    iEval (rewrite HB5a1) in "Hdata1".
    iEval (rewrite HB5a0) in "Hdata2".
    iDestruct (it_data_back (b_data (bpa k1)) (Lw t) 1024%nat Hlen1 with "Hdata1") as "Hdata1".
    iDestruct (it_data_back (b_data (bpa k2)) (Lw t) 1024%nat Hlen2 with "Hdata2") as "Hdata2".
    assert (Hpca0 : ret_pc (B5 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.install_trans + 0xa0)).
    { rewrite HB5ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpca0) in "Hpc".
    assert (Hmf3regs : it_lregs m mf3 t) by exact (it_lregs_cs m B5 mf3 t Hcs3 HB5regs).
    assert (Hmf3s1 : mf3 !!! Regidx Rs1 = bnode k2).
    { rewrite (callee_saved_lookup Hcs3 Rs1 ltac:(vm_compute; reflexivity)). exact HB5s1. }
    (* ===== +0xa0 c.mv a0,s1 : a0 := dbuf ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.install_trans + 0xa0)) Ra0 Rs1
              mf3 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hia0 [-]").
    iIntros (CIDa17 Hsa17) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B6 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mf3 !!! Regidx Rs1))]> mf3).
    assert (HB6a0 : B6 !!! Regidx Ra0 = bnode k2).
    { rewrite /B6 upd_eq add_vec_zero_l. exact Hmf3s1. }
    assert (HB6s1 : B6 !!! Regidx Rs1 = bnode k2)
      by (rewrite /B6 upd_ne; [exact Hmf3s1 | vm_compute; discriminate]).
    assert (HB6regs : it_lregs m B6 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact Hmf3regs]).
    assert (Hppa2 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xa0) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xa2))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppa2) in "Hpc".
    (* ===== +0xa2 jal ra,bwrite : the home block's disk cell moves ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.install_trans + 0xa2)) Rra (mword_of_int 2093256 : mword 21)
              B6 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hia2 [-]").
    iIntros (CIDa18 Hsa18) "Hcg Hpc".
    set (B7 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.install_trans + 0xa2) : mword 64) 4)]> B6).
    assert (Htgta2 : add_vec (mword_of_int (KernelSyms.install_trans + 0xa2) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093256 : mword 21))
                     = mword_of_int KernelSyms.bwrite)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgta2) in "Hpc".
    assert (HB7a0 : B7 !!! Regidx Ra0 = bnode k2)
      by (rewrite /B7 upd_ne; [exact HB6a0 | vm_compute; discriminate]).
    assert (HB7s1 : B7 !!! Regidx Rs1 = bnode k2)
      by (rewrite /B7 upd_ne; [exact HB6s1 | vm_compute; discriminate]).
    assert (HB7ra : B7 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.install_trans + 0xa2) : mword 64) 4)
      by (rewrite /B7; apply upd_eq).
    assert (HB7regs : it_lregs m B7 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HB6regs]).
    (* the payload-less handle bwrite takes *)
    iAssert (buf_own (bpa k2) w (mword_of_int 0 : mword 32) (Lw t))
      with "[Hbno2 Hbdsk2 Hdata2]" as "Hbuf2".
    { rewrite /buf_own. iFrame "Hbno2 Hbdsk2 Hdata2". iPureIntro. exact Hlen2. }
    iAssert (bio_hold0 bn (fs_view γfs γd dev cov) k2 pidv dev w (Lw t) bsd2)
      with "[Hslk2 Hspid2 Hvld2 Hbdev2 Hbuf2 Hdsk2]" as "Hhold".
    { rewrite /bio_hold0.
      iSplitR; [iPureIntro; exact Hk2|].
      iSplitR; [iPureIntro; exact Hcv2|].
      iSplitR; [iPureIntro; exact Hdv2|].
      iFrame "Hslk2 Hspid2 Hvld2 Hbdev2 Hbuf2 Hdsk2". }
    iDestruct (cpu_own_transport CIDb2 CIDa18 0%nat eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDb2 CIDa18 eb (proc_addr j) ltac:(wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDb2 CIDa18 eb (proc_addr j) ltac:(wp_next_chain) with "Hextm") as "Hextm".
    iApply (Bwrite.wp_bwrite_sconf γs j γl γu γd γk pd pav pu bn
              (fs_view γfs γd dev cov) k2 pidv dev w dq B7 (K - 10)%nat eb C
              (Lw t) bsd2 eb R
              (it_Kbwrite K HK)
              ltac:(exact (it_lt_lit _ Hwrange)) ltac:(reflexivity) Hj Hgl Hk2 HB7a0
              with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hppid Hprocs
                    Hdev Hgeo Hdlock Hhold [HR] [-]").
    (* THIS ENTRY'S CRASH PERMIT, out of the generator, at the home block the
       code is about to overwrite: the threaded resource goes in and comes
       back through the write's own [▷ Q]. *)
    { iApply ("Hperm" $! t w (Lw t) with "[%] [%] HR");
        [exact Hw | exact Hlen2]. }
    iIntros (CIDb3 Hsb3 mf4) "%Hcs4 Hcg Hcnt Hextc Hextm Hpc Hppid Hhold HR".
    assert (Hpca6 : ret_pc (B7 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.install_trans + 0xa6)).
    { rewrite HB7ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpca6) in "Hpc".
    assert (Hmf4regs : it_lregs m mf4 t) by exact (it_lregs_cs m B7 mf4 t Hcs4 HB7regs).
    pose proof Hmf4regs as (_ & _ & _ & _ & Hmf4s6 & _ & _ & _ & _).
    assert (Hmf4s1 : mf4 !!! Regidx Rs1 = bnode k2).
    { rewrite (callee_saved_lookup Hcs4 Rs1 ltac:(vm_compute; reflexivity)). exact HB7s1. }
    (* ---- THE DIRTY FLIP: the pin is released, the payload turns clean ---- *)
    iDestruct (it_pay_open with "Hpay2") as "(HLhalf & Hdhalf & Hbref)".
    iMod (fs_dirty_flip γfs (dirty_clear D (map uint (take t W))) (uint w) true true false
            with "HauthD Hdhalf Hdirty") as "(%Hflip & HauthD & Hdn1 & Hdn2)".
    iEval (rewrite (it_dirty_flip_step D W t w Hnd Hw)) in "HauthD".
    iDestruct (it_pay_clean bn γfs γd dev cov k2 dev w (Lw t) with "HLhalf Hdn1") as "Hpay2c".
    (* ===== +0xa6 bnez s6 : NOT taken, so bunpin runs ===== *)
    assert (Hnza6 : neq_vec (rget mf4 Rs6) (zero_reg : mword 64) = false).
    { rgne. rewrite Hmf4s6. vm_compute. reflexivity. }
    iApply (wp_bnez_x0_fall_s_sconf (mword_of_int (KernelSyms.install_trans + 0xa6))
              (mword_of_int 8110 : mword 13) Rs6 mf4 (K - 10)%nat eb
              ltac:(vm_compute; discriminate) Hnza6 with "Hcg Hpc Hia6 [-]").
    iIntros (CIDa19 Hsa19) "Hcg Hpc".
    assert (Hppaa : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xa6) : mword 64) 4
                    = mword_of_int (KernelSyms.install_trans + 0xaa))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppaa) in "Hpc".
    (* ===== +0xaa c.mv a0,s1 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.install_trans + 0xaa)) Ra0 Rs1
              mf4 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hiaa [-]").
    iIntros (CIDa20 Hsa20) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B8 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (zero_reg : mword 64) (mf4 !!! Regidx Rs1))]> mf4).
    assert (HB8a0 : B8 !!! Regidx Ra0 = bnode k2).
    { rewrite /B8 upd_eq add_vec_zero_l. exact Hmf4s1. }
    assert (HB8s1 : B8 !!! Regidx Rs1 = bnode k2)
      by (rewrite /B8 upd_ne; [exact Hmf4s1 | vm_compute; discriminate]).
    assert (HB8regs : it_lregs m B8 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact Hmf4regs]).
    assert (Hppac : add_vec_int (mword_of_int (KernelSyms.install_trans + 0xaa) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0xac))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hppac) in "Hpc".
    (* ===== +0xac jal ra,bunpin : the freed pin unit comes back ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.install_trans + 0xac)) Rra (mword_of_int 2093480 : mword 21)
              B8 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hiac [-]").
    iIntros (CIDa21 Hsa21) "Hcg Hpc".
    set (B9 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KernelSyms.install_trans + 0xac) : mword 64) 4)]> B8).
    assert (Htgtac : add_vec (mword_of_int (KernelSyms.install_trans + 0xac) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093480 : mword 21))
                     = mword_of_int KernelSyms.bunpin)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtac) in "Hpc".
    assert (HB9a0 : B9 !!! Regidx Ra0 = bnode k2)
      by (rewrite /B9 upd_ne; [exact HB8a0 | vm_compute; discriminate]).
    assert (HB9s1 : B9 !!! Regidx Rs1 = bnode k2)
      by (rewrite /B9 upd_ne; [exact HB8s1 | vm_compute; discriminate]).
    assert (HB9ra : B9 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KernelSyms.install_trans + 0xac) : mword 64) 4)
      by (rewrite /B9; apply upd_eq).
    assert (HB9regs : it_lregs m B9 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HB8regs]).
    iDestruct "Hbref" as (qref) "Hbref".
    iDestruct (cpu_own_transport CIDb3 CIDa21 0%nat eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Bunpin.wp_bunpin_sconf bn (fs_view γfs γd dev cov) k2 qref dev w
              B9 0%nat eb (proc_addr j) C (K - 10)%nat eb
              (it_Kbunpin K HK) it_noff0 Hk2 HB9a0
              with "Hcg Hcnt Htext Hpc Hbio Hpanic Hbref [-]").
    iIntros (CIDb4 Hsb4 mf5) "Hcg Hcnt Hpc %Hcs5 Hu3".
    assert (Hpcb0 : ret_pc (B9 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.install_trans + 0xb0)).
    { rewrite HB9ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpcb0) in "Hpc".
    assert (Hmf5regs : it_lregs m mf5 t) by exact (it_lregs_cs m B9 mf5 t Hcs5 HB9regs).
    assert (Hmf5s1 : mf5 !!! Regidx Rs1 = bnode k2).
    { rewrite (callee_saved_lookup Hcs5 Rs1 ltac:(vm_compute; reflexivity)). exact HB9s1. }
    assert (Hmf5s2 : mf5 !!! Regidx Rs2 = bnode k1).
    { rewrite (callee_saved_lookup Hcs5 Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /B9 upd_ne; [| vm_compute; discriminate].
      rewrite /B8 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs4 Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /B7 upd_ne; [| vm_compute; discriminate].
      rewrite /B6 upd_ne; [| vm_compute; discriminate].
      rewrite (callee_saved_lookup Hcs3 Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /B5 upd_ne; [| vm_compute; discriminate].
      rewrite /B4 upd_ne; [| vm_compute; discriminate].
      rewrite /B3 upd_ne; [| vm_compute; discriminate].
      exact HB2s2. }
    (* ===== +0xb0 c.j -> +0x54 ===== *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.install_trans + 0xb0))
              (sign_extend' 21 (concat_vec (mword_of_int 2002 : mword 11) ('b"0")))
              mf5 (K - 10)%nat eb ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hib0 [-]").
    iIntros (CIDa22 Hsa22). iApply bi.later_intro. iIntros "Hcg Hpc".
    assert (Htgtb0 : add_vec (mword_of_int (KernelSyms.install_trans + 0xb0) : mword 64)
                       (sign_extend' 64 (sign_extend' 21
                          (concat_vec (mword_of_int 2002 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.install_trans + 0x54))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgtb0) in "Hpc".
    (* ===== +0x54 c.mv a0,s2 ; +0x56 jal brelse(lbuf) ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.install_trans + 0x54)) Ra0 Rs2
              mf5 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi54 [-]").
    iIntros (CIDa23 Hsa23) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B10 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (zero_reg : mword 64) (mf5 !!! Regidx Rs2))]> mf5).
    assert (HB10a0 : B10 !!! Regidx Ra0 = bnode k1).
    { rewrite /B10 upd_eq add_vec_zero_l. exact Hmf5s2. }
    assert (HB10s1 : B10 !!! Regidx Rs1 = bnode k2)
      by (rewrite /B10 upd_ne; [exact Hmf5s1 | vm_compute; discriminate]).
    assert (HB10regs : it_lregs m B10 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact Hmf5regs]).
    assert (Hpp56 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x54) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0x56))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp56) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.install_trans + 0x56)) Rra (mword_of_int 2093382 : mword 21)
              B10 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi56 [-]").
    iIntros (CIDa24 Hsa24) "Hcg Hpc".
    set (B11 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (KernelSyms.install_trans + 0x56) : mword 64) 4)]> B10).
    assert (Htgt56 : add_vec (mword_of_int (KernelSyms.install_trans + 0x56) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093382 : mword 21))
                     = mword_of_int KernelSyms.brelse)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt56) in "Hpc".
    assert (HB11a0 : B11 !!! Regidx Ra0 = bnode k1)
      by (rewrite /B11 upd_ne; [exact HB10a0 | vm_compute; discriminate]).
    assert (HB11s1 : B11 !!! Regidx Rs1 = bnode k2)
      by (rewrite /B11 upd_ne; [exact HB10s1 | vm_compute; discriminate]).
    assert (HB11ra : B11 !!! Regidx Rra
                     = add_vec_int (mword_of_int (KernelSyms.install_trans + 0x56) : mword 64) 4)
      by (rewrite /B11; apply upd_eq).
    assert (HB11regs : it_lregs m B11 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HB10regs]).
    iAssert (buf_own (bpa k1) bnol (mword_of_int 0 : mword 32) (Lw t))
      with "[Hbno1 Hbdsk1 Hdata1]" as "Hbuf1".
    { rewrite /buf_own. iFrame "Hbno1 Hbdsk1 Hdata1". iPureIntro. exact Hlen1. }
    iAssert (bio_locked bn (fs_view γfs γd dev cov) k1 pidv dev bnol (Lw t) bsd1 d1)
      with "[Hslk1 Hspid1 Hvld1 Hbdev1 Hbuf1 Hdsk1 Hpay1]" as "Hlk1".
    { rewrite /bio_locked /bio_held.
      iSplitR; [iPureIntro; exact Hk1|].
      iSplitR; [iPureIntro; exact Hcv1|].
      iSplitR; [iPureIntro; exact Hdv1|].
      iFrame "Hslk1 Hspid1 Hvld1 Hbdev1 Hbuf1 Hdsk1 Hpay1". }
    iDestruct (cpu_own_transport CIDb4 CIDa24 0%nat eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Brelse.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) k1 pidv dev bnol dq
              B11 (K - 10)%nat eb (proc_addr j) C (Lw t) bsd1 d1 eb
              (it_Kbrelse K HK) Hk1 HB11a0
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs Hlk1 [-]").
    iIntros (CIDb5 Hsb5 mf6) "%Hcs6 Hcg Hcnt Hpc Hppid Hu4".
    assert (Hpc5a : ret_pc (B11 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.install_trans + 0x5a)).
    { rewrite HB11ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc5a) in "Hpc".
    assert (Hmf6regs : it_lregs m mf6 t) by exact (it_lregs_cs m B11 mf6 t Hcs6 HB11regs).
    assert (Hmf6s1 : mf6 !!! Regidx Rs1 = bnode k2).
    { rewrite (callee_saved_lookup Hcs6 Rs1 ltac:(vm_compute; reflexivity)). exact HB11s1. }
    (* ===== +0x5a c.mv a0,s1 ; +0x5c jal brelse(dbuf) ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.install_trans + 0x5a)) Ra0 Rs1
              mf6 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5a [-]").
    iIntros (CIDa25 Hsa25) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B12 := <[Regidx Ra0 := regval_into_reg
                   (add_vec (zero_reg : mword 64) (mf6 !!! Regidx Rs1))]> mf6).
    assert (HB12a0 : B12 !!! Regidx Ra0 = bnode k2).
    { rewrite /B12 upd_eq add_vec_zero_l. exact Hmf6s1. }
    assert (HB12regs : it_lregs m B12 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact Hmf6regs]).
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x5a) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0x5c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.install_trans + 0x5c)) Rra (mword_of_int 2093376 : mword 21)
              B12 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi5c [-]").
    iIntros (CIDa26 Hsa26) "Hcg Hpc".
    set (B13 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (KernelSyms.install_trans + 0x5c) : mword 64) 4)]> B12).
    assert (Htgt5c : add_vec (mword_of_int (KernelSyms.install_trans + 0x5c) : mword 64)
                       (sign_extend' 64 (mword_of_int 2093376 : mword 21))
                     = mword_of_int KernelSyms.brelse)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt5c) in "Hpc".
    assert (HB13a0 : B13 !!! Regidx Ra0 = bnode k2)
      by (rewrite /B13 upd_ne; [exact HB12a0 | vm_compute; discriminate]).
    assert (HB13ra : B13 !!! Regidx Rra
                     = add_vec_int (mword_of_int (KernelSyms.install_trans + 0x5c) : mword 64) 4)
      by (rewrite /B13; apply upd_eq).
    assert (HB13regs : it_lregs m B13 t)
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HB12regs]).
    iEval (rewrite /bio_hold0) in "Hhold".
    iDestruct "Hhold" as "(%Hk2b & %Hcv2b & %Hdv2b & Hslk2 & Hspid2 & Hvld2 & Hbdev2 & Hbuf2 & Hdsk2)".
    iAssert (bio_locked bn (fs_view γfs γd dev cov) k2 pidv dev w (Lw t) (Lw t) false)
      with "[Hslk2 Hspid2 Hvld2 Hbdev2 Hbuf2 Hdsk2 Hpay2c]" as "Hlk2".
    { rewrite /bio_locked /bio_held.
      iSplitR; [iPureIntro; exact Hk2|].
      iSplitR; [iPureIntro; exact Hcv2|].
      iSplitR; [iPureIntro; exact Hdv2|].
      iFrame "Hslk2 Hspid2 Hvld2 Hbdev2 Hbuf2 Hdsk2 Hpay2c". }
    iDestruct (cpu_own_transport CIDb5 CIDa26 0%nat eb (proc_addr j) C eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Brelse.wp_brelse_sconf γs bn (fs_view γfs γd dev cov) k2 pidv dev w dq
              B13 (K - 10)%nat eb (proc_addr j) C (Lw t) (Lw t) false eb
              (it_Kbrelse K HK) Hk2 HB13a0
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hppid Hprocs Hlk2 [-]").
    iIntros (CIDb6 Hsb6 mf7) "%Hcs7 Hcg Hcnt Hpc Hppid Hu5".
    assert (Hpc60 : ret_pc (B13 !!! Regidx Rra : mword 64) = mword_of_int (KernelSyms.install_trans + 0x60)).
    { rewrite HB13ra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hpc60) in "Hpc".
    assert (Hmf7regs : it_lregs m mf7 t) by exact (it_lregs_cs m B13 mf7 t Hcs7 HB13regs).
    pose proof Hmf7regs as (Hmf7sp & Hmf7s3 & Hmf7s4 & Hmf7s5 & Hmf7s6 & Hmf7s7 &
                            Hmf7s9 & Hmf7s10 & Hmf7s11).
    (* ---- the batch's pieces, re-formed at tail+1 ---- *)
    iDestruct ("Hblkback" with "Hblk") as "Hblks".
    iAssert ([∗ list] i ↦ v ∈ take (S t) W,
               fsblock γfs (log_slot_bno logstart i) (Lw i) ∗
               (uint v) ↪[fs_dirty γfs]{#(1/2)} false)%I
      with "[Hdone Hfblog Hdn2]" as "Hdone".
    { rewrite (take_S_r W t w Hw) big_sepL_app (it_take_len W t (it_lt_len_le t n W Ht HnW)).
      iSplitL "Hdone"; [iExact "Hdone"|].
      rewrite big_sepL_singleton Nat.add_0_r.
      iEval (rewrite Hubnol) in "Hfblog". iFrame "Hfblog Hdn2". }
    iDestruct (it_rest_shift γfs logstart Lw t (drop (S t) W) with "Hrest") as "Hrest".
    iAssert (bslots bn (2 + S t)) with "[Hslots Hu3 Hu4 Hu5]" as "Hslots".
    { assert (Hq : (2 + S t)%nat = (1 + (1 + (1 + t)))%nat) by reflexivity.
      rewrite Hq !bslots_op. iFrame "Hu3 Hu4 Hu5 Hslots". }
    (* ===== +0x60 c.addiw s3,s3,1 ; +0x62 c.addi s5,s5,4 ===== *)
    assert (Hwv60 : sign_extend' 64 (subrange_vec_dec
                      (add_vec (rget mf7 Rs3)
                         (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0)
                    = (mword_of_int (Z.of_nat (S t)) : mword 64)).
    { rgne. rewrite Hmf7s3.
      rewrite (it_addiw (Z.of_nat t) Har2 (it_t1_small t n Ht Hn30)).
      exact (it_succ_moi t). }
    iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.install_trans + 0x60)) Rs3 (mword_of_int 1 : mword 6)
              mf7 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi60 [-]").
    iIntros (CIDa27 Hsa27) "Hcg Hpc".
    iEval (rewrite Hwv60) in "Hcg".
    set (B14 := <[Regidx Rs3 := regval_into_reg
                   (mword_of_int (Z.of_nat (S t)) : mword 64)]> mf7).
    assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x60) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0x62))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp62) in "Hpc".
    assert (Hwv62 : add_vec (rget B14 Rs5)
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 4 : mword 6)))
                    = (lh_block (S t) : mword 64)).
    { rgne. rewrite /B14 upd_ne; [| vm_compute; discriminate].
      rewrite Hmf7s5. exact (it_cursor_step t). }
    iApply (wp_caddi_s_sconf (mword_of_int (KernelSyms.install_trans + 0x62)) Rs5 (mword_of_int 4 : mword 6)
              B14 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi62 [-]").
    iIntros (CIDa28 Hsa28) "Hcg Hpc".
    iEval (rewrite Hwv62) in "Hcg".
    set (B15 := <[Regidx Rs5 := regval_into_reg (lh_block (S t) : mword 64)]> B14).
    assert (HB15regs : it_lregs m B15 (S t)).
    { rewrite /it_lregs. split_and!.
      - rewrite /B15 upd_ne; [| vm_compute; discriminate].
        rewrite /B14 upd_ne; [exact Hmf7sp | vm_compute; discriminate].
      - rewrite /B15 upd_ne; [| vm_compute; discriminate].
        rewrite /B14 upd_eq. reflexivity.
      - rewrite /B15 upd_ne; [| vm_compute; discriminate].
        rewrite /B14 upd_ne; [exact Hmf7s4 | vm_compute; discriminate].
      - rewrite /B15 upd_eq. reflexivity.
      - rewrite /B15 upd_ne; [| vm_compute; discriminate].
        rewrite /B14 upd_ne; [exact Hmf7s6 | vm_compute; discriminate].
      - rewrite /B15 upd_ne; [| vm_compute; discriminate].
        rewrite /B14 upd_ne; [exact Hmf7s7 | vm_compute; discriminate].
      - rewrite /B15 upd_ne; [| vm_compute; discriminate].
        rewrite /B14 upd_ne; [exact Hmf7s9 | vm_compute; discriminate].
      - rewrite /B15 upd_ne; [| vm_compute; discriminate].
        rewrite /B14 upd_ne; [exact Hmf7s10 | vm_compute; discriminate].
      - rewrite /B15 upd_ne; [| vm_compute; discriminate].
        rewrite /B14 upd_ne; [exact Hmf7s11 | vm_compute; discriminate]. }
    pose proof HB15regs as (HB15sp & HB15s3 & HB15s4 & HB15s5 & HB15s6 & HB15s7 &
                            HB15s9 & HB15s10 & HB15s11).
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x62) : mword 64) 2
                    = mword_of_int (KernelSyms.install_trans + 0x64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    (* ===== +0x64 lw a5,44(s4) : reload log.lh.n ===== *)
    assert (Halhn : add_vec (rget B15 Rs4) (sign_extend' 64 (mword_of_int 44 : mword 12))
                    = lh_n_pa).
    { rgne. rewrite HB15s4. exact it_addr_lhn. }
    iEval (rewrite -Halhn) in "Hncell".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.install_trans + 0x64)) Ra5 Rs4 (mword_of_int 44 : mword 12)
              B15 (K - 10)%nat (mword_of_int (Z.of_nat n) : mword 32) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi64 Hncell [-]").
    iIntros (CIDa29 Hsa29) "Hcg Hpc Hncell".
    iEval (rewrite Halhn) in "Hncell".
    set (B16 := <[Regidx Ra5 := regval_into_reg
                   (sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32))]> B15).
    assert (HB16a5 : B16 !!! Regidx Ra5 = (mword_of_int (Z.of_nat n) : mword 64))
      by (rewrite /B16 upd_eq; apply it_sext32; exact (it_n_small n Hn30)).
    assert (HB16regs : it_lregs m B16 (S t))
      by (apply it_lregs_upd; [vm_compute; reflexivity | exact HB15regs]).
    pose proof HB16regs as (HB16sp & HB16s3 & _ & _ & _ & _ & HB16s9 & HB16s10 & HB16s11).
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x64) : mword 64) 4
                    = mword_of_int (KernelSyms.install_trans + 0x68))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* ===== +0x68 bge s3,a5 : the loop's exit test ===== *)
    assert (Hgeq : zopz0zKzJ_s (rget B16 Rs3) (rget B16 Ra5)
                   = Z.geb (Z.of_nat (S t)) (Z.of_nat n)).
    { rgne. rgne. rewrite HB16s3 HB16a5.
      apply it_geb_s; [ exact (it_St_small t n Ht Hn30) | exact (it_n_small n Hn30) ]. }
    destruct (decide (S t = n)) as [Hend | Hmore].
    + (* ---- the last entry: take the exit into the epilogue ---- *)
      iApply (wp_bge_taken_s_sconf (mword_of_int (KernelSyms.install_trans + 0x68)) (mword_of_int 74 : mword 13)
                Ra5 Rs3 B16 (K - 10)%nat eb
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hgeq; exact (it_geb_eq t n Hend))
                ltac:(vm_compute; reflexivity) with "Hcg Hpc Hi68 [-]").
      iNext. iIntros (CIDa30 Hsa30) "Hcg Hpc".
      assert (Htgtb2 : add_vec (mword_of_int (KernelSyms.install_trans + 0x68) : mword 64)
                         (sign_extend' 64 (mword_of_int 74 : mword 13))
                       = mword_of_int (KernelSyms.install_trans + 0xb2))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtb2) in "Hpc".
      rewrite Hend.
      rewrite (it_take_all W n HnW).
      iDestruct (cpu_own_transport CIDb6 CIDa30 0%nat eb (proc_addr j) C eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      (* [bunpin]/[brelse] thread neither -- transport across the WIDER span
         from the last hart that actually carried them (right after
         [bwrite]'s own continuation), not their own crossing. *)
      iDestruct (trap_csrs_ext_transport CIDb3 CIDa30 eb (proc_addr j) ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDb3 CIDa30 eb (proc_addr j) ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (it_cont_shift (CIDa := CID0) (CIDb := CIDa30)  j bn γfs logstart n W
                   Lw L D pidv dq m K eb C eb R ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (it_epi (CID0 := CIDa30)  j bn γfs logstart n W Lw L D pidv dq m B16 K eb C R
                HK HB16sp HB16s9 HB16s10 HB16s11
                with "Hcg Htext Hpc Hframe Hcnt Hextc Hextm Hppid
                      [Hncell Hblks HauthL HauthD Hdone Hslots] HR Hcont").
      rewrite /it_out (it_len_eq W n HnW).
      iFrame "Hncell Hblks HauthL HauthD Hdone Hslots".
    + (* ---- another entry: back to +0x6c ---- *)
      iApply (wp_bge_fall_s_sconf (mword_of_int (KernelSyms.install_trans + 0x68)) (mword_of_int 74 : mword 13)
                Ra5 Rs3 B16 (K - 10)%nat eb
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                ltac:(rewrite Hgeq; exact (it_geb_ne t n Ht Hmore))
                with "Hcg Hpc Hi68 [-]").
      iIntros (CIDa30 Hsa30) "Hcg Hpc".
      assert (Hpp6c : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x68) : mword 64) 4
                      = mword_of_int (KernelSyms.install_trans + 0x6c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp6c) in "Hpc".
      iDestruct (cpu_own_transport CIDb6 CIDa30 0%nat eb (proc_addr j) C eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      (* same wider-span transport as the exit arm: [bunpin]/[brelse] never
         held these. *)
      iDestruct (trap_csrs_ext_transport CIDb3 CIDa30 eb (proc_addr j) ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CIDb3 CIDa30 eb (proc_addr j) ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (it_cont_shift (CIDa := CID0) (CIDb := CIDa30)  j bn γfs logstart n W
                   Lw L D pidv dq m K eb C eb R ltac:(wp_next_chain) with "Hcont") as "Hcont".
      iApply (IH CIDa30 (S t) B16 (it_more t n Ht Hmore) (it_fuel_step t n fuel Hfuel)
                HB16regs
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio [] Hppid Hprocs
                      Hdev Hgeo Hdlock Hframe Hncell Hblks HauthL HauthD Hdone Hrest
                      Hslots Hperm HR Hcont").
      rewrite /log_frozen. iFrame "Hdevc Hstc".
  Qed.

End InstallTransBlocks.

(* ===================================================================== *)

Section ProofInstallTrans.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !uartGhostG Σ, !fsLogG Σ, !logG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_install_trans_sconf 
      (γs : list gname) (j : nat) (γl : gname)
      (γu : uart_names) (γd : disk_names) (γk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (recovering : bool)
      (n : nat) (W : list (mword 32)) (Lw : nat -> list (bv 8))
      (L : gmap Z (list (bv 8))) (D : gmap Z bool)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) (R : iProp Σ)
    : wp_install_trans_sconf_body γs j γl γu γd γk pd pav pu bn γfs
                                  cov logstart dev recovering n W Lw L D
                                  pidv dq m K eb C b R.
  Proof.
    cbv beta delta [wp_install_trans_sconf_body].
    intros pcE pj ret_tgt HK Hgeom Hj Hgl Hstage Ha0 Hshape Hnd Hwok HLw.
    destruct Hshape as [HnW Hn30].
    iIntros "Hcg Hcnt Hextc Hextm #Htext Hpc #Hpanic #Hbio #Hlfz Hppid #Hprocs".
    iIntros "#Hdev #Hgeo #Hdlock Hncell Hblks HauthL HauthD Hents Hslots #Hperm HR Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hbe. cbn in Hbe. subst b.
    iAssert (it_cont (CID0 := CID)  j bn γfs logstart n W Lw L D pidv dq m K eb C eb R)
      with "[Hcont]" as "Hcont".
    { rewrite /it_cont. iExact "Hcont". }
    iPoseProof (iti_00 with "Htext") as "Hi00".
    iPoseProof (iti_04 with "Htext") as "Hi04".
    iPoseProof (iti_08 with "Htext") as "Hi08".
    iPoseProof (iti_ca with "Htext") as "Hica".
    (* ===== +0x00 auipc a5,0x1f ===== *)
    iApply (wp_auipc_s_sconf pcE Ra5 (mword_of_int 31 : mword 20)
              m K eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hpc".
    set (R1 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (pcE : mword 64) (auipc_off (mword_of_int 31 : mword 20)))]> m).
    assert (Hpp04 : add_vec_int (pcE : mword 64) 4 = mword_of_int (KernelSyms.install_trans + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ===== +0x04 lw a5,-1864(a5) : a5 := log.lh.n ===== *)
    assert (Hna : add_vec (rget R1 Ra5) (sign_extend' 64 (mword_of_int 2276 : mword 12))
                  = lh_n_pa).
    { rgne. rewrite /R1 upd_eq. exact it_reloc_lhn. }
    iEval (rewrite -Hna) in "Hncell".
    iApply (wp_lw_s_sconf (mword_of_int (KernelSyms.install_trans + 0x04)) Ra5 Ra5
              (mword_of_int 2276 : mword 12) R1 K
              (mword_of_int (Z.of_nat n) : mword 32) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi04 Hncell [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hncell".
    iEval (rewrite Hna) in "Hncell".
    set (R2 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32))]> R1).
    assert (HR2a5 : R2 !!! Regidx Ra5 = (mword_of_int (Z.of_nat n) : mword 64))
      by (rewrite /R2 upd_eq; apply it_sext32; exact (it_n_small n Hn30)).
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x04) : mword 64) 4
                    = mword_of_int (KernelSyms.install_trans + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* the register threading across the two a5 writes *)
    assert (HR2thr : forall c : mword 5, is_cs_idx c = true ->
                       R2 !!! Regidx c = (m !!! Regidx c : mword 64)).
    { intros c Hcs.
      rewrite /R2 upd_ne; [| regne].
      rewrite /R1 upd_ne; [reflexivity | regne]. }
    assert (HR2ra : R2 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR2a0 : R2 !!! Regidx Ra0 = (m !!! Regidx Ra0 : mword 64)).
    { rewrite /R2 upd_ne; [| vm_compute; discriminate].
      rewrite /R1 upd_ne; [reflexivity | vm_compute; discriminate]. }
    assert (HR2cs : callee_saved m R2).
    { unfold callee_saved. split_and!; (apply HR2thr; vm_compute; reflexivity). }
    (* ===== +0x08 blez a5 : the PRE-FRAME test ===== *)
    destruct (decide (n = 0%nat)) as [Hn0 | Hnpos].
    - (* ---- n = 0: the bare [c.ret] at +0xca, nothing done ---- *)
      assert (Hge : zopz0zKzJ_s (zero_reg : mword 64) (rget R2 Ra5) = true).
      { rgne. rewrite HR2a5 (it_geb_s0 (Z.of_nat n) (it_n_small n Hn30)) Hn0.
        reflexivity. }
      iApply (wp_bge_x0_taken_s_sconf (mword_of_int (KernelSyms.install_trans + 0x08))
                (mword_of_int 194 : mword 13) Ra5 R2 K eb
                ltac:(vm_compute; discriminate) Hge
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi08 [-]").
      iNext. iIntros (CID3 Hs3) "Hcg Hpc".
      assert (Htgtca : add_vec (mword_of_int (KernelSyms.install_trans + 0x08) : mword 64)
                         (sign_extend' 64 (mword_of_int 194 : mword 13))
                       = mword_of_int (KernelSyms.install_trans + 0xca))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgtca) in "Hpc".
      iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.install_trans + 0xca)) Rra R2 K eb
                ltac:(vm_compute; discriminate) with "Hcg Hpc Hica [-]").
      iIntros (CID4 Hs4) "Hcg Hpc".
      assert (Hretf : ret_pc (rget R2 Rra) = ret_tgt).
      { rgne. rewrite HR2ra. reflexivity. }
      iEval (rewrite Hretf) in "Hpc".
      assert (HWnil : W = []) by exact (it_len0 n W HnW Hn0).
      subst W.
      iDestruct (cpu_own_transport CID CID4 0%nat eb (proc_addr j) C eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID CID4 eb (proc_addr j) ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID CID4 eb (proc_addr j) ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (it_cont_shift (CIDa := CID) (CIDb := CID4)  j bn γfs logstart n []
                   Lw L D pidv dq m K eb C eb R ltac:(wp_next_chain) with "Hcont") as "Hcont".
      rewrite /it_cont.
      iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain|].
      iApply ("Hcont" $! R2 with "[%] Hcg Hcnt Hextc Hextm Hpc Hppid Hncell Hblks
                                   HauthL HauthD Hents Hslots HR").
      exact HR2cs.
    - (* ---- n > 0: recovering = false, and the whole loop runs ---- *)
      assert (Hnp : (0 < n)%nat) by exact (it_pos n Hnpos).
      assert (Hrec : recovering = false)
        by (destruct Hstage as [Hr | Hz]; [exact Hr | congruence]).
      subst recovering.
      assert (Hge : zopz0zKzJ_s (zero_reg : mword 64) (rget R2 Ra5) = false).
      { rgne. rewrite HR2a5 (it_geb_s0 (Z.of_nat n) (it_n_small n Hn30)).
        exact (it_geb_pos n Hnp). }
      iApply (wp_bge_x0_fall_s_sconf (mword_of_int (KernelSyms.install_trans + 0x08))
                (mword_of_int 194 : mword 13) Ra5 R2 K eb
                ltac:(vm_compute; discriminate) Hge
                with "Hcg Hpc Hi08 [-]").
      iIntros (CID3 Hs3) "Hcg Hpc".
      assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x08) : mword 64) 4
                      = mword_of_int (KernelSyms.install_trans + 0x0c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp0c) in "Hpc".
      iPoseProof (iti_0c with "Htext") as "Hi0c".
      iPoseProof (iti_0e with "Htext") as "Hi0e".
      iPoseProof (iti_10 with "Htext") as "Hi10".
      iPoseProof (iti_12 with "Htext") as "Hi12".
      iPoseProof (iti_14 with "Htext") as "Hi14".
      iPoseProof (iti_16 with "Htext") as "Hi16".
      iPoseProof (iti_18 with "Htext") as "Hi18".
      iPoseProof (iti_1a with "Htext") as "Hi1a".
      iPoseProof (iti_1c with "Htext") as "Hi1c".
      iPoseProof (iti_1e with "Htext") as "Hi1e".
      iPoseProof (iti_20 with "Htext") as "Hi20".
      iPoseProof (iti_22 with "Htext") as "Hi22".
      iPoseProof (iti_24 with "Htext") as "Hi24".
      iPoseProof (iti_26 with "Htext") as "Hi26".
      iPoseProof (iti_2a with "Htext") as "Hi2a".
      iPoseProof (iti_2e with "Htext") as "Hi2e".
      iPoseProof (iti_30 with "Htext") as "Hi30".
      iPoseProof (iti_34 with "Htext") as "Hi34".
      iPoseProof (iti_38 with "Htext") as "Hi38".
      iPoseProof (iti_3c with "Htext") as "Hi3c".
      iPoseProof (iti_40 with "Htext") as "Hi40".
      iPoseProof (iti_44 with "Htext") as "Hi44".
      (* ===== +0x0c c.addi16sp sp,-80 : the frame ===== *)
      assert (Hpush : add_vec (R2 !!! Regidx csp_rs1 : mword 64)
                        (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6)))
                      = pa_stk (R2 !!! Regidx csp_rs1 : mword 64) 10).
      { unfold pa_stk, add_vec_int. apply f_equal.
        apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_caddi16sp_push_s_sconf (mword_of_int (KernelSyms.install_trans + 0x0c))
                (mword_of_int 59 : mword 6) R2 K 10 eb
                ltac:(unfold K_install_trans in HK; lia) Hpush
                with "Hcg Hpc Hi0c [-]").
      iIntros (CID4 Hs4) "Hcg Hframe Hpc".
      set (Q1 := <[Regidx csp_rs1 := regval_into_reg
                    (add_vec (R2 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> R2).
      change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (R2 !!! Regidx csp_rs1 : mword 64)
           (sign_extend' 64 (caddi16sp_imm (mword_of_int 59 : mword 6))))]> R2) with Q1.
      assert (HR2sp : R2 !!! Regidx csp_rs1 = (m !!! Regidx csp_rs1 : mword 64))
        by (exact (HR2thr csp_rs1 ltac:(vm_compute; reflexivity))).
      assert (HQ1sp : Q1 !!! Regidx csp_rs1 = it_spr m).
      { rewrite /Q1 upd_eq /it_spr HR2sp. reflexivity. }
      iEval (rewrite HR2sp) in "Hframe".
      iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
      iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & _)".
      iDestruct "S1" as (v1) "Hf1".   iDestruct "S2" as (v2) "Hf2".
      iDestruct "S3" as (v3) "Hf3".   iDestruct "S4" as (v4) "Hf4".
      iDestruct "S5" as (v5) "Hf5".   iDestruct "S6" as (v6) "Hf6".
      iDestruct "S7" as (v7) "Hf7".   iDestruct "S8" as (v8) "Hf8".
      iDestruct "S9" as (v9) "Hf9".   iDestruct "S10" as (v10) "Hf10".
      assert (Hb1 : add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 9 : mword 6) ('b"000")))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 1).
      { rewrite HQ1sp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      assert (HQ1r1 : Q1 !!! Regidx Rra = (m !!! Regidx Rra : mword 64)).
      { rewrite /Q1 upd_ne; [| vm_compute; discriminate]. exact (HR2ra). }
      iEval (rewrite -Hb1) in "Hf1".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0x0e)) (mword_of_int 9 : mword 6) Rra
                Q1 (K - 10)%nat v1 eb with "Hcg Hpc Hi0e Hf1 [-]").
      iIntros (CIDp1 Hsp1) "Hcg Hpc Hf1".
      iEval (rgne) in "Hf1".
      iEval (rewrite Hb1 HQ1r1) in "Hf1".
      assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x0e) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x10))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp10) in "Hpc".
      assert (Hb2 : add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 8 : mword 6) ('b"000")))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 2).
      { rewrite HQ1sp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      assert (HQ1r2 : Q1 !!! Regidx Rs0 = (m !!! Regidx Rs0 : mword 64)).
      { rewrite /Q1 upd_ne; [| vm_compute; discriminate]. exact (HR2thr Rs0 ltac:(vm_compute; reflexivity)). }
      iEval (rewrite -Hb2) in "Hf2".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0x10)) (mword_of_int 8 : mword 6) Rs0
                Q1 (K - 10)%nat v2 eb with "Hcg Hpc Hi10 Hf2 [-]").
      iIntros (CIDp2 Hsp2) "Hcg Hpc Hf2".
      iEval (rgne) in "Hf2".
      iEval (rewrite Hb2 HQ1r2) in "Hf2".
      assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x10) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x12))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp12) in "Hpc".
      assert (Hb3 : add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 7 : mword 6) ('b"000")))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 3).
      { rewrite HQ1sp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      assert (HQ1r3 : Q1 !!! Regidx Rs1 = (m !!! Regidx Rs1 : mword 64)).
      { rewrite /Q1 upd_ne; [| vm_compute; discriminate]. exact (HR2thr Rs1 ltac:(vm_compute; reflexivity)). }
      iEval (rewrite -Hb3) in "Hf3".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0x12)) (mword_of_int 7 : mword 6) Rs1
                Q1 (K - 10)%nat v3 eb with "Hcg Hpc Hi12 Hf3 [-]").
      iIntros (CIDp3 Hsp3) "Hcg Hpc Hf3".
      iEval (rgne) in "Hf3".
      iEval (rewrite Hb3 HQ1r3) in "Hf3".
      assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x12) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x14))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp14) in "Hpc".
      assert (Hb4 : add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 6 : mword 6) ('b"000")))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 4).
      { rewrite HQ1sp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      assert (HQ1r4 : Q1 !!! Regidx Rs2 = (m !!! Regidx Rs2 : mword 64)).
      { rewrite /Q1 upd_ne; [| vm_compute; discriminate]. exact (HR2thr Rs2 ltac:(vm_compute; reflexivity)). }
      iEval (rewrite -Hb4) in "Hf4".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0x14)) (mword_of_int 6 : mword 6) Rs2
                Q1 (K - 10)%nat v4 eb with "Hcg Hpc Hi14 Hf4 [-]").
      iIntros (CIDp4 Hsp4) "Hcg Hpc Hf4".
      iEval (rgne) in "Hf4".
      iEval (rewrite Hb4 HQ1r4) in "Hf4".
      assert (Hpp16 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x14) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x16))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp16) in "Hpc".
      assert (Hb5 : add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 5 : mword 6) ('b"000")))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 5).
      { rewrite HQ1sp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      assert (HQ1r5 : Q1 !!! Regidx Rs3 = (m !!! Regidx Rs3 : mword 64)).
      { rewrite /Q1 upd_ne; [| vm_compute; discriminate]. exact (HR2thr Rs3 ltac:(vm_compute; reflexivity)). }
      iEval (rewrite -Hb5) in "Hf5".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0x16)) (mword_of_int 5 : mword 6) Rs3
                Q1 (K - 10)%nat v5 eb with "Hcg Hpc Hi16 Hf5 [-]").
      iIntros (CIDp5 Hsp5) "Hcg Hpc Hf5".
      iEval (rgne) in "Hf5".
      iEval (rewrite Hb5 HQ1r5) in "Hf5".
      assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x16) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x18))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp18) in "Hpc".
      assert (Hb6 : add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 4 : mword 6) ('b"000")))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 6).
      { rewrite HQ1sp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      assert (HQ1r6 : Q1 !!! Regidx Rs4 = (m !!! Regidx Rs4 : mword 64)).
      { rewrite /Q1 upd_ne; [| vm_compute; discriminate]. exact (HR2thr Rs4 ltac:(vm_compute; reflexivity)). }
      iEval (rewrite -Hb6) in "Hf6".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0x18)) (mword_of_int 4 : mword 6) Rs4
                Q1 (K - 10)%nat v6 eb with "Hcg Hpc Hi18 Hf6 [-]").
      iIntros (CIDp6 Hsp6) "Hcg Hpc Hf6".
      iEval (rgne) in "Hf6".
      iEval (rewrite Hb6 HQ1r6) in "Hf6".
      assert (Hpp1a : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x18) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x1a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1a) in "Hpc".
      assert (Hb7 : add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000")))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 7).
      { rewrite HQ1sp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      assert (HQ1r7 : Q1 !!! Regidx Rs5 = (m !!! Regidx Rs5 : mword 64)).
      { rewrite /Q1 upd_ne; [| vm_compute; discriminate]. exact (HR2thr Rs5 ltac:(vm_compute; reflexivity)). }
      iEval (rewrite -Hb7) in "Hf7".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0x1a)) (mword_of_int 3 : mword 6) Rs5
                Q1 (K - 10)%nat v7 eb with "Hcg Hpc Hi1a Hf7 [-]").
      iIntros (CIDp7 Hsp7) "Hcg Hpc Hf7".
      iEval (rgne) in "Hf7".
      iEval (rewrite Hb7 HQ1r7) in "Hf7".
      assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x1a) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x1c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1c) in "Hpc".
      assert (Hb8 : add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000")))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 8).
      { rewrite HQ1sp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      assert (HQ1r8 : Q1 !!! Regidx Rs6 = (m !!! Regidx Rs6 : mword 64)).
      { rewrite /Q1 upd_ne; [| vm_compute; discriminate]. exact (HR2thr Rs6 ltac:(vm_compute; reflexivity)). }
      iEval (rewrite -Hb8) in "Hf8".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0x1c)) (mword_of_int 2 : mword 6) Rs6
                Q1 (K - 10)%nat v8 eb with "Hcg Hpc Hi1c Hf8 [-]").
      iIntros (CIDp8 Hsp8) "Hcg Hpc Hf8".
      iEval (rgne) in "Hf8".
      iEval (rewrite Hb8 HQ1r8) in "Hf8".
      assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x1c) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x1e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp1e) in "Hpc".
      assert (Hb9 : add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 9).
      { rewrite HQ1sp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      assert (HQ1r9 : Q1 !!! Regidx Rs7 = (m !!! Regidx Rs7 : mword 64)).
      { rewrite /Q1 upd_ne; [| vm_compute; discriminate]. exact (HR2thr Rs7 ltac:(vm_compute; reflexivity)). }
      iEval (rewrite -Hb9) in "Hf9".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0x1e)) (mword_of_int 1 : mword 6) Rs7
                Q1 (K - 10)%nat v9 eb with "Hcg Hpc Hi1e Hf9 [-]").
      iIntros (CIDp9 Hsp9) "Hcg Hpc Hf9".
      iEval (rgne) in "Hf9".
      iEval (rewrite Hb9 HQ1r9) in "Hf9".
      assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x1e) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x20))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      assert (Hb10 : add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                      (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))
                    = pa_stk (m !!! Regidx csp_rs1 : mword 64) 10).
      { rewrite HQ1sp (it_push m). unfold pa_stk, add_vec_int. rewrite add_vec_off2.
        f_equal; try (apply bv_eq; vm_compute; reflexivity). }
      assert (HQ1r10 : Q1 !!! Regidx Rs8 = (m !!! Regidx Rs8 : mword 64)).
      { rewrite /Q1 upd_ne; [| vm_compute; discriminate]. exact (HR2thr Rs8 ltac:(vm_compute; reflexivity)). }
      iEval (rewrite -Hb10) in "Hf10".
      iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.install_trans + 0x20)) (mword_of_int 0 : mword 6) Rs8
                Q1 (K - 10)%nat v10 eb with "Hcg Hpc Hi20 Hf10 [-]").
      iIntros (CIDp10 Hsp10) "Hcg Hpc Hf10".
      iEval (rgne) in "Hf10".
      iEval (rewrite Hb10 HQ1r10) in "Hf10".
      assert (Hpp22 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x20) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x22))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      iAssert (it_frame m) with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10]" as "Hframe".
      { rewrite /it_frame. iFrame. }
      (* ===== +0x22 c.addi4spn s0,sp,80 ===== *)
      iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.install_trans + 0x22)) (Cregidx (mword_of_int 0))
                (mword_of_int 20 : mword 8) Rs0 Q1 (K - 10)%nat eb
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rdok) with "Hcg Hpc Hi22 [-]").
      iIntros (CIDq2 Hsq2) "Hcg Hpc".
      set (Q2 := <[Regidx Rs0 := regval_into_reg
                    (add_vec (Q1 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi4spn_imm (mword_of_int 20 : mword 8))))]> Q1).
      assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x22) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x24))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp24) in "Hpc".
      (* ===== +0x24 c.mv s6,a0 : s6 := recovering = 0 ===== *)
      iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.install_trans + 0x24)) Rs6 Ra0
                Q2 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi24 [-]").
      iIntros (CIDq3 Hsq3) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (Q3 := <[Regidx Rs6 := regval_into_reg
                    (add_vec (zero_reg : mword 64) (Q2 !!! Regidx Ra0))]> Q2).
      assert (HQ3s6 : Q3 !!! Regidx Rs6 = (mword_of_int 0 : mword 64)).
      { rewrite /Q3 upd_eq. rewrite add_vec_zero_l.
        rewrite /Q2 upd_ne; [| vm_compute; discriminate].
        rewrite /Q1 upd_ne; [| vm_compute; discriminate].
        rewrite HR2a0. exact Ha0. }
      assert (Hpp26 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x24) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x26))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp26) in "Hpc".
      (* ===== +0x26 / +0x2a : s5 := &log.lh.block[0] ===== *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.install_trans + 0x26)) Rs5 (mword_of_int 31 : mword 20)
                Q3 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi26 [-]").
      iIntros (CIDq4 Hsq4) "Hcg Hpc".
      set (Q4 := <[Regidx Rs5 := regval_into_reg
                    (add_vec (mword_of_int (KernelSyms.install_trans + 0x26) : mword 64)
                       (auipc_off (mword_of_int 31 : mword 20)))]> Q3).
      assert (Hpp2a : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x26) : mword 64) 4
                      = mword_of_int (KernelSyms.install_trans + 0x2a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.install_trans + 0x2a)) Rs5 Rs5
                (mword_of_int 2242 : mword 12) Q4 (K - 10)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi2a [-]").
      iIntros (CIDq5 Hsq5) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (Q5 := <[Regidx Rs5 := regval_into_reg
                    (add_vec (Q4 !!! Regidx Rs5 : mword 64)
                       (sign_extend' 64 (mword_of_int 2242 : mword 12)))]> Q4).
      assert (HQ5s5 : Q5 !!! Regidx Rs5 = (lh_block 0 : mword 64)).
      { rewrite /Q5 upd_eq /Q4 upd_eq. exact it_reloc_blk0. }
      assert (Hpp2e : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x2a) : mword 64) 4
                      = mword_of_int (KernelSyms.install_trans + 0x2e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      (* ===== +0x2e c.li s3,0 ===== *)
      iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.install_trans + 0x2e)) Rs3 (mword_of_int 0 : mword 6)
                (mword_of_int (Z.of_nat 0) : mword 64) Q5 (K - 10)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok) it_li0
                with "Hcg Hpc Hi2e [-]").
      iIntros (CIDq6 Hsq6) "Hcg Hpc".
      set (Q6 := <[Regidx Rs3 := regval_into_reg
                    (mword_of_int (Z.of_nat 0) : mword 64)]> Q5).
      assert (Hpp30 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x2e) : mword 64) 2
                      = mword_of_int (KernelSyms.install_trans + 0x30))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp30) in "Hpc".
      (* ===== +0x30 / +0x34 : s8 := the printk format string ===== *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.install_trans + 0x30)) Rs8 (mword_of_int 4 : mword 20)
                Q6 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi30 [-]").
      iIntros (CIDq7 Hsq7) "Hcg Hpc".
      set (Q7 := <[Regidx Rs8 := regval_into_reg
                    (add_vec (mword_of_int (KernelSyms.install_trans + 0x30) : mword 64)
                       (auipc_off (mword_of_int 4 : mword 20)))]> Q6).
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x30) : mword 64) 4
                      = mword_of_int (KernelSyms.install_trans + 0x34))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.install_trans + 0x34)) Rs8 Rs8
                (mword_of_int 2512 : mword 12) Q7 (K - 10)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi34 [-]").
      iIntros (CIDq8 Hsq8) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (Q8 := <[Regidx Rs8 := regval_into_reg
                    (add_vec (Q7 !!! Regidx Rs8 : mword 64)
                       (sign_extend' 64 (mword_of_int 2512 : mword 12)))]> Q7).
      assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x34) : mword 64) 4
                      = mword_of_int (KernelSyms.install_trans + 0x38))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp38) in "Hpc".
      (* ===== +0x38 / +0x3c : s4 := &log ===== *)
      iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.install_trans + 0x38)) Rs4 (mword_of_int 31 : mword 20)
                Q8 (K - 10)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi38 [-]").
      iIntros (CIDq9 Hsq9) "Hcg Hpc".
      set (Q9 := <[Regidx Rs4 := regval_into_reg
                    (add_vec (mword_of_int (KernelSyms.install_trans + 0x38) : mword 64)
                       (auipc_off (mword_of_int 31 : mword 20)))]> Q8).
      assert (Hpp3c : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x38) : mword 64) 4
                      = mword_of_int (KernelSyms.install_trans + 0x3c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp3c) in "Hpc".
      iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.install_trans + 0x3c)) Rs4 Rs4
                (mword_of_int 2176 : mword 12) Q9 (K - 10)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3c [-]").
      iIntros (CIDq10 Hsq10) "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (Q10 := <[Regidx Rs4 := regval_into_reg
                     (add_vec (Q9 !!! Regidx Rs4 : mword 64)
                        (sign_extend' 64 (mword_of_int 2176 : mword 12)))]> Q9).
      assert (HQ10s4 : Q10 !!! Regidx Rs4 = log_addr).
      { rewrite /Q10 upd_eq /Q9 upd_eq. exact it_reloc_log. }
      assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x3c) : mword 64) 4
                      = mword_of_int (KernelSyms.install_trans + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* ===== +0x40 li s7,1024 ===== *)
      iApply (wp_li4_s_sconf (mword_of_int (KernelSyms.install_trans + 0x40)) Rs7 (mword_of_int 1024 : mword 12)
                (mword_of_int 1024 : mword 64) Q10 (K - 10)%nat eb
                ltac:(vm_compute; discriminate) ltac:(rdok) it_li1024
                with "Hcg Hpc Hi40 [-]").
      iIntros (CIDq11 Hsq11) "Hcg Hpc".
      set (Q11 := <[Regidx Rs7 := regval_into_reg (mword_of_int 1024 : mword 64)]> Q10).
      assert (Hpp44 : add_vec_int (mword_of_int (KernelSyms.install_trans + 0x40) : mword 64) 4
                      = mword_of_int (KernelSyms.install_trans + 0x44))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp44) in "Hpc".
      (* ===== +0x44 c.j -> +0x6c : into the loop ===== *)
      iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.install_trans + 0x44))
                (sign_extend' 21 (concat_vec (mword_of_int 20 : mword 11) ('b"0")))
                Q11 (K - 10)%nat eb ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi44 [-]").
      iIntros (CIDq12 Hsq12). iApply bi.later_intro. iIntros "Hcg Hpc".
      assert (Htgt6c : add_vec (mword_of_int (KernelSyms.install_trans + 0x44) : mword 64)
                         (sign_extend' 64 (sign_extend' 21
                            (concat_vec (mword_of_int 20 : mword 11) ('b"0"))))
                       = mword_of_int (KernelSyms.install_trans + 0x6c))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt6c) in "Hpc".
      (* the loop's register invariant at tail = 0 *)
      assert (HQ11thr : forall c : mword 5, is_cs_idx c = true ->
                          c <> csp_rs1 -> c <> Rs0 -> c <> Rs3 -> c <> Rs4 ->
                          c <> Rs5 -> c <> Rs6 -> c <> Rs7 -> c <> Rs8 ->
                          Q11 !!! Regidx c = (Q1 !!! Regidx c : mword 64)).
      { intros c Hcs N2 N8 N19 N20 N21 N22 N23 N24.
        rewrite /Q11 upd_ne; [| regne].
        rewrite /Q10 upd_ne; [| regne].
        rewrite /Q9 upd_ne; [| regne].
        rewrite /Q8 upd_ne; [| regne].
        rewrite /Q7 upd_ne; [| regne].
        rewrite /Q6 upd_ne; [| regne].
        rewrite /Q5 upd_ne; [| regne].
        rewrite /Q4 upd_ne; [| regne].
        rewrite /Q3 upd_ne; [| regne].
        rewrite /Q2 upd_ne; [reflexivity | regne]. }
      assert (HQ11sp : Q11 !!! Regidx csp_rs1 = it_spr m).
      { rewrite /Q11 upd_ne; [| vm_compute; discriminate].
        rewrite /Q10 upd_ne; [| vm_compute; discriminate].
        rewrite /Q9 upd_ne; [| vm_compute; discriminate].
        rewrite /Q8 upd_ne; [| vm_compute; discriminate].
        rewrite /Q7 upd_ne; [| vm_compute; discriminate].
        rewrite /Q6 upd_ne; [| vm_compute; discriminate].
        rewrite /Q5 upd_ne; [| vm_compute; discriminate].
        rewrite /Q4 upd_ne; [| vm_compute; discriminate].
        rewrite /Q3 upd_ne; [| vm_compute; discriminate].
        rewrite /Q2 upd_ne; [exact HQ1sp | vm_compute; discriminate]. }
      assert (HQ11s3 : Q11 !!! Regidx Rs3 = (mword_of_int (Z.of_nat 0) : mword 64)).
      { rewrite /Q11 upd_ne; [| vm_compute; discriminate].
        rewrite /Q10 upd_ne; [| vm_compute; discriminate].
        rewrite /Q9 upd_ne; [| vm_compute; discriminate].
        rewrite /Q8 upd_ne; [| vm_compute; discriminate].
        rewrite /Q7 upd_ne; [| vm_compute; discriminate].
        rewrite /Q6 upd_eq. reflexivity. }
      assert (HQ11s4 : Q11 !!! Regidx Rs4 = log_addr).
      { rewrite /Q11 upd_ne; [| vm_compute; discriminate].
        exact HQ10s4. }
      assert (HQ11s5 : Q11 !!! Regidx Rs5 = (lh_block 0 : mword 64)).
      { rewrite /Q11 upd_ne; [| vm_compute; discriminate].
        rewrite /Q10 upd_ne; [| vm_compute; discriminate].
        rewrite /Q9 upd_ne; [| vm_compute; discriminate].
        rewrite /Q8 upd_ne; [| vm_compute; discriminate].
        rewrite /Q7 upd_ne; [| vm_compute; discriminate].
        rewrite /Q6 upd_ne; [| vm_compute; discriminate].
        exact HQ5s5. }
      assert (HQ11s6 : Q11 !!! Regidx Rs6 = (mword_of_int 0 : mword 64)).
      { rewrite /Q11 upd_ne; [| vm_compute; discriminate].
        rewrite /Q10 upd_ne; [| vm_compute; discriminate].
        rewrite /Q9 upd_ne; [| vm_compute; discriminate].
        rewrite /Q8 upd_ne; [| vm_compute; discriminate].
        rewrite /Q7 upd_ne; [| vm_compute; discriminate].
        rewrite /Q6 upd_ne; [| vm_compute; discriminate].
        rewrite /Q5 upd_ne; [| vm_compute; discriminate].
        rewrite /Q4 upd_ne; [| vm_compute; discriminate].
        exact HQ3s6. }
      assert (HQ11s7 : Q11 !!! Regidx Rs7 = (mword_of_int 1024 : mword 64))
        by (rewrite /Q11 upd_eq; reflexivity).
      assert (HQ1thr : forall c : mword 5, is_cs_idx c = true -> c <> csp_rs1 ->
                         Q1 !!! Regidx c = (m !!! Regidx c : mword 64)).
      { intros c Hcs N2. rewrite /Q1 upd_ne; [| regne]. exact (HR2thr c Hcs). }
      assert (HQ11s9 : Q11 !!! Regidx Rs9 = (m !!! Regidx Rs9 : mword 64)).
      { rewrite (HQ11thr Rs9 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact (HQ1thr Rs9 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). }
      assert (HQ11s10 : Q11 !!! Regidx Rs10 = (m !!! Regidx Rs10 : mword 64)).
      { rewrite (HQ11thr Rs10 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact (HQ1thr Rs10 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). }
      assert (HQ11s11 : Q11 !!! Regidx Rs11 = (m !!! Regidx Rs11 : mword 64)).
      { rewrite (HQ11thr Rs11 ltac:(vm_compute; reflexivity)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                   ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)).
        exact (HQ1thr Rs11 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)). }
      iDestruct (cpu_own_transport CID CIDq12 0%nat eb (proc_addr j) C eb
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iDestruct (trap_csrs_ext_transport CID CIDq12 eb (proc_addr j) ltac:(wp_next_chain) with "Hextc") as "Hextc".
      iDestruct (cpu_claim_ext_transport CID CIDq12 eb (proc_addr j) ltac:(wp_next_chain) with "Hextm") as "Hextm".
      iDestruct (it_cont_shift (CIDa := CID) (CIDb := CIDq12)  j bn γfs logstart n W
                   Lw L D pidv dq m K eb C eb R ltac:(wp_next_chain) with "Hcont") as "Hcont".
      assert (HQ11regs : it_lregs m Q11 0%nat).
      { rewrite /it_lregs. split_and!; assumption. }
      iAssert ([∗ list] i ↦ w ∈ take 0 W,
                 fsblock γfs (log_slot_bno logstart i) (Lw i) ∗
                 (uint w) ↪[fs_dirty γfs]{#(1/2)} false)%I as "Hdone".
      { done. }
      iApply (it_loop n γs j γl γu γd γk pd pav pu bn γfs cov logstart dev
                n W Lw L D pidv dq m K eb C R
                HK Hgeom Hj Hgl (conj HnW Hn30) Hnd Hwok HLw
                CIDq12 0%nat Q11 Hnp (it_fuel0 n) HQ11regs
                with "Hcg Hcnt Hextc Hextm Htext Hpc Hpanic Hbio Hlfz Hppid Hprocs
                      Hdev Hgeo Hdlock Hframe Hncell Hblks HauthL HauthD Hdone Hents
                      Hslots Hperm HR Hcont").
  Qed.

End ProofInstallTrans.

End InstallTransProof.
