(* ProofBeginOp.v -- begin_op() over the SIE-agnostic sconf world.

     void begin_op(void) {
       acquire(&log.lock);
       while (1) {
         if (log.committing)                                      sleep(&log,&log.lock);
         else if (log.lh.n + (log.outstanding+1)*MAXOPBLOCKS > LOGBLOCKS)
                                                                  sleep(&log,&log.lock);
         else { log.outstanding += 1; break; }
       }
       release(&log.lock);
     }

   Structure (CodeBeginOp.v has the byte-exact disassembly): a 32-byte
   ra/s0/s1/s2 frame, acquire(&log), then the retry loop whose test sits at
   +0x2c; s1 = &log (reloaded AFTER the acquire call), s2 = 30 = LOGBLOCKS.
   Two sleep arms (+0x24 for "committing", +0x46 for "no space"), one exit
   (the +0x42 bge taken) into the [outstanding += 1] tail at +0x50 and the
   release/epilogue.

   THE PROOF SHAPE.  Both sleeps PARK, so the retry loop is proved by iLöb
   over a [wp_next]-anchored loop invariant, exactly as ProofAcquiresleep.v
   does -- a park can resume the thread on a hart nobody knew about when the
   invariant was established, and a [wp_next] is the proposition that
   survives that.  [bo_loop] (control at +0x2c, the log lock HELD with
   [log_res] closed) and [bo_exit] (control at +0x58, after the store, with
   the freshly minted [log_op]) are both anchored at the function's entry
   hart [CID0].

   THE LEDGER STEP is the whole content of the function (SpecBeginOp.v):
   each iteration opens [log_res]; the committing arm and the space arm
   re-close it VERBATIM and sleep; the grant arm reads the guard true, and
   there [LogInv.log_begin_step] mints the op at MAXOPBLOCKS while
   [LogInv.log_reserve_ok] turns the code's conservative
   (out+1)*MAXOPBLOCKS test into the exact sum tie the invariant carries.

   THE GUARD'S ARITHMETIC is computed by the image in W-form
   (addiw/slliw/addw/slliw/addw, all 32-bit and sign-extended).  Every value
   involved is tiny -- [out <= 3] is a log_res conjunct and [n <= LOGBLOCKS]
   a log_batch one -- so the register values stay 64-bit literals
   ([mword_of_int z] with 0 <= z < 2^31) all the way through.  The three
   steps whose operand is the small [out] are discharged by a four-way case
   split ([bo_slli2] / [bo_addw1] / [bo_slli1]); only the final
   [addw a5,a5,a3] has a symbolic operand and gets the general
   [bo_addw2] bridge.

   A functor over ACQUIRE / RELEASE / SLEEP. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import auth gmap frac excl.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RiscvModelBytes.
Require Import InstrBytes KernelText WpMmodeLeafBase.
Require Import RegFile.
Require Import SmodeCore.
Require Import StackOwn CalleeSaved.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import KernelRvcDecode.
Require Import WpSmodeIntr.
Require Import ProcGeom.
Require Import FdSlots.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import WpLock.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import SpecPanic.
Require Import SpecAcquire SpecRelease SpecSleep.
Require Import SpecBeginOp.
Require Import CodeBeginOp.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Local Open Scope Z_scope.

Set Printing Depth 40.


(* ===================================================================== *)
(*  Pure arithmetic bridges (mword-FREE side conditions -- the zify-hook  *)
(*  rule in claude-notes/durable-notes.md).                              *)
(* ===================================================================== *)

Lemma bo_zout_nonneg (out : nat) : (0 <= Z.of_nat out)%Z.
Proof. lia. Qed.

Lemma bo_zout_lt (out : nat) : (out <= 3)%nat -> (0 <= Z.of_nat out < 2^31)%Z.
Proof. lia. Qed.

Lemma bo_zout1_lt (out : nat) : (out <= 3)%nat -> (Z.of_nat out + 1 < 2^31)%Z.
Proof. lia. Qed.

Lemma bo_zn_lt (n : nat) : (n <= LOGBLOCKS)%nat -> (0 <= Z.of_nat n < 2^31)%Z.
Proof. rewrite /LOGBLOCKS. lia. Qed.

Lemma bo_sz_nonneg (out : nat) : (0 <= 10 * (Z.of_nat out + 1))%Z.
Proof. lia. Qed.

Lemma bo_sz_lt (out n : nat) :
  (out <= 3)%nat -> (n <= LOGBLOCKS)%nat ->
  (10 * (Z.of_nat out + 1) + Z.of_nat n < 2^31)%Z.
Proof. rewrite /LOGBLOCKS. lia. Qed.

Lemma bo_sz_b63 (out n : nat) :
  (out <= 3)%nat -> (n <= LOGBLOCKS)%nat ->
  (- 2^63 <= 10 * (Z.of_nat out + 1) + Z.of_nat n < 2^63)%Z.
Proof. rewrite /LOGBLOCKS. lia. Qed.

Lemma bo_30_b63 : (- 2^63 <= 30 < 2^63)%Z.
Proof. lia. Qed.

Lemma bo_zsucc (out : nat) : Z.of_nat (S out) = (Z.of_nat out + 1)%Z.
Proof. lia. Qed.

Lemma bo_geb_true (a b : Z) : Z.geb a b = true -> (b <= a)%Z.
Proof. intro H. lia. Qed.

Lemma bo_geb_false (a b : Z) : Z.geb a b = false -> (a < b)%Z.
Proof. intro H. lia. Qed.

(* the stack budget: the 4-slot frame, then sleep's 22 (acquire/release's 10) *)
Lemma bo_K4  (K : nat) : (K_begin_op <= K)%nat -> (4 <= K)%nat.
Proof. rewrite /K_begin_op. lia. Qed.
Lemma bo_K10 (K : nat) : (K_begin_op <= K)%nat -> (10 <= K - 4)%nat.
Proof. rewrite /K_begin_op. lia. Qed.
Lemma bo_K22 (K : nat) : (K_begin_op <= K)%nat -> (22 <= K - 4)%nat.
Proof. rewrite /K_begin_op. lia. Qed.
Lemma bo_Kback (K : nat) : (K_begin_op <= K)%nat -> ((K - 4) + 4)%nat = K.
Proof. rewrite /K_begin_op. lia. Qed.
Lemma bo_noff1 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

(* the guard, read as the ledger's premises *)
Lemma bo_guard_sum (out n : nat) :
  (10 * (Z.of_nat out + 1) + Z.of_nat n <= 30)%Z ->
  (n + (out + 1) * MAXOPBLOCKS <= LOGBLOCKS)%nat.
Proof. rewrite /MAXOPBLOCKS /LOGBLOCKS. lia. Qed.

Lemma bo_guard_out3 (out n : nat) :
  (10 * (Z.of_nat out + 1) + Z.of_nat n <= 30)%Z -> (S out <= 3)%nat.
Proof. lia. Qed.

Lemma bo_nospace_sz (out n : nat) :
  (10 * (Z.of_nat out + 1) + Z.of_nat n <= 30)%Z ->
  (0 <= 10 * (Z.of_nat out + 1) + Z.of_nat n)%Z.
Proof. lia. Qed.

(* ---- the bitvector bridges ---- *)

Lemma bo_sext32 (z : Z) : (0 <= z < 2^31)%Z ->
  (sign_extend' 64 (mword_of_int z : mword 32) : mword 64) = mword_of_int z.
Proof.
  intro Hz. apply bv_eq.
  rewrite (sext64_moi32_unsigned z Hz) moi64_unsigned.
  symmetry. apply bvw64_small. lia.
Qed.

Lemma bo_moi32_add (a b : Z) :
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

Lemma bo_addiw (z : Z) : (0 <= z)%Z -> (z + 1 < 2^31)%Z ->
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
  rewrite HK (bo_moi32_add z 1 Hz ltac:(lia) ltac:(lia)).
  apply bo_sext32. lia.
Qed.

Lemma bo_addw2 (a b : Z) :
  (0 <= a)%Z -> (0 <= b)%Z -> (a + b < 2^31)%Z ->
  sign_extend' 64 (add_vec (subrange_vec_dec (mword_of_int a : mword 64) 31 0 : mword 32)
                           (subrange_vec_dec (mword_of_int b : mword 64) 31 0 : mword 32))
  = (mword_of_int (a + b) : mword 64).
Proof.
  intros Ha Hb Hab.
  rewrite -!trunc32_subrange !trunc32_mword_of_int.
  rewrite (bo_moi32_add a b Ha Hb ltac:(lia)).
  apply bo_sext32. lia.
Qed.

(* the three W-form steps whose operand is the SMALL outstanding count:
   [out <= 3] makes each a four-way concrete computation. *)
Lemma bo_slli2 (out : nat) : (out <= 3)%nat ->
  sign_extend' 64 (shift_bits_left
     (subrange_vec_dec (mword_of_int (Z.of_nat out + 1) : mword 64) 31 0 : mword 32)
     (mword_of_int 2 : mword 5))
  = (mword_of_int (4 * (Z.of_nat out + 1)) : mword 64).
Proof.
  intro H. destruct out as [|[|[|[|o]]]]; try (exfalso; lia);
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma bo_addw1 (out : nat) : (out <= 3)%nat ->
  sign_extend' 64 (add_vec
     (subrange_vec_dec (mword_of_int (4 * (Z.of_nat out + 1)) : mword 64) 31 0 : mword 32)
     (subrange_vec_dec (mword_of_int (Z.of_nat out + 1) : mword 64) 31 0 : mword 32))
  = (mword_of_int (5 * (Z.of_nat out + 1)) : mword 64).
Proof.
  intro H. destruct out as [|[|[|[|o]]]]; try (exfalso; lia);
    apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma bo_slli1 (out : nat) : (out <= 3)%nat ->
  sign_extend' 64 (shift_bits_left
     (subrange_vec_dec (mword_of_int (5 * (Z.of_nat out + 1)) : mword 64) 31 0 : mword 32)
     (mword_of_int 1 : mword 5))
  = (mword_of_int (10 * (Z.of_nat out + 1)) : mword 64).
Proof.
  intro H. destruct out as [|[|[|[|o]]]]; try (exfalso; lia);
    apply bv_eq; vm_compute; reflexivity.
Qed.

(* signed comparison on 64-bit literals (the [bge] guard) *)
Lemma bo_sint_moi (z : Z) :
  (- 2 ^ 63 <= z < 2 ^ 63)%Z -> sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  assert (Hhm : bv_half_modulus 64 = (2 ^ 63)%Z) by reflexivity.
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned bv_swrap_wrap.
  apply bv_swrap_small. rewrite Hhm. lia.
Qed.

Lemma bo_geb_s (a b : Z) :
  (- 2 ^ 63 <= a < 2 ^ 63)%Z -> (- 2 ^ 63 <= b < 2 ^ 63)%Z ->
  zopz0zKzJ_s (mword_of_int a : mword 64) (mword_of_int b : mword 64) = Z.geb a b.
Proof.
  intros Ha Hb. unfold zopz0zKzJ_s.
  rewrite (bo_sint_moi a Ha) (bo_sint_moi b Hb). reflexivity.
Qed.

(* ---- the four relocations, and the two struct-log cell addresses ---- *)

Lemma bo_reloc_a0_0c :
  add_vec (add_vec (mword_of_int (KernelSyms.begin_op + 0x0c) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1822 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma bo_reloc_s1_18 :
  add_vec (add_vec (mword_of_int (KernelSyms.begin_op + 0x18) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1810 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma bo_reloc_a0_58 :
  add_vec (add_vec (mword_of_int (KernelSyms.begin_op + 0x58) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1746 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma bo_reloc_out_50 :
  add_vec (add_vec (mword_of_int (KernelSyms.begin_op + 0x50) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1782 : mword 12)) = l_out.
Proof.
  rewrite /l_out /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma bo_addr_cmt : add_vec log_addr (sign_extend' 64 (mword_of_int 32 : mword 12)) = l_cmt.
Proof.
  rewrite /l_cmt /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma bo_addr_out : add_vec log_addr (sign_extend' 64 (mword_of_int 28 : mword 12)) = l_out.
Proof.
  rewrite /l_out /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma bo_addr_lhn : add_vec log_addr (sign_extend' 64 (mword_of_int 44 : mword 12)) = lh_n_pa.
Proof.
  rewrite /lh_n_pa /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* ===================================================================== *)
(*  The loop/exit register-map invariant.  HART-FREE (tp is pinned by     *)
(*  [HartTp]): s1 = &log, s2 = LOGBLOCKS, sp = the pushed frame base,     *)
(*  s3..s11 preserved from the entry map [m].                            *)
(* ===================================================================== *)
Definition bo_regs (m M : regfile) (spd : mword 64) : Prop :=
  M !!! Regidx (mword_of_int 9 : mword 5) = log_addr /\
  M !!! Regidx (mword_of_int 18 : mword 5) = (mword_of_int 30 : mword 64) /\
  M !!! Regidx csp_rs1 = spd /\
  M !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) /\
  M !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) /\
  M !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) /\
  M !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5) /\
  M !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5) /\
  M !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5) /\
  M !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5) /\
  M !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5) /\
  M !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5).

Lemma bo_regs_cs (m M1 M2 : regfile) (spd : mword 64) :
  callee_saved M1 M2 -> bo_regs m M1 spd -> bo_regs m M2 spd.
Proof.
  intros Hcs Ha. unfold bo_regs in *.
  destruct Ha as (A&B&Cc&E&F&G&H&I&J&Kk&L&N).
  repeat split.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 9 : mword 5) ltac:(vm_compute; reflexivity)). exact A.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 18 : mword 5) ltac:(vm_compute; reflexivity)). exact B.
  - rewrite (callee_saved_lookup Hcs csp_rs1 ltac:(vm_compute; reflexivity)). exact Cc.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity)). exact E.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity)). exact F.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity)). exact G.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity)). exact H.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity)). exact I.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity)). exact J.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity)). exact Kk.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity)). exact L.
  - rewrite (callee_saved_lookup Hcs (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity)). exact N.
Qed.

(* ===================================================================== *)

Section BoProps.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !fsLogG Σ, !logG Σ}.

  (* the log lock's batch, opened just for its [lh.n] cell *)
  Lemma bo_batch_lhn (bn : bio_names) (γfs : fs_names) (cov : gset Z)
      (logstart : Z) (n : nat) (LB : gset Z) :
    log_batch bn γfs cov logstart n LB -∗
    ⌜(n <= LOGBLOCKS)%nat⌝ ∗
    lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) ∗
    (lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
       log_batch bn γfs cov logstart n LB).
  Proof.
    iIntros "H". rewrite /log_batch.
    iDestruct "H" as (W L D) "(%Hlen & %HLB & %Hnd & %Hcv & Hn & Hblk & Hjunk & HL & HD & Hdirty & Hhdr & Hsl & Hpool & Hmirc)".
    iSplitR; [iPureIntro; exact (proj2 Hlen)|].
    iFrame "Hn". iIntros "Hn".
    iExists W, L, D.
    iSplitR; [iPureIntro; exact Hlen|].
    iSplitR; [iPureIntro; exact HLB|].
    iSplitR; [iPureIntro; exact Hnd|].
    iSplitR; [iPureIntro; exact Hcv|].
    iFrame "Hn Hblk Hjunk HL HD Hdirty Hhdr Hsl Hpool Hmirc".
  Qed.

  (* The exit continuation, control at +0x58 (the store has already
     committed the new [outstanding] and the reservation is minted), and the
     wait-loop invariant, control at +0x2c (the log lock held, [log_res]
     closed).  Both are [wp_next]s ANCHORED at the function's entry hart
     [CID0]: the park inside the loop means either can be entered at a hart
     nobody knew about when it was established. *)
  Definition bo_exit `{GEN : GenId} (CID0 : CPU)
       (j : nat)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z)
      (m : regfile) (pidv : mword 32) (dq : dfrac)
      (K : nat) (eb : bool) (C : iProp Σ) (spd sp0 : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (M : regfile),
      ⌜ bo_regs m M spd ⌝ -∗
      pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
      pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
      pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
      locked (ln_lk γ) cpu_id -∗
      log_res γ bn γfs cov logstart -∗
      log_op γ MAXOPBLOCKS -∗
      p_pid (proc_addr j) ↦₄{dq} pidv -∗
      cpu_own 1 eb (proc_addr j) C false -∗
      arm_pay 0 eb (proc_addr j) -∗
      sie_cap_gpr M (K - 4)%nat false (proc_addr j) -∗
      pc_is (mword_of_int (KernelSyms.begin_op + 0x58)) -∗
      WP (Loop : expr riscv_lang)))%I.

  Definition bo_loop `{GEN : GenId} (CID0 : CPU)
      (j : nat)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z)
      (m : regfile) (pidv : mword 32) (dq : dfrac)
      (K : nat) (eb : bool) (C : iProp Σ) (spd sp0 : mword 64) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (M : regfile),
      ⌜ bo_regs m M spd ⌝ -∗
      pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
      pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
      pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
      locked (ln_lk γ) cpu_id -∗
      log_res γ bn γfs cov logstart -∗
      p_pid (proc_addr j) ↦₄{dq} pidv -∗
      cpu_own 1 eb (proc_addr j) C false -∗
      arm_pay 0 eb (proc_addr j) -∗
      sie_cap_gpr M (K - 4)%nat false (proc_addr j) -∗
      pc_is (mword_of_int (KernelSyms.begin_op + 0x2c)) -∗
      bo_exit CID0 j γ bn γfs cov logstart m pidv dq K eb C spd sp0 -∗
      WP (Loop : expr riscv_lang)))%I.

End BoProps.

(* ===================================================================== *)

Module BeginOpProof (Acquire : ACQUIRE) (Release : RELEASE) (Sleep : SLEEP) : BEGIN_OP.

Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.

Section BoBodies.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !fsLogG Σ, !logG Σ}.

  (* ---- the exit path: +0x58 (a0 := &log) .. +0x6e (c.ret) ---- *)
  Lemma bo_exit_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU) (j : nat)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m M : regfile) (pidv : mword 32) (dq : dfrac)
      (K : nat) (eb : bool) (C : iProp Σ) (spd sp0 : mword 64) :
    let pj := proc_addr j in
    (K_begin_op <= K)%nat ->
    eb = true ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd ->
    sp0 = m !!! Regidx csp_rs1 ->
    bo_regs m M spd ->
    kernel_text -∗
    log_ctx γ bn γfs cov logstart dev -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    log_op γ MAXOPBLOCKS -∗
    p_pid pj ↦₄{dq} pidv -∗
    cpu_own 1 eb pj C false -∗
    arm_pay 0 eb pj -∗
    sie_cap_gpr M (K - 4)%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.begin_op + 0x58)) -∗
    wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜ callee_saved m mf ⌝ -∗
        sie_cap_gpr mf K true pj -∗
        cpu_own 0 eb pj C true -∗
        pc_is (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) -∗
        p_pid pj ↦₄{dq} pidv -∗
        log_op γ MAXOPBLOCKS -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj HK Heb Hanch Hspd Hsp0 Hbo. subst eb.
    destruct Hbo as (Hs1 & Hs2 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iIntros "#Htext #Hlog Hr24 Hr16 Hr8 Hr0 Htok Hres Hop Hpid Hown Hpay Hcg Hpc Hcont".
    iDestruct "Hlog" as "(#Hislock & #Hldev & #Hlstart)".
    (* the four saved-slot addresses in the [c.ldsp] leaf's spelling *)
    assert (Hb1 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb2 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb3 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hb4 : add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite -Hspd. unfold pa_stk, add_vec_int. rewrite add_vec_off2.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iPoseProof (boi_58 with "Htext") as "Hi58".
    iPoseProof (boi_5c with "Htext") as "Hi5c".
    iPoseProof (boi_60 with "Htext") as "Hi60".
    iPoseProof (boi_64 with "Htext") as "Hi64".
    iPoseProof (boi_66 with "Htext") as "Hi66".
    iPoseProof (boi_68 with "Htext") as "Hi68".
    iPoseProof (boi_6a with "Htext") as "Hi6a".
    iPoseProof (boi_6c with "Htext") as "Hi6c".
    iPoseProof (boi_6e with "Htext") as "Hi6e".
    (* +0x58 auipc a0,0x1e *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.begin_op + 0x58)) (mword_of_int 10 : mword 5)
              (mword_of_int 30 : mword 20) M (K - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi58 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (X1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.begin_op + 0x58) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> M).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.begin_op + 0x58) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> M) with X1.
    assert (Hp5c : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x58) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x5c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5c) in "Hpc".
    (* +0x5c addi a0,a0,1766 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.begin_op + 0x5c)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 1746 : mword 12) X1 (K - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi5c [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (X2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (X1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1746 : mword 12)))]> X1).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (X1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1746 : mword 12)))]> X1) with X2.
    assert (Hp60 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x5c) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x60))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp60) in "Hpc".
    assert (HX2a0 : X2 !!! Regidx (mword_of_int 10 : mword 5) = log_addr).
    { rewrite /X2 upd_eq /X1 upd_eq. exact bo_reloc_a0_58. }
    (* +0x60 jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x60)) (mword_of_int 1 : mword 5)
              (mword_of_int 2084930 : mword 21) X2 (K - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi60 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (X3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x60) : mword 64) 4)]> X2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x60) : mword 64) 4)]> X2) with X3.
    assert (Hjrel : add_vec (mword_of_int (KernelSyms.begin_op + 0x60) : mword 64) (sign_extend' 64 (mword_of_int 2084930 : mword 21))
                    = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HX3ra : X3 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x60) : mword 64) 4)
      by (rewrite /X3; apply upd_eq).
    assert (HX3a0 : X3 !!! Regidx (mword_of_int 10 : mword 5) = log_addr)
      by (rewrite /X3 upd_ne; [exact HX2a0 | reg_neq]).
    assert (HX3csp : X3 !!! Regidx csp_rs1 = spd).
    { rewrite /X3 upd_ne; [| reg_neq]. rewrite /X2 upd_ne; [| reg_neq].
      rewrite /X1 upd_ne; [| reg_neq]. exact Hsp. }
    assert (Hrel_lka : add_vec (X3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = log_addr)
      by (rewrite HX3a0; apply addv_sext0).
    iApply (Release.wp_release_sconf (ln_lk γ) log_addr "log"%string
              (log_res γ bn γfs cov logstart) X3 0%nat true pj C (K - 4)%nat
              Hrel_lka ltac:(rewrite /K_begin_op in HK; lia)
              with "Hcg Htext Hpc Hislock Htok Hres Hown Hpay [-]").
    iIntros (CIDr Hsr mrel) "Hcg Hpc %Hrelcs Hown".
    assert (Hpc64 : ret_pc (X3 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x64))
      by (rewrite HX3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc64) in "Hpc".
    (* ===== EPILOGUE (+0x64..+0x6e): restore ra/s0/s1/s2, pop, ret ===== *)
    pose proof Hrelcs as Hrelcs2.
    assert (HmrelSp : mrel !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hrelcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HX3csp. }
    (* +0x64 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x64)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mrel (K - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi64 [Hr24] [-]").
    { iEval (rewrite HmrelSp Hb1). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    iEval (rewrite HmrelSp Hb1) in "Hr24".
    set (Q64 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel) with Q64.
    assert (HQ64sp : Q64 !!! Regidx csp_rs1 = spd) by (rewrite /Q64 upd_ne; [exact HmrelSp | reg_neq]).
    assert (Hp66 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x64) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x66))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp66) in "Hpc".
    (* +0x66 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x66)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              Q64 (K - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi66 [Hr16] [-]").
    { iEval (rewrite HQ64sp Hb2). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    iEval (rewrite HQ64sp Hb2) in "Hr16".
    set (Q66 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q64).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q64) with Q66.
    assert (HQ66sp : Q66 !!! Regidx csp_rs1 = spd) by (rewrite /Q66 upd_ne; [exact HQ64sp | reg_neq]).
    assert (Hp68 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x66) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x68))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp68) in "Hpc".
    (* +0x68 c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x68)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              Q66 (K - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi68 [Hr8] [-]").
    { iEval (rewrite HQ66sp Hb3). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    iEval (rewrite HQ66sp Hb3) in "Hr8".
    set (Q68 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> Q66).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> Q66) with Q68.
    assert (HQ68sp : Q68 !!! Regidx csp_rs1 = spd) by (rewrite /Q68 upd_ne; [exact HQ66sp | reg_neq]).
    assert (Hp6a : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x68) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x6a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6a) in "Hpc".
    (* +0x6a c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x6a)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              Q68 (K - 4)%nat (m !!! Regidx (mword_of_int 18 : mword 5)) true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi6a [Hr0] [-]").
    { iEval (rewrite HQ68sp Hb4). iExact "Hr0". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hr0".
    iEval (rewrite HQ68sp Hb4) in "Hr0".
    set (Q6a := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> Q68).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> Q68) with Q6a.
    assert (HQ6asp : Q6a !!! Regidx csp_rs1 = spd) by (rewrite /Q6a upd_ne; [exact HQ68sp | reg_neq]).
    assert (Hp6c : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x6a) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x6c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6c) in "Hpc".
    (* +0x6c c.addi16sp sp,32 -- the frame trade back *)
    assert (Hwv : add_vec (Q6a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HQ6asp -Hspd. apply frame_cancel_32. }
    assert (Hpop : Q6a !!! Regidx csp_rs1
                   = pa_stk (add_vec (Q6a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HQ6asp -Hspd. unfold pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iExists _; iExact "Hr8"|].
      iSplitL "Hr0";  [iExists _; iExact "Hr0"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.begin_op + 0x6c)) (mword_of_int 2 : mword 6) Q6a (K - 4)%nat 4 true Hpop
              with "Hcg Hpc Hi6c Hframe4 [-]").
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by (rewrite /K_begin_op in HK; lia).
    iEval (rewrite Hnk) in "Hcg".
    set (Q6c := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (Q6a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q6a).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (Q6a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q6a) with Q6c.
    assert (Hp6e : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x6c) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x6e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6e) in "Hpc".
    (* +0x6e c.ret *)
    assert (HQ6cra : Q6c !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Q6c upd_ne; [| reg_neq]. rewrite /Q6a upd_ne; [| reg_neq].
      rewrite /Q68 upd_ne; [| reg_neq]. rewrite /Q66 upd_ne; [| reg_neq].
      rewrite /Q64 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.begin_op + 0x6e)) (mword_of_int 1 : mword 5) Q6c K true
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi6e [-]").
    iIntros (CIDe6 Hse6) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (Q6c !!! Regidx (mword_of_int 1 : mword 5)) = ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)))
      by (rewrite HQ6cra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* the postcondition *)
    assert (Hthr : forall c : mword 5, is_cs_idx c = true ->
              c <> mword_of_int 1 -> c <> csp_rs1 -> c <> mword_of_int 8 ->
              c <> mword_of_int 9 -> c <> mword_of_int 10 -> c <> mword_of_int 18 ->
              Q6c !!! Regidx c = M !!! Regidx c).
    { intros c Hcs N1 N2 N8 N9 N10 N18.
      rewrite /Q6c /Q6a /Q68 /Q66 /Q64. repeat (rewrite upd_ne; [| congruence]).
      rewrite (callee_saved_lookup Hrelcs2 c Hcs).
      rewrite /X3 /X2 /X1. repeat (rewrite upd_ne; [| congruence]). reflexivity. }
    iDestruct (cpu_own_transport CIDr CIDe6 0 true pj C true ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iSpecialize ("Hcont" $! CIDe6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Q6c with "[%] Hcg Hown Hpc Hpid Hop").
    { unfold callee_saved.
      split. { rewrite /Q6c upd_eq. rewrite Hwv. exact Hsp0. }
      split. { rewrite /Q6c upd_ne; [| reg_neq]. rewrite /Q6a upd_ne; [| reg_neq].
               rewrite /Q68 upd_ne; [| reg_neq]. rewrite /Q66 upd_eq. reflexivity. }
      split. { rewrite /Q6c upd_ne; [| reg_neq]. rewrite /Q6a upd_ne; [| reg_neq].
               rewrite /Q68 upd_eq. reflexivity. }
      split. { rewrite /Q6c upd_ne; [| reg_neq]. rewrite /Q6a upd_eq. reflexivity. }
      split. { rewrite (Hthr (mword_of_int 19 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H19. }
      split. { rewrite (Hthr (mword_of_int 20 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H20. }
      split. { rewrite (Hthr (mword_of_int 21 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H21. }
      split. { rewrite (Hthr (mword_of_int 22 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H22. }
      split. { rewrite (Hthr (mword_of_int 23 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H23. }
      split. { rewrite (Hthr (mword_of_int 24 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H24. }
      split. { rewrite (Hthr (mword_of_int 25 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H25. }
      split. { rewrite (Hthr (mword_of_int 26 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H26. }
      { rewrite (Hthr (mword_of_int 27 : mword 5) ltac:(vm_compute; reflexivity) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq) ltac:(reg_neq)). exact H27. } }
  Qed.

  (* ---- the COMMITTING sleep arm: +0x24 .. +0x28 (the park), returning
     straight into the loop test at +0x2c.  Entered from the taken
     [c.bnez] at +0x2e, whose later has already been stripped, so the Löb
     hypothesis arrives here WITHOUT its [▷]. ---- *)
  Lemma bo_armA_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γs : list gname) (j : nat) (γl : gname)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m M : regfile) (pidv : mword 32) (dq : dfrac)
      (K : nat) (eb : bool) (C : iProp Σ) (spd sp0 : mword 64) :
    let pj := proc_addr j in
    (K_begin_op <= K)%nat ->
    eb = true ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    bo_regs m M spd ->
    kernel_text -∗
    log_ctx γ bn γfs cov logstart dev -∗
    panic_wp_any -∗
    procs_inv γs -∗
    bo_loop CID0 j γ bn γfs cov logstart m pidv dq K eb C spd sp0 -∗
    bo_exit CID0 j γ bn γfs cov logstart m pidv dq K eb C spd sp0 -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    p_pid pj ↦₄{dq} pidv -∗
    cpu_own 1 eb pj C false -∗
    arm_pay 0 eb pj -∗
    sie_cap_gpr M (K - 4)%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.begin_op + 0x24)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj HK Heb Hj Hjl Hanch Hbo.
    iIntros "#Htext #Hlog #Hpanic #Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Hpay Hcg Hpc".
    iDestruct "Hlog" as "(#Hislock & #Hldev & #Hlstart)".
    assert (HboM : bo_regs m M spd) by exact Hbo.
    destruct Hbo as (Hs1 & Hs2 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iPoseProof (boi_24 with "Htext") as "Hi24".
    iPoseProof (boi_26 with "Htext") as "Hi26".
    iPoseProof (boi_28 with "Htext") as "Hi28".
    (* +0x24 c.mv a1,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.begin_op + 0x24)) (mword_of_int 11 : mword 5) (mword_of_int 9 : mword 5)
              M (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi24 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A0 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 9 : mword 5)))]> M).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 9 : mword 5)))]> M) with A0.
    assert (Hp26 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp26) in "Hpc".
    (* +0x26 c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.begin_op + 0x26)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              A0 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi26 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (A0 !!! Regidx (mword_of_int 9 : mword 5)))]> A0).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (A0 !!! Regidx (mword_of_int 9 : mword 5)))]> A0) with A1.
    assert (Hp28 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x26) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x28))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp28) in "Hpc".
    (* +0x28 jal ra,sleep *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x28)) (mword_of_int 1 : mword 5)
              (mword_of_int 2089722 : mword 21) A1 (K - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi28 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (A2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x28) : mword 64) 4)]> A1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x28) : mword 64) 4)]> A1) with A2.
    assert (Hjsl : add_vec (mword_of_int (KernelSyms.begin_op + 0x28) : mword 64) (sign_extend' 64 (mword_of_int 2089722 : mword 21))
                   = mword_of_int KernelSyms.sleep)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjsl) in "Hpc".
    assert (HA2a1 : A2 !!! Regidx (mword_of_int 11 : mword 5) = log_addr).
    { rewrite /A2 upd_ne; [| reg_neq]. rewrite /A1 upd_ne; [| reg_neq]. rewrite /A0 upd_eq.
      rewrite Hs1. apply add_vec_zero_l. }
    assert (HA2ra : A2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x28) : mword 64) 4)
      by (rewrite /A2; apply upd_eq).
    assert (HcsMA2 : callee_saved M A2).
    { rewrite /A2 /A1 /A0.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HboA2 : bo_regs m A2 spd) by (apply (bo_regs_cs m M A2 spd HcsMA2 HboM)).
    assert (Hsl_lka : add_vec (A2 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = log_addr)
      by (rewrite HA2a1; apply addv_sext0).
    iApply (Sleep.wp_sleep_sconf γs j γl (ln_lk γ) log_addr "log"%string
              (log_res γ bn γfs cov logstart) A2 (K - 4)%nat eb C
              Hj Hjl Hsl_lka Heb (bo_K22 K HK)
              with "Hcg Hown Hpay Htext Hpc Hpinv Hislock Htok Hres Hpanic [-]").
    iIntros (CIDs Hss mfs) "%Hs_cs Hcg Hown Hpay Hpc Htok Hres".
    assert (Hpc2c : ret_pc (A2 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x2c))
      by (rewrite HA2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc2c) in "Hpc".
    assert (HboMfs : bo_regs m mfs spd) by (apply (bo_regs_cs m A2 mfs spd Hs_cs HboA2)).
    rewrite /bo_loop.
    iSpecialize ("IH" $! CIDs with "[%]"); [wp_next_chain|].
    iApply ("IH" $! mfs with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Hpay Hcg Hpc Hexit").
    exact HboMfs.
  Qed.

  (* ---- the NO-SPACE sleep arm: +0x46 .. +0x4a (the park), returning at
     +0x4e whose [c.j] closes the back edge to +0x2c.  Entered from the
     FALLING [bge] at +0x42, which carries no later, so the Löb hypothesis
     arrives WITH its [▷] and is stripped at that [c.j]. ---- *)
  Lemma bo_armB_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γs : list gname) (j : nat) (γl : gname)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m M : regfile) (pidv : mword 32) (dq : dfrac)
      (K : nat) (eb : bool) (C : iProp Σ) (spd sp0 : mword 64) :
    let pj := proc_addr j in
    (K_begin_op <= K)%nat ->
    eb = true ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    bo_regs m M spd ->
    kernel_text -∗
    log_ctx γ bn γfs cov logstart dev -∗
    panic_wp_any -∗
    procs_inv γs -∗
    ▷ bo_loop CID0 j γ bn γfs cov logstart m pidv dq K eb C spd sp0 -∗
    bo_exit CID0 j γ bn γfs cov logstart m pidv dq K eb C spd sp0 -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    p_pid pj ↦₄{dq} pidv -∗
    cpu_own 1 eb pj C false -∗
    arm_pay 0 eb pj -∗
    sie_cap_gpr M (K - 4)%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.begin_op + 0x46)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj HK Heb Hj Hjl Hanch Hbo.
    iIntros "#Htext #Hlog #Hpanic #Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Hpay Hcg Hpc".
    iDestruct "Hlog" as "(#Hislock & #Hldev & #Hlstart)".
    assert (HboM : bo_regs m M spd) by exact Hbo.
    destruct Hbo as (Hs1 & Hs2 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iPoseProof (boi_46 with "Htext") as "Hi46".
    iPoseProof (boi_48 with "Htext") as "Hi48".
    iPoseProof (boi_4a with "Htext") as "Hi4a".
    iPoseProof (boi_4e with "Htext") as "Hi4e".
    (* +0x46 c.mv a1,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.begin_op + 0x46)) (mword_of_int 11 : mword 5) (mword_of_int 9 : mword 5)
              M (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi46 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B0 := <[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 9 : mword 5)))]> M).
    change (<[Regidx (mword_of_int 11 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 9 : mword 5)))]> M) with B0.
    assert (Hp48 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x48))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp48) in "Hpc".
    (* +0x48 c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.begin_op + 0x48)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              B0 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi48 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (B0 !!! Regidx (mword_of_int 9 : mword 5)))]> B0).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (B0 !!! Regidx (mword_of_int 9 : mword 5)))]> B0) with B1.
    assert (Hp4a : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x48) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x4a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp4a) in "Hpc".
    (* +0x4a jal ra,sleep *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x4a)) (mword_of_int 1 : mword 5)
              (mword_of_int 2089688 : mword 21) B1 (K - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi4a [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (B2 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x4a) : mword 64) 4)]> B1).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x4a) : mword 64) 4)]> B1) with B2.
    assert (Hjsl : add_vec (mword_of_int (KernelSyms.begin_op + 0x4a) : mword 64) (sign_extend' 64 (mword_of_int 2089688 : mword 21))
                   = mword_of_int KernelSyms.sleep)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjsl) in "Hpc".
    assert (HB2a1 : B2 !!! Regidx (mword_of_int 11 : mword 5) = log_addr).
    { rewrite /B2 upd_ne; [| reg_neq]. rewrite /B1 upd_ne; [| reg_neq]. rewrite /B0 upd_eq.
      rewrite Hs1. apply add_vec_zero_l. }
    assert (HB2ra : B2 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x4a) : mword 64) 4)
      by (rewrite /B2; apply upd_eq).
    assert (HcsMB2 : callee_saved M B2).
    { rewrite /B2 /B1 /B0.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HboB2 : bo_regs m B2 spd) by (apply (bo_regs_cs m M B2 spd HcsMB2 HboM)).
    assert (Hsl_lka : add_vec (B2 !!! Regidx (mword_of_int 11 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = log_addr)
      by (rewrite HB2a1; apply addv_sext0).
    iApply (Sleep.wp_sleep_sconf γs j γl (ln_lk γ) log_addr "log"%string
              (log_res γ bn γfs cov logstart) B2 (K - 4)%nat eb C
              Hj Hjl Hsl_lka Heb (bo_K22 K HK)
              with "Hcg Hown Hpay Htext Hpc Hpinv Hislock Htok Hres Hpanic [-]").
    iIntros (CIDs Hss mfs) "%Hs_cs Hcg Hown Hpay Hpc Htok Hres".
    assert (Hpc4e : ret_pc (B2 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x4e))
      by (rewrite HB2ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc4e) in "Hpc".
    assert (HboMfs : bo_regs m mfs spd) by (apply (bo_regs_cs m B2 mfs spd Hs_cs HboB2)).
    (* +0x4e c.j -> +0x2c : the back edge *)
    iPoseProof (boi_4e with "Htext") as "Hi4e2".
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.begin_op + 0x4e))
              (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0"))) mfs (K - 4)%nat false
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi4e2 [-]").
    iApply wp_next_off_intro.
    iNext.
    iIntros "Hcg Hpc".
    assert (Hbk : add_vec (mword_of_int (KernelSyms.begin_op + 0x4e) : mword 64)
                    (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0"))))
                  = mword_of_int (KernelSyms.begin_op + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hbk) in "Hpc".
    rewrite /bo_loop.
    iSpecialize ("IH" $! CIDs with "[%]"); [wp_next_chain|].
    iApply ("IH" $! mfs with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Hpay Hcg Hpc Hexit").
    exact HboMfs.
  Qed.

  (* ---- ONE ITERATION: the test at +0x2c, the size estimate, and the
     three-way dispatch (committing arm / no-space arm / the grant tail
     +0x50..+0x54 that mints the reservation and hands control to
     [bo_exit]). ---- *)
  Lemma bo_loop_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU)
      (γs : list gname) (j : nat) (γl : gname)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m M : regfile) (pidv : mword 32) (dq : dfrac)
      (K : nat) (eb : bool) (C : iProp Σ) (spd sp0 : mword 64) :
    let pj := proc_addr j in
    (K_begin_op <= K)%nat ->
    eb = true ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    bo_regs m M spd ->
    kernel_text -∗
    log_ctx γ bn γfs cov logstart dev -∗
    panic_wp_any -∗
    procs_inv γs -∗
    ▷ bo_loop CID0 j γ bn γfs cov logstart m pidv dq K eb C spd sp0 -∗
    bo_exit CID0 j γ bn γfs cov logstart m pidv dq K eb C spd sp0 -∗
    pa_stk sp0 1 ↦₈ (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈ (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈ (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈ (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    p_pid pj ↦₄{dq} pidv -∗
    cpu_own 1 eb pj C false -∗
    arm_pay 0 eb pj -∗
    sie_cap_gpr M (K - 4)%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.begin_op + 0x2c)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj HK Heb Hj Hjl Hanch Hbo.
    iIntros "#Htext #Hlog #Hpanic #Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Hpay Hcg Hpc".
    iPoseProof "Hlog" as "#Hlogc".
    iDestruct "Hlogc" as "(#Hislock & #Hldev & #Hlstart)".
    assert (HboM : bo_regs m M spd) by exact Hbo.
    destruct Hbo as (Hs1 & Hs2 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    assert (Hc5 : creg2reg_idx (Cregidx (mword_of_int 5)) = Regidx (mword_of_int 13 : mword 5))
      by (vm_compute; reflexivity).
    assert (Hc6 : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx (mword_of_int 14 : mword 5))
      by (vm_compute; reflexivity).
    assert (Hc7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15 : mword 5))
      by (vm_compute; reflexivity).
    iPoseProof (boi_2c with "Htext") as "Hi2c".
    iPoseProof (boi_2e with "Htext") as "Hi2e".
    (* open the lock's resource for the committing test *)
    rewrite /log_res.
    iDestruct "Hres" as (out cmt nc om) "(Hout & Hcmt & Hnc & Hauth & %Hsz & %Hbnd & %Hout3 & %Hcmtout & Hrest)".
    assert (Hacmt : add_vec (rget M (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 32 : mword 12)) = l_cmt).
    { rgne. rewrite Hs1. exact bo_addr_cmt. }
    (* +0x2c c.lw a5,32(s1) : a5 := log.committing *)
    iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x2c)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 32 : mword 12) M (K - 4)%nat
              (mword_of_int (if cmt then 1 else 0) : mword 32) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi2c [Hcmt] [-]").
    { iEval (rewrite Hacmt). iExact "Hcmt". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcmt".
    iEval (rewrite Hacmt) in "Hcmt".
    set (E1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (mword_of_int (if cmt then 1 else 0) : mword 32))]> M).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (mword_of_int (if cmt then 1 else 0) : mword 32))]> M) with E1.
    assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x2c) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x2e))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp2e) in "Hpc".
    assert (HE1a5 : E1 !!! Regidx (mword_of_int 15 : mword 5)
                    = sign_extend' 64 (mword_of_int (if cmt then 1 else 0) : mword 32))
      by (rewrite /E1; apply upd_eq).
    assert (HcsE1 : callee_saved M E1).
    { rewrite /E1. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HboE1 : bo_regs m E1 spd) by (apply (bo_regs_cs m M E1 spd HcsE1 HboM)).
    assert (HE1s1 : E1 !!! Regidx (mword_of_int 9 : mword 5) = log_addr)
      by (rewrite /E1 upd_ne; [exact Hs1 | reg_neq]).
    iPoseProof (boi_30 with "Htext") as "Hi30".
    iPoseProof (boi_32 with "Htext") as "Hi32".
    iPoseProof (boi_34 with "Htext") as "Hi34".
    iPoseProof (boi_38 with "Htext") as "Hi38".
    iPoseProof (boi_3a with "Htext") as "Hi3a".
    iPoseProof (boi_3e with "Htext") as "Hi3e".
    iPoseProof (boi_40 with "Htext") as "Hi40".
    iPoseProof (boi_42 with "Htext") as "Hi42".
    destruct cmt.
    - (* ================= COMMITTING: c.bnez TAKEN -> +0x24 ================= *)
      iAssert (∃ (out : nat) (cmt : bool) (nc : SailStdpp.Values.mword 32) (om : gmap nat op_entry),
                 l_out ↦₄ (mword_of_int (Z.of_nat out) : mword 32) ∗
                 l_cmt ↦₄ (mword_of_int (if cmt then 1 else 0) : mword 32) ∗
                 l_ncommit ↦₄ nc ∗
                 ghost_map_auth (ln_ops γ) 1 om ∗
                 ⌜size om = out⌝ ∗
                 ⌜forall i e, om !! i = Some e -> (e.1 <= MAXOPBLOCKS)%nat⌝ ∗
                 ⌜(out <= 3)%nat⌝ ∗
                 ⌜cmt = true -> out = 0%nat⌝ ∗
                 (if cmt then emp
                  else ∃ (n : nat) (LB : gset Z),
                       ⌜(n + op_sum om <= LOGBLOCKS)%nat⌝ ∗
                       ⌜forall i e, om !! i = Some e -> e.2 ⊆ LB⌝ ∗
                       log_batch bn γfs cov logstart n LB))%I
        with "[Hout Hcmt Hnc Hauth Hrest]" as "Hres".
      { iExists out, true, nc, om. iFrame "Hout Hcmt Hnc Hauth".
        iSplitR; [iPureIntro; exact Hsz|].
        iSplitR; [iPureIntro; exact Hbnd|].
        iSplitR; [iPureIntro; exact Hout3|].
        iSplitR; [iPureIntro; exact Hcmtout|].
        iExact "Hrest". }
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.begin_op + 0x2e)) (mword_of_int 251 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) E1 (K - 4)%nat false
                Hc7 ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HE1a5; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc Hi2e [-]").
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htgt24 : add_vec (mword_of_int (KernelSyms.begin_op + 0x2e) : mword 64)
                         (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.begin_op + 0x24))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt24) in "Hpc".
      iApply (bo_armA_body (CID := CID) CID0 γs j γl γ bn γfs cov logstart dev m E1 pidv dq K eb C spd sp0
                HK Heb Hj Hjl Hanch HboE1
                with "Htext Hlog Hpanic Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Hpay Hcg Hpc").
    - (* ================= NOT COMMITTING: fall through to +0x30 ============ *)
      iDestruct "Hrest" as (n LB) "(%Hsum & %Hsub & Hbatch)".
      iDestruct (bo_batch_lhn with "Hbatch") as "(%Hn30 & Hlhn & Hbclose)".
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.begin_op + 0x2e)) (mword_of_int 251 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) E1 (K - 4)%nat false
                Hc7 ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HE1a5; vm_compute; reflexivity)
                with "Hcg Hpc Hi2e [-]").
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x2e) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x30))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp30) in "Hpc".
      (* +0x30 c.lw a4,28(s1) : a4 := log.outstanding *)
      assert (Haout : add_vec (rget E1 (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 28 : mword 12)) = l_out).
      { rgne. rewrite HE1s1. exact bo_addr_out. }
      iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x30)) (mword_of_int 14 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 28 : mword 12) E1 (K - 4)%nat
                (mword_of_int (Z.of_nat out) : mword 32) false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi30 [Hout] [-]").
      { iEval (rewrite Haout). iExact "Hout". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hout".
      iEval (rewrite Haout) in "Hout".
      set (E2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
          (sign_extend' 64 (mword_of_int (Z.of_nat out) : mword 32))]> E1).
      change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
          (sign_extend' 64 (mword_of_int (Z.of_nat out) : mword 32))]> E1) with E2.
      assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x30) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x32))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp32) in "Hpc".
      assert (HE2a4 : E2 !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int (Z.of_nat out) : mword 64)).
      { rewrite /E2 upd_eq. apply bo_sext32. exact (bo_zout_lt out Hout3). }
      (* +0x32 c.addiw a4,a4,1 *)
      iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x32)) (mword_of_int 14 : mword 5) (mword_of_int 1 : mword 6)
                E2 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi32 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rgne) in "Hcg".
      set (E3 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (E2 !!! Regidx (mword_of_int 14 : mword 5))
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> E2).
      change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
          (sign_extend' 64 (subrange_vec_dec
             (add_vec (E2 !!! Regidx (mword_of_int 14 : mword 5))
                      (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))]> E2) with E3.
      assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x32) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x34))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp34) in "Hpc".
      assert (HE3a4 : E3 !!! Regidx (mword_of_int 14 : mword 5)
                      = (mword_of_int (Z.of_nat out + 1) : mword 64)).
      { rewrite /E3 upd_eq HE2a4. apply bo_addiw; [apply bo_zout_nonneg | exact (bo_zout1_lt out Hout3)]. }
      (* +0x34 slliw a5,a4,2 *)
      assert (Hsl2 : sign_extend' 64 (shift_bits_left
                        (subrange_vec_dec (rget E3 (mword_of_int 14 : mword 5)) 31 0 : mword 32)
                        (mword_of_int 2 : mword 5))
                     = (mword_of_int (4 * (Z.of_nat out + 1)) : mword 64)).
      { rgne. rewrite HE3a4. exact (bo_slli2 out Hout3). }
      iApply (wp_slliw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x34)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
                (mword_of_int 2 : mword 5) (mword_of_int (4 * (Z.of_nat out + 1)) : mword 64)
                E3 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) Hsl2
                with "Hcg Hpc Hi34 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (mword_of_int (4 * (Z.of_nat out + 1)) : mword 64)]> E3).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (mword_of_int (4 * (Z.of_nat out + 1)) : mword 64)]> E3) with E4.
      assert (Hp38 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x38))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp38) in "Hpc".
      assert (HE4a5 : E4 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int (4 * (Z.of_nat out + 1)) : mword 64))
        by (rewrite /E4; apply upd_eq).
      assert (HE4a4 : E4 !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int (Z.of_nat out + 1) : mword 64))
        by (rewrite /E4 upd_ne; [exact HE3a4 | reg_neq]).
      (* +0x38 c.addw a5,a5,a4 *)
      iEval (rewrite Hc6 Hc7) in "Hi38".
      iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x38)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
                E4 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi38 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rgne; rgne) in "Hcg".
      set (E5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (sign_extend' 64 (add_vec
             (subrange_vec_dec (E4 !!! Regidx (mword_of_int 15 : mword 5)) 31 0 : mword 32)
             (subrange_vec_dec (E4 !!! Regidx (mword_of_int 14 : mword 5)) 31 0 : mword 32)))]> E4).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (sign_extend' 64 (add_vec
             (subrange_vec_dec (E4 !!! Regidx (mword_of_int 15 : mword 5)) 31 0 : mword 32)
             (subrange_vec_dec (E4 !!! Regidx (mword_of_int 14 : mword 5)) 31 0 : mword 32)))]> E4) with E5.
      assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x38) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x3a))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3a) in "Hpc".
      assert (HE5a5 : E5 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int (5 * (Z.of_nat out + 1)) : mword 64)).
      { rewrite /E5 upd_eq HE4a5 HE4a4. exact (bo_addw1 out Hout3). }
      (* +0x3a slliw a5,a5,1 *)
      assert (Hsl1 : sign_extend' 64 (shift_bits_left
                        (subrange_vec_dec (rget E5 (mword_of_int 15 : mword 5)) 31 0 : mword 32)
                        (mword_of_int 1 : mword 5))
                     = (mword_of_int (10 * (Z.of_nat out + 1)) : mword 64)).
      { rgne. rewrite HE5a5. exact (bo_slli1 out Hout3). }
      iApply (wp_slliw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x3a)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5)
                (mword_of_int 1 : mword 5) (mword_of_int (10 * (Z.of_nat out + 1)) : mword 64)
                E5 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok) Hsl1
                with "Hcg Hpc Hi3a [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (mword_of_int (10 * (Z.of_nat out + 1)) : mword 64)]> E5).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (mword_of_int (10 * (Z.of_nat out + 1)) : mword 64)]> E5) with E6.
      assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x3a) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp3e) in "Hpc".
      assert (HE6a5 : E6 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int (10 * (Z.of_nat out + 1)) : mword 64))
        by (rewrite /E6; apply upd_eq).
      assert (HE6s1 : E6 !!! Regidx (mword_of_int 9 : mword 5) = log_addr).
      { rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
        rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_ne; [| reg_neq]. exact HE1s1. }
      (* +0x3e c.lw a3,44(s1) : a3 := log.lh.n *)
      assert (Halhn : add_vec (rget E6 (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 44 : mword 12)) = lh_n_pa).
      { rgne. rewrite HE6s1. exact bo_addr_lhn. }
      iApply (wp_clw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x3e)) (mword_of_int 13 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 44 : mword 12) E6 (K - 4)%nat
                (mword_of_int (Z.of_nat n) : mword 32) false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi3e [Hlhn] [-]").
      { iEval (rewrite Halhn). iExact "Hlhn". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hlhn".
      iEval (rewrite Halhn) in "Hlhn".
      set (E7 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg
          (sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32))]> E6).
      change (<[Regidx (mword_of_int 13 : mword 5) := regval_into_reg
          (sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32))]> E6) with E7.
      assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp40) in "Hpc".
      assert (HE7a3 : E7 !!! Regidx (mword_of_int 13 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64)).
      { rewrite /E7 upd_eq. apply bo_sext32. exact (bo_zn_lt n Hn30). }
      assert (HE7a5 : E7 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int (10 * (Z.of_nat out + 1)) : mword 64))
        by (rewrite /E7 upd_ne; [exact HE6a5 | reg_neq]).
      (* +0x40 c.addw a5,a5,a3 *)
      iEval (rewrite Hc5 Hc7) in "Hi40".
      iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x40)) (mword_of_int 15 : mword 5) (mword_of_int 13 : mword 5)
                E7 (K - 4)%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc Hi40 [-]").
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      iEval (rgne; rgne) in "Hcg".
      set (E8 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (sign_extend' 64 (add_vec
             (subrange_vec_dec (E7 !!! Regidx (mword_of_int 15 : mword 5)) 31 0 : mword 32)
             (subrange_vec_dec (E7 !!! Regidx (mword_of_int 13 : mword 5)) 31 0 : mword 32)))]> E7).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (sign_extend' 64 (add_vec
             (subrange_vec_dec (E7 !!! Regidx (mword_of_int 15 : mword 5)) 31 0 : mword 32)
             (subrange_vec_dec (E7 !!! Regidx (mword_of_int 13 : mword 5)) 31 0 : mword 32)))]> E7) with E8.
      assert (Hp42 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp42) in "Hpc".
      assert (HE8a5 : E8 !!! Regidx (mword_of_int 15 : mword 5)
                      = (mword_of_int (10 * (Z.of_nat out + 1) + Z.of_nat n) : mword 64)).
      { rewrite /E8 upd_eq HE7a5 HE7a3.
        apply bo_addw2; [apply (bo_sz_nonneg out) | apply bo_zout_nonneg
                        | exact (bo_sz_lt out n Hout3 Hn30)]. }
      assert (HE8s2 : E8 !!! Regidx (mword_of_int 18 : mword 5) = (mword_of_int 30 : mword 64)).
      { rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq].
        rewrite /E4 upd_ne; [| reg_neq]. rewrite /E3 upd_ne; [| reg_neq].
        rewrite /E2 upd_ne; [| reg_neq]. rewrite /E1 upd_ne; [| reg_neq]. exact Hs2. }
      assert (HE8a4 : E8 !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int (Z.of_nat out + 1) : mword 64)).
      { rewrite /E8 upd_ne; [| reg_neq]. rewrite /E7 upd_ne; [| reg_neq].
        rewrite /E6 upd_ne; [| reg_neq]. rewrite /E5 upd_ne; [| reg_neq]. exact HE4a4. }
      assert (HcsE8 : callee_saved M E8).
      { rewrite /E8 /E7 /E6 /E5 /E4 /E3 /E2 /E1.
        repeat (apply callee_saved_insert_r; [vm_compute; reflexivity|]).
        apply callee_saved_refl. }
      assert (HboE8 : bo_regs m E8 spd) by (apply (bo_regs_cs m M E8 spd HcsE8 HboM)).
      (* +0x42 bge s2,a5 : 30 >= lh.n + 10*(outstanding+1) ? *)
      assert (Hcmp : zopz0zKzJ_s (rget E8 (mword_of_int 18 : mword 5)) (rget E8 (mword_of_int 15 : mword 5))
                     = Z.geb 30 (10 * (Z.of_nat out + 1) + Z.of_nat n)).
      { rgne. rgne. rewrite HE8s2 HE8a5.
        apply bo_geb_s; [exact bo_30_b63 | exact (bo_sz_b63 out n Hout3 Hn30)]. }
      remember (Z.geb 30 (10 * (Z.of_nat out + 1) + Z.of_nat n)) as gb eqn:Hgb.
      destruct gb.
      + (* ---- GRANT: the branch is TAKEN, control at +0x50 ---- *)
        assert (Hle : (10 * (Z.of_nat out + 1) + Z.of_nat n <= 30)%Z)
          by (apply bo_geb_true; symmetry; exact Hgb).
        iPoseProof (boi_50 with "Htext") as "Hi50".
        iPoseProof (boi_54 with "Htext") as "Hi54".
        iApply (wp_bge_taken_s_sconf (mword_of_int (KernelSyms.begin_op + 0x42)) (mword_of_int 14 : mword 13)
                  (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5) E8 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc Hi42 [-]").
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgt50 : add_vec (mword_of_int (KernelSyms.begin_op + 0x42) : mword 64)
                           (sign_extend' 64 (mword_of_int 14 : mword 13)) = mword_of_int (KernelSyms.begin_op + 0x50))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt50) in "Hpc".
        (* +0x50 auipc a5,0x1e *)
        iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.begin_op + 0x50)) (mword_of_int 15 : mword 5)
                  (mword_of_int 30 : mword 20) E8 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc Hi50 [-]").
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc".
        set (E9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
            (add_vec (mword_of_int (KernelSyms.begin_op + 0x50) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> E8).
        change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
            (add_vec (mword_of_int (KernelSyms.begin_op + 0x50) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> E8) with E9.
        assert (Hp54 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x50) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x54))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp54) in "Hpc".
        assert (HE9a5 : E9 !!! Regidx (mword_of_int 15 : mword 5)
                        = add_vec (mword_of_int (KernelSyms.begin_op + 0x50) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))
          by (rewrite /E9; apply upd_eq).
        assert (HE9a4 : E9 !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int (Z.of_nat out + 1) : mword 64))
          by (rewrite /E9 upd_ne; [exact HE8a4 | reg_neq]).
        assert (HcsE9 : callee_saved E8 E9).
        { rewrite /E9. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
        assert (HboE9 : bo_regs m E9 spd) by (apply (bo_regs_cs m E8 E9 spd HcsE9 HboE8)).
        (* +0x54 sw a4,1802(a5) : log.outstanding := out+1 *)
        assert (Hsta : add_vec (rget E9 (mword_of_int 15 : mword 5))
                         (sign_extend' 64 (mword_of_int 1782 : mword 12)) = l_out).
        { rgne. rewrite HE9a5. exact bo_reloc_out_50. }
        iApply (wp_sw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x54)) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5)
                  (mword_of_int 1782 : mword 12) E9 (K - 4)%nat
                  (mword_of_int (Z.of_nat out) : mword 32) false
                  with "Hcg Hpc Hi54 [Hout] [-]").
        { iEval (rewrite Hsta). iExact "Hout". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hout".
        iEval (rewrite Hsta) in "Hout".
        assert (Hstv : trunc32 (rget E9 (mword_of_int 14 : mword 5))
                       = (mword_of_int (Z.of_nat out + 1) : mword 32)).
        { rgne. rewrite HE9a4. apply trunc32_mword_of_int. }
        iEval (rewrite Hstv) in "Hout".
        iEval (rewrite -(bo_zsucc out)) in "Hout".
        assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x54) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x58))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp58) in "Hpc".
        (* THE LEDGER STEP: mint a fresh operation at full budget *)
        iMod (log_begin_step γ om with "Hauth") as (i Hi) "(Hauth & HopS)".
        iDestruct (log_opS_op with "HopS") as "Hop".
        iAssert (log_res γ bn γfs cov logstart) with "[Hout Hcmt Hnc Hauth Hlhn Hbclose]" as "Hres".
        { rewrite /log_res. iExists (S out), false, nc, (<[i := (MAXOPBLOCKS, ∅)]> om).
          iFrame "Hout Hcmt Hnc Hauth".
          iSplitR.
          { iPureIntro. rewrite map_size_insert_None; [ by rewrite Hsz | exact Hi ]. }
          iSplitR.
          { iPureIntro. intros k e Hk.
            destruct (decide (k = i)) as [->|Hne].
            - rewrite lookup_insert in Hk.
              assert (e = (MAXOPBLOCKS, ∅)) as -> by congruence.
              apply Nat.le_refl.
            - rewrite lookup_insert_ne in Hk; [| exact (not_eq_sym Hne)]. exact (Hbnd k e Hk). }
          iSplitR; [iPureIntro; exact (bo_guard_out3 out n Hle)|].
          iSplitR; [iPureIntro; discriminate|].
          iExists n, LB. iSplitR.
          { iPureIntro. rewrite (op_sum_insert om i (MAXOPBLOCKS, ∅) Hi).
            exact (log_reserve_ok n out om Hsz Hbnd (bo_guard_sum out n Hle)). }
          iSplitR.
          (* THE FRESH OP HAS LOGGED NOTHING, so its credit set is empty and
             the soundness clause is immediate; the other entries are
             untouched. *)
          { iPureIntro. intros k e Hk.
            destruct (decide (k = i)) as [->|Hne].
            - rewrite lookup_insert in Hk.
              assert (e = (MAXOPBLOCKS, ∅)) as -> by congruence.
              apply empty_subseteq.
            - rewrite lookup_insert_ne in Hk; [| exact (not_eq_sym Hne)]. exact (Hsub k e Hk). }
          iApply ("Hbclose" with "Hlhn"). }
        rewrite /bo_exit.
        iSpecialize ("Hexit" $! CID with "[%]"); [wp_next_chain|].
        iApply ("Hexit" $! E9 with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hres Hop Hpid Hown Hpay Hcg Hpc").
        exact HboE9.
      + (* ---- NO SPACE: the branch FALLS THROUGH, control at +0x46 ---- *)
        iAssert (log_res γ bn γfs cov logstart) with "[Hout Hcmt Hnc Hauth Hlhn Hbclose]" as "Hres".
        { rewrite /log_res. iExists out, false, nc, om.
          iFrame "Hout Hcmt Hnc Hauth".
          iSplitR; [iPureIntro; exact Hsz|].
          iSplitR; [iPureIntro; exact Hbnd|].
          iSplitR; [iPureIntro; exact Hout3|].
          iSplitR; [iPureIntro; exact Hcmtout|].
          iExists n, LB. iSplitR; [iPureIntro; exact Hsum|].
          iSplitR; [iPureIntro; exact Hsub|].
          iApply ("Hbclose" with "Hlhn"). }
        iApply (wp_bge_fall_s_sconf (mword_of_int (KernelSyms.begin_op + 0x42)) (mword_of_int 14 : mword 13)
                  (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5) E8 (K - 4)%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp
                  with "Hcg Hpc Hi42 [-]").
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp46 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x46))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp46) in "Hpc".
        iApply (bo_armB_body (CID := CID) CID0 γs j γl γ bn γfs cov logstart dev m E8 pidv dq K eb C spd sp0
                  HK Heb Hj Hjl Hanch HboE8
                  with "Htext Hlog Hpanic Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Hpay Hcg Hpc").
  Qed.

End BoBodies.

(* ===================================================================== *)

Section ProofBeginOp.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefNameG Σ, !irefslotG Σ, !bioG Σ, !diskGhostG Σ,
            !fsLogG Σ, !logG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_begin_op_sconf 
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool)
    : wp_begin_op_sconf_body γs j γl bn γ γfs cov logstart dev pidv dq m K eb C b.
  Proof.
    cbv beta delta [wp_begin_op_sconf_body].
    intros pcE pj ret_tgt HK Hj Hjl Heb.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hown #Htext Hpc #Hpanic #Hlog Hpid #Hpinv Hcont".
    iPoseProof "Hlog" as "#Hlogc".
    iDestruct "Hlogc" as "(#Hislock & #Hldev & #Hlstart)".
    (* level 0 with an enabled base forces the enabled index *)
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbm.
    assert (Hb : b = true) by (rewrite -Hbm; exact Heb).
    clear Hbm. subst b.
    iPoseProof (boi_00 with "Htext") as "Hi00".
    iPoseProof (boi_02 with "Htext") as "Hi02".
    iPoseProof (boi_04 with "Htext") as "Hi04".
    iPoseProof (boi_06 with "Htext") as "Hi06".
    iPoseProof (boi_08 with "Htext") as "Hi08".
    iPoseProof (boi_0a with "Htext") as "Hi0a".
    iPoseProof (boi_0c with "Htext") as "Hi0c".
    iPoseProof (boi_10 with "Htext") as "Hi10".
    iPoseProof (boi_14 with "Htext") as "Hi14".
    (* ===================== PROLOGUE: 4-slot frame + saves ================ *)
    set (R1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m).
    assert (Hspm : m !!! Regidx csp_rs1 = sp0) by reflexivity.
    assert (Hpush : add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))
                    = pa_stk (m !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    assert (Hspd : add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd)
      by reflexivity.
    assert (Hsp0 : sp0 = m !!! Regidx csp_rs1) by reflexivity.
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 true (bo_K4 K HK) Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spd) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vr0)  "Hr0".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite HspR1. rewrite /spd. unfold sp0, pa_stk, add_vec_int. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".  iEval (rewrite -Hb4) in "Hr0".
    assert (Hp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x02))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp02) in "Hpc".
    (* +0x02..+0x08 the four c.sdsp saves *)
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x02)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              R1 (K - 4)%nat vr24 true with "Hcg Hpc Hi02 Hr24 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 4)%nat vr16 true with "Hcg Hpc Hi04 Hr16 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 (K - 4)%nat vr8 true with "Hcg Hpc Hi06 Hr8 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              R1 (K - 4)%nat vr0 true with "Hcg Hpc Hi08 Hr0 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc Hr0".
    iEval (rgne) in "Hr0".
    assert (Hp0a : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x0a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0a) in "Hpc".
    iEval (rewrite Hb1) in "Hr24". iEval (rewrite Hb2) in "Hr16".
    iEval (rewrite Hb3) in "Hr8".  iEval (rewrite Hb4) in "Hr0".
    assert (Hr1v : R1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr8v : R1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr9v : R1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    assert (Hr18v : R1 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5))
      by (rewrite /R1 upd_ne; [reflexivity | reg_neq]).
    iEval (rewrite Hr1v) in "Hr24". iEval (rewrite Hr8v) in "Hr16".
    iEval (rewrite Hr9v) in "Hr8".  iEval (rewrite Hr18v) in "Hr0".
    (* +0x0a c.addi4spn s0,sp,32 *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KernelSyms.begin_op + 0x0a)) (Cregidx (mword_of_int 0)) (mword_of_int 8 : mword 8)
              (mword_of_int 8 : mword 5) R1 (K - 4)%nat true
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1) with R2.
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c auipc a0,0x1e ; +0x10 addi a0,a0,1842 : a0 := &log *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.begin_op + 0x0c)) (mword_of_int 10 : mword 5)
              (mword_of_int 30 : mword 20) R2 (K - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.begin_op + 0x0c) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> R2).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.begin_op + 0x0c) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> R2) with R3.
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.begin_op + 0x10)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 1822 : mword 12) R3 (K - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi10 [-]").
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (R3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1822 : mword 12)))]> R3).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (R3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1822 : mword 12)))]> R3) with R4.
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    assert (HR4a0 : R4 !!! Regidx (mword_of_int 10 : mword 5) = log_addr).
    { rewrite /R4 upd_eq /R3 upd_eq. exact bo_reloc_a0_0c. }
    (* +0x14 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x14)) (mword_of_int 1 : mword 5)
              (mword_of_int 2084870 : mword 21) R4 (K - 4)%nat true
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi14 [-]").
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (Maq := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x14) : mword 64) 4)]> R4).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x14) : mword 64) 4)]> R4) with Maq.
    assert (Hjaq : add_vec (mword_of_int (KernelSyms.begin_op + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2084870 : mword 21))
                   = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjaq) in "Hpc".
    assert (HMaqa0 : Maq !!! Regidx (mword_of_int 10 : mword 5) = log_addr)
      by (rewrite /Maq upd_ne; [exact HR4a0 | reg_neq]).
    assert (HMaqra : Maq !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x14) : mword 64) 4)
      by (rewrite /Maq; apply upd_eq).
    assert (HMaqcsp : Maq !!! Regidx csp_rs1 = spd).
    { rewrite /Maq upd_ne; [| reg_neq]. rewrite /R4 upd_ne; [| reg_neq].
      rewrite /R3 upd_ne; [| reg_neq]. rewrite /R2 upd_ne; [| reg_neq]. exact HspR1. }
    assert (Hpro_cs : forall c : mword 5,
              c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 10 -> c <> mword_of_int 1 ->
              Maq !!! Regidx c = m !!! Regidx c).
    { intros c N2 N8 N10 N1.
      rewrite /Maq upd_ne; [| congruence]. rewrite /R4 upd_ne; [| congruence].
      rewrite /R3 upd_ne; [| congruence]. rewrite /R2 upd_ne; [| congruence].
      rewrite /R1 upd_ne; [reflexivity | congruence]. }
    (* ===================== acquire(&log.lock) ===================== *)
    iDestruct (cpu_own_transport CID CID9 0 eb pj C true ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Acquire.wp_acquire_sconf (ln_lk γ) "log"%string (log_res γ bn γfs cov logstart) Maq
              0%nat eb pj C (K - 4)%nat true
              bo_noff1 (bo_K10 K HK)
              with "Hcg Hown Htext Hpc [] Hpanic [-]").
    { iEval (rewrite HMaqa0). iExact "Hislock". }
    iIntros (CIDa Hsa ms Macq) "%Hmsf Hcg Hpc %Hcsacq Htok Hres Hown Hpay".
    assert (Hpc18 : ret_pc (Maq !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x18))
      by (rewrite HMaqra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc18) in "Hpc".
    assert (Hacq_csp : Macq !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hcsacq csp_rs1 ltac:(vm_compute; reflexivity)). exact HMaqcsp. }
    assert (Hacq_rest : forall c : mword 5, is_cs_idx c = true ->
              c <> csp_rs1 -> c <> mword_of_int 8 -> c <> mword_of_int 10 -> c <> mword_of_int 1 ->
              Macq !!! Regidx c = m !!! Regidx c).
    { intros c Hcs N2 N8 N10 N1.
      rewrite (callee_saved_lookup Hcsacq c Hcs). exact (Hpro_cs c N2 N8 N10 N1). }
    (* ============ the anchored EXIT continuation (+0x58 -> ret) ============ *)
    iAssert (bo_exit CID j γ bn γfs cov logstart m pidv dq K eb C spd sp0) with "[Hcont]" as "Hexit".
    { rewrite /bo_exit.
      iIntros (CIDx Hsx Mx) "%HboE Hr24 Hr16 Hr8 Hr0 Htok Hres Hop Hpid Hown Hpay Hcg Hpc".
      iApply (bo_exit_body (CID := CIDx) CID j γ bn γfs cov logstart dev m Mx pidv dq K eb C spd sp0
                HK Heb Hsx Hspd Hsp0 HboE
                with "Htext Hlog Hr24 Hr16 Hr8 Hr0 Htok Hres Hop Hpid Hown Hpay Hcg Hpc Hcont"). }
    (* ============ the WAIT LOOP (iLöb over the anchored invariant) ======== *)
    iAssert (bo_loop CID j γ bn γfs cov logstart m pidv dq K eb C spd sp0) with "[]" as "Hloop".
    { iLöb as "IH". rewrite /bo_loop.
      iIntros (CIDy Hsy My) "%HboL Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Hpay Hcg Hpc Hexit".
      iApply (bo_loop_body (CID := CIDy) CID γs j γl γ bn γfs cov logstart dev m My pidv dq K eb C spd sp0
                HK Heb Hj Hjl Hsy HboL
                with "Htext Hlog Hpanic Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Hpay Hcg Hpc"). }
    (* ============ +0x18..+0x22: s1 := &log, s2 := 30, jump to the test ==== *)
    iPoseProof (boi_18 with "Htext") as "Hi18".
    iPoseProof (boi_1c with "Htext") as "Hi1c".
    iPoseProof (boi_20 with "Htext") as "Hi20".
    iPoseProof (boi_22 with "Htext") as "Hi22".
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.begin_op + 0x18)) (mword_of_int 9 : mword 5)
              (mword_of_int 30 : mword 20) Macq (K - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi18 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (T1 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.begin_op + 0x18) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> Macq).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.begin_op + 0x18) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> Macq) with T1.
    assert (Hp1c : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x18) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x1c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp1c) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.begin_op + 0x1c)) (mword_of_int 9 : mword 5)
              (mword_of_int 9 : mword 5) (mword_of_int 1810 : mword 12) T1 (K - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi1c [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec (T1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 1810 : mword 12)))]> T1).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec (T1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 1810 : mword 12)))]> T1) with T2.
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    assert (HT2s1 : T2 !!! Regidx (mword_of_int 9 : mword 5) = log_addr).
    { rewrite /T2 upd_eq /T1 upd_eq. exact bo_reloc_s1_18. }
    (* +0x20 c.li s2,30 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.begin_op + 0x20)) (mword_of_int 18 : mword 5)
              (mword_of_int 30 : mword 6) (mword_of_int 30 : mword 64) T2 (K - 4)%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi20 [-]").
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (T3 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mword_of_int 30 : mword 64)]> T2).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (mword_of_int 30 : mword 64)]> T2) with T3.
    assert (Hp22 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x20) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x22))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp22) in "Hpc".
    (* the loop invariant's register facts at T3 *)
    assert (HboT3 : bo_regs m T3 spd).
    { unfold bo_regs. split_and!.
      - rewrite /T3 upd_ne; [| reg_neq]. exact HT2s1.
      - rewrite /T3 upd_eq. reflexivity.
      - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
        rewrite /T1 upd_ne; [| reg_neq]. exact Hacq_csp.
      - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
        rewrite /T1 upd_ne; [| reg_neq]. apply Hacq_rest; [vm_compute; reflexivity|reg_neq..].
      - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
        rewrite /T1 upd_ne; [| reg_neq]. apply Hacq_rest; [vm_compute; reflexivity|reg_neq..].
      - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
        rewrite /T1 upd_ne; [| reg_neq]. apply Hacq_rest; [vm_compute; reflexivity|reg_neq..].
      - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
        rewrite /T1 upd_ne; [| reg_neq]. apply Hacq_rest; [vm_compute; reflexivity|reg_neq..].
      - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
        rewrite /T1 upd_ne; [| reg_neq]. apply Hacq_rest; [vm_compute; reflexivity|reg_neq..].
      - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
        rewrite /T1 upd_ne; [| reg_neq]. apply Hacq_rest; [vm_compute; reflexivity|reg_neq..].
      - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
        rewrite /T1 upd_ne; [| reg_neq]. apply Hacq_rest; [vm_compute; reflexivity|reg_neq..].
      - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
        rewrite /T1 upd_ne; [| reg_neq]. apply Hacq_rest; [vm_compute; reflexivity|reg_neq..].
      - rewrite /T3 upd_ne; [| reg_neq]. rewrite /T2 upd_ne; [| reg_neq].
        rewrite /T1 upd_ne; [| reg_neq]. apply Hacq_rest; [vm_compute; reflexivity|reg_neq..]. }
    (* +0x22 c.j -> +0x2c *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.begin_op + 0x22))
              (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0"))) T3 (K - 4)%nat false
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc Hi22 [-]").
    iApply wp_next_off_intro.
    iNext.
    iIntros "Hcg Hpc".
    assert (Htgt2c : add_vec (mword_of_int (KernelSyms.begin_op + 0x22) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.begin_op + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt2c) in "Hpc".
    rewrite /bo_loop.
    iSpecialize ("Hloop" $! CIDa with "[%]"); [wp_next_chain|].
    iApply ("Hloop" $! T3 with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Hpay Hcg Hpc Hexit").
    exact HboT3.
  Qed.

End ProofBeginOp.

End BeginOpProof.
