(* ProofBeginOp.v -- begin_op() over the SIE-agnostic sconf world.

     void begin_op(void) {
       acquire(&log.lock);
       while (1) {
         if (log.committing)                        SLEEP;
         else if (log.lh.n + (log.outstanding+1)*MAXOPBLOCKS > LOGBLOCKS)
                                                    SLEEP;
         else { log.outstanding += 1; break; }
       }
       release(&log.lock);
     }

   where SLEEP is the SPLIT sleep protocol (SpecSleep.v's header):

       sleep_prepare(&log); release(&log.lock); sleep(); acquire(&log.lock);

   Structure (CodeBeginOp.v has the byte-exact disassembly): a 32-byte
   ra/s0/s1/s2 frame, acquire(&log), then the retry loop whose test sits at
   +0x3a; s1 = &log (reloaded AFTER the acquire call), s2 = 30 = LOGBLOCKS.
   Two sleep arms (+0x24 for "committing", +0x54 for "no space"), each seven
   instructions long, one exit (the +0x50 bge taken) into the
   [outstanding += 1] tail at +0x6c and the release/epilogue.

   THE PROOF SHAPE.  Both sleeps PARK, so the retry loop is proved by iLöb
   over a [wp_next]-anchored loop invariant, exactly as ProofAcquiresleep.v
   does -- a park can resume the thread on a hart nobody knew about when the
   invariant was established, and a [wp_next] is the proposition that
   survives that.  [bo_loop] (control at +0x3a, the log lock HELD with
   [log_res] closed) and [bo_exit] (control at +0x74, after the store, with
   the freshly minted [log_op]) are both anchored at the function's entry
   hart [CID0].

   THE PAIR SPLITS AND REJOINS AROUND EACH ARM.  The loop invariant carries
   [trap_csrs] and [cpu_claim pj] index-free; the arm's own release wants
   the PAY half ([IntrDefs.arm_pay 0 eb pj]) and the lock-free sleep() wants
   the COMPLEMENT, so each arm splits once ([arm_pay_ext_split]), hands the
   complement across the park, and rejoins ([arm_pay_ext_join]) once the
   re-acquire has minted a fresh pay.  Between the interior release and the
   re-acquire the thread holds NO lock -- a window this function did not
   have before the protocol was split.

   THE LEDGER STEP is the whole content of the function (SpecBeginOp.v):
   each iteration opens [log_res]; the committing arm and the space arm
   re-close it VERBATIM and sleep; the grant arm reads the guard true, and
   there [LogInv.log_begin_step] mints the op at MAXOPBLOCKS while
   [LogInv.log_reserve_ok] turns the code's conservative
   (out+1)*MAXOPBLOCKS test into the exact sum tie the invariant carries.

   THE GUARD'S ARITHMETIC is computed by the image in W-form
   (addiw/slliw/addw/slliw/addw, all 32-bit and sign-extended).  Every value
   involved is tiny -- [out <= 3] is a log_res conjunct and [n <= LOGBLOCKS]
   a log_state one -- so the register values stay 64-bit literals
   ([mword_of_int z] with 0 <= z < 2^31) all the way through.  The three
   steps whose operand is the small [out] are discharged by a four-way case
   split ([bo_slli2] / [bo_addw1] / [bo_slli1]); only the final
   [addw a5,a5,a3] has a symbolic operand and gets the general
   [bo_addw2] bridge.

   A functor over ACQUIRE / RELEASE / SLEEP_PREPARE / SLEEP. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import auth gmap gset frac excl.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvModelBytes.
Require Import InstrBytes KernelText WpMmodeLeafBase.
Require Import RegFile.
Require Import RiscvExtras.
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
Require Import ProcDefs.  (* [proc_priv_bare] *)
Require Import WpLock.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import SpecAcquire SpecRelease SpecSleepPrepare SpecSleep.
Require Import SpecBeginOp.
Require Import CodeBeginOp.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
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
Proof. lia. Qed.
Lemma bo_K10 (K : nat) : (K_begin_op <= K)%nat -> (10 <= K - 4)%nat.
Proof. lia. Qed.
Lemma bo_K22 (K : nat) : (K_begin_op <= K)%nat -> (22 <= K - 4)%nat.
Proof. lia. Qed.
Lemma bo_Kback (K : nat) : (K_begin_op <= K)%nat -> ((K - 4) + 4)%nat = K.
Proof. lia. Qed.
Lemma bo_noff2 : (Z.of_nat 1 + 1 < 2 ^ 31)%Z.
Proof. vm_compute. reflexivity. Qed.
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
          (sign_extend' 64 (mword_of_int 1820 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma bo_reloc_s1_18 :
  add_vec (add_vec (mword_of_int (KernelSyms.begin_op + 0x18) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1808 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma bo_reloc_a0_58 :
  add_vec (add_vec (mword_of_int (KernelSyms.begin_op + 0x74) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1716 : mword 12)) = log_addr.
Proof. rewrite /log_addr. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma bo_reloc_out_50 :
  add_vec (add_vec (mword_of_int (KernelSyms.begin_op + 0x6c) : mword 64)
                   (auipc_off (mword_of_int 30 : mword 20)))
          (sign_extend' 64 (mword_of_int 1752 : mword 12)) = l_out.
Proof.
  rewrite /l_out /log_pa /log_addr /pa_add /add_vec_int.
  apply bv_eq; vm_compute; reflexivity.
Qed.

(* sleep_prepare's panic arm, refuted: the channel is a static address *)
Lemma bo_log_nz : eq_vec log_addr (zero_reg : mword 64) = false.
Proof. rewrite /log_addr. vm_compute. reflexivity. Qed.

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
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  (* the log lock's batch, opened just for its [lh.n] cell *)
  Lemma bo_batch_lhn (bn : bio_names) (γfs : fs_names) (cov : gset Z)
      (logstart : Z) (n : nat) (LB : gset Z) (pend : gset fsobj) :
    log_state bn γfs cov logstart n LB pend -∗
    ⌜(n <= LOGBLOCKS)%nat⌝ ∗
    lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) ∗
    (lh_n_pa ↦₄ (mword_of_int (Z.of_nat n) : mword 32) -∗
       log_state bn γfs cov logstart n LB pend).
  Proof.
    iIntros "H". rewrite /log_state.
    iDestruct "H" as (W L D M) "(%Hlen & %HLB & %Hnd & %Hcv & Hn & Hblk & Hjunk & HL & HD & Hdirty & Hhdr & Hsl & Hpool & Hmirh & %Hmhdr & %Hmtie & %Hrowa)".
    iSplitR; [iPureIntro; exact (proj2 Hlen)|].
    iFrame "Hn". iIntros "Hn".
    iExists W, L, D, M.
    iSplitR; [iPureIntro; exact Hlen|].
    iSplitR; [iPureIntro; exact HLB|].
    iSplitR; [iPureIntro; exact Hnd|].
    iSplitR; [iPureIntro; exact Hcv|].
    iFrame "Hn Hblk Hjunk HL HD Hdirty Hhdr Hsl Hpool Hmirh".
    iSplitR; [iPureIntro; exact Hmhdr|].
    iSplitR; [iPureIntro; exact Hmtie|].
    iPureIntro; exact Hrowa.
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
      (K : nat) (eb : bool) (spd sp0 : mword 64) (lks : gset string) (Vpr : pprivate) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (M : regfile),
      ⌜ bo_regs m M spd ⌝ -∗
      pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
      pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
      pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
      locked (ln_lk γ) cpu_id -∗
      log_res γ bn γfs cov logstart -∗
      log_op γ MAXOPBLOCKS -∗
      proc_priv_bare (proc_addr j) pidv Vpr -∗
      (* HELD: "log" is still taken at this point (it is released by the
         [+0x7c jal release] this covers) -- [lks] itself is the OUTER set,
         matching what this stretch's own continuation ([Hcont], threaded
         straight through from the caller) hands back once that release
         fires. *)
      cpu_own 1 eb (proc_addr j) false ({["log"]} ∪ lks) -∗
      trap_csrs KT1 -∗
      cpu_claim (proc_addr j) -∗
      sie_cap_gpr KT1 M (trap_res eb + (K - 4))%nat false (proc_addr j) -∗
      pc_is (mword_of_int (KernelSyms.begin_op + 0x74)) -∗
      WP (Loop : expr riscv_lang)))%I.

  Definition bo_loop `{GEN : GenId} (CID0 : CPU)
      (j : nat)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z)
      (m : regfile) (pidv : mword 32) (dq : dfrac)
      (K : nat) (eb : bool) (spd sp0 : mword 64) (lks : gset string) (Vpr : pprivate) : iProp Σ :=
    (wp_next (CID0 := CID0) true (proc_addr j) (fun (CID : CpuId) =>
      ∀ (M : regfile),
      ⌜ bo_regs m M spd ⌝ -∗
      pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
      pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
      pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
      pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
      locked (ln_lk γ) cpu_id -∗
      log_res γ bn γfs cov logstart -∗
      proc_priv_bare (proc_addr j) pidv Vpr -∗
      (* same convention as [bo_exit]: [lks] is the OUTER set, this loop
         iteration is entered still HOLDING "log". *)
      cpu_own 1 eb (proc_addr j) false ({["log"]} ∪ lks) -∗
      trap_csrs KT1 -∗
      cpu_claim (proc_addr j) -∗
      sie_cap_gpr KT1 M (trap_res eb + (K - 4))%nat false (proc_addr j) -∗
      pc_is (mword_of_int (KernelSyms.begin_op + 0x3a)) -∗
      bo_exit CID0 j γ bn γfs cov logstart m pidv dq K eb spd sp0 lks Vpr -∗
      WP (Loop : expr riscv_lang)))%I.

End BoProps.

(* ===================================================================== *)

Module BeginOpProof (Acquire : ACQUIRE) (Release : RELEASE)
                    (SleepPrepare : SLEEP_PREPARE) (Sleep : SLEEP) : BEGIN_OP.

Local Ltac reg_neq :=
  lazymatch goal with |- ?a <> ?b =>
    tryif unify a b then fail else (vm_compute; discriminate) end.

Section BoBodies.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.

  (* ---- the exit path: +0x58 (a0 := &log) .. +0x6e (c.ret) ---- *)
  Lemma bo_exit_body `{GEN : GenId} `{CID : CpuId} (CID0 : CPU) (j : nat)
      (γ : log_names) (bn : bio_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (m M : regfile) (pidv : mword 32) (dq : dfrac)
      (K : nat) (eb : bool) (spd sp0 : mword 64) (lks : gset string) (Vpr : pprivate) :
    let pj := proc_addr j in
    (K_begin_op <= K)%nat ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))) = spd ->
    sp0 = m !!! Regidx csp_rs1 ->
    bo_regs m M spd ->
    (* [lks] is the OUTER set (see [bo_exit]'s header note); this is what
       lets the [Hcont]-shaped continuation below be handed the CALLER's own
       [Hcont] unmodified. *)
    locks_below lks "log" ->
    kernel_text -∗
    log_ctx γ bn γfs cov logstart dev -∗
    pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    log_op γ MAXOPBLOCKS -∗
    proc_priv_bare pj pidv Vpr -∗
    cpu_own 1 eb pj false ({["log"]} ∪ lks) -∗
    trap_csrs KT1 -∗
    cpu_claim pj -∗
    sie_cap_gpr KT1 M (trap_res eb + (K - 4))%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.begin_op + 0x74)) -∗
    wp_next (CID0 := CID0) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile),
        ⌜ callee_saved m mf ⌝ -∗
        sie_cap_gpr KT1 mf K eb pj -∗
        cpu_own 0 eb pj eb lks -∗
        trap_csrs_ext KT1 eb -∗
        cpu_claim_ext eb pj -∗
        pc_is (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) -∗
        proc_priv_bare pj pidv Vpr -∗
        log_op γ MAXOPBLOCKS -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj HK Hanch Hspd Hsp0 Hbo Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    destruct Hbo as (Hs1 & Hs2 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    iIntros "#Htext #Hlog Hr24 Hr16 Hr8 Hr0 Htok Hres Hop Hpid Hown Htc Hclm Hcg Hpc Hcont".
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
    (* +0x58 auipc a0,0x1e *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.begin_op + 0x74)) (mword_of_int 10 : mword 5)
              (mword_of_int 30 : mword 20) M (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_74 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (X1 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.begin_op + 0x74) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> M).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.begin_op + 0x74) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> M) with X1.
    assert (Hp5c : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x74) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x78))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp5c) in "Hpc".
    (* +0x5c addi a0,a0,1766 *)
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.begin_op + 0x78)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 1716 : mword 12) X1 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_78 with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (X2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (X1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1716 : mword 12)))]> X1).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (X1 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1716 : mword 12)))]> X1) with X2.
    assert (Hp60 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x78) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x7c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp60) in "Hpc".
    assert (HX2a0 : X2 !!! Regidx (mword_of_int 10 : mword 5) = log_addr).
    { rewrite /X2 upd_eq /X1 upd_eq. exact bo_reloc_a0_58. }
    (* +0x60 jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x7c)) (mword_of_int 1 : mword 5)
              (mword_of_int 2084710 : mword 21) X2 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_7c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    set (X3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x7c) : mword 64) 4)]> X2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x7c) : mword 64) 4)]> X2) with X3.
    assert (Hjrel : add_vec (mword_of_int (KernelSyms.begin_op + 0x7c) : mword 64) (sign_extend' 64 (mword_of_int 2084710 : mword 21))
                    = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjrel) in "Hpc".
    assert (HX3ra : X3 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x7c) : mword 64) 4)
      by (rewrite /X3; apply upd_eq).
    assert (HX3a0 : X3 !!! Regidx (mword_of_int 10 : mword 5) = log_addr)
      by (rewrite /X3 upd_ne; [exact HX2a0 | reg_neq]).
    assert (HX3csp : X3 !!! Regidx csp_rs1 = spd).
    { rewrite /X3 upd_ne; [| reg_neq]. rewrite /X2 upd_ne; [| reg_neq].
      rewrite /X1 upd_ne; [| reg_neq]. exact Hsp. }
    assert (Hrel_lka : add_vec (X3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = log_addr)
      by (rewrite HX3a0; apply addv_sext0).
    (* SPLIT AT THE INDEX: release takes [arm_pay 0 eb pj] -- the pair at
       [eb = true], [emp] at [eb = false] -- and the complement rides out to
       the caller, which is what makes this contract index-generic. *)
    iDestruct (arm_pay_ext_split eb _ with "Htc Hclm") as "[Hpay Hext]".
    iApply (Release.wp_release_sconf KT1 (ln_lk γ) log_addr "log"%string
              (log_res γ bn γfs cov logstart) X3 0%nat eb pj (K - 4)%nat
              ({["log"]} ∪ lks)
              Hrel_lka ltac:(lia)
              with "Hcg Htext Hpc Hislock Htok Hres Hown Hpay").
    iIntros (CIDr Hsr mrel) "Hcg Hpc %Hrelcs Hown".
    (* back to the OUTER set, matching [Hcont]'s expectation unmodified. *)
    assert (Hsetback : ({["log"]} ∪ lks) ∖ {["log"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hown".
    assert (Hpc64 : ret_pc (X3 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x80))
      by (rewrite HX3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc64) in "Hpc".
    (* ===== EPILOGUE (+0x64..+0x6e): restore ra/s0/s1/s2, pop, ret ===== *)
    pose proof Hrelcs as Hrelcs2.
    assert (HmrelSp : mrel !!! Regidx csp_rs1 = spd).
    { rewrite (callee_saved_lookup Hrelcs csp_rs1 ltac:(vm_compute; reflexivity)). exact HX3csp. }
    (* +0x64 c.ldsp ra,24(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x80)) (mword_of_int 3 : mword 6) (mword_of_int 1 : mword 5)
              mrel (K - 4)%nat (m !!! Regidx (mword_of_int 1 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr24]").
    { iApply (boi_80 with "Htext"). }
    { iEval (rewrite HmrelSp Hb1). iExact "Hr24". }
    iIntros (CIDe1 Hse1) "Hcg Hpc Hr24".
    iEval (rewrite HmrelSp Hb1) in "Hr24".
    set (Q64 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> mrel) with Q64.
    assert (HQ64sp : Q64 !!! Regidx csp_rs1 = spd) by (rewrite /Q64 upd_ne; [exact HmrelSp | reg_neq]).
    assert (Hp66 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x80) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x82))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp66) in "Hpc".
    (* +0x66 c.ldsp s0,16(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x82)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              Q64 (K - 4)%nat (m !!! Regidx (mword_of_int 8 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr16]").
    { iApply (boi_82 with "Htext"). }
    { iEval (rewrite HQ64sp Hb2). iExact "Hr16". }
    iIntros (CIDe2 Hse2) "Hcg Hpc Hr16".
    iEval (rewrite HQ64sp Hb2) in "Hr16".
    set (Q66 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q64).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q64) with Q66.
    assert (HQ66sp : Q66 !!! Regidx csp_rs1 = spd) by (rewrite /Q66 upd_ne; [exact HQ64sp | reg_neq]).
    assert (Hp68 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x82) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x84))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp68) in "Hpc".
    (* +0x68 c.ldsp s1,8(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x84)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              Q66 (K - 4)%nat (m !!! Regidx (mword_of_int 9 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr8]").
    { iApply (boi_84 with "Htext"). }
    { iEval (rewrite HQ66sp Hb3). iExact "Hr8". }
    iIntros (CIDe3 Hse3) "Hcg Hpc Hr8".
    iEval (rewrite HQ66sp Hb3) in "Hr8".
    set (Q68 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> Q66).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 9 : mword 5))]> Q66) with Q68.
    assert (HQ68sp : Q68 !!! Regidx csp_rs1 = spd) by (rewrite /Q68 upd_ne; [exact HQ66sp | reg_neq]).
    assert (Hp6a : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x84) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x86))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6a) in "Hpc".
    (* +0x6a c.ldsp s2,0(sp) *)
    iApply (wp_cldsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x86)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              Q68 (K - 4)%nat (m !!! Regidx (mword_of_int 18 : mword 5)) eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hr0]").
    { iApply (boi_86 with "Htext"). }
    { iEval (rewrite HQ68sp Hb4). iExact "Hr0". }
    iIntros (CIDe4 Hse4) "Hcg Hpc Hr0".
    iEval (rewrite HQ68sp Hb4) in "Hr0".
    set (Q6a := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> Q68).
    change (<[Regidx (mword_of_int 18 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 18 : mword 5))]> Q68) with Q6a.
    assert (HQ6asp : Q6a !!! Regidx csp_rs1 = spd) by (rewrite /Q6a upd_ne; [exact HQ68sp | reg_neq]).
    assert (Hp6c : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x86) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x88))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6c) in "Hpc".
    (* +0x6c c.addi16sp sp,32 -- the frame trade back *)
    assert (Hwv : add_vec (Q6a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HQ6asp -Hspd. apply frame_cancel_32. }
    assert (Hpop : Q6a !!! Regidx csp_rs1
                   = pa_stk (add_vec (Q6a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HQ6asp -Hspd. unfold pa_stk, add_vec_int.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iAssert (stack_own (KTR := KT1) sp0 4) with "[Hr24 Hr16 Hr8 Hr0]" as "Hframe4".
    { rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
      iSplitL "Hr24"; [iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iExists _; iExact "Hr8"|].
      iSplitL "Hr0";  [iExists _; iExact "Hr0"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (KernelSyms.begin_op + 0x88)) (mword_of_int 2 : mword 6) Q6a (K - 4)%nat 4 eb Hpop
              with "Hcg Hpc [] Hframe4").
    { iApply (boi_88 with "Htext"). }
    iIntros (CIDe5 Hse5) "Hcg Hpc".
    assert (Hnk : ((K - 4) + 4)%nat = K) by (lia).
    iEval (rewrite Hnk) in "Hcg".
    set (Q6c := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (Q6a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q6a).
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (Q6a !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> Q6a) with Q6c.
    assert (Hp6e : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x88) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x8a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp6e) in "Hpc".
    (* +0x6e c.ret *)
    assert (HQ6cra : Q6c !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { rewrite /Q6c upd_ne; [| reg_neq]. rewrite /Q6a upd_ne; [| reg_neq].
      rewrite /Q68 upd_ne; [| reg_neq]. rewrite /Q66 upd_ne; [| reg_neq].
      rewrite /Q64 upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf (mword_of_int (KernelSyms.begin_op + 0x8a)) (mword_of_int 1 : mword 5) Q6c K eb
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc []").
    { iApply (boi_8a with "Htext"). }
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
    iDestruct (cpu_own_transport CIDr CIDe6 0 eb pj eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    (* the complement the release did not take, at the hart the epilogue
       ends on.  Free at both indices: [emp] at [eb = true], and at
       [eb = false] no step here could have moved the hart. *)
    iDestruct "Hext" as "[Hextc Hextm]".
    iDestruct (trap_csrs_ext_transport CID CIDe6 eb pj ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CIDe6 eb pj ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    iSpecialize ("Hcont" $! CIDe6 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! Q6c with "[%] Hcg Hown Hextc Hextm Hpc Hpid Hop").
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
      (K : nat) (eb : bool) (spd sp0 : mword 64) (lks : gset string) (Vpr : pprivate) :
    let pj := proc_addr j in
    (K_begin_op <= K)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    bo_regs m M spd ->
    (* [lks] is the OUTER set: [IH]/[Hexit] are threaded straight through
       from the caller, so this arm's own precondition (still HOLDING "log")
       reads [{["log"]} ∪ lks], and it needs its own order bound
       to run the interior release/re-acquire's set arithmetic. *)
    locks_below lks "log" ->
    kernel_text -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    bo_loop CID0 j γ bn γfs cov logstart m pidv dq K eb spd sp0 lks Vpr -∗
    bo_exit CID0 j γ bn γfs cov logstart m pidv dq K eb spd sp0 lks Vpr -∗
    pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    proc_priv_bare pj pidv Vpr -∗
    cpu_own 1 eb pj false ({["log"]} ∪ lks) -∗
    trap_csrs KT1 -∗
    cpu_claim pj -∗
    sie_cap_gpr KT1 M (trap_res eb + (K - 4))%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.begin_op + 0x24)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj HK Hj Hjl Hanch Hbo Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    iIntros "#Htext #Hlog #Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Htc Hclm Hcg Hpc".
    iDestruct "Hlog" as "(#Hislock & #Hldev & #Hlstart)".
    assert (HboM : bo_regs m M spd) by exact Hbo.
    destruct Hbo as (Hs1 & Hs2 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    (* THE SPLIT SLEEP PROTOCOL.  The loop invariant carries [trap_csrs] and
       [cpu_claim pj] index-free; the interior release wants the PAY half of
       that pair and the park wants the COMPLEMENT, so split once here and
       rejoin after the re-acquire.  Between +0x2c and +0x36 this thread
       holds no lock at all -- that window is new, and it is where the park
       lives. *)
    iDestruct (arm_pay_ext_split eb pj with "Htc Hclm") as "[Hpay [Htcx Hclmx]]".
    (* +0x24 c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.begin_op + 0x24)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              M (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_24 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 9 : mword 5)))]> M).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 9 : mword 5)))]> M) with A0.
    assert (HAp2 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x24) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x26))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HAp2) in "Hpc".
    assert (HA0a0 : A0 !!! Regidx (mword_of_int 10 : mword 5) = log_addr).
    { rewrite /A0 upd_eq. rewrite Hs1. apply add_vec_zero_l. }
    (* +0x26 jal ra,sleep_prepare *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x26)) (mword_of_int 1 : mword 5)
              (mword_of_int 2089566 : mword 21) A0 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_26 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x26) : mword 64) 4)]> A0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x26) : mword 64) 4)]> A0) with A1.
    assert (HAjsp : add_vec (mword_of_int (KernelSyms.begin_op + 0x26) : mword 64) (sign_extend' 64 (mword_of_int 2089566 : mword 21))
                   = mword_of_int KernelSyms.sleep_prepare)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HAjsp) in "Hpc".
    assert (HA1ra : A1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x26) : mword 64) 4)
      by (rewrite /A1; apply upd_eq).
    assert (HA1a0 : A1 !!! Regidx (mword_of_int 10 : mword 5) = log_addr)
      by (rewrite /A1 upd_ne; [exact HA0a0 | reg_neq]).
    assert (HcsA1 : callee_saved M A1).
    { rewrite /A1 /A0.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HboA1 : bo_regs m A1 spd) by (apply (bo_regs_cs m M A1 spd HcsA1 HboM)).
    assert (HA1nz : eq_vec (A1 !!! Regidx (mword_of_int 10 : mword 5)) (zero_reg : mword 64) = false)
      by (rewrite HA1a0; exact bo_log_nz).
    (* -------------------- sleep_prepare(&log) -------------------- *)
    (* still HOLDING "log" here -- lift [Hbelow] to "proc" and push it across
       the "log" singleton this hart is holding right now
       ([locks_below_union_singleton]), matching the OUTER set [Hown] carries
       at this point. *)
    assert (HbelowA1 : locks_below ({["log"]} ∪ lks) "proc").
    { apply locks_below_union_singleton; [vm_compute; lia |].
      lkbelow. }
    iApply (SleepPrepare.wp_sleep_prepare_sconf γs j γl A1
              (trap_res eb + (K - 4))%nat 1%nat eb false
              ({["log"]} ∪ lks) Hj Hjl HA1nz bo_noff2 ltac:(pose proof (bo_K22 K HK); lia)
              HbelowA1
              with "Hcg Hown Htext Hpc Hpinv").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (mfp) "%HApcs Hcg Hown Hpc".
    assert (HAp3 : ret_pc (A1 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x2a))
      by (rewrite HA1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HAp3) in "Hpc".
    assert (HboAPr : bo_regs m mfp spd) by (apply (bo_regs_cs m A1 mfp spd HApcs HboA1)).
    assert (HAPrs1 : mfp !!! Regidx (mword_of_int 9 : mword 5) = log_addr)
      by (destruct HboAPr as (X & _); exact X).
    (* +0x2a c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.begin_op + 0x2a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mfp (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_2a with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfp !!! Regidx (mword_of_int 9 : mword 5)))]> mfp).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfp !!! Regidx (mword_of_int 9 : mword 5)))]> mfp) with A2.
    assert (HA2a0 : A2 !!! Regidx (mword_of_int 10 : mword 5) = log_addr).
    { rewrite /A2 upd_eq. rewrite HAPrs1. apply add_vec_zero_l. }
    assert (HAp4 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x2c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HAp4) in "Hpc".
    (* +0x2c jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x2c)) (mword_of_int 1 : mword 5)
              (mword_of_int 2084790 : mword 21) A2 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_2c with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (A3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x2c) : mword 64) 4)]> A2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x2c) : mword 64) 4)]> A2) with A3.
    assert (HAjrl : add_vec (mword_of_int (KernelSyms.begin_op + 0x2c) : mword 64) (sign_extend' 64 (mword_of_int 2084790 : mword 21))
                   = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HAjrl) in "Hpc".
    assert (HA3ra : A3 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x2c) : mword 64) 4)
      by (rewrite /A3; apply upd_eq).
    assert (HA3a0 : A3 !!! Regidx (mword_of_int 10 : mword 5) = log_addr)
      by (rewrite /A3 upd_ne; [exact HA2a0 | reg_neq]).
    assert (HcsA3 : callee_saved mfp A3).
    { rewrite /A3 /A2.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HboA3 : bo_regs m A3 spd) by (apply (bo_regs_cs m mfp A3 spd HcsA3 HboAPr)).
    assert (HArel_lka : add_vec (A3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = log_addr)
      by (rewrite HA3a0; apply addv_sext0).
    (* -------------------- release(&log.lock) -------------------- *)
    iApply (Release.wp_release_sconf KT1 (ln_lk γ) log_addr "log"%string
              (log_res γ bn γfs cov logstart) A3 0%nat eb pj (K - 4)%nat
              ({["log"]} ∪ lks)
              HArel_lka ltac:(pose proof (bo_K10 K HK); lia)
              with "Hcg Htext Hpc Hislock Htok Hres Hown Hpay").
    iIntros (CIDAr HAsr mfr) "Hcg Hpc %HArcs Hown".
    (* between the interior release and the re-acquire this thread holds no
       lock: back to the bare, order-bounded [lks]. *)
    assert (Hsetback : ({["log"]} ∪ lks) ∖ {["log"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hown".
    assert (HAp5 : ret_pc (A3 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x30))
      by (rewrite HA3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HAp5) in "Hpc".
    assert (HboARl : bo_regs m mfr spd) by (apply (bo_regs_cs m A3 mfr spd HArcs HboA3)).
    (* +0x30 jal ra,sleep *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x30)) (mword_of_int 1 : mword 5)
              (mword_of_int 2089616 : mword 21) mfr (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_30 with "Htext"). }
    iIntros (CIDAj HAsj) "Hcg Hpc".
    set (A4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x30) : mword 64) 4)]> mfr).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x30) : mword 64) 4)]> mfr) with A4.
    assert (HAjsl : add_vec (mword_of_int (KernelSyms.begin_op + 0x30) : mword 64) (sign_extend' 64 (mword_of_int 2089616 : mword 21))
                   = mword_of_int KernelSyms.sleep)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HAjsl) in "Hpc".
    assert (HA4ra : A4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x30) : mword 64) 4)
      by (rewrite /A4; apply upd_eq).
    assert (HcsA4 : callee_saved mfr A4).
    { rewrite /A4. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HboA4 : bo_regs m A4 spd) by (apply (bo_regs_cs m mfr A4 spd HcsA4 HboARl)).
    (* ========================== sleep() ==========================
       No condition lock in the contract any more -- begin_op dropped
       log.lock itself two instructions ago. *)
    iDestruct (cpu_own_transport CIDAr CIDAj 0 eb pj eb ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID CIDAj eb pj ltac:(wp_next_chain) with "Htcx") as "Htcx".
    iDestruct (cpu_claim_ext_transport CID CIDAj eb pj ltac:(wp_next_chain) with "Hclmx") as "Hclmx".
    (* the interior release two instructions ago already dropped "log" -- the
       bare [lks] is what [Hown] carries here, and sleep's own acquire wants
       it bounded below "proc". *)
    assert (HbelowA4 : locks_below lks "proc").
    { lkbelow. }
    iApply (Sleep.wp_sleep_sconf γs j γl A4 (K - 4)%nat eb lks Hj Hjl
              ltac:(pose proof (bo_K22 K HK); lia)
              HbelowA4
              with "Hcg Hown Htext Hpc Hpinv Htcx Hclmx").
    all: try lkbelow.
    iIntros (CIDAs HAss mfs) "%HAscs Hcg Hown Hpc Htcx Hclmx".
    assert (HAp6 : ret_pc (A4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x34))
      by (rewrite HA4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HAp6) in "Hpc".
    assert (HboASl : bo_regs m mfs spd) by (apply (bo_regs_cs m A4 mfs spd HAscs HboA4)).
    assert (HASls1 : mfs !!! Regidx (mword_of_int 9 : mword 5) = log_addr)
      by (destruct HboASl as (X & _); exact X).
    (* +0x34 c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.begin_op + 0x34)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mfs (K - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_34 with "Htext"). }
    iIntros (CIDAm HAsm) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (A5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfs !!! Regidx (mword_of_int 9 : mword 5)))]> mfs).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfs !!! Regidx (mword_of_int 9 : mword 5)))]> mfs) with A5.
    assert (HA5a0 : A5 !!! Regidx (mword_of_int 10 : mword 5) = log_addr).
    { rewrite /A5 upd_eq. rewrite HASls1. apply add_vec_zero_l. }
    assert (HAp7 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x34) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x36))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HAp7) in "Hpc".
    (* +0x36 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x36)) (mword_of_int 1 : mword 5)
              (mword_of_int 2084644 : mword 21) A5 (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_36 with "Htext"). }
    iIntros (CIDAn HAsn) "Hcg Hpc".
    set (A6 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x36) : mword 64) 4)]> A5).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x36) : mword 64) 4)]> A5) with A6.
    assert (HAjaq : add_vec (mword_of_int (KernelSyms.begin_op + 0x36) : mword 64) (sign_extend' 64 (mword_of_int 2084644 : mword 21))
                   = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HAjaq) in "Hpc".
    assert (HA6ra : A6 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x36) : mword 64) 4)
      by (rewrite /A6; apply upd_eq).
    assert (HA6a0 : A6 !!! Regidx (mword_of_int 10 : mword 5) = log_addr)
      by (rewrite /A6 upd_ne; [exact HA5a0 | reg_neq]).
    assert (HcsA6 : callee_saved mfs A6).
    { rewrite /A6 /A5.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HboA6 : bo_regs m A6 spd) by (apply (bo_regs_cs m mfs A6 spd HcsA6 HboASl)).
    (* -------------------- acquire(&log.lock) -------------------- *)
    iDestruct (cpu_own_transport CIDAs CIDAn 0 eb pj eb ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Acquire.wp_acquire_sconf KT1 (ln_lk γ) "log"%string
              (log_res γ bn γfs cov logstart) A6 0%nat eb pj (K - 4)%nat eb lks
              bo_noff1 ltac:(pose proof (bo_K10 K HK); lia) Hbelow
              with "Hcg Hown Htext Hpc []").
    all: try lkbelow.
    { iEval (rewrite HA6a0). iExact "Hislock". }
    iIntros (CIDAa HAsa msA mfa) "%HAms Hcg Hpc %HAacs Htok Hres Hown Hpay".
    assert (HAp8 : ret_pc (A6 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x3a))
      by (rewrite HA6ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HAp8) in "Hpc".
    assert (HboAAq : bo_regs m mfa spd) by (apply (bo_regs_cs m A6 mfa spd HAacs HboA6)).
    (* the pair, rebuilt at the hart the loop is re-entered on *)
    iDestruct (trap_csrs_ext_transport CIDAs CIDAa eb pj ltac:(wp_next_chain) with "Htcx") as "Htcx".
    iDestruct (cpu_claim_ext_transport CIDAs CIDAa eb pj ltac:(wp_next_chain) with "Hclmx") as "Hclmx".
    iDestruct (arm_pay_ext_join eb pj with "Hpay [Htcx Hclmx]") as "[Htc Hclm]".
    { iSplitL "Htcx"; [iExact "Htcx" | iExact "Hclmx"]. }
    rewrite /bo_loop.
    iSpecialize ("IH" $! CIDAa with "[%]"); [wp_next_chain|].
    iApply ("IH" $! mfa with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Htc Hclm Hcg Hpc Hexit").
    exact HboAAq.
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
      (K : nat) (eb : bool) (spd sp0 : mword 64) (lks : gset string) (Vpr : pprivate) :
    let pj := proc_addr j in
    (K_begin_op <= K)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    bo_regs m M spd ->
    (* same OUTER convention as [bo_armA_body]'s note. *)
    locks_below lks "log" ->
    kernel_text -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    ▷ bo_loop CID0 j γ bn γfs cov logstart m pidv dq K eb spd sp0 lks Vpr -∗
    bo_exit CID0 j γ bn γfs cov logstart m pidv dq K eb spd sp0 lks Vpr -∗
    pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    proc_priv_bare pj pidv Vpr -∗
    cpu_own 1 eb pj false ({["log"]} ∪ lks) -∗
    trap_csrs KT1 -∗
    cpu_claim pj -∗
    sie_cap_gpr KT1 M (trap_res eb + (K - 4))%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.begin_op + 0x54)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj HK Hj Hjl Hanch Hbo Hbelow.
    pose proof (locks_below_not_elem _ _ Hbelow) as Hfresh.
    iIntros "#Htext #Hlog #Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Htc Hclm Hcg Hpc".
    iDestruct "Hlog" as "(#Hislock & #Hldev & #Hlstart)".
    assert (HboM : bo_regs m M spd) by exact Hbo.
    destruct Hbo as (Hs1 & Hs2 & Hsp & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
    (* THE SPLIT SLEEP PROTOCOL.  The loop invariant carries [trap_csrs] and
       [cpu_claim pj] index-free; the interior release wants the PAY half of
       that pair and the park wants the COMPLEMENT, so split once here and
       rejoin after the re-acquire.  Between +0x5c and +0x66 this thread
       holds no lock at all -- that window is new, and it is where the park
       lives. *)
    iDestruct (arm_pay_ext_split eb pj with "Htc Hclm") as "[Hpay [Htcx Hclmx]]".
    (* +0x54 c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.begin_op + 0x54)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              M (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_54 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B0 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 9 : mword 5)))]> M).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (M !!! Regidx (mword_of_int 9 : mword 5)))]> M) with B0.
    assert (HBp2 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x54) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x56))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HBp2) in "Hpc".
    assert (HB0a0 : B0 !!! Regidx (mword_of_int 10 : mword 5) = log_addr).
    { rewrite /B0 upd_eq. rewrite Hs1. apply add_vec_zero_l. }
    (* +0x56 jal ra,sleep_prepare *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x56)) (mword_of_int 1 : mword 5)
              (mword_of_int 2089518 : mword 21) B0 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_56 with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (B1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x56) : mword 64) 4)]> B0).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x56) : mword 64) 4)]> B0) with B1.
    assert (HBjsp : add_vec (mword_of_int (KernelSyms.begin_op + 0x56) : mword 64) (sign_extend' 64 (mword_of_int 2089518 : mword 21))
                   = mword_of_int KernelSyms.sleep_prepare)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HBjsp) in "Hpc".
    assert (HB1ra : B1 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x56) : mword 64) 4)
      by (rewrite /B1; apply upd_eq).
    assert (HB1a0 : B1 !!! Regidx (mword_of_int 10 : mword 5) = log_addr)
      by (rewrite /B1 upd_ne; [exact HB0a0 | reg_neq]).
    assert (HcsB1 : callee_saved M B1).
    { rewrite /B1 /B0.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HboB1 : bo_regs m B1 spd) by (apply (bo_regs_cs m M B1 spd HcsB1 HboM)).
    assert (HB1nz : eq_vec (B1 !!! Regidx (mword_of_int 10 : mword 5)) (zero_reg : mword 64) = false)
      by (rewrite HB1a0; exact bo_log_nz).
    (* -------------------- sleep_prepare(&log) -------------------- *)
    (* still HOLDING "log" here -- same OUTER-set lift as [bo_armA_body]'s
       note. *)
    assert (HbelowB1 : locks_below ({["log"]} ∪ lks) "proc").
    { apply locks_below_union_singleton; [vm_compute; lia |].
      lkbelow. }
    iApply (SleepPrepare.wp_sleep_prepare_sconf γs j γl B1
              (trap_res eb + (K - 4))%nat 1%nat eb false
              ({["log"]} ∪ lks) Hj Hjl HB1nz bo_noff2 ltac:(pose proof (bo_K22 K HK); lia)
              HbelowB1
              with "Hcg Hown Htext Hpc Hpinv").
    all: try lkbelow.
    iApply wp_next_off_intro. iIntros (mfp) "%HBpcs Hcg Hown Hpc".
    assert (HBp3 : ret_pc (B1 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x5a))
      by (rewrite HB1ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HBp3) in "Hpc".
    assert (HboBPr : bo_regs m mfp spd) by (apply (bo_regs_cs m B1 mfp spd HBpcs HboB1)).
    assert (HBPrs1 : mfp !!! Regidx (mword_of_int 9 : mword 5) = log_addr)
      by (destruct HboBPr as (X & _); exact X).
    (* +0x5a c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.begin_op + 0x5a)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mfp (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_5a with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B2 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfp !!! Regidx (mword_of_int 9 : mword 5)))]> mfp).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfp !!! Regidx (mword_of_int 9 : mword 5)))]> mfp) with B2.
    assert (HB2a0 : B2 !!! Regidx (mword_of_int 10 : mword 5) = log_addr).
    { rewrite /B2 upd_eq. rewrite HBPrs1. apply add_vec_zero_l. }
    assert (HBp4 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x5a) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x5c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HBp4) in "Hpc".
    (* +0x5c jal ra,release *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x5c)) (mword_of_int 1 : mword 5)
              (mword_of_int 2084742 : mword 21) B2 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_5c with "Htext"). }
    iApply wp_next_off_intro. iIntros "Hcg Hpc".
    set (B3 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x5c) : mword 64) 4)]> B2).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x5c) : mword 64) 4)]> B2) with B3.
    assert (HBjrl : add_vec (mword_of_int (KernelSyms.begin_op + 0x5c) : mword 64) (sign_extend' 64 (mword_of_int 2084742 : mword 21))
                   = mword_of_int KernelSyms.release)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HBjrl) in "Hpc".
    assert (HB3ra : B3 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x5c) : mword 64) 4)
      by (rewrite /B3; apply upd_eq).
    assert (HB3a0 : B3 !!! Regidx (mword_of_int 10 : mword 5) = log_addr)
      by (rewrite /B3 upd_ne; [exact HB2a0 | reg_neq]).
    assert (HcsB3 : callee_saved mfp B3).
    { rewrite /B3 /B2.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HboB3 : bo_regs m B3 spd) by (apply (bo_regs_cs m mfp B3 spd HcsB3 HboBPr)).
    assert (HBrel_lka : add_vec (B3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 0 : mword 12)) = log_addr)
      by (rewrite HB3a0; apply addv_sext0).
    (* -------------------- release(&log.lock) -------------------- *)
    iApply (Release.wp_release_sconf KT1 (ln_lk γ) log_addr "log"%string
              (log_res γ bn γfs cov logstart) B3 0%nat eb pj (K - 4)%nat
              ({["log"]} ∪ lks)
              HBrel_lka ltac:(pose proof (bo_K10 K HK); lia)
              with "Hcg Htext Hpc Hislock Htok Hres Hown Hpay").
    iIntros (CIDBr HBsr mfr) "Hcg Hpc %HBrcs Hown".
    assert (Hsetback : ({["log"]} ∪ lks) ∖ {["log"]} = lks)
      by (apply locks_add_del_below; lkbelow).
    iEval (rewrite Hsetback) in "Hown".
    assert (HBp5 : ret_pc (B3 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x60))
      by (rewrite HB3ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HBp5) in "Hpc".
    assert (HboBRl : bo_regs m mfr spd) by (apply (bo_regs_cs m B3 mfr spd HBrcs HboB3)).
    (* +0x60 jal ra,sleep *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x60)) (mword_of_int 1 : mword 5)
              (mword_of_int 2089568 : mword 21) mfr (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_60 with "Htext"). }
    iIntros (CIDBj HBsj) "Hcg Hpc".
    set (B4 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x60) : mword 64) 4)]> mfr).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x60) : mword 64) 4)]> mfr) with B4.
    assert (HBjsl : add_vec (mword_of_int (KernelSyms.begin_op + 0x60) : mword 64) (sign_extend' 64 (mword_of_int 2089568 : mword 21))
                   = mword_of_int KernelSyms.sleep)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HBjsl) in "Hpc".
    assert (HB4ra : B4 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x60) : mword 64) 4)
      by (rewrite /B4; apply upd_eq).
    assert (HcsB4 : callee_saved mfr B4).
    { rewrite /B4. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
    assert (HboB4 : bo_regs m B4 spd) by (apply (bo_regs_cs m mfr B4 spd HcsB4 HboBRl)).
    (* ========================== sleep() ==========================
       No condition lock in the contract any more -- begin_op dropped
       log.lock itself two instructions ago. *)
    iDestruct (cpu_own_transport CIDBr CIDBj 0 eb pj eb ltac:(wp_next_chain) with "Hown") as "Hown".
    iDestruct (trap_csrs_ext_transport CID CIDBj eb pj ltac:(wp_next_chain) with "Htcx") as "Htcx".
    iDestruct (cpu_claim_ext_transport CID CIDBj eb pj ltac:(wp_next_chain) with "Hclmx") as "Hclmx".
    (* the bare [lks], as in [bo_armA_body]'s note. *)
    assert (HbelowB4 : locks_below lks "proc").
    { lkbelow. }
    iApply (Sleep.wp_sleep_sconf γs j γl B4 (K - 4)%nat eb lks Hj Hjl
              ltac:(pose proof (bo_K22 K HK); lia)
              HbelowB4
              with "Hcg Hown Htext Hpc Hpinv Htcx Hclmx").
    all: try lkbelow.
    iIntros (CIDBs HBss mfs) "%HBscs Hcg Hown Hpc Htcx Hclmx".
    assert (HBp6 : ret_pc (B4 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x64))
      by (rewrite HB4ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HBp6) in "Hpc".
    assert (HboBSl : bo_regs m mfs spd) by (apply (bo_regs_cs m B4 mfs spd HBscs HboB4)).
    assert (HBSls1 : mfs !!! Regidx (mword_of_int 9 : mword 5) = log_addr)
      by (destruct HboBSl as (X & _); exact X).
    (* +0x64 c.mv a0,s1 *)
    iApply (wp_cmv_s_sconf (mword_of_int (KernelSyms.begin_op + 0x64)) (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
              mfs (K - 4)%nat eb ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_64 with "Htext"). }
    iIntros (CIDBm HBsm) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (B5 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfs !!! Regidx (mword_of_int 9 : mword 5)))]> mfs).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg (add_vec zero_reg (mfs !!! Regidx (mword_of_int 9 : mword 5)))]> mfs) with B5.
    assert (HB5a0 : B5 !!! Regidx (mword_of_int 10 : mword 5) = log_addr).
    { rewrite /B5 upd_eq. rewrite HBSls1. apply add_vec_zero_l. }
    assert (HBp7 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x64) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x66))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HBp7) in "Hpc".
    (* +0x66 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x66)) (mword_of_int 1 : mword 5)
              (mword_of_int 2084596 : mword 21) B5 (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_66 with "Htext"). }
    iIntros (CIDBn HBsn) "Hcg Hpc".
    set (B6 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x66) : mword 64) 4)]> B5).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x66) : mword 64) 4)]> B5) with B6.
    assert (HBjaq : add_vec (mword_of_int (KernelSyms.begin_op + 0x66) : mword 64) (sign_extend' 64 (mword_of_int 2084596 : mword 21))
                   = mword_of_int KernelSyms.acquire)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HBjaq) in "Hpc".
    assert (HB6ra : B6 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.begin_op + 0x66) : mword 64) 4)
      by (rewrite /B6; apply upd_eq).
    assert (HB6a0 : B6 !!! Regidx (mword_of_int 10 : mword 5) = log_addr)
      by (rewrite /B6 upd_ne; [exact HB5a0 | reg_neq]).
    assert (HcsB6 : callee_saved mfs B6).
    { rewrite /B6 /B5.
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_insert_r; [vm_compute; reflexivity|].
      apply callee_saved_refl. }
    assert (HboB6 : bo_regs m B6 spd) by (apply (bo_regs_cs m mfs B6 spd HcsB6 HboBSl)).
    (* -------------------- acquire(&log.lock) -------------------- *)
    iDestruct (cpu_own_transport CIDBs CIDBn 0 eb pj eb ltac:(wp_next_chain) with "Hown") as "Hown".
    iApply (Acquire.wp_acquire_sconf KT1 (ln_lk γ) "log"%string
              (log_res γ bn γfs cov logstart) B6 0%nat eb pj (K - 4)%nat eb lks
              bo_noff1 ltac:(pose proof (bo_K10 K HK); lia) Hbelow
              with "Hcg Hown Htext Hpc []").
    all: try lkbelow.
    { iEval (rewrite HB6a0). iExact "Hislock". }
    iIntros (CIDBa HBsa msA mfa) "%HBms Hcg Hpc %HBacs Htok Hres Hown Hpay".
    assert (HBp8 : ret_pc (B6 !!! Regidx (mword_of_int 1 : mword 5)) = mword_of_int (KernelSyms.begin_op + 0x6a))
      by (rewrite HB6ra; apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite HBp8) in "Hpc".
    assert (HboBAq : bo_regs m mfa spd) by (apply (bo_regs_cs m B6 mfa spd HBacs HboB6)).
    (* the pair, rebuilt at the hart the loop is re-entered on *)
    iDestruct (trap_csrs_ext_transport CIDBs CIDBa eb pj ltac:(wp_next_chain) with "Htcx") as "Htcx".
    iDestruct (cpu_claim_ext_transport CIDBs CIDBa eb pj ltac:(wp_next_chain) with "Hclmx") as "Hclmx".
    iDestruct (arm_pay_ext_join eb pj with "Hpay [Htcx Hclmx]") as "[Htc Hclm]".
    { iSplitL "Htcx"; [iExact "Htcx" | iExact "Hclmx"]. }
    (* +0x6a c.j -> +0x3a : the back edge *)
    iApply (wp_cj_s_sconf (mword_of_int (KernelSyms.begin_op + 0x6a))
              (sign_extend' 21 (concat_vec (mword_of_int 2024 : mword 11) ('b"0"))) mfa (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_6a with "Htext"). }
    iApply wp_next_off_intro.
    iNext.
    iIntros "Hcg Hpc".
    assert (Hbk : add_vec (mword_of_int (KernelSyms.begin_op + 0x6a) : mword 64)
                    (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2024 : mword 11) ('b"0"))))
                  = mword_of_int (KernelSyms.begin_op + 0x3a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hbk) in "Hpc".
    rewrite /bo_loop.
    iSpecialize ("IH" $! CIDBa with "[%]"); [wp_next_chain|].
    iApply ("IH" $! mfa with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Htc Hclm Hcg Hpc Hexit").
    exact HboBAq.
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
      (K : nat) (eb : bool) (spd sp0 : mword 64) (lks : gset string) (Vpr : pprivate) :
    let pj := proc_addr j in
    (K_begin_op <= K)%nat ->
    (j < NPROC)%nat ->
    γs !! j = Some γl ->
    (true = false \/ pj = zero_reg -> (CID : CPU) = CID0) ->
    bo_regs m M spd ->
    (* same OUTER convention as [bo_armA_body]'s note -- carried through to
       the arm calls below, which each need their own copy of it. *)
    locks_below lks "log" ->
    kernel_text -∗
    log_ctx γ bn γfs cov logstart dev -∗
    procs_inv γs -∗
    ▷ bo_loop CID0 j γ bn γfs cov logstart m pidv dq K eb spd sp0 lks Vpr -∗
    bo_exit CID0 j γ bn γfs cov logstart m pidv dq K eb spd sp0 lks Vpr -∗
    pa_stk sp0 1 ↦₈[KT1] (m !!! Regidx (mword_of_int 1 : mword 5)) -∗
    pa_stk sp0 2 ↦₈[KT1] (m !!! Regidx (mword_of_int 8 : mword 5)) -∗
    pa_stk sp0 3 ↦₈[KT1] (m !!! Regidx (mword_of_int 9 : mword 5)) -∗
    pa_stk sp0 4 ↦₈[KT1] (m !!! Regidx (mword_of_int 18 : mword 5)) -∗
    locked (ln_lk γ) cpu_id -∗
    log_res γ bn γfs cov logstart -∗
    proc_priv_bare pj pidv Vpr -∗
    cpu_own 1 eb pj false ({["log"]} ∪ lks) -∗
    trap_csrs KT1 -∗
    cpu_claim pj -∗
    sie_cap_gpr KT1 M (trap_res eb + (K - 4))%nat false pj -∗
    pc_is (mword_of_int (KernelSyms.begin_op + 0x3a)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros pj HK Hj Hjl Hanch Hbo Hbelow.
    iIntros "#Htext #Hlog #Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Htc Hclm Hcg Hpc".
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
    (* open the lock's resource for the committing test *)
    rewrite /log_res.
    iDestruct "Hres" as (out cmt nc om Ep Xr)
      "(Hout & Hcmt & Hnc & Hauth & %Hsz & %Hbnd & %Hout3 & %Hcmtout & Hepa & %Hepos & Hxa & %Hlive & %Hcap & Hrest)".
    assert (Hacmt : add_vec (rget M (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 32 : mword 12)) = l_cmt).
    { rgne. rewrite Hs1. exact bo_addr_cmt. }
    (* +0x2c c.lw a5,32(s1) : a5 := log.committing *)
    iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.begin_op + 0x3a)) (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
              (mword_of_int 32 : mword 12) M (trap_res eb + (K - 4))%nat
              (mword_of_int (if cmt then 1 else 0) : mword 32) false (dqm := DfracOwn 1)
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc [] [Hcmt]").
    { iApply (boi_3a with "Htext"). }
    { iEval (rewrite Hacmt). iExact "Hcmt". }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc Hcmt".
    iEval (rewrite Hacmt) in "Hcmt".
    set (E1 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (mword_of_int (if cmt then 1 else 0) : mword 32))]> M).
    change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (mword_of_int (if cmt then 1 else 0) : mword 32))]> M) with E1.
    assert (Hp2e : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x3a) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x3c))
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
    destruct cmt.
    - (* ================= COMMITTING: c.bnez TAKEN -> +0x24 ================= *)
      iAssert (∃ (out : nat) (cmt : bool) (nc : SailStdpp.Values.mword 32) (om : gmap nat op_entry)
                 (E : nat) (X : gset (nat * Z)),
                 l_out ↦₄ (mword_of_int (Z.of_nat out) : mword 32) ∗
                 l_cmt ↦₄ (mword_of_int (if cmt then 1 else 0) : mword 32) ∗
                 l_ncommit ↦₄ nc ∗
                 ghost_map_auth (ln_ops γ) 1 om ∗
                 ⌜size om = out⌝ ∗
                 ⌜forall i e, om !! i = Some e -> (e.1.1.1 <= MAXOPBLOCKS)%nat⌝ ∗
                 ⌜(out <= 3)%nat⌝ ∗
                 ⌜cmt = true -> out = 0%nat⌝ ∗
                 mono_nat_auth_own (ln_ep γ) 1 E ∗
                 ⌜(1 <= E)%nat⌝ ∗
                 own (ln_lg γ) (● X) ∗
                 ⌜forall i e, om !! i = Some e -> e.1.2 = E⌝ ∗
                 ⌜forall e' b', ((e', b') : nat * Z) ∈ X -> (e' <= E)%nat⌝ ∗
                 (if cmt then emp
                  else ∃ (n : nat) (LB : gset Z),
                       ⌜(n + op_sum om <= LOGBLOCKS)%nat⌝ ∗
                       ⌜forall i e, om !! i = Some e -> e.1.1.2 ⊆ LB⌝ ∗
                       ⌜forall b : Z, (E, b) ∈ X -> b ∈ LB⌝ ∗
                       log_state bn γfs cov logstart n LB (op_pending om)))%I
        with "[Hout Hcmt Hnc Hauth Hepa Hxa Hrest]" as "Hres".
      { iExists out, true, nc, om, Ep, Xr. iFrame "Hout Hcmt Hnc Hauth".
        iSplitR; [iPureIntro; exact Hsz|].
        iSplitR; [iPureIntro; exact Hbnd|].
        iSplitR; [iPureIntro; exact Hout3|].
        iSplitR; [iPureIntro; exact Hcmtout|].
        iFrame "Hepa".
        iSplitR; [iPureIntro; exact Hepos|].
        iFrame "Hxa".
        iSplitR; [iPureIntro; exact Hlive|].
        iSplitR; [iPureIntro; exact Hcap|].
        iExact "Hrest". }
      iApply (wp_cbnez_taken_s_sconf (mword_of_int (KernelSyms.begin_op + 0x3c)) (mword_of_int 244 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) E1 (trap_res eb + (K - 4))%nat false
                Hc7 ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HE1a5; vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (boi_3c with "Htext"). }
      iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Htgt24 : add_vec (mword_of_int (KernelSyms.begin_op + 0x3c) : mword 64)
                         (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 244 : mword 8) ('b"0"))))
                       = mword_of_int (KernelSyms.begin_op + 0x24))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt24) in "Hpc".
      iApply (bo_armA_body (CID := CID) CID0 γs j γl γ bn γfs cov logstart dev m E1 pidv dq K eb spd sp0 lks
                Vpr HK Hj Hjl Hanch HboE1 Hbelow
                with "Htext Hlog Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Htc Hclm Hcg Hpc").
    - (* ================= NOT COMMITTING: fall through to +0x30 ============ *)
      iDestruct "Hrest" as (n LB) "(%Hsum & %Hsub & %Hreg & Hbatch)".
      iDestruct (bo_batch_lhn with "Hbatch") as "(%Hn30 & Hlhn & Hbclose)".
      iApply (wp_cbnez_fall_s_sconf (mword_of_int (KernelSyms.begin_op + 0x3c)) (mword_of_int 244 : mword 8)
                (Cregidx (mword_of_int 7)) (mword_of_int 15 : mword 5) E1 (trap_res eb + (K - 4))%nat false
                Hc7 ltac:(vm_compute; discriminate)
                ltac:(rgne; rewrite HE1a5; vm_compute; reflexivity)
                with "Hcg Hpc []").
      { iApply (boi_3c with "Htext"). }
      iApply wp_next_off_intro. iIntros "Hcg Hpc".
      assert (Hp30 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x3c) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x3e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp30) in "Hpc".
      (* +0x30 c.lw a4,28(s1) : a4 := log.outstanding *)
      assert (Haout : add_vec (rget E1 (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 28 : mword 12)) = l_out).
      { rgne. rewrite HE1s1. exact bo_addr_out. }
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.begin_op + 0x3e)) (mword_of_int 14 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 28 : mword 12) E1 (trap_res eb + (K - 4))%nat
                (mword_of_int (Z.of_nat out) : mword 32) false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hout]").
      { iApply (boi_3e with "Htext"). }
      { iEval (rewrite Haout). iExact "Hout". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hout".
      iEval (rewrite Haout) in "Hout".
      set (E2 := <[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
          (sign_extend' 64 (mword_of_int (Z.of_nat out) : mword 32))]> E1).
      change (<[Regidx (mword_of_int 14 : mword 5) := regval_into_reg
          (sign_extend' 64 (mword_of_int (Z.of_nat out) : mword 32))]> E1) with E2.
      assert (Hp32 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x3e) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp32) in "Hpc".
      assert (HE2a4 : E2 !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int (Z.of_nat out) : mword 64)).
      { rewrite /E2 upd_eq. apply bo_sext32. exact (bo_zout_lt out Hout3). }
      (* +0x32 c.addiw a4,a4,1 *)
      iApply (wp_caddiw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x40)) (mword_of_int 14 : mword 5) (mword_of_int 1 : mword 6)
                E2 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iApply (boi_40 with "Htext"). }
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
      assert (Hp34 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x42))
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
      iApply (wp_slliw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x42)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
                (mword_of_int 2 : mword 5) (mword_of_int (4 * (Z.of_nat out + 1)) : mword 64)
                E3 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok) Hsl2
                with "Hcg Hpc []").
      { iApply (boi_42 with "Htext"). }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (mword_of_int (4 * (Z.of_nat out + 1)) : mword 64)]> E3).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (mword_of_int (4 * (Z.of_nat out + 1)) : mword 64)]> E3) with E4.
      assert (Hp38 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x42) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x46))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp38) in "Hpc".
      assert (HE4a5 : E4 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int (4 * (Z.of_nat out + 1)) : mword 64))
        by (rewrite /E4; apply upd_eq).
      assert (HE4a4 : E4 !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int (Z.of_nat out + 1) : mword 64))
        by (rewrite /E4 upd_ne; [exact HE3a4 | reg_neq]).
      (* +0x38 c.addw a5,a5,a4 *)
      iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x46)) (mword_of_int 15 : mword 5) (mword_of_int 14 : mword 5)
                E4 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iEval (rewrite -Hc6 -Hc7). iApply (boi_46 with "Htext"). }
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
      assert (Hp3a : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x46) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x48))
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
      iApply (wp_slliw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x48)) (mword_of_int 15 : mword 5) (mword_of_int 15 : mword 5)
                (mword_of_int 1 : mword 5) (mword_of_int (10 * (Z.of_nat out + 1)) : mword 64)
                E5 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok) Hsl1
                with "Hcg Hpc []").
      { iApply (boi_48 with "Htext"). }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc".
      set (E6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (mword_of_int (10 * (Z.of_nat out + 1)) : mword 64)]> E5).
      change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
          (mword_of_int (10 * (Z.of_nat out + 1)) : mword 64)]> E5) with E6.
      assert (Hp3e : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x48) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x4c))
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
      iApply (wp_clw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.begin_op + 0x4c)) (mword_of_int 13 : mword 5) (mword_of_int 9 : mword 5)
                (mword_of_int 44 : mword 12) E6 (trap_res eb + (K - 4))%nat
                (mword_of_int (Z.of_nat n) : mword 32) false (dqm := DfracOwn 1)
                ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc [] [Hlhn]").
      { iApply (boi_4c with "Htext"). }
      { iEval (rewrite Halhn). iExact "Hlhn". }
      iApply wp_next_off_intro.
      iIntros "Hcg Hpc Hlhn".
      iEval (rewrite Halhn) in "Hlhn".
      set (E7 := <[Regidx (mword_of_int 13 : mword 5) := regval_into_reg
          (sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32))]> E6).
      change (<[Regidx (mword_of_int 13 : mword 5) := regval_into_reg
          (sign_extend' 64 (mword_of_int (Z.of_nat n) : mword 32))]> E6) with E7.
      assert (Hp40 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x4c) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x4e))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hp40) in "Hpc".
      assert (HE7a3 : E7 !!! Regidx (mword_of_int 13 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64)).
      { rewrite /E7 upd_eq. apply bo_sext32. exact (bo_zn_lt n Hn30). }
      assert (HE7a5 : E7 !!! Regidx (mword_of_int 15 : mword 5) = (mword_of_int (10 * (Z.of_nat out + 1)) : mword 64))
        by (rewrite /E7 upd_ne; [exact HE6a5 | reg_neq]).
      (* +0x40 c.addw a5,a5,a3 *)
      iApply (wp_addw_s_sconf (mword_of_int (KernelSyms.begin_op + 0x4e)) (mword_of_int 15 : mword 5) (mword_of_int 13 : mword 5)
                E7 (trap_res eb + (K - 4))%nat false ltac:(vm_compute; discriminate) ltac:(rdok)
                with "Hcg Hpc []").
      { iEval (rewrite -Hc5 -Hc7). iApply (boi_4e with "Htext"). }
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
      assert (Hp42 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x4e) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x50))
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
        iApply (wp_bge_taken_s_sconf (mword_of_int (KernelSyms.begin_op + 0x50)) (mword_of_int 28 : mword 13)
                  (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5) E8 (trap_res eb + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp ltac:(vm_compute; reflexivity)
                  with "Hcg Hpc []").
        { iApply (boi_50 with "Htext"). }
        iNext. iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Htgt50 : add_vec (mword_of_int (KernelSyms.begin_op + 0x50) : mword 64)
                           (sign_extend' 64 (mword_of_int 28 : mword 13)) = mword_of_int (KernelSyms.begin_op + 0x6c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt50) in "Hpc".
        (* +0x50 auipc a5,0x1e *)
        iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.begin_op + 0x6c)) (mword_of_int 15 : mword 5)
                  (mword_of_int 30 : mword 20) E8 (trap_res eb + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(rdok)
                  with "Hcg Hpc []").
        { iApply (boi_6c with "Htext"). }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc".
        set (E9 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
            (add_vec (mword_of_int (KernelSyms.begin_op + 0x6c) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> E8).
        change (<[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
            (add_vec (mword_of_int (KernelSyms.begin_op + 0x6c) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> E8) with E9.
        assert (Hp54 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x6c) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x70))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp54) in "Hpc".
        assert (HE9a5 : E9 !!! Regidx (mword_of_int 15 : mword 5)
                        = add_vec (mword_of_int (KernelSyms.begin_op + 0x6c) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))
          by (rewrite /E9; apply upd_eq).
        assert (HE9a4 : E9 !!! Regidx (mword_of_int 14 : mword 5) = (mword_of_int (Z.of_nat out + 1) : mword 64))
          by (rewrite /E9 upd_ne; [exact HE8a4 | reg_neq]).
        assert (HcsE9 : callee_saved E8 E9).
        { rewrite /E9. apply callee_saved_insert_r; [vm_compute; reflexivity|]. apply callee_saved_refl. }
        assert (HboE9 : bo_regs m E9 spd) by (apply (bo_regs_cs m E8 E9 spd HcsE9 HboE8)).
        (* +0x54 sw a4,1802(a5) : log.outstanding := out+1 *)
        assert (Hsta : add_vec (rget E9 (mword_of_int 15 : mword 5))
                         (sign_extend' 64 (mword_of_int 1752 : mword 12)) = l_out).
        { rgne. rewrite HE9a5. exact bo_reloc_out_50. }
        iApply (wp_sw_s_sconf (kt := KT1) (ktd := KT0) (mword_of_int (KernelSyms.begin_op + 0x70)) (mword_of_int 14 : mword 5) (mword_of_int 15 : mword 5)
                  (mword_of_int 1752 : mword 12) E9 (trap_res eb + (K - 4))%nat
                  (mword_of_int (Z.of_nat out) : mword 32) false
                  with "Hcg Hpc [] [Hout]").
        { iApply (boi_70 with "Htext"). }
        { iEval (rewrite Hsta). iExact "Hout". }
        iApply wp_next_off_intro.
        iIntros "Hcg Hpc Hout".
        iEval (rewrite Hsta) in "Hout".
        assert (Hstv : trunc32 (rget E9 (mword_of_int 14 : mword 5))
                       = (mword_of_int (Z.of_nat out + 1) : mword 32)).
        { rgne. rewrite HE9a4. apply trunc32_mword_of_int. }
        iEval (rewrite Hstv) in "Hout".
        iEval (rewrite -(bo_zsucc out)) in "Hout".
        assert (Hp58 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x70) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x74))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp58) in "Hpc".
        (* THE LEDGER STEP: mint a fresh operation at full budget *)
        (* THE OP IS BORN IN THE CURRENT EPOCH [Ep] -- that is the whole of
           the birth-epoch bookkeeping on this side (fs-log.md §G.2): the
           entry records the epoch it was minted in, and [log_res]'s
           soundness clause below is re-established for the new row by
           [reflexivity].

           ...AND THE EPOCH LOWER BOUND IS MINTED HERE TOO (fs-log.md
           §G.13): this is the ONLY moment in an operation's life at which
           the [ln_ep] auth and the client are in the same place, so
           [log_begin_step] takes the auth and hands it straight back with
           a persistent [log_epoch_lb γ Ep] bundled into the entry.  It
           costs the step one extra resource in and one out and nothing
           else -- which is why every other log ghost step below merely
           re-packs it. *)
        iMod (log_begin_step γ om Ep Hepos with "Hauth Hepa")
          as (i Hi) "(Hauth & Hepa & HopS)".
        iDestruct (log_opSe_opS with "HopS") as "HopS".
        iDestruct (log_opS_op with "HopS") as "Hop".
        iAssert (log_res γ bn γfs cov logstart)
          with "[Hout Hcmt Hnc Hauth Hepa Hxa Hlhn Hbclose]" as "Hres".
        { rewrite /log_res.
          iExists (S out), false, nc, (<[i := (MAXOPBLOCKS, ∅, Ep, (∅ : gset fsobj))]> om), Ep, Xr.
          iFrame "Hout Hcmt Hnc Hauth".
          iSplitR.
          { iPureIntro. rewrite map_size_insert_None; [ by rewrite Hsz | exact Hi ]. }
          iSplitR.
          { iPureIntro. intros k e Hk.
            destruct (decide (k = i)) as [->|Hne].
            - rewrite lookup_insert in Hk.
              assert (e = (MAXOPBLOCKS, ∅, Ep, (∅ : gset fsobj))) as -> by congruence.
              apply Nat.le_refl.
            - rewrite lookup_insert_ne in Hk; [| exact (not_eq_sym Hne)]. exact (Hbnd k e Hk). }
          iSplitR; [iPureIntro; exact (bo_guard_out3 out n Hle)|].
          iSplitR; [iPureIntro; discriminate|].
          iFrame "Hepa".
          iSplitR; [iPureIntro; exact Hepos|].
          iFrame "Hxa".
          (* the new entry's birth epoch IS the current one, by construction *)
          iSplitR.
          { iPureIntro. intros k e Hk.
            destruct (decide (k = i)) as [->|Hne].
            - rewrite lookup_insert in Hk.
              assert (e = (MAXOPBLOCKS, ∅, Ep, (∅ : gset fsobj))) as -> by congruence.
              reflexivity.
            - rewrite lookup_insert_ne in Hk; [| exact (not_eq_sym Hne)]. exact (Hlive k e Hk). }
          (* the registry and the epoch are untouched by a begin_op *)
          iSplitR; [iPureIntro; exact Hcap|].
          iExists n, LB. iSplitR.
          { iPureIntro. rewrite (op_sum_insert om i (MAXOPBLOCKS, ∅, Ep, (∅ : gset fsobj)) Hi).
            exact (log_reserve_ok n out om Hsz Hbnd (bo_guard_sum out n Hle)). }
          iSplitR.
          (* THE FRESH OP HAS LOGGED NOTHING, so its credit set is empty and
             the soundness clause is immediate; the other entries are
             untouched. *)
          { iPureIntro. intros k e Hk.
            destruct (decide (k = i)) as [->|Hne].
            - rewrite lookup_insert in Hk.
              assert (e = (MAXOPBLOCKS, ∅, Ep, (∅ : gset fsobj))) as -> by congruence.
              apply empty_subseteq.
            - rewrite lookup_insert_ne in Hk; [| exact (not_eq_sym Hne)]. exact (Hsub k e Hk). }
          iSplitR; [iPureIntro; exact Hreg|].
          (* THE PENDING SET GROWS (durable-disk stage G1): the fresh op
             contributes its own (empty) already-logged set, so [pend] only
             gets bigger and every row of [log_state] that excludes it only
             weakens.  Free at this site, forever. *)
          assert (Hpm : op_pending om
                        ⊆ op_pending (<[i := (MAXOPBLOCKS, ∅, Ep, (∅ : gset fsobj))]> om)).
          { apply op_pending_insert_mono. intros e He.
            rewrite Hi in He. discriminate. }
          iApply (log_state_pend_mono _ _ _ _ _ _ _ _ Hpm).
          iApply ("Hbclose" with "Hlhn"). }
        rewrite /bo_exit.
        iSpecialize ("Hexit" $! CID with "[%]"); [wp_next_chain|].
        iApply ("Hexit" $! E9 with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hres Hop Hpid Hown Htc Hclm Hcg Hpc").
        exact HboE9.
      + (* ---- NO SPACE: the branch FALLS THROUGH, control at +0x46 ---- *)
        iAssert (log_res γ bn γfs cov logstart)
          with "[Hout Hcmt Hnc Hauth Hepa Hxa Hlhn Hbclose]" as "Hres".
        { rewrite /log_res. iExists out, false, nc, om, Ep, Xr.
          iFrame "Hout Hcmt Hnc Hauth".
          iSplitR; [iPureIntro; exact Hsz|].
          iSplitR; [iPureIntro; exact Hbnd|].
          iSplitR; [iPureIntro; exact Hout3|].
          iSplitR; [iPureIntro; exact Hcmtout|].
          iFrame "Hepa".
          iSplitR; [iPureIntro; exact Hepos|].
          iFrame "Hxa".
          iSplitR; [iPureIntro; exact Hlive|].
          iSplitR; [iPureIntro; exact Hcap|].
          iExists n, LB. iSplitR; [iPureIntro; exact Hsum|].
          iSplitR; [iPureIntro; exact Hsub|].
          iSplitR; [iPureIntro; exact Hreg|].
          iApply ("Hbclose" with "Hlhn"). }
        iApply (wp_bge_fall_s_sconf (mword_of_int (KernelSyms.begin_op + 0x50)) (mword_of_int 28 : mword 13)
                  (mword_of_int 15 : mword 5) (mword_of_int 18 : mword 5) E8 (trap_res eb + (K - 4))%nat false
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) Hcmp
                  with "Hcg Hpc []").
        { iApply (boi_50 with "Htext"). }
        iApply wp_next_off_intro. iIntros "Hcg Hpc".
        assert (Hp46 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x50) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x54))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hp46) in "Hpc".
        iApply (bo_armB_body (CID := CID) CID0 γs j γl γ bn γfs cov logstart dev m E8 pidv dq K eb spd sp0 lks
                  Vpr HK Hj Hjl Hanch HboE8 Hbelow
                  with "Htext Hlog Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Htc Hclm Hcg Hpc").
  Qed.

End BoBodies.

(* ===================================================================== *)

Section ProofBeginOp.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wp_begin_op_sconf 
      (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names)
      (γ : log_names) (γfs : fs_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32)
      (pidv : mword 32) (dq : dfrac)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) (Vpr : pprivate)
    : wp_begin_op_sconf_body γs j γl bn γ γfs cov logstart dev pidv dq m K eb b lks Vpr.
  Proof.
    cbv beta delta [wp_begin_op_sconf_body].
    intros pcE pj ret_tgt HK Hj Hjl Hbelow.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    set (spd := add_vec sp0 (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)))).
    iIntros "Hcg Hown Hextc Hextm #Htext Hpc #Hlog Hpid #Hpinv Hcont".
    iPoseProof "Hlog" as "#Hlogc".
    iDestruct "Hlogc" as "(#Hislock & #Hldev & #Hlstart)".
    (* LEVEL 0 TIES THE TWO INDICES: [cpu_own_eb_agree] gives [eb = b]
       outright, so the function runs at ONE index throughout and there is
       nothing left to pin.  This used to derive [b = true] from the
       [eb = true] premise; with that premise gone the derivation is the
       agreement alone, which is what makes the [eb = false] instance live
       rather than vacuous. *)
    iDestruct (cpu_own_eb_agree with "Hcg Hown") as %Hbm.
    subst b.
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
    iApply (wp_caddi_sp_push_s_sconf pcE (mword_of_int 32 : mword 6) m K 4 eb ltac:(pose proof (bo_K4 K HK); lia) Hpush
              with "Hcg Hpc []").
    { iApply (boi_00 with "Htext"). }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iEval (rewrite Hspm) in "Hframe".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))]> m) with R1.
    assert (HspR1 : R1 !!! Regidx csp_rs1 = spd) by (rewrite /R1 upd_eq; reflexivity).
    iEval (rewrite (stack_own_slots (KTR := KT1)); cbn [seq]) in "Hframe".
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
              R1 (K - 4)%nat vr24 eb with "Hcg Hpc [] Hr24").
    { iApply (boi_02 with "Htext"). }
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    iEval (rgne) in "Hr24".
    assert (Hp04 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x04))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp04) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x04)) (mword_of_int 2 : mword 6) (mword_of_int 8 : mword 5)
              R1 (K - 4)%nat vr16 eb with "Hcg Hpc [] Hr16").
    { iApply (boi_04 with "Htext"). }
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    iEval (rgne) in "Hr16".
    assert (Hp06 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x06))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp06) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x06)) (mword_of_int 1 : mword 6) (mword_of_int 9 : mword 5)
              R1 (K - 4)%nat vr8 eb with "Hcg Hpc [] Hr8").
    { iApply (boi_06 with "Htext"). }
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    iEval (rgne) in "Hr8".
    assert (Hp08 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x08))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp08) in "Hpc".
    iApply (wp_csdsp_s_sconf (mword_of_int (KernelSyms.begin_op + 0x08)) (mword_of_int 0 : mword 6) (mword_of_int 18 : mword 5)
              R1 (K - 4)%nat vr0 eb with "Hcg Hpc [] Hr0").
    { iApply (boi_08 with "Htext"). }
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
              (mword_of_int 8 : mword 5) R1 (K - 4)%nat eb
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_0a with "Htext"). }
    iIntros (CID6 Hs6) "Hcg Hpc".
    set (R2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1).
    change (<[Regidx (mword_of_int 8 : mword 5) := regval_into_reg
        (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 8 : mword 8))))]> R1) with R2.
    assert (Hp0c : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.begin_op + 0x0c))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp0c) in "Hpc".
    (* +0x0c auipc a0,0x1e ; +0x10 addi a0,a0,1862 : a0 := &log *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.begin_op + 0x0c)) (mword_of_int 10 : mword 5)
              (mword_of_int 30 : mword 20) R2 (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_0c with "Htext"). }
    iIntros (CID7 Hs7) "Hcg Hpc".
    set (R3 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.begin_op + 0x0c) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> R2).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (mword_of_int (KernelSyms.begin_op + 0x0c) : mword 64) (auipc_off (mword_of_int 30 : mword 20)))]> R2) with R3.
    assert (Hp10 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x0c) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x10))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp10) in "Hpc".
    iApply (wp_addi4_s_sconf (mword_of_int (KernelSyms.begin_op + 0x10)) (mword_of_int 10 : mword 5)
              (mword_of_int 10 : mword 5) (mword_of_int 1820 : mword 12) R3 (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_10 with "Htext"). }
    iIntros (CID8 Hs8) "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (R4 := <[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (R3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1820 : mword 12)))]> R3).
    change (<[Regidx (mword_of_int 10 : mword 5) := regval_into_reg
        (add_vec (R3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 1820 : mword 12)))]> R3) with R4.
    assert (Hp14 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x10) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x14))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp14) in "Hpc".
    assert (HR4a0 : R4 !!! Regidx (mword_of_int 10 : mword 5) = log_addr).
    { rewrite /R4 upd_eq /R3 upd_eq. exact bo_reloc_a0_0c. }
    (* +0x14 jal ra,acquire *)
    iApply (wp_jal_s_sconf (mword_of_int (KernelSyms.begin_op + 0x14)) (mword_of_int 1 : mword 5)
              (mword_of_int 2084678 : mword 21) R4 (K - 4)%nat eb
              ltac:(vm_compute; discriminate) ltac:(rdok) ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_14 with "Htext"). }
    iIntros (CID9 Hs9) "Hcg Hpc".
    set (Maq := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x14) : mword 64) 4)]> R4).
    change (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.begin_op + 0x14) : mword 64) 4)]> R4) with Maq.
    assert (Hjaq : add_vec (mword_of_int (KernelSyms.begin_op + 0x14) : mword 64) (sign_extend' 64 (mword_of_int 2084678 : mword 21))
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
    iDestruct (cpu_own_transport CID CID9 0 eb pj eb ltac:(wp_next_chain)
                 with "Hown") as "Hown".
    iApply (Acquire.wp_acquire_sconf KT1 (ln_lk γ) "log"%string (log_res γ bn γfs cov logstart) Maq
              0%nat eb pj (K - 4)%nat eb lks
              bo_noff1 ltac:(pose proof (bo_K10 K HK); lia) Hbelow
              with "Hcg Hown Htext Hpc []").
    all: try lkbelow.
    { iEval (rewrite HMaqa0). iExact "Hislock". }
    iIntros (CIDa Hsa ms Macq) "%Hmsf Hcg Hpc %Hcsacq Htok Hres Hown Hpay".
    (* JOIN AT THE INDEX: the acquire's push_off freed the pair at
       [eb = true] and nothing at [eb = false], where the caller brought it.
       From here the loop carries [trap_csrs ∗ cpu_claim pj] index-free.
       The caller's complement is hart-indexed and the prologue rebound the
       hart, so move it first -- free at both indices. *)
    iDestruct (trap_csrs_ext_transport CID CIDa eb pj ltac:(wp_next_chain)
                 with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID CIDa eb pj ltac:(wp_next_chain)
                 with "Hextm") as "Hextm".
    iDestruct (arm_pay_ext_join eb _ with "Hpay [$Hextc $Hextm]") as "[Htc Hclm]".
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
    iAssert (bo_exit CID j γ bn γfs cov logstart m pidv dq K eb spd sp0 lks Vpr) with "[Hcont]" as "Hexit".
    { rewrite /bo_exit.
      iIntros (CIDx Hsx Mx) "%HboE Hr24 Hr16 Hr8 Hr0 Htok Hres Hop Hpid Hown Htc Hclm Hcg Hpc".
      iApply (bo_exit_body (CID := CIDx) CID j γ bn γfs cov logstart dev m Mx pidv dq K eb spd sp0 lks
                Vpr HK Hsx Hspd Hsp0 HboE Hbelow
                with "Htext Hlog Hr24 Hr16 Hr8 Hr0 Htok Hres Hop Hpid Hown Htc Hclm Hcg Hpc Hcont"). }
    (* ============ the WAIT LOOP (iLöb over the anchored invariant) ======== *)
    iAssert (bo_loop CID j γ bn γfs cov logstart m pidv dq K eb spd sp0 lks Vpr) with "[]" as "Hloop".
    { iLöb as "IH". rewrite /bo_loop.
      iIntros (CIDy Hsy My) "%HboL Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Htc Hclm Hcg Hpc Hexit".
      iApply (bo_loop_body (CID := CIDy) CID γs j γl γ bn γfs cov logstart dev m My pidv dq K eb spd sp0 lks
                Vpr HK Hj Hjl Hsy HboL Hbelow
                with "Htext Hlog Hpinv IH Hexit Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Htc Hclm Hcg Hpc"). }
    (* ============ +0x18..+0x22: s1 := &log, s2 := 30, jump to the test ==== *)
    iApply (wp_auipc_s_sconf (mword_of_int (KernelSyms.begin_op + 0x18)) (mword_of_int 9 : mword 5)
              (mword_of_int 30 : mword 20) Macq (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_18 with "Htext"). }
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
              (mword_of_int 9 : mword 5) (mword_of_int 1808 : mword 12) T1 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (boi_1c with "Htext"). }
    iApply wp_next_off_intro.
    iIntros "Hcg Hpc".
    iEval (rgne) in "Hcg".
    set (T2 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec (T1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 1808 : mword 12)))]> T1).
    change (<[Regidx (mword_of_int 9 : mword 5) := regval_into_reg
        (add_vec (T1 !!! Regidx (mword_of_int 9 : mword 5)) (sign_extend' 64 (mword_of_int 1808 : mword 12)))]> T1) with T2.
    assert (Hp20 : add_vec_int (mword_of_int (KernelSyms.begin_op + 0x1c) : mword 64) 4 = mword_of_int (KernelSyms.begin_op + 0x20))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp20) in "Hpc".
    assert (HT2s1 : T2 !!! Regidx (mword_of_int 9 : mword 5) = log_addr).
    { rewrite /T2 upd_eq /T1 upd_eq. exact bo_reloc_s1_18. }
    (* +0x20 c.li s2,30 *)
    iApply (wp_cli_s_sconf (mword_of_int (KernelSyms.begin_op + 0x20)) (mword_of_int 18 : mword 5)
              (mword_of_int 30 : mword 6) (mword_of_int 30 : mword 64) T2 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; discriminate) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_20 with "Htext"). }
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
              (sign_extend' 21 (concat_vec (mword_of_int 12 : mword 11) ('b"0"))) T3 (trap_res eb + (K - 4))%nat false
              ltac:(vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (boi_22 with "Htext"). }
    iApply wp_next_off_intro.
    iNext.
    iIntros "Hcg Hpc".
    assert (Htgt2c : add_vec (mword_of_int (KernelSyms.begin_op + 0x22) : mword 64)
                       (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 12 : mword 11) ('b"0"))))
                     = mword_of_int (KernelSyms.begin_op + 0x3a))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Htgt2c) in "Hpc".
    rewrite /bo_loop.
    iSpecialize ("Hloop" $! CIDa with "[%]"); [wp_next_chain|].
    iApply ("Hloop" $! T3 with "[%] Hr24 Hr16 Hr8 Hr0 Htok Hres Hpid Hown Htc Hclm Hcg Hpc Hexit").
    exact HboT3.
  Qed.

End ProofBeginOp.

End BeginOpProof.
