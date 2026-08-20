(* ProofSysExec.v -- sys_exec, the marshaller in front of kexec and the last
   function of sysfile.c.

   101 instructions, a 480-byte frame, eight callees and three loops.  The
   frame is the whole story, so here it is once, in slots ([pa_stk sp0 k] is
   [sp0 - 8k], and [sp0] is the entry sp, which is also [s0]):

     slot  1        ra                spilled at +0x02
     slot  2        s0                spilled at +0x04
     slots 3 ..  9  s1 s2 s3 s4 s5 s6 s7   spilled LAZILY at +0x28..+0x36,
                                      i.e. only AFTER the argstr test, which
                                      is why the -1 tail at +0x104 restores
                                      ra and s0 and nothing else
     slot 10        unused (alignment)
     slots 11 .. 26 char path[MAXPATH]     base [pa_stk sp0 26], 128 bytes
     slots 27 .. 58 char *argv[MAXARG]     argv[i] IS slot [58 - i]
     slot 59        uint64 uargv
     slot 60        uint64 uarg

   ---- THE THREE LOOPS -------------------------------------------------

   (1) THE FILL LOOP, +0x56 .. +0x90, head at +0x56 and back edge at the
       [bne s2,s7] at +0x8e.  Per iteration: fetchaddr of [uargv[i]], test
       for NULL (the break, to +0xb6), kalloc, fetchstr into the page.  Four
       exits: the break, and three to [bad:] (+0x92) from fetchaddr, kalloc
       and fetchstr.  A FIFTH is the back edge falling through at [i = 32],
       which is how gcc compiled the C's [i >= NELEM(argv)] test -- so the
       break is reached only at [i < 32], and that is where kexec's
       [na < MAXARG] premise comes from.

   (2) THE bad: FREE LOOP, +0x96 .. +0xa0, and (3) THE SUCCESS FREE LOOP,
       +0xd4 .. +0xde.  Same two instructions at two addresses, walking
       [s1] up the argv array and kfree-ing until it reads a NULL or reaches
       [s4 = argv + 256].  They are one lemma, [sx_free_loop], taking the
       two addresses and their [instr] facts -- the same move
       [ProofKexecC.kxc_c_exit_m1] makes for kexec's three [-1] stubs.

   ---- WHAT MAKES THE ARGV ARRAY WORK ----------------------------------

   [memset] writes BYTES and the array is read as WORDS, and the zero has to
   survive the round trip: the loop's [bad:] exit walks argv until it finds
   a NULL, and the NULL it finds at index [i] is memset's, not one the code
   wrote.  [bytes_own_slotsn (KTR := KT1)] would give the words back EXISTENTIALLY and
   lose exactly that, so the rebuild goes through [sx_zeros_slots] instead,
   which reassembles each eight zero bytes into a zero WORD.  That is the
   one place this proof cannot use the generic frame vocabulary.

   ---- WHAT IS IN THIS FILE --------------------------------------------

   The pure side conditions, the zero round trip, the sixty-slot frame carve
   and join, and the epilogue block (+0x104 .. +0x10a) -- all [Qed], no
   admits.  The BODY (+0x000 .. +0x102) is not written yet; its block
   decomposition, loop invariant and callee inventory are worked out in
   claude-notes/projects/kexec.md's worklist, which is what to write it
   from. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import HartTp.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import SmodeCore.
Require Import StackOwn.
Require Import StackBytes.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import KernelDataInv.
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import LockRank.
Require Import CpuOwn.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioDefs.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import ByteBuf.
Require Import InodeInv.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import KallocInv.
Require Import KvmSpec.
Require Import PageGeom.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import W32Arith.
Require Import SpecDirlink.
Require Import SpecArgaddr.
Require Import SpecArgstr.
(* [proc_priv_tfp_valid] -- [page_valid] of the trapframe page, which
   argaddr's own load now takes as a premise (SpecArgraw's mem-tier fix).
   It is a PROJECTION of [proc_priv], not an obligation on this caller. *)
Require Import ProofKforkParts.
Require Import SpecFetchaddr.
Require Import SpecFetchstr.
Require Import SpecKalloc.
Require Import SpecKfree.
Require Import SpecMemset.
Require Import SpecKexec.
Require Import CodeSysExec.
Require Import SpecSysExec.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation SX := KernelSyms.sys_exec (only parsing).

(* ===================================================================== *)
(*  THE PURE SIDE CONDITIONS, as closed top-level facts.                  *)
(* ===================================================================== *)

(* The nine callee-saved registers this function writes: sp, s0 (frame
   pointer), and s1..s7.  Everything else rides straight through. *)
Definition sx_thr (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) ->
    c <> (mword_of_int 9 : mword 5) ->
    c <> (mword_of_int 18 : mword 5) ->
    c <> (mword_of_int 19 : mword 5) ->
    c <> (mword_of_int 20 : mword 5) ->
    c <> (mword_of_int 21 : mword 5) ->
    c <> (mword_of_int 22 : mword 5) ->
    c <> (mword_of_int 23 : mword 5) ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Lemma sx_thr_refl (m : regfile) : sx_thr m m.
Proof. intros c ?????????. reflexivity. Qed.

Lemma sx_thr_trans (m M P : regfile) : sx_thr m M -> sx_thr M P -> sx_thr m P.
Proof.
  intros H1 H2 c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23.
  rewrite (H2 c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23).
  exact (H1 c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23).
Qed.

(* The prologue's threading, which is STRONGER: +0x000 .. +0x026 writes only
   sp, s0, ra and the argument registers, so s1..s7 are still at their entry
   values there and the seven equations the epilogue wants come for free.  The
   body proper needs [sx_thr]; this is what the head publishes. *)
Definition sx_thr2 (m M : regfile) : Prop :=
  forall c : mword 5, is_cs_idx c = true ->
    c <> csp_rs1 ->
    c <> (mword_of_int 8 : mword 5) ->
    M !!! Regidx c = (m !!! Regidx c : mword 64).

Lemma sx_thr2_thr (m M : regfile) : sx_thr2 m M -> sx_thr m M.
Proof. intros H c Hc N2 N8 _ _ _ _ _ _ _. exact (H c Hc N2 N8). Qed.

Lemma sx_thr2_refl (m : regfile) : sx_thr2 m m.
Proof. intros c _ _ _. reflexivity. Qed.

Definition sx_sp (sp0 : mword 64) (M : regfile) : Prop :=
  M !!! Regidx csp_rs1 = pa_stk sp0 60.

(* -480 / +480, both a [c.addi16sp] (34 is -30 in a 6-bit field, x16). *)
Lemma sx_push (X : mword 64) :
  add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 34 : mword 6)))
  = pa_stk X 60.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_pop (X : mword 64) :
  add_vec (pa_stk X 60) (sign_extend' 64 (caddi16sp_imm (mword_of_int 30 : mword 6)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* [c.addi4spn s0,sp,480] -- the frame pointer, back at the entry sp. *)
Lemma sx_fp (X : mword 64) :
  add_vec (pa_stk X 60) (sign_extend' 64 (caddi4spn_imm (mword_of_int 120 : mword 8)))
  = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

(* the four [addi rd,s0,-N] the body uses, off the frame pointer (which IS
   the entry sp): uarg, uargv, argv, path. *)
Lemma sx_uarg (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3616 : mword 12)) = pa_stk X 60.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_uargv (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3624 : mword 12)) = pa_stk X 59.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_argv (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3632 : mword 12)) = pa_stk X 58.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_path (X : mword 64) :
  add_vec X (sign_extend' 64 (mword_of_int 3888 : mword 12)) = pa_stk X 26.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* the c.sdsp / c.ldsp displacements off the pushed sp *)
Lemma sx_frm (X : mword 64) (u : mword 6) (k : nat) :
  (mword_of_int (bv_wrap 64 (uint (mword_of_int (- (8 * Z.of_nat 60)) : mword 64)
                         + uint (zero_extend' 64 (concat_vec u ('b"000")) : mword 64)))
   : mword 64)
  = mword_of_int (- (8 * Z.of_nat k)) ->
  add_vec (pa_stk X 60) (zero_extend' 64 (concat_vec u ('b"000"))) = pa_stk X k.
Proof.
  intro H. unfold pa_stk, add_vec_int. rewrite pa_stk_off2. apply f_equal. exact H.
Qed.

Lemma sx_frm1 (X : mword 64) :
  add_vec (pa_stk X 60)
    (zero_extend' 64 (concat_vec (mword_of_int 59 : mword 6) ('b"000")))
  = pa_stk X 1.
Proof. apply sx_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_frm2 (X : mword 64) :
  add_vec (pa_stk X 60)
    (zero_extend' 64 (concat_vec (mword_of_int 58 : mword 6) ('b"000")))
  = pa_stk X 2.
Proof. apply sx_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_frm3 (X : mword 64) :
  add_vec (pa_stk X 60)
    (zero_extend' 64 (concat_vec (mword_of_int 57 : mword 6) ('b"000")))
  = pa_stk X 3.
Proof. apply sx_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_frm4 (X : mword 64) :
  add_vec (pa_stk X 60)
    (zero_extend' 64 (concat_vec (mword_of_int 56 : mword 6) ('b"000")))
  = pa_stk X 4.
Proof. apply sx_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_frm5 (X : mword 64) :
  add_vec (pa_stk X 60)
    (zero_extend' 64 (concat_vec (mword_of_int 55 : mword 6) ('b"000")))
  = pa_stk X 5.
Proof. apply sx_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_frm6 (X : mword 64) :
  add_vec (pa_stk X 60)
    (zero_extend' 64 (concat_vec (mword_of_int 54 : mword 6) ('b"000")))
  = pa_stk X 6.
Proof. apply sx_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_frm7 (X : mword 64) :
  add_vec (pa_stk X 60)
    (zero_extend' 64 (concat_vec (mword_of_int 53 : mword 6) ('b"000")))
  = pa_stk X 7.
Proof. apply sx_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_frm8 (X : mword 64) :
  add_vec (pa_stk X 60)
    (zero_extend' 64 (concat_vec (mword_of_int 52 : mword 6) ('b"000")))
  = pa_stk X 8.
Proof. apply sx_frm. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma sx_frm9 (X : mword 64) :
  add_vec (pa_stk X 60)
    (zero_extend' 64 (concat_vec (mword_of_int 51 : mword 6) ('b"000")))
  = pa_stk X 9.
Proof. apply sx_frm. apply bv_eq; vm_compute; reflexivity. Qed.

(* K_sys_exec's single premise, turned into every bound the eight callees
   and the [sie_cap_gpr] pop want.  kexec dominates by a wide margin. *)
Lemma sx_kb (K : nat) : (K_sys_exec <= K)%nat ->
  (K_kexec <= K - 60)%nat /\ (argstr_stack <= K - 60)%nat /\
  (argaddr_stack <= K - 60)%nat /\ (fetchaddr_stack <= K - 60)%nat /\
  (fetchstr_stack <= K - 60)%nat /\ (14 <= K - 60)%nat /\ (2 <= K - 60)%nat /\
  (60 <= K)%nat /\ ((K - 60) + 60 = K)%nat.
Proof.
  
  intro H. split_and!; lia.
Qed.

(* the syscall argument indices are in range *)
Lemma sx_arg0_lt : (0 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma sx_arg1_lt : (1 < NARG)%nat.
Proof. unfold NARG. lia. Qed.

Lemma sx_noff0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma sx_maxpath_lt : (Z.of_nat 128 < 2 ^ 31)%Z.
Proof. lia. Qed.

Lemma sx_pgsize_lt : (Z.of_nat 4096 < 2 ^ 31)%Z.
Proof. lia. Qed.

(* the [bltz] tests: a value that is either [-1] or a length below its cap
   decides the branch by its SIGN.  ProofSysChdir's cluster, restated -- a
   whole-function proof file is not a dependency any other one may take. *)
Lemma sx_sint_moi (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  sint (mword_of_int z : mword 64) = z.
Proof.
  intro Hz.
  assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  assert (E64 : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  change (sint ?x) with (bv_swrap 64 (bv_unsigned x)).
  rewrite moi64_unsigned. rewrite bvw64_small; [| lia].
  apply bv_swrap_small.
  assert (Hhm : bv_half_modulus 64 = (2 ^ 63)%Z) by reflexivity. rewrite Hhm.
  assert (E63 : (2 ^ 63 = 9223372036854775808)%Z) by (vm_compute; reflexivity).
  lia.
Qed.

Lemma sx_nonneg (z : Z) : (0 <= z < 2 ^ 31)%Z ->
  zopz0zI_s (mword_of_int z : mword 64) (zero_reg : mword 64) = false.
Proof.
  intro Hz. unfold zopz0zI_s. apply Z.ltb_ge.
  assert (Hz0 : sint (zero_reg : mword 64) = 0%Z) by reflexivity. rewrite Hz0.
  rewrite (sx_sint_moi z Hz). lia.
Qed.

Lemma sx_m1_neg :
  zopz0zI_s (mword_of_int (-1) : mword 64) (zero_reg : mword 64) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma sx_len_range (k n : nat) : (k < n)%nat -> (Z.of_nat n < 2 ^ 31)%Z ->
  (0 <= Z.of_nat k < 2 ^ 31)%Z.
Proof. lia. Qed.

(* memset's byte at [cval = 0] IS the zero byte, and [32 <= S 58]: the two
   side conditions [sx_zeros_slots] takes.  Top-level rather than inline
   [ltac:]s at the call site, where the byte is still an evar -- see
   optimization.md, "Inline [ltac:] in argument position". *)
Lemma sx_zb_zero (j : nat) : (j < 8)%nat ->
  nth_byte (mword_of_int 0 : mword 64) j
  = nth_byte (autocast (T := mword)
       (subrange_vec_dec (mword_of_int 0 : mword 64)
          (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0.
Proof.
  intro Hj. destruct j as [|[|[|[|[|[|[|[|j']]]]]]]];
    try (vm_compute; reflexivity). lia.
Qed.

Lemma sx_argv_slots_fit : (32 <= S 58)%nat.
Proof. lia. Qed.

(* ===================================================================== *)
(*  THE ZERO ROUND TRIP: memset writes bytes, the array is read as words,  *)
(*  and the NULL the [bad:] free loop stops at is memset's own.            *)
(* ===================================================================== *)
Section SysExecZeros.
  Context `{!riscvGS Σ}.

  Lemma sx_zero_slot (a : mword 64) (zb : bv 8) :
    (forall j, (j < 8)%nat -> nth_byte (mword_of_int 0 : mword 64) j = zb) ->
    is_aligned_paddr (Physaddr a) 8 = true ->
    ([∗ list] j ∈ seq 0 8, pa_add a j ↦ₘ[KT1] zb) ⊢ a ↦₈[KT1] (mword_of_int 0 : mword 64).
  Proof.
    intros Hzb Hal. iIntros "H".
    iApply (word_pointsto_intro (KTR := KT1) _ _ _ Hal).
    iApply (big_sepL_mono with "H"). intros i j Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite (Hzb i Hlt). done.
  Qed.

  Lemma sx_zeros_slots (sp : mword 64) (zb : bv 8) (k n : nat) :
    (forall j, (j < 8)%nat -> nth_byte (mword_of_int 0 : mword 64) j = zb) ->
    (n <= S k)%nat ->
    (forall i, (i < n)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp (k - i))) 8 = true) ->
    ([∗ list] j ∈ seq 0 (8 * n), pa_add (pa_stk sp k) j ↦ₘ[KT1] zb) ⊢
    [∗ list] i ∈ seq 0 n, pa_stk sp (k - i) ↦₈[KT1] (mword_of_int 0 : mword 64).
  Proof.
    intro Hzb. revert k. induction n as [| n IH]; intros k Hk Hal.
    - iIntros "_". by rewrite big_sepL_nil.
    - rewrite seq_S big_sepL_app big_sepL_singleton.
      replace (8 * S n)%nat with (8 * n + 8)%nat by lia.
      rewrite (bb_split (pa_stk sp k) (8 * n) 8 (fun _ => zb)).
      rewrite (pa_stk_addn sp k n ltac:(lia)).
      iIntros "[Hb Hbn]".
      iSplitL "Hb".
      + iApply (IH k ltac:(lia) ltac:(intros i Hi; apply Hal; lia) with "Hb").
      + iApply (sx_zero_slot _ zb Hzb (Hal n ltac:(lia)) with "Hbn").
  Qed.

End SysExecZeros.

(* ===================================================================== *)
(*  THE FRAME CARVE: sixty slots into ten spill words, the path buffer,   *)
(*  the argv array (as BYTES, because memset writes it), and the two      *)
(*  out-parameter cells.                                                  *)
(* ===================================================================== *)
Section SysExecFrame.
  Context `{!riscvGS Σ}.

  Definition sx_alp (sp0 : mword 64) : Prop :=
    forall i, (i < 16)%nat ->
      is_aligned_paddr (Physaddr (pa_stk sp0 (26 - i)%nat)) 8 = true.
  Definition sx_ala (sp0 : mword 64) : Prop :=
    forall i, (i < 32)%nat ->
      is_aligned_paddr (Physaddr (pa_stk sp0 (58 - i)%nat)) 8 = true.

  Lemma sx_frame_carve (sp0 : mword 64) :
    stack_own (KTR := KT1) sp0 60 -∗
    ⌜sx_alp sp0⌝ ∗ ⌜sx_ala sp0⌝ ∗
    (∃ w : mword 64, (pa_stk sp0 1) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 2) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 3) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 4) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 5) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 6) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 7) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 8) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 9) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 10) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 59) ↦₈[KT1] w) ∗
    (∃ w : mword 64, (pa_stk sp0 60) ↦₈[KT1] w) ∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 26) 128 ∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 58) 256.
  Proof.
    iIntros "H". rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
    iDestruct "H" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28 & S29 & S30 & S31 & S32 & S33 & S34 & S35 & S36 & S37 & S38 & S39 & S40 & S41 & S42 & S43 & S44 & S45 & S46 & S47 & S48 & S49 & S50 & S51 & S52 & S53 & S54 & S55 & S56 & S57 & S58 & S59 & S60 & _)".
    change 128%nat with (8 * 16)%nat. change 256%nat with (8 * 32)%nat.
    iDestruct (slotsn_bytes_own (KTR := KT1) sp0 26 16 ltac:(lia)
                 with "[S26 S25 S24 S23 S22 S21 S20 S19 S18 S17 S16 S15 S14 S13 S12 S11]") as "[%Halp Hpb]".
    { cbn [seq].
      iSplitL "S26"; [iExact "S26" |].
      iSplitL "S25"; [iExact "S25" |].
      iSplitL "S24"; [iExact "S24" |].
      iSplitL "S23"; [iExact "S23" |].
      iSplitL "S22"; [iExact "S22" |].
      iSplitL "S21"; [iExact "S21" |].
      iSplitL "S20"; [iExact "S20" |].
      iSplitL "S19"; [iExact "S19" |].
      iSplitL "S18"; [iExact "S18" |].
      iSplitL "S17"; [iExact "S17" |].
      iSplitL "S16"; [iExact "S16" |].
      iSplitL "S15"; [iExact "S15" |].
      iSplitL "S14"; [iExact "S14" |].
      iSplitL "S13"; [iExact "S13" |].
      iSplitL "S12"; [iExact "S12" |].
      iSplitL "S11"; [iExact "S11" |].
      done. }
    iDestruct (slotsn_bytes_own (KTR := KT1) sp0 58 32 ltac:(lia)
                 with "[S58 S57 S56 S55 S54 S53 S52 S51 S50 S49 S48 S47 S46 S45 S44 S43 S42 S41 S40 S39 S38 S37 S36 S35 S34 S33 S32 S31 S30 S29 S28 S27]") as "[%Hala Hab]".
    { cbn [seq].
      iSplitL "S58"; [iExact "S58" |].
      iSplitL "S57"; [iExact "S57" |].
      iSplitL "S56"; [iExact "S56" |].
      iSplitL "S55"; [iExact "S55" |].
      iSplitL "S54"; [iExact "S54" |].
      iSplitL "S53"; [iExact "S53" |].
      iSplitL "S52"; [iExact "S52" |].
      iSplitL "S51"; [iExact "S51" |].
      iSplitL "S50"; [iExact "S50" |].
      iSplitL "S49"; [iExact "S49" |].
      iSplitL "S48"; [iExact "S48" |].
      iSplitL "S47"; [iExact "S47" |].
      iSplitL "S46"; [iExact "S46" |].
      iSplitL "S45"; [iExact "S45" |].
      iSplitL "S44"; [iExact "S44" |].
      iSplitL "S43"; [iExact "S43" |].
      iSplitL "S42"; [iExact "S42" |].
      iSplitL "S41"; [iExact "S41" |].
      iSplitL "S40"; [iExact "S40" |].
      iSplitL "S39"; [iExact "S39" |].
      iSplitL "S38"; [iExact "S38" |].
      iSplitL "S37"; [iExact "S37" |].
      iSplitL "S36"; [iExact "S36" |].
      iSplitL "S35"; [iExact "S35" |].
      iSplitL "S34"; [iExact "S34" |].
      iSplitL "S33"; [iExact "S33" |].
      iSplitL "S32"; [iExact "S32" |].
      iSplitL "S31"; [iExact "S31" |].
      iSplitL "S30"; [iExact "S30" |].
      iSplitL "S29"; [iExact "S29" |].
      iSplitL "S28"; [iExact "S28" |].
      iSplitL "S27"; [iExact "S27" |].
      done. }
    iSplitR; [iPureIntro; exact Halp |]. iSplitR; [iPureIntro; exact Hala |].
    iSplitL "S1"; [iExact "S1" |].
    iSplitL "S2"; [iExact "S2" |].
    iSplitL "S3"; [iExact "S3" |].
    iSplitL "S4"; [iExact "S4" |].
    iSplitL "S5"; [iExact "S5" |].
    iSplitL "S6"; [iExact "S6" |].
    iSplitL "S7"; [iExact "S7" |].
    iSplitL "S8"; [iExact "S8" |].
    iSplitL "S9"; [iExact "S9" |].
    iSplitL "S10"; [iExact "S10" |].
    iSplitL "S59"; [iExact "S59" |].
    iSplitL "S60"; [iExact "S60" |].
    iSplitL "Hpb"; [iExact "Hpb" | iExact "Hab"].
  Qed.

  Lemma sx_frame_join (sp0 : mword 64)
      (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v59 v60 : mword 64) :
    sx_alp sp0 -> sx_ala sp0 ->
    (pa_stk sp0 1) ↦₈[KT1] v1 -∗
    (pa_stk sp0 2) ↦₈[KT1] v2 -∗
    (pa_stk sp0 3) ↦₈[KT1] v3 -∗
    (pa_stk sp0 4) ↦₈[KT1] v4 -∗
    (pa_stk sp0 5) ↦₈[KT1] v5 -∗
    (pa_stk sp0 6) ↦₈[KT1] v6 -∗
    (pa_stk sp0 7) ↦₈[KT1] v7 -∗
    (pa_stk sp0 8) ↦₈[KT1] v8 -∗
    (pa_stk sp0 9) ↦₈[KT1] v9 -∗
    (pa_stk sp0 10) ↦₈[KT1] v10 -∗
    (pa_stk sp0 59) ↦₈[KT1] v59 -∗
    (pa_stk sp0 60) ↦₈[KT1] v60 -∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 26) 128 -∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 58) 256 -∗
    stack_own (KTR := KT1) sp0 60.
  Proof.
    intros Halp Hala. iIntros "S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S59 S60 Hpb Hab".
    change 128%nat with (8 * 16)%nat. change 256%nat with (8 * 32)%nat.
    iDestruct (bytes_own_slotsn (KTR := KT1) sp0 26 16 ltac:(lia) Halp with "Hpb") as "Hp".
    iDestruct (bytes_own_slotsn (KTR := KT1) sp0 58 32 ltac:(lia) Hala with "Hab") as "Ha".
    cbn [seq].
    iDestruct "Hp" as "(P26 & P25 & P24 & P23 & P22 & P21 & P20 & P19 & P18 & P17 & P16 & P15 & P14 & P13 & P12 & P11 & _)".
    iDestruct "Ha" as "(A58 & A57 & A56 & A55 & A54 & A53 & A52 & A51 & A50 & A49 & A48 & A47 & A46 & A45 & A44 & A43 & A42 & A41 & A40 & A39 & A38 & A37 & A36 & A35 & A34 & A33 & A32 & A31 & A30 & A29 & A28 & A27 & _)".
    rewrite (stack_own_slots (KTR := KT1)). cbn [seq].
    iSplitL "S1"; [iExists v1; iExact "S1" |].
    iSplitL "S2"; [iExists v2; iExact "S2" |].
    iSplitL "S3"; [iExists v3; iExact "S3" |].
    iSplitL "S4"; [iExists v4; iExact "S4" |].
    iSplitL "S5"; [iExists v5; iExact "S5" |].
    iSplitL "S6"; [iExists v6; iExact "S6" |].
    iSplitL "S7"; [iExists v7; iExact "S7" |].
    iSplitL "S8"; [iExists v8; iExact "S8" |].
    iSplitL "S9"; [iExists v9; iExact "S9" |].
    iSplitL "S10"; [iExists v10; iExact "S10" |].
    iSplitL "P11"; [iExact "P11" |].
    iSplitL "P12"; [iExact "P12" |].
    iSplitL "P13"; [iExact "P13" |].
    iSplitL "P14"; [iExact "P14" |].
    iSplitL "P15"; [iExact "P15" |].
    iSplitL "P16"; [iExact "P16" |].
    iSplitL "P17"; [iExact "P17" |].
    iSplitL "P18"; [iExact "P18" |].
    iSplitL "P19"; [iExact "P19" |].
    iSplitL "P20"; [iExact "P20" |].
    iSplitL "P21"; [iExact "P21" |].
    iSplitL "P22"; [iExact "P22" |].
    iSplitL "P23"; [iExact "P23" |].
    iSplitL "P24"; [iExact "P24" |].
    iSplitL "P25"; [iExact "P25" |].
    iSplitL "P26"; [iExact "P26" |].
    iSplitL "A27"; [iExact "A27" |].
    iSplitL "A28"; [iExact "A28" |].
    iSplitL "A29"; [iExact "A29" |].
    iSplitL "A30"; [iExact "A30" |].
    iSplitL "A31"; [iExact "A31" |].
    iSplitL "A32"; [iExact "A32" |].
    iSplitL "A33"; [iExact "A33" |].
    iSplitL "A34"; [iExact "A34" |].
    iSplitL "A35"; [iExact "A35" |].
    iSplitL "A36"; [iExact "A36" |].
    iSplitL "A37"; [iExact "A37" |].
    iSplitL "A38"; [iExact "A38" |].
    iSplitL "A39"; [iExact "A39" |].
    iSplitL "A40"; [iExact "A40" |].
    iSplitL "A41"; [iExact "A41" |].
    iSplitL "A42"; [iExact "A42" |].
    iSplitL "A43"; [iExact "A43" |].
    iSplitL "A44"; [iExact "A44" |].
    iSplitL "A45"; [iExact "A45" |].
    iSplitL "A46"; [iExact "A46" |].
    iSplitL "A47"; [iExact "A47" |].
    iSplitL "A48"; [iExact "A48" |].
    iSplitL "A49"; [iExact "A49" |].
    iSplitL "A50"; [iExact "A50" |].
    iSplitL "A51"; [iExact "A51" |].
    iSplitL "A52"; [iExact "A52" |].
    iSplitL "A53"; [iExact "A53" |].
    iSplitL "A54"; [iExact "A54" |].
    iSplitL "A55"; [iExact "A55" |].
    iSplitL "A56"; [iExact "A56" |].
    iSplitL "A57"; [iExact "A57" |].
    iSplitL "A58"; [iExact "A58" |].
    iSplitL "S59"; [iExists v59; iExact "S59" |].
    iSplitL "S60"; [iExists v60; iExact "S60" |].
    done.
  Qed.

  (* the path buffer, named as bytes and back, and split at the NUL that
     [fetchstr] reports: kexec reads the prefix, the rest rides through. *)
  Lemma sx_bytes_name (a : mword 64) (N : nat) :
    bytes_own (KTR := KT1) (DfracOwn 1) a N ⊢
    ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] f j.
  Proof. rewrite /bytes_own. exact (bb_any_named (KTR := KT1) a N). Qed.

  Lemma sx_name_bytes (a : mword 64) (N : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] f j) ⊢ bytes_own (KTR := KT1) (DfracOwn 1) a N.
  Proof. rewrite /bytes_own. exact (bb_named_any (KTR := KT1) a N f). Qed.

  Lemma sx_buf_split (a : mword 64) (f : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 128, pa_add a j ↦ₘ[KT1] f j) -∗
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ[KT1] f j)
    ∗ ([∗ list] j ∈ seq 0 (127 - k)%nat,
         pa_add (pa_add a (S k)) j ↦ₘ[KT1] f (S k + j)%nat).
  Proof.
    intro Hk.
    replace 128%nat with (S k + (127 - k))%nat by lia.
    rewrite (bb_split a (S k) (127 - k)%nat f). iIntros "[$ $]".
  Qed.

  (* the two halves are named INDEPENDENTLY -- the string [argstr] left and
     the rest of the buffer are separate functions everywhere downstream, so
     a single [f] would force the body to reconcile them at every seam. *)
  Lemma sx_buf_join (a : mword 64) (f g : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ[KT1] f j) -∗
    ([∗ list] j ∈ seq 0 (127 - k)%nat, pa_add (pa_add a (S k)) j ↦ₘ[KT1] g j) -∗
    bytes_own (KTR := KT1) (DfracOwn 1) a 128.
  Proof.
    intro Hk. iIntros "H1 H2".
    iDestruct (sx_name_bytes a (S k) f with "H1") as "B1".
    iDestruct (sx_name_bytes (pa_add a (S k)) (127 - k)%nat g with "H2") as "B2".
    replace 128%nat with (S k + (127 - k))%nat by lia.
    rewrite bytes_own_app. iFrame.
  Qed.

End SysExecFrame.

(* ===================================================================== *)
(*  +0x104 .. +0x10a : THE EPILOGUE, which all three arms leave through.  *)
(*  It restores ra and s0 ONLY -- s1..s7 are spilled lazily at +0x28 and  *)
(*  each arm reloads its own subset before jumping here, which is why     *)
(*  they arrive as premises rather than as loads. *)
(* ===================================================================== *)
Section SysExecEpilogue.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  (* everything in the frame the epilogue does not itself touch *)
  Definition sx_rest (sp0 : mword 64) : iProp Σ :=
    ((∃ w : mword 64, (pa_stk sp0 3) ↦₈[KT1] w) ∗
    ((∃ w : mword 64, (pa_stk sp0 4) ↦₈[KT1] w) ∗
    ((∃ w : mword 64, (pa_stk sp0 5) ↦₈[KT1] w) ∗
    ((∃ w : mword 64, (pa_stk sp0 6) ↦₈[KT1] w) ∗
    ((∃ w : mword 64, (pa_stk sp0 7) ↦₈[KT1] w) ∗
    ((∃ w : mword 64, (pa_stk sp0 8) ↦₈[KT1] w) ∗
    ((∃ w : mword 64, (pa_stk sp0 9) ↦₈[KT1] w) ∗
    ((∃ w : mword 64, (pa_stk sp0 10) ↦₈[KT1] w) ∗
    ((∃ w : mword 64, (pa_stk sp0 59) ↦₈[KT1] w) ∗
    ((∃ w : mword 64, (pa_stk sp0 60) ↦₈[KT1] w) ∗
     bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 26) 128 ∗
     bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 58) 256))))))))))%I.

  Lemma sx_rest_join (sp0 v1 v2 : mword 64) :
    sx_alp sp0 -> sx_ala sp0 ->
    (pa_stk sp0 1) ↦₈[KT1] v1 -∗ (pa_stk sp0 2) ↦₈[KT1] v2 -∗ sx_rest sp0 -∗
    stack_own (KTR := KT1) sp0 60.
  Proof.
    intros Halp Hala. iIntros "S1 S2 Hr". rewrite /sx_rest.
    iDestruct "Hr" as "(E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E59 & E60 & Hpb & Hab)".
    iDestruct "E3" as (v3) "S3".
    iDestruct "E4" as (v4) "S4".
    iDestruct "E5" as (v5) "S5".
    iDestruct "E6" as (v6) "S6".
    iDestruct "E7" as (v7) "S7".
    iDestruct "E8" as (v8) "S8".
    iDestruct "E9" as (v9) "S9".
    iDestruct "E10" as (v10) "S10".
    iDestruct "E59" as (v59) "S59".
    iDestruct "E60" as (v60) "S60".
    iApply (sx_frame_join sp0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v59 v60 Halp Hala
              with "S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S59 S60 Hpb Hab").
  Qed.

  Local Ltac regne :=
    first [ apply not_eq_sym; apply is_cs_idx_true_neq;
            [vm_compute; reflexivity | assumption]
          | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
          | congruence ].
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.
  Local Ltac scidx := first [ vm_compute; reflexivity | vm_compute; discriminate ].

  Lemma sx_epilogue `{GEN : GenId} `{CID0 : CpuId}
      (m M : regfile) (sp0 : mword 64) (K : nat) (b : bool) (pj : mword 64) :
    (60 <= K)%nat -> ((K - 60) + 60 = K)%nat ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sx_sp sp0 M -> sx_thr m M ->
    (M !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64) ->
    (M !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) ->
    (M !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) ->
    (M !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64) ->
    (M !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64) ->
    (M !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64) ->
    (M !!! Regidx Rs7 : mword 64) = (m !!! Regidx Rs7 : mword 64) ->
    sx_alp sp0 -> sx_ala sp0 ->
    sie_cap_gpr KT1 M (K - 60) b pj -∗
    kernel_text -∗ pc_is (mword_of_int (SX + 0x104)) -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) -∗
    sx_rest sp0 -∗
    wp_next b pj (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64)⌝ -∗
        sie_cap_gpr KT1 mf K b pj -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK60 Kpop Hsp0 HMsp HMthr HMs1 HMs2 HMs3 HMs4 HMs5 HMs6 HMs7 Halp Hala.
    iIntros "Hcg #Htext Hpc Hf1 Hf2 Hrest Hcont".
    iPoseProof (sxi_104 with "Htext") as "Hi104".
    iPoseProof (sxi_106 with "Htext") as "Hi106".
    iPoseProof (sxi_108 with "Htext") as "Hi108".
    iPoseProof (sxi_10a with "Htext") as "Hi10a".
    (* ===== +0x104 c.ldsp ra,472(sp) ===== *)
    assert (Hc1 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 59 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HMsp; apply sx_frm1).
    iApply (wp_cldsp_s_sconf (mword_of_int (SX + 0x104))
              (mword_of_int 59 : mword 6) Rra M (K - 60)%nat
              (m !!! Regidx Rra : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi104 [Hf1]").
    { iEval (rewrite Hc1). iExact "Hf1". }
    iIntros (CID1 Hq1) "Hcg Hpc Hf1".
    iEval (rewrite Hc1) in "Hf1".
    set (M1 := <[Regidx Rra := regval_into_reg (m !!! Regidx Rra : mword 64)]> M).
    assert (HM1sp : sx_sp sp0 M1)
      by (rewrite /sx_sp /M1 upd_ne; [exact HMsp | nz]).
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1; apply upd_eq).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = (M !!! Regidx Rs0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1rs1 : (M1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1rs2 : (M1 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs2 | nz]).
    assert (HM1rs3 : (M1 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs3 | nz]).
    assert (HM1rs4 : (M1 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs4 | nz]).
    assert (HM1rs5 : (M1 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs5 | nz]).
    assert (HM1rs6 : (M1 !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs6 | nz]).
    assert (HM1rs7 : (M1 !!! Regidx Rs7 : mword 64) = (m !!! Regidx Rs7 : mword 64))
      by (rewrite /M1 upd_ne; [exact HMs7 | nz]).
    assert (HM1thr : sx_thr m M1).
    { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite /M1 upd_ne; [| regne].
      exact (HMthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23). }
    assert (Hpp106 : add_vec_int (mword_of_int (SX + 0x104) : mword 64) 2
                     = mword_of_int (SX + 0x106)) by pcw.
    iEval (rewrite Hpp106) in "Hpc".
    (* ===== +0x106 c.ldsp s0,464(sp) ===== *)
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 58 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply sx_frm2).
    iApply (wp_cldsp_s_sconf (mword_of_int (SX + 0x106))
              (mword_of_int 58 : mword 6) Rs0 M1 (K - 60)%nat
              (m !!! Regidx Rs0 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi106 [Hf2]").
    { iEval (rewrite Hc2). iExact "Hf2". }
    iIntros (CID2 Hq2) "Hcg Hpc Hf2".
    iEval (rewrite Hc2) in "Hf2".
    set (M2 := <[Regidx Rs0 := regval_into_reg (m !!! Regidx Rs0 : mword 64)]> M1).
    assert (HM2sp : sx_sp sp0 M2)
      by (rewrite /sx_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1ra | nz]).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M2; apply upd_eq).
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2rs1 : (M2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1rs1 | nz]).
    assert (HM2rs2 : (M2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1rs2 | nz]).
    assert (HM2rs3 : (M2 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1rs3 | nz]).
    assert (HM2rs4 : (M2 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1rs4 | nz]).
    assert (HM2rs5 : (M2 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1rs5 | nz]).
    assert (HM2rs6 : (M2 !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1rs6 | nz]).
    assert (HM2rs7 : (M2 !!! Regidx Rs7 : mword 64) = (m !!! Regidx Rs7 : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1rs7 | nz]).
    assert (HM2thr : sx_thr m M2).
    { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23). }
    assert (Hpp108 : add_vec_int (mword_of_int (SX + 0x106) : mword 64) 2
                     = mword_of_int (SX + 0x108)) by pcw.
    iEval (rewrite Hpp108) in "Hpc".
    (* ===== +0x108 c.addi16sp sp,480 : the pop ===== *)
    assert (Hwv : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                    (sign_extend' 64 (caddi16sp_imm (mword_of_int 30 : mword 6)))
                  = sp0)
      by (rewrite HM2sp; apply sx_pop).
    assert (Hpop : (M2 !!! Regidx csp_rs1 : mword 64)
                   = pa_stk (add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                       (sign_extend' 64 (caddi16sp_imm (mword_of_int 30 : mword 6)))) 60)
      by (rewrite Hwv HM2sp; reflexivity).
    iDestruct (sx_rest_join sp0 _ _ Halp Hala with "Hf1 Hf2 Hrest") as "Hstk".
    iEval (rewrite -Hwv) in "Hstk".
    iApply (wp_caddi16sp_pop_s_sconf (mword_of_int (SX + 0x108))
              (mword_of_int 30 : mword 6) M2 (K - 60)%nat 60 b Hpop
              with "Hcg Hpc Hi108 Hstk").
    iIntros (CID3 Hq3) "Hcg Hpc".
    set (M3 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 30 : mword 6))))]> M2).
    iEval (rewrite Kpop) in "Hcg".
    assert (Hpp10a : add_vec_int (mword_of_int (SX + 0x108) : mword 64) 2
                     = mword_of_int (SX + 0x10a)) by pcw.
    iEval (rewrite Hpp10a) in "Hpc".
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2ra | nz]).
    (* ===== +0x10a c.ret ===== *)
    iApply (wp_cret_s_sconf (mword_of_int (SX + 0x10a)) Rra M3 K b
              ltac:(nz) with "Hcg Hpc Hi10a").
    iIntros (CID4 Hq4) "Hcg Hpc".
    iEval (rgne) in "Hpc".
    assert (Hretf : ret_pc (M3 !!! Regidx Rra : mword 64)
                    = ret_pc (m !!! Regidx Rra : mword 64))
      by (rewrite HM3ra; reflexivity).
    iEval (rewrite Hretf) in "Hpc".
    (* ===== THE HANDOVER ===== *)
    assert (Hwv' : add_vec (M2 !!! Regidx csp_rs1 : mword 64)
                     (sign_extend' 64 (caddi16sp_imm (mword_of_int 30 : mword 6)))
                   = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite Hwv; exact Hsp0).
    assert (Csp : (M3 !!! Regidx csp_rs1 : mword 64)
                  = (m !!! Regidx csp_rs1 : mword 64))
      by (rewrite /M3 upd_eq; exact Hwv').
    assert (Cs0 : (M3 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (Crs1 : (M3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2rs1 | nz]).
    assert (Crs2 : (M3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2rs2 | nz]).
    assert (Crs3 : (M3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2rs3 | nz]).
    assert (Crs4 : (M3 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2rs4 | nz]).
    assert (Crs5 : (M3 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2rs5 | nz]).
    assert (Crs6 : (M3 !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2rs6 | nz]).
    assert (Crs7 : (M3 !!! Regidx Rs7 : mword 64) = (m !!! Regidx Rs7 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2rs7 | nz]).
    assert (HM3a0 : (M3 !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2a0 | nz]).
    assert (Hfin : sx_thr m M3).
    { intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23. rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23). }
    iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! M3 with "[%] [%] Hcg Hpc").
    { unfold callee_saved. split_and!;
        [ exact Csp | exact Cs0 | exact Crs1 | exact Crs2 | exact Crs3
        | exact Crs4 | exact Crs5 | exact Crs6 | exact Crs7
        | apply Hfin; scidx | apply Hfin; scidx | apply Hfin; scidx
        | apply Hfin; scidx ]. }
    { exact HM3a0. }
  Qed.

End SysExecEpilogue.

(* ===================================================================== *)
(*  THE BODY.  Eight functor arguments, one per callee.                   *)
(* ===================================================================== *)
Module SysExecProof (Argaddr : ARGADDR) (Argstr : ARGSTR) (Memset : MEMSET)
                    (Fetchaddr : FETCHADDR) (Kalloc : KALLOC)
                    (Fetchstr : FETCHSTR) (Kexec : KEXEC) (Kfree : KFREE)
                    : SYSEXEC.

(* ===================================================================== *)
(*  +0x000 .. +0x026 -- THE PROLOGUE, argaddr and argstr.                 *)
(*                                                                        *)
(*  Owns the FIRST of the three [-1] exits, and it is the odd one: s1..s7 *)
(*  are not spilled until +0x28, so this path reloads nothing and goes    *)
(*  straight to the epilogue with every callee-saved register still at    *)
(*  its entry value.                                                      *)
(* ===================================================================== *)
Section SysExecHead.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac regne :=
    first [ apply not_eq_sym; apply is_cs_idx_true_neq;
            [vm_compute; reflexivity | assumption]
          | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
          | congruence ].
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  Lemma sx_head
      (γf γa : gname) (jp : nat)
      (pid : mword 32) (V : pprivate) (v0 v1 : mword 64)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
    (K_sys_exec <= K)%nat ->
    pv_tf V !! tf_arg_idx 0 = Some v0 ->
    pv_tf V !! tf_arg_idx 1 = Some v1 ->
    locks_below lks "kmem" ->
    sie_cap_gpr KT1 m K b (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) b lks -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int SX : mword 64) -∗
    proc_priv γf (proc_addr jp) pid V -∗
    kalloc_env γa None -∗
    (* ---- THE TWO WAYS OUT, AS ONE CONTINUATION.  Both of them need the
       caller's exit and a [wp_next] is LINEAR, so this block cannot publish
       two of them (kexec.md's block-interface rule): the -1 return, which
       has already been through the epilogue, and the fall-through at
       +0x028 with the path copied in, are one output carrying a
       DISJUNCTION.  The variables the -1 arm does not use are instantiated
       arbitrarily there. ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M : regfile) (P' : uptd) (plen : nat) (pfun : nat -> bv 8)
        (rest : nat -> bv 8) (v59 v60 : mword 64),
        ((⌜ callee_saved m M /\ uptd_ext (pv_upt V) P' /\
             (M !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64) ⌝ ∗
           sie_cap_gpr KT1 M K b (proc_addr jp) ∗
           cpu_own 0 eb (proc_addr jp) b lks ∗
           pc_is (ret_pc (m !!! Regidx Rra : mword 64)) ∗
           proc_priv γf (proc_addr jp) pid (upd_upt V P'))
         ∨
         (⌜ sx_sp (m !!! Regidx csp_rs1 : mword 64) M /\
            (M !!! Regidx Rs0 : mword 64) = (m !!! Regidx csp_rs1 : mword 64) /\
            sx_thr2 m M /\
            uptd_ext (pv_upt V) P' /\ (plen < 128)%nat /\ bb_cstr pfun plen /\
            sx_alp (m !!! Regidx csp_rs1 : mword 64) /\
            sx_ala (m !!! Regidx csp_rs1 : mword 64) ⌝ ∗
          pc_is (mword_of_int (SX + 0x28) : mword 64) ∗
          sie_cap_gpr KT1 M (K - 60)%nat b (proc_addr jp) ∗
          cpu_own 0 eb (proc_addr jp) b lks ∗
          proc_priv γf (proc_addr jp) pid (upd_upt V P') ∗
          (* the frame: ra and s0 spilled, s1..s7 and slot 10 still free,
             the path buffer holding its NUL-terminated string, the argv
             array untouched, and the two out-parameter cells *)
          (pa_stk (m !!! Regidx csp_rs1) 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
          (pa_stk (m !!! Regidx csp_rs1) 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
          (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 3) ↦₈[KT1] w) ∗
          (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 4) ↦₈[KT1] w) ∗
          (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 5) ↦₈[KT1] w) ∗
          (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 6) ↦₈[KT1] w) ∗
          (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 7) ↦₈[KT1] w) ∗
          (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 8) ↦₈[KT1] w) ∗
          (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 9) ↦₈[KT1] w) ∗
          (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 10) ↦₈[KT1] w) ∗
          ([∗ list] j ∈ seq 0 (S plen),
             pa_add (pa_stk (m !!! Regidx csp_rs1) 26) j ↦ₘ[KT1] pfun j) ∗
          ([∗ list] j ∈ seq 0 (127 - plen)%nat,
             pa_add (pa_add (pa_stk (m !!! Regidx csp_rs1) 26) (S plen)) j
               ↦ₘ[KT1] rest j) ∗
          bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk (m !!! Regidx csp_rs1) 58) 256 ∗
          (pa_stk (m !!! Regidx csp_rs1) 59) ↦₈[KT1] v59 ∗
          (pa_stk (m !!! Regidx csp_rs1) 60) ↦₈[KT1] v60)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Harg0 Harg1 Hlb.
    destruct (sx_kb K HK) as (Kkx & Kar & Kaa & Kfa & Kfs & K14 & K2 & K60 & Kpop).
    set (sp0 := m !!! Regidx csp_rs1).
    iIntros "Hcg Hcnt #Htext #Hdata Hpc Hpriv #Hka Hout".
    iPoseProof (sxi_000 with "Htext") as "Hi000".
    iPoseProof (sxi_002 with "Htext") as "Hi002".
    iPoseProof (sxi_004 with "Htext") as "Hi004".
    iPoseProof (sxi_006 with "Htext") as "Hi006".
    iPoseProof (sxi_008 with "Htext") as "Hi008".
    iPoseProof (sxi_00c with "Htext") as "Hi00c".
    iPoseProof (sxi_00e with "Htext") as "Hi00e".
    iPoseProof (sxi_012 with "Htext") as "Hi012".
    iPoseProof (sxi_016 with "Htext") as "Hi016".
    iPoseProof (sxi_01a with "Htext") as "Hi01a".
    iPoseProof (sxi_01c with "Htext") as "Hi01c".
    iPoseProof (sxi_020 with "Htext") as "Hi020".
    iPoseProof (sxi_022 with "Htext") as "Hi022".
    iPoseProof (sxi_024 with "Htext") as "Hi024".
    (* ================= +0x000 c.addi16sp sp,-480 ================= *)
    iApply (wp_caddi16sp_push_s_sconf (mword_of_int SX)
              (mword_of_int 34 : mword 6) m K 60 b ltac:(lia) (sx_push sp0)
              with "Hcg Hpc Hi000").
    iIntros (CID1 Hq1) "Hcg Hstk Hpc".
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec sp0 (sign_extend' 64
                     (caddi16sp_imm (mword_of_int 34 : mword 6))))]> m).
    assert (HM1sp : sx_sp sp0 M1).
    { unfold sx_sp. etransitivity; [ rewrite /M1; apply upd_eq | apply sx_push ]. }
    assert (HM1thr : sx_thr2 m M1).
    { intros c Hc N2 N8.
      rewrite /M1 upd_ne; [reflexivity | congruence]. }
    assert (HM1ra : (M1 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    assert (HM1s0 : (M1 !!! Regidx Rs0 : mword 64) = (m !!! Regidx Rs0 : mword 64))
      by (rewrite /M1 upd_ne; [reflexivity | nz]).
    (* the frame, carved *)
    iDestruct (sx_frame_carve sp0 with "Hstk")
      as "(%Halp & %Hala & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 &
           F59 & F60 & Hpb & Hab)".
    iDestruct "F1" as (u1) "F1". iDestruct "F2" as (u2) "F2".
    iDestruct "F59" as (u59) "F59". iDestruct "F60" as (u60) "F60".
    assert (Hpp002 : add_vec_int (mword_of_int SX : mword 64) 2
                     = mword_of_int (SX + 0x2)) by pcw.
    iEval (rewrite Hpp002) in "Hpc".
    (* ================= +0x002 c.sdsp ra,472(sp) ================= *)
    assert (Hc1 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 59 : mword 6) ('b"000")))
                  = pa_stk sp0 1) by (rewrite HM1sp; apply sx_frm1).
    assert (Hrra : rget M1 Rra = (M1 !!! Regidx Rra : mword 64))
      by (apply rget_ne; nz).
    iEval (rewrite -Hc1) in "F1".
    iApply (wp_csdsp_s_sconf (mword_of_int (SX + 0x2))
              (mword_of_int 59 : mword 6) Rra M1 (K - 60)%nat u1 b
              with "Hcg Hpc Hi002 F1").
    iIntros (CID2 Hq2) "Hcg Hpc F1".
    iEval (rewrite Hc1 Hrra HM1ra) in "F1".
    assert (Hpp004 : add_vec_int (mword_of_int (SX + 0x2) : mword 64) 2
                     = mword_of_int (SX + 0x4)) by pcw.
    iEval (rewrite Hpp004) in "Hpc".
    (* ================= +0x004 c.sdsp s0,464(sp) ================= *)
    assert (Hc2 : add_vec (M1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 58 : mword 6) ('b"000")))
                  = pa_stk sp0 2) by (rewrite HM1sp; apply sx_frm2).
    assert (Hrs0 : rget M1 Rs0 = (M1 !!! Regidx Rs0 : mword 64))
      by (apply rget_ne; nz).
    iEval (rewrite -Hc2) in "F2".
    iApply (wp_csdsp_s_sconf (mword_of_int (SX + 0x4))
              (mword_of_int 58 : mword 6) Rs0 M1 (K - 60)%nat u2 b
              with "Hcg Hpc Hi004 F2").
    iIntros (CID3 Hq3) "Hcg Hpc F2".
    iEval (rewrite Hc2 Hrs0 HM1s0) in "F2".
    assert (Hpp006 : add_vec_int (mword_of_int (SX + 0x4) : mword 64) 2
                     = mword_of_int (SX + 0x6)) by pcw.
    iEval (rewrite Hpp006) in "Hpc".
    (* ================= +0x006 c.addi4spn s0,sp,480 ================= *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (SX + 0x6))
              (Cregidx (mword_of_int 0)) (mword_of_int 120 : mword 8) Rs0
              M1 (K - 60)%nat b ltac:(vm_compute; reflexivity) ltac:(nz)
              ltac:(rdok) with "Hcg Hpc Hi006").
    iIntros (CID4 Hq4) "Hcg Hpc".
    set (M2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (M1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 120 : mword 8))))]> M1).
    assert (HM2s0 : (M2 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite /M2 upd_eq HM1sp. apply sx_fp. }
    assert (HM2sp : sx_sp sp0 M2)
      by (rewrite /sx_sp /M2 upd_ne; [exact HM1sp | nz]).
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M2 upd_ne; [exact HM1ra | nz]).
    assert (HM2thr : sx_thr2 m M2).
    { intros c Hc N2 N8.
      rewrite /M2 upd_ne; [| regne].
      exact (HM1thr c Hc N2 N8). }
    assert (Hpp008 : add_vec_int (mword_of_int (SX + 0x6) : mword 64) 2
                     = mword_of_int (SX + 0x8)) by pcw.
    iEval (rewrite Hpp008) in "Hpc".
    (* ================= +0x008 addi a1,s0,-472 : &uargv ================= *)
    iApply (wp_addi4_s_sconf (mword_of_int (SX + 0x8)) Ra1 Rs0
              (mword_of_int 3624 : mword 12) M2 (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi008").
    iIntros (CID5 Hq5) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (M3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (M2 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3624 : mword 12)))]> M2).
    assert (HM3a1 : (M3 !!! Regidx Ra1 : mword 64) = pa_stk sp0 59).
    { rewrite /M3 upd_eq HM2s0. apply sx_uargv. }
    assert (HM3sp : sx_sp sp0 M3)
      by (rewrite /sx_sp /M3 upd_ne; [exact HM2sp | nz]).
    assert (HM3s0 : (M3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M3 upd_ne; [exact HM2s0 | nz]).
    assert (HM3ra : (M3 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M3 upd_ne; [exact HM2ra | nz]).
    assert (HM3thr : sx_thr2 m M3).
    { intros c Hc N2 N8.
      rewrite /M3 upd_ne; [| regne].
      exact (HM2thr c Hc N2 N8). }
    assert (Hpp00c : add_vec_int (mword_of_int (SX + 0x8) : mword 64) 4
                     = mword_of_int (SX + 0xc)) by pcw.
    iEval (rewrite Hpp00c) in "Hpc".
    (* ================= +0x00c c.li a0,1 ================= *)
    iApply (wp_cli_s_sconf (mword_of_int (SX + 0xc)) Ra0
              (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 64)
              M3 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi00c").
    iIntros (CID6 Hq6) "Hcg Hpc".
    set (M4 := <[Regidx Ra0 := regval_into_reg (mword_of_int 1 : mword 64)]> M3).
    assert (HM4a0 : (M4 !!! Regidx Ra0 : mword 64) = (mword_of_int 1 : mword 64))
      by (rewrite /M4; apply upd_eq).
    assert (HM4a1 : (M4 !!! Regidx Ra1 : mword 64) = pa_stk sp0 59)
      by (rewrite /M4 upd_ne; [exact HM3a1 | nz]).
    assert (HM4sp : sx_sp sp0 M4)
      by (rewrite /sx_sp /M4 upd_ne; [exact HM3sp | nz]).
    assert (HM4s0 : (M4 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M4 upd_ne; [exact HM3s0 | nz]).
    assert (HM4ra : (M4 !!! Regidx Rra : mword 64) = (m !!! Regidx Rra : mword 64))
      by (rewrite /M4 upd_ne; [exact HM3ra | nz]).
    assert (HM4thr : sx_thr2 m M4).
    { intros c Hc N2 N8.
      rewrite /M4 upd_ne; [| regne].
      exact (HM3thr c Hc N2 N8). }
    assert (Hpp00e : add_vec_int (mword_of_int (SX + 0xc) : mword 64) 2
                     = mword_of_int (SX + 0xe)) by pcw.
    iEval (rewrite Hpp00e) in "Hpc".
    (* ================= +0x00e jal ra,argaddr ================= *)
    assert (Htaa : add_vec (mword_of_int (SX + 0xe) : mword 64)
                     (sign_extend' 64 (mword_of_int 2086064 : mword 21))
                   = mword_of_int KernelSyms.argaddr) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (SX + 0xe)) Rra
              (mword_of_int 2086064 : mword 21) M4 (K - 60)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htaa; vm_compute; reflexivity)
              with "Hcg Hpc Hi00e").
    iIntros (CID7 Hq7) "Hcg Hpc". iEval (rewrite Htaa) in "Hpc".
    set (M5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SX + 0xe) : mword 64) 4)]> M4).
    assert (HM5ra : (M5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SX + 0xe) : mword 64) 4)
      by (rewrite /M5; apply upd_eq).
    assert (HM5a0 : (M5 !!! Regidx Ra0 : mword 64) = (mword_of_int 1 : mword 64))
      by (rewrite /M5 upd_ne; [exact HM4a0 | nz]).
    assert (HM5a1 : (M5 !!! Regidx Ra1 : mword 64) = pa_stk sp0 59)
      by (rewrite /M5 upd_ne; [exact HM4a1 | nz]).
    assert (HM5sp : sx_sp sp0 M5)
      by (rewrite /sx_sp /M5 upd_ne; [exact HM4sp | nz]).
    assert (HM5s0 : (M5 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M5 upd_ne; [exact HM4s0 | nz]).
    assert (HM5thr : sx_thr2 m M5).
    { intros c Hc N2 N8.
      rewrite /M5 upd_ne; [| regne].
      exact (HM4thr c Hc N2 N8). }
    (* argaddr wants the trapframe pointer quarter AND the page, as one
       accessor -- and its out-cell is slot 59, which the frame just gave us. *)
    iDestruct (proc_priv_tfp_valid with "Hpriv") as %Hpv.
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hprivback)".
    iEval (rewrite -HM5a1) in "F59".
    iDestruct (cpu_own_transport CID0 CID7 0%nat eb (proc_addr jp) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Argaddr.wp_argaddr_sconf M5 (K - 60)%nat 0%nat eb (proc_addr jp)
              1%nat (ud_tfp (pv_upt V)) (pv_tf V) v1 u59 (DfracOwn (1/4)) b lks
              sx_arg1_lt ltac:(rewrite HM5a0; reflexivity) Harg1 sx_noff0 Kaa
              Hpv
              with "Hcg Hcnt Htext Hdata Hpc Htfc Htfp F59").
    iIntros (CID8 Hq8 M6) "%Hcs6 Hcg Hcnt Hpc Htfc Htfp F59".
    iEval (rewrite HM5a1) in "F59".
    iDestruct ("Hprivback" with "Htfc Htfp") as "Hpriv".
    assert (Hpc012 : ret_pc (M5 !!! Regidx Rra : mword 64)
                     = mword_of_int (SX + 0x12))
      by (rewrite HM5ra; pcw).
    iEval (rewrite Hpc012) in "Hpc".
    assert (HM6sp : sx_sp sp0 M6).
    { rewrite /sx_sp (callee_saved_lookup Hcs6 csp_rs1
                        ltac:(vm_compute; reflexivity)). exact HM5sp. }
    assert (HM6s0 : (M6 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcs6 Rs0 ltac:(vm_compute; reflexivity)).
      exact HM5s0. }
    assert (HM6thr : sx_thr2 m M6).
    { intros c Hc N2 N8.
      rewrite (callee_saved_lookup Hcs6 c Hc).
      exact (HM5thr c Hc N2 N8). }
    (* ================= +0x012 addi a2,zero,128 ================= *)
    iApply (wp_li4_s_sconf (mword_of_int (SX + 0x12)) Ra2
              (mword_of_int 128 : mword 12) (mword_of_int 128 : mword 64)
              M6 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi012").
    iIntros (CID9 Hq9) "Hcg Hpc".
    set (M7 := <[Regidx Ra2 := regval_into_reg (mword_of_int 128 : mword 64)]> M6).
    assert (HM7a2 : (M7 !!! Regidx Ra2 : mword 64) = (mword_of_int 128 : mword 64))
      by (rewrite /M7; apply upd_eq).
    assert (HM7sp : sx_sp sp0 M7)
      by (rewrite /sx_sp /M7 upd_ne; [exact HM6sp | nz]).
    assert (HM7s0 : (M7 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M7 upd_ne; [exact HM6s0 | nz]).
    assert (HM7thr : sx_thr2 m M7).
    { intros c Hc N2 N8.
      rewrite /M7 upd_ne; [| regne].
      exact (HM6thr c Hc N2 N8). }
    assert (Hpp016 : add_vec_int (mword_of_int (SX + 0x12) : mword 64) 4
                     = mword_of_int (SX + 0x16)) by pcw.
    iEval (rewrite Hpp016) in "Hpc".
    (* ================= +0x016 addi a1,s0,-208 : path ================= *)
    iApply (wp_addi4_s_sconf (mword_of_int (SX + 0x16)) Ra1 Rs0
              (mword_of_int 3888 : mword 12) M7 (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi016").
    iIntros (CID10 Hq10) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (M8 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (M7 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3888 : mword 12)))]> M7).
    assert (HM8a1 : (M8 !!! Regidx Ra1 : mword 64) = pa_stk sp0 26).
    { rewrite /M8 upd_eq HM7s0. apply sx_path. }
    assert (HM8a2 : (M8 !!! Regidx Ra2 : mword 64) = (mword_of_int 128 : mword 64))
      by (rewrite /M8 upd_ne; [exact HM7a2 | nz]).
    assert (HM8sp : sx_sp sp0 M8)
      by (rewrite /sx_sp /M8 upd_ne; [exact HM7sp | nz]).
    assert (HM8s0 : (M8 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M8 upd_ne; [exact HM7s0 | nz]).
    assert (HM8thr : sx_thr2 m M8).
    { intros c Hc N2 N8.
      rewrite /M8 upd_ne; [| regne].
      exact (HM7thr c Hc N2 N8). }
    assert (Hpp01a : add_vec_int (mword_of_int (SX + 0x16) : mword 64) 4
                     = mword_of_int (SX + 0x1a)) by pcw.
    iEval (rewrite Hpp01a) in "Hpc".
    (* ================= +0x01a c.li a0,0 ================= *)
    iApply (wp_cli_s_sconf (mword_of_int (SX + 0x1a)) Ra0
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              M8 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi01a").
    iIntros (CID11 Hq11) "Hcg Hpc".
    set (M9 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> M8).
    assert (HM9a0 : (M9 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /M9; apply upd_eq).
    assert (HM9a1 : (M9 !!! Regidx Ra1 : mword 64) = pa_stk sp0 26)
      by (rewrite /M9 upd_ne; [exact HM8a1 | nz]).
    assert (HM9a2 : (M9 !!! Regidx Ra2 : mword 64) = (mword_of_int 128 : mword 64))
      by (rewrite /M9 upd_ne; [exact HM8a2 | nz]).
    assert (HM9sp : sx_sp sp0 M9)
      by (rewrite /sx_sp /M9 upd_ne; [exact HM8sp | nz]).
    assert (HM9s0 : (M9 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M9 upd_ne; [exact HM8s0 | nz]).
    assert (HM9thr : sx_thr2 m M9).
    { intros c Hc N2 N8.
      rewrite /M9 upd_ne; [| regne].
      exact (HM8thr c Hc N2 N8). }
    assert (Hpp01c : add_vec_int (mword_of_int (SX + 0x1a) : mword 64) 2
                     = mword_of_int (SX + 0x1c)) by pcw.
    iEval (rewrite Hpp01c) in "Hpc".
    (* ================= +0x01c jal ra,argstr ================= *)
    assert (Htas : add_vec (mword_of_int (SX + 0x1c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2086078 : mword 21))
                   = mword_of_int KernelSyms.argstr) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (SX + 0x1c)) Rra
              (mword_of_int 2086078 : mword 21) M9 (K - 60)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htas; vm_compute; reflexivity)
              with "Hcg Hpc Hi01c").
    iIntros (CID12 Hq12) "Hcg Hpc". iEval (rewrite Htas) in "Hpc".
    set (M10 := <[Regidx Rra := regval_into_reg
                   (add_vec_int (mword_of_int (SX + 0x1c) : mword 64) 4)]> M9).
    assert (HM10ra : (M10 !!! Regidx Rra : mword 64)
                     = add_vec_int (mword_of_int (SX + 0x1c) : mword 64) 4)
      by (rewrite /M10; apply upd_eq).
    assert (HM10a0 : (M10 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /M10 upd_ne; [exact HM9a0 | nz]).
    assert (HM10a1 : (M10 !!! Regidx Ra1 : mword 64) = pa_stk sp0 26)
      by (rewrite /M10 upd_ne; [exact HM9a1 | nz]).
    assert (HM10a2 : (M10 !!! Regidx Ra2 : mword 64) = (mword_of_int 128 : mword 64))
      by (rewrite /M10 upd_ne; [exact HM9a2 | nz]).
    assert (HM10sp : sx_sp sp0 M10)
      by (rewrite /sx_sp /M10 upd_ne; [exact HM9sp | nz]).
    assert (HM10s0 : (M10 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M10 upd_ne; [exact HM9s0 | nz]).
    assert (HM10thr : sx_thr2 m M10).
    { intros c Hc N2 N8.
      rewrite /M10 upd_ne; [| regne].
      exact (HM9thr c Hc N2 N8). }
    (* the path buffer, named *)
    iDestruct (sx_bytes_name (pa_stk sp0 26) 128 with "Hpb") as (bf) "Hbuf".
    iEval (rewrite -HM10a1) in "Hbuf".
    iDestruct (cpu_own_transport CID8 CID12 0%nat eb (proc_addr jp) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Argstr.wp_argstr_sconf γa γf M10 (K - 60)%nat 0%nat eb
              (proc_addr jp) 0%nat v0 pid V 128%nat bf b lks
              sx_arg0_lt ltac:(rewrite HM10a0; reflexivity) Harg0 sx_noff0 Kar
              ltac:(rewrite HM10a2; reflexivity) sx_maxpath_lt Hlb
              with "Hcg Hcnt Htext Hdata Hpc Hpriv Hka Hbuf").
    iIntros (CID13 Hq13 M11 P' bnew) "%Hcs11 %Hext Hcg Hcnt Hpc Hpriv Hbuf %Hret".
    iEval (rewrite HM10a1) in "Hbuf".
    assert (Hpc020 : ret_pc (M10 !!! Regidx Rra : mword 64)
                     = mword_of_int (SX + 0x20))
      by (rewrite HM10ra; pcw).
    iEval (rewrite Hpc020) in "Hpc".
    assert (HM11sp : sx_sp sp0 M11).
    { rewrite /sx_sp (callee_saved_lookup Hcs11 csp_rs1
                        ltac:(vm_compute; reflexivity)). exact HM10sp. }
    assert (HM11s0 : (M11 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcs11 Rs0 ltac:(vm_compute; reflexivity)).
      exact HM10s0. }
    assert (HM11thr : sx_thr2 m M11).
    { intros c Hc N2 N8.
      rewrite (callee_saved_lookup Hcs11 c Hc).
      exact (HM10thr c Hc N2 N8). }
    (* ================= +0x020 c.mv a5,a0 ================= *)
    iApply (wp_cmv_s_sconf (mword_of_int (SX + 0x20)) Ra5 Ra0
              M11 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi020").
    iIntros (CID14 Hq14) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (M12 := <[Regidx Ra5 := regval_into_reg
                   (add_vec zero_reg (M11 !!! Regidx Ra0))]> M11).
    assert (HM12a5 : (M12 !!! Regidx Ra5 : mword 64) = (M11 !!! Regidx Ra0 : mword 64)).
    { rewrite /M12 upd_eq. apply add_vec_zero_l. }
    assert (HM12sp : sx_sp sp0 M12)
      by (rewrite /sx_sp /M12 upd_ne; [exact HM11sp | nz]).
    assert (HM12s0 : (M12 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M12 upd_ne; [exact HM11s0 | nz]).
    assert (HM12thr : sx_thr2 m M12).
    { intros c Hc N2 N8.
      rewrite /M12 upd_ne; [| regne].
      exact (HM11thr c Hc N2 N8). }
    assert (Hpp022 : add_vec_int (mword_of_int (SX + 0x20) : mword 64) 2
                     = mword_of_int (SX + 0x22)) by pcw.
    iEval (rewrite Hpp022) in "Hpc".
    (* ================= +0x022 c.li a0,-1 ================= *)
    iApply (wp_cli_s_sconf (mword_of_int (SX + 0x22)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              M12 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi022").
    iIntros (CID15 Hq15) "Hcg Hpc".
    set (M13 := <[Regidx Ra0 := regval_into_reg (mword_of_int (-1) : mword 64)]> M12).
    assert (HM13a0 : (M13 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
      by (rewrite /M13; apply upd_eq).
    assert (HM13a5 : (M13 !!! Regidx Ra5 : mword 64) = (M11 !!! Regidx Ra0 : mword 64))
      by (rewrite /M13 upd_ne; [exact HM12a5 | nz]).
    assert (HM13sp : sx_sp sp0 M13)
      by (rewrite /sx_sp /M13 upd_ne; [exact HM12sp | nz]).
    assert (HM13s0 : (M13 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /M13 upd_ne; [exact HM12s0 | nz]).
    assert (HM13thr : sx_thr2 m M13).
    { intros c Hc N2 N8.
      rewrite /M13 upd_ne; [| regne].
      exact (HM12thr c Hc N2 N8). }
    assert (Hpp024 : add_vec_int (mword_of_int (SX + 0x22) : mword 64) 2
                     = mword_of_int (SX + 0x24)) by pcw.
    iEval (rewrite Hpp024) in "Hpc".
    (* ================= +0x024 blt a5,zero,+0x104 ================= *)
    assert (Hra5 : rget M13 Ra5 = (M13 !!! Regidx Ra5 : mword 64))
      by (apply rget_ne; nz).
    destruct Hret as [(k & Hklt & Hkstr & Hka0) | Hm1].
    - (* ---- argstr SUCCEEDED: a5 = k >= 0, fall through to +0x028 ---- *)
      assert (Hcmp : zopz0zI_s (rget M13 Ra5) zero_reg = false).
      { rewrite Hra5 HM13a5 Hka0. apply sx_nonneg.
        exact (sx_len_range k 128 Hklt sx_maxpath_lt). }
      iApply (wp_blt_x0_fall_s_sconf (mword_of_int (SX + 0x24))
                (mword_of_int 224 : mword 13) Ra5 M13 (K - 60)%nat b
                ltac:(nz) Hcmp with "Hcg Hpc Hi024").
      iIntros (CID16 Hq16) "Hcg Hpc".
      assert (Hpp028 : add_vec_int (mword_of_int (SX + 0x24) : mword 64) 4
                       = mword_of_int (SX + 0x28)) by pcw.
      iEval (rewrite Hpp028) in "Hpc".
      iDestruct (sx_buf_split (pa_stk sp0 26) bnew k Hklt with "Hbuf")
        as "[Hpre Hsuf]".
      iDestruct (cpu_own_transport CID13 CID16 0%nat eb (proc_addr jp) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hout" $! CID16 with "[%]"); [wp_next_chain |].
      iApply ("Hout" $! M13 P' k bnew (fun j => bnew (S k + j)%nat) v1 u60).
      iRight.
      iSplitR; [iPureIntro; split_and!;
        [ exact HM13sp | exact HM13s0 | exact HM13thr | exact Hext
        | exact Hklt | exact Hkstr | exact Halp | exact Hala ] |].
      iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
      iSplitL "Hcnt"; [iExact "Hcnt" |]. iSplitL "Hpriv"; [iExact "Hpriv" |].
      iSplitL "F1"; [iExact "F1" |]. iSplitL "F2"; [iExact "F2" |].
      iSplitL "F3"; [iExact "F3" |]. iSplitL "F4"; [iExact "F4" |].
      iSplitL "F5"; [iExact "F5" |]. iSplitL "F6"; [iExact "F6" |].
      iSplitL "F7"; [iExact "F7" |]. iSplitL "F8"; [iExact "F8" |].
      iSplitL "F9"; [iExact "F9" |]. iSplitL "F10"; [iExact "F10" |].
      iSplitL "Hpre"; [iExact "Hpre" |]. iSplitL "Hsuf"; [iExact "Hsuf" |].
      iSplitL "Hab"; [iExact "Hab" |].
      iSplitL "F59"; [iExact "F59" | iExact "F60"].
    - (* ---- argstr FAILED: a5 = -1, take the branch to +0x104 ---- *)
      assert (Hcmp : zopz0zI_s (rget M13 Ra5) zero_reg = true).
      { rewrite Hra5 HM13a5 Hm1. exact sx_m1_neg. }
      assert (Htgt : add_vec (mword_of_int (SX + 0x24) : mword 64)
                       (sign_extend' 64 (mword_of_int 224 : mword 13))
                     = mword_of_int (SX + 0x104)) by pcw.
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (SX + 0x24))
                (mword_of_int 224 : mword 13) Ra5 M13 (K - 60)%nat b
                ltac:(nz) Hcmp
                ltac:(rewrite Htgt; vm_compute; reflexivity)
                with "Hcg Hpc Hi024").
      iIntros (CID16 Hq16). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htgt) in "Hpc".
      (* the frame goes back WHOLE: nothing below slot 2 was written, and
         s1..s7 were never spilled, so the epilogue's seven premises are
         [sx_thr2]'s and the caller's block is unchanged. *)
      iDestruct (sx_name_bytes (pa_stk sp0 26) 128 bnew with "Hbuf") as "Hpb".
      iAssert (sx_rest sp0) with "[F3 F4 F5 F6 F7 F8 F9 F10 F59 F60 Hpb Hab]"
        as "Hrest".
      { rewrite /sx_rest.
        iSplitL "F3"; [iExact "F3" |]. iSplitL "F4"; [iExact "F4" |].
        iSplitL "F5"; [iExact "F5" |]. iSplitL "F6"; [iExact "F6" |].
        iSplitL "F7"; [iExact "F7" |]. iSplitL "F8"; [iExact "F8" |].
        iSplitL "F9"; [iExact "F9" |]. iSplitL "F10"; [iExact "F10" |].
        iSplitL "F59"; [iExists v1; iExact "F59" |].
        iSplitL "F60"; [iExists u60; iExact "F60" |].
        iSplitL "Hpb"; [iExact "Hpb" | iExact "Hab"]. }
      iApply (sx_epilogue (CID0 := CID16) m M13 sp0 K b (proc_addr jp)
                K60 Kpop eq_refl HM13sp (sx_thr2_thr _ _ HM13thr)
                (HM13thr Rs1 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))
                (HM13thr Rs2 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))
                (HM13thr Rs3 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))
                (HM13thr Rs4 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))
                (HM13thr Rs5 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))
                (HM13thr Rs6 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))
                (HM13thr Rs7 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))
                Halp Hala with "Hcg Htext Hpc F1 F2 Hrest [Hcnt Hpriv Hout]").
      iIntros (CID17) "%Hq17". iIntros (mf) "%Hcsf %Hfa0 Hcg Hpc".
      iDestruct (cpu_own_transport CID13 CID17 0%nat eb (proc_addr jp) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hout" $! CID17 with "[%]"); [wp_next_chain |].
      iApply ("Hout" $! mf P' 0%nat bnew bnew v1 u60). iLeft.
      iSplitR; [iPureIntro; split_and!;
        [ exact Hcsf | exact Hext | rewrite Hfa0; exact HM13a0 ] |].
      iSplitL "Hcg"; [iExact "Hcg" |]. iSplitL "Hcnt"; [iExact "Hcnt" |].
      iSplitL "Hpc"; [iExact "Hpc" | iExact "Hpriv"].
  Qed.

End SysExecHead.

(* ===================================================================== *)
(*  +0x028 .. +0x054 -- THE LAZY SPILLS, memset, and the loop's six       *)
(*  register initialisations.  Straight-line, no exits.                   *)
(*                                                                        *)
(*  [memset] writes BYTES and argv is read as WORDS: [sx_zeros_slots] is  *)
(*  what carries the zero across, and the file header says why nothing    *)
(*  weaker will do.                                                       *)
(* ===================================================================== *)
Section SysExecSetup.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).

  Local Ltac regne :=
    first [ apply not_eq_sym; apply is_cs_idx_true_neq;
            [vm_compute; reflexivity | assumption]
          | apply is_cs_idx_true_neq; [vm_compute; reflexivity | assumption]
          | congruence ].
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  Lemma sx_setup (m M : regfile) (sp0 : mword 64) (K : nat) (b : bool)
      (pj : mword 64) :
    (K_sys_exec <= K)%nat ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    sx_sp sp0 M -> (M !!! Regidx Rs0 : mword 64) = sp0 -> sx_thr2 m M ->
    sx_ala sp0 ->
    sie_cap_gpr KT1 M (K - 60)%nat b pj -∗
    kernel_text -∗ pc_is (mword_of_int (SX + 0x28) : mword 64) -∗
    (∃ w : mword 64, (pa_stk sp0 3) ↦₈[KT1] w) -∗
    (∃ w : mword 64, (pa_stk sp0 4) ↦₈[KT1] w) -∗
    (∃ w : mword 64, (pa_stk sp0 5) ↦₈[KT1] w) -∗
    (∃ w : mword 64, (pa_stk sp0 6) ↦₈[KT1] w) -∗
    (∃ w : mword 64, (pa_stk sp0 7) ↦₈[KT1] w) -∗
    (∃ w : mword 64, (pa_stk sp0 8) ↦₈[KT1] w) -∗
    (∃ w : mword 64, (pa_stk sp0 9) ↦₈[KT1] w) -∗
    bytes_own (KTR := KT1) (DfracOwn 1) (pa_stk sp0 58) 256 -∗
    wp_next b pj (fun (CID : CpuId) =>
      ∀ M' : regfile,
        ⌜ sx_sp sp0 M' /\ sx_thr m M' /\
          (M' !!! Regidx Rs0 : mword 64) = sp0 /\
          (M' !!! Regidx Rs1 : mword 64) = pa_stk sp0 58 /\
          (M' !!! Regidx Rs2 : mword 64) = (mword_of_int 0 : mword 64) /\
          (M' !!! Regidx Rs3 : mword 64) = pa_stk sp0 58 /\
          (M' !!! Regidx Rs4 : mword 64) = pa_stk sp0 58 /\
          (M' !!! Regidx Rs5 : mword 64) = pa_stk sp0 60 /\
          (M' !!! Regidx Rs6 : mword 64) = (mword_of_int 4096 : mword 64) /\
          (M' !!! Regidx Rs7 : mword 64) = (mword_of_int 32 : mword 64) ⌝ -∗
        pc_is (mword_of_int (SX + 0x56) : mword 64) -∗
        sie_cap_gpr KT1 M' (K - 60)%nat b pj -∗
        (* the seven spill slots, at the values the epilogue reloads *)
        (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) -∗
        (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) -∗
        (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) -∗
        (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) -∗
        (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) -∗
        (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) -∗
        (pa_stk sp0 9) ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) -∗
        (* argv, zeroed, as thirty-two WORDS *)
        ([∗ list] i ∈ seq 0 32,
           (pa_stk sp0 (58 - i)) ↦₈[KT1] (mword_of_int 0 : mword 64)) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp0 HMsp HMs0 HMthr Hala.
    destruct (sx_kb K HK) as (Kkx & Kar & Kaa & Kfa & Kfs & K14 & K2 & K60 & Kpop).
    iIntros "Hcg #Htext Hpc F3 F4 F5 F6 F7 F8 F9 Hab Hout".
    iPoseProof (sxi_028 with "Htext") as "Hi028".
    iPoseProof (sxi_02a with "Htext") as "Hi02a".
    iPoseProof (sxi_02c with "Htext") as "Hi02c".
    iPoseProof (sxi_02e with "Htext") as "Hi02e".
    iPoseProof (sxi_030 with "Htext") as "Hi030".
    iPoseProof (sxi_032 with "Htext") as "Hi032".
    iPoseProof (sxi_034 with "Htext") as "Hi034".
    iPoseProof (sxi_036 with "Htext") as "Hi036".
    iPoseProof (sxi_03a with "Htext") as "Hi03a".
    iPoseProof (sxi_03e with "Htext") as "Hi03e".
    iPoseProof (sxi_040 with "Htext") as "Hi040".
    iPoseProof (sxi_042 with "Htext") as "Hi042".
    iPoseProof (sxi_046 with "Htext") as "Hi046".
    iPoseProof (sxi_048 with "Htext") as "Hi048".
    iPoseProof (sxi_04a with "Htext") as "Hi04a".
    iPoseProof (sxi_04c with "Htext") as "Hi04c".
    iPoseProof (sxi_050 with "Htext") as "Hi050".
    iPoseProof (sxi_052 with "Htext") as "Hi052".
    iDestruct "F3" as (u3) "F3".
    iDestruct "F4" as (u4) "F4".
    iDestruct "F5" as (u5) "F5".
    iDestruct "F6" as (u6) "F6".
    iDestruct "F7" as (u7) "F7".
    iDestruct "F8" as (u8) "F8".
    iDestruct "F9" as (u9) "F9".
    (* ===== +0x028 c.sdsp Rs1 ===== *)
    assert (Hc3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 57 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite HMsp; apply sx_frm3).
    assert (Hg3 : rget M Rs1 = (M !!! Regidx Rs1 : mword 64))
      by (apply rget_ne; nz).
    iEval (rewrite -Hc3) in "F3".
    iApply (wp_csdsp_s_sconf (mword_of_int (SX + 0x28))
              (mword_of_int 57 : mword 6) Rs1 M (K - 60)%nat u3 b
              with "Hcg Hpc Hi028 F3").
    iIntros (CIDs3 Hqs3) "Hcg Hpc F3".
    iEval (rewrite Hc3 Hg3 (HMthr Rs1 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))) in "F3".
    assert (Hps3 : add_vec_int (mword_of_int (SX + 0x28) : mword 64) 2
                   = mword_of_int (SX + 0x2a)) by pcw.
    iEval (rewrite Hps3) in "Hpc".
    (* ===== +0x02a c.sdsp Rs2 ===== *)
    assert (Hc4 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 56 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite HMsp; apply sx_frm4).
    assert (Hg4 : rget M Rs2 = (M !!! Regidx Rs2 : mword 64))
      by (apply rget_ne; nz).
    iEval (rewrite -Hc4) in "F4".
    iApply (wp_csdsp_s_sconf (mword_of_int (SX + 0x2a))
              (mword_of_int 56 : mword 6) Rs2 M (K - 60)%nat u4 b
              with "Hcg Hpc Hi02a F4").
    iIntros (CIDs4 Hqs4) "Hcg Hpc F4".
    iEval (rewrite Hc4 Hg4 (HMthr Rs2 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))) in "F4".
    assert (Hps4 : add_vec_int (mword_of_int (SX + 0x2a) : mword 64) 2
                   = mword_of_int (SX + 0x2c)) by pcw.
    iEval (rewrite Hps4) in "Hpc".
    (* ===== +0x02c c.sdsp Rs3 ===== *)
    assert (Hc5 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 55 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite HMsp; apply sx_frm5).
    assert (Hg5 : rget M Rs3 = (M !!! Regidx Rs3 : mword 64))
      by (apply rget_ne; nz).
    iEval (rewrite -Hc5) in "F5".
    iApply (wp_csdsp_s_sconf (mword_of_int (SX + 0x2c))
              (mword_of_int 55 : mword 6) Rs3 M (K - 60)%nat u5 b
              with "Hcg Hpc Hi02c F5").
    iIntros (CIDs5 Hqs5) "Hcg Hpc F5".
    iEval (rewrite Hc5 Hg5 (HMthr Rs3 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))) in "F5".
    assert (Hps5 : add_vec_int (mword_of_int (SX + 0x2c) : mword 64) 2
                   = mword_of_int (SX + 0x2e)) by pcw.
    iEval (rewrite Hps5) in "Hpc".
    (* ===== +0x02e c.sdsp Rs4 ===== *)
    assert (Hc6 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 54 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (rewrite HMsp; apply sx_frm6).
    assert (Hg6 : rget M Rs4 = (M !!! Regidx Rs4 : mword 64))
      by (apply rget_ne; nz).
    iEval (rewrite -Hc6) in "F6".
    iApply (wp_csdsp_s_sconf (mword_of_int (SX + 0x2e))
              (mword_of_int 54 : mword 6) Rs4 M (K - 60)%nat u6 b
              with "Hcg Hpc Hi02e F6").
    iIntros (CIDs6 Hqs6) "Hcg Hpc F6".
    iEval (rewrite Hc6 Hg6 (HMthr Rs4 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))) in "F6".
    assert (Hps6 : add_vec_int (mword_of_int (SX + 0x2e) : mword 64) 2
                   = mword_of_int (SX + 0x30)) by pcw.
    iEval (rewrite Hps6) in "Hpc".
    (* ===== +0x030 c.sdsp Rs5 ===== *)
    assert (Hc7 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 53 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite HMsp; apply sx_frm7).
    assert (Hg7 : rget M Rs5 = (M !!! Regidx Rs5 : mword 64))
      by (apply rget_ne; nz).
    iEval (rewrite -Hc7) in "F7".
    iApply (wp_csdsp_s_sconf (mword_of_int (SX + 0x30))
              (mword_of_int 53 : mword 6) Rs5 M (K - 60)%nat u7 b
              with "Hcg Hpc Hi030 F7").
    iIntros (CIDs7 Hqs7) "Hcg Hpc F7".
    iEval (rewrite Hc7 Hg7 (HMthr Rs5 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))) in "F7".
    assert (Hps7 : add_vec_int (mword_of_int (SX + 0x30) : mword 64) 2
                   = mword_of_int (SX + 0x32)) by pcw.
    iEval (rewrite Hps7) in "Hpc".
    (* ===== +0x032 c.sdsp Rs6 ===== *)
    assert (Hc8 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 52 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite HMsp; apply sx_frm8).
    assert (Hg8 : rget M Rs6 = (M !!! Regidx Rs6 : mword 64))
      by (apply rget_ne; nz).
    iEval (rewrite -Hc8) in "F8".
    iApply (wp_csdsp_s_sconf (mword_of_int (SX + 0x32))
              (mword_of_int 52 : mword 6) Rs6 M (K - 60)%nat u8 b
              with "Hcg Hpc Hi032 F8").
    iIntros (CIDs8 Hqs8) "Hcg Hpc F8".
    iEval (rewrite Hc8 Hg8 (HMthr Rs6 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))) in "F8".
    assert (Hps8 : add_vec_int (mword_of_int (SX + 0x32) : mword 64) 2
                   = mword_of_int (SX + 0x34)) by pcw.
    iEval (rewrite Hps8) in "Hpc".
    (* ===== +0x034 c.sdsp Rs7 ===== *)
    assert (Hc9 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 51 : mword 6) ('b"000")))
                  = pa_stk sp0 9) by (rewrite HMsp; apply sx_frm9).
    assert (Hg9 : rget M Rs7 = (M !!! Regidx Rs7 : mword 64))
      by (apply rget_ne; nz).
    iEval (rewrite -Hc9) in "F9".
    iApply (wp_csdsp_s_sconf (mword_of_int (SX + 0x34))
              (mword_of_int 51 : mword 6) Rs7 M (K - 60)%nat u9 b
              with "Hcg Hpc Hi034 F9").
    iIntros (CIDs9 Hqs9) "Hcg Hpc F9".
    iEval (rewrite Hc9 Hg9 (HMthr Rs7 ltac:(vm_compute; reflexivity) ltac:(nz) ltac:(nz))) in "F9".
    assert (Hps9 : add_vec_int (mword_of_int (SX + 0x34) : mword 64) 2
                   = mword_of_int (SX + 0x36)) by pcw.
    iEval (rewrite Hps9) in "Hpc".
    (* ===== +0x036 addi s4,s0,-464 : s4 = argv ===== *)
    assert (HMs0' : (M !!! Regidx Rs0 : mword 64) = sp0) by exact HMs0.
    iApply (wp_addi4_s_sconf (mword_of_int (SX + 0x36)) Rs4 Rs0
              (mword_of_int 3632 : mword 12) M (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi036").
    iIntros (CIDa1 Hqa1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N1 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (M !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3632 : mword 12)))]> M).
    assert (HN1s4 : (N1 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58).
    { rewrite /N1 upd_eq HMs0'. apply sx_argv. }
    assert (HN1sp : sx_sp sp0 N1)
      by (rewrite /sx_sp /N1 upd_ne; [exact HMsp | nz]).
    assert (HN1s0 : (N1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /N1 upd_ne; [exact HMs0' | nz]).
    assert (Hpa1 : add_vec_int (mword_of_int (SX + 0x36) : mword 64) 4
                   = mword_of_int (SX + 0x3a)) by pcw.
    iEval (rewrite Hpa1) in "Hpc".
    (* ===== +0x03a addi a2,zero,256 ===== *)
    iApply (wp_li4_s_sconf (mword_of_int (SX + 0x3a)) Ra2
              (mword_of_int 256 : mword 12) (mword_of_int 256 : mword 64)
              N1 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi03a").
    iIntros (CIDa2 Hqa2) "Hcg Hpc".
    set (N2 := <[Regidx Ra2 := regval_into_reg (mword_of_int 256 : mword 64)]> N1).
    assert (HN2a2 : (N2 !!! Regidx Ra2 : mword 64) = (mword_of_int 256 : mword 64))
      by (rewrite /N2; apply upd_eq).
    assert (HN2s4 : (N2 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58)
      by (rewrite /N2 upd_ne; [exact HN1s4 | nz]).
    assert (HN2sp : sx_sp sp0 N2)
      by (rewrite /sx_sp /N2 upd_ne; [exact HN1sp | nz]).
    assert (HN2s0 : (N2 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /N2 upd_ne; [exact HN1s0 | nz]).
    assert (Hpa2 : add_vec_int (mword_of_int (SX + 0x3a) : mword 64) 4
                   = mword_of_int (SX + 0x3e)) by pcw.
    iEval (rewrite Hpa2) in "Hpc".
    (* ===== +0x03e c.li a1,0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (SX + 0x3e)) Ra1
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              N2 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi03e").
    iIntros (CIDa3 Hqa3) "Hcg Hpc".
    set (N3 := <[Regidx Ra1 := regval_into_reg (mword_of_int 0 : mword 64)]> N2).
    assert (HN3a1 : (N3 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /N3; apply upd_eq).
    assert (HN3a2 : (N3 !!! Regidx Ra2 : mword 64) = (mword_of_int 256 : mword 64))
      by (rewrite /N3 upd_ne; [exact HN2a2 | nz]).
    assert (HN3s4 : (N3 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58)
      by (rewrite /N3 upd_ne; [exact HN2s4 | nz]).
    assert (HN3sp : sx_sp sp0 N3)
      by (rewrite /sx_sp /N3 upd_ne; [exact HN2sp | nz]).
    assert (HN3s0 : (N3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /N3 upd_ne; [exact HN2s0 | nz]).
    assert (Hpa3 : add_vec_int (mword_of_int (SX + 0x3e) : mword 64) 2
                   = mword_of_int (SX + 0x40)) by pcw.
    iEval (rewrite Hpa3) in "Hpc".
    (* ===== +0x040 c.mv a0,s4 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (SX + 0x40)) Ra0 Rs4
              N3 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi040").
    iIntros (CIDa4 Hqa4) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (N3 !!! Regidx Rs4))]> N3).
    assert (HN4a0 : (N4 !!! Regidx Ra0 : mword 64) = pa_stk sp0 58).
    { rewrite /N4 upd_eq HN3s4. apply add_vec_zero_l. }
    assert (HN4a1 : (N4 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /N4 upd_ne; [exact HN3a1 | nz]).
    assert (HN4a2 : (N4 !!! Regidx Ra2 : mword 64) = (mword_of_int 256 : mword 64))
      by (rewrite /N4 upd_ne; [exact HN3a2 | nz]).
    assert (HN4s4 : (N4 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58)
      by (rewrite /N4 upd_ne; [exact HN3s4 | nz]).
    assert (HN4sp : sx_sp sp0 N4)
      by (rewrite /sx_sp /N4 upd_ne; [exact HN3sp | nz]).
    assert (HN4s0 : (N4 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /N4 upd_ne; [exact HN3s0 | nz]).
    assert (Hpa4 : add_vec_int (mword_of_int (SX + 0x40) : mword 64) 2
                   = mword_of_int (SX + 0x42)) by pcw.
    iEval (rewrite Hpa4) in "Hpc".
    (* ===== +0x042 jal memset ===== *)
    assert (Htms : add_vec (mword_of_int (SX + 0x42) : mword 64)
                     (sign_extend' 64 (mword_of_int 2078910 : mword 21))
                   = mword_of_int KernelSyms.memset) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (SX + 0x42)) Rra
              (mword_of_int 2078910 : mword 21) N4 (K - 60)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htms; vm_compute; reflexivity)
              with "Hcg Hpc Hi042").
    iIntros (CIDa5 Hqa5) "Hcg Hpc". iEval (rewrite Htms) in "Hpc".
    set (N5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SX + 0x42) : mword 64) 4)]> N4).
    assert (HN5ra : (N5 !!! Regidx Rra : mword 64)
                    = add_vec_int (mword_of_int (SX + 0x42) : mword 64) 4)
      by (rewrite /N5; apply upd_eq).
    assert (HN5a0 : (N5 !!! Regidx Ra0 : mword 64) = pa_stk sp0 58)
      by (rewrite /N5 upd_ne; [exact HN4a0 | nz]).
    assert (HN5a1 : (N5 !!! Regidx Ra1 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /N5 upd_ne; [exact HN4a1 | nz]).
    assert (HN5a2 : (N5 !!! Regidx Ra2 : mword 64) = (mword_of_int 256 : mword 64))
      by (rewrite /N5 upd_ne; [exact HN4a2 | nz]).
    assert (HN5s4 : (N5 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58)
      by (rewrite /N5 upd_ne; [exact HN4s4 | nz]).
    assert (HN5sp : sx_sp sp0 N5)
      by (rewrite /sx_sp /N5 upd_ne; [exact HN4sp | nz]).
    assert (HN5s0 : (N5 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /N5 upd_ne; [exact HN4s0 | nz]).
    iDestruct (sx_bytes_name (pa_stk sp0 58) 256 with "Hab") as (af) "Haz".
    iEval (rewrite -HN5a0) in "Haz".
    iApply (Memset.wp_memset_sconf KT1 KT1 N5 (K - 60)%nat 256%nat
              (mword_of_int 0 : mword 64) af b pj
              K2 ltac:(lia) HN5a1 HN5a2 with "Hcg Htext Hpc Haz").
    iIntros (CIDa6 Hqa6 N6) "Hcg Hpc Haz %Hcsa6".
    iEval (rewrite HN5a0) in "Haz".
    assert (HN6sp : sx_sp sp0 N6).
    { rewrite /sx_sp (callee_saved_lookup Hcsa6 csp_rs1
                        ltac:(vm_compute; reflexivity)). exact HN5sp. }
    assert (HN6s0 : (N6 !!! Regidx Rs0 : mword 64) = sp0).
    { rewrite (callee_saved_lookup Hcsa6 Rs0 ltac:(vm_compute; reflexivity)).
      exact HN5s0. }
    assert (HN6s4 : (N6 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58).
    { rewrite (callee_saved_lookup Hcsa6 Rs4 ltac:(vm_compute; reflexivity)).
      exact HN5s4. }
    assert (Hpcret : ret_pc (N5 !!! Regidx Rra : mword 64)
                     = mword_of_int (SX + 0x46)) by (rewrite HN5ra; pcw).
    iEval (rewrite Hpcret) in "Hpc".
    (* ===== +0x046 c.mv Rs1,s4 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (SX + 0x46)) Rs1 Rs4
              N6 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi046").
    iIntros (CIDb46 Hqb46) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P1 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (N6 !!! Regidx Rs4))]> N6).
    assert (HP1s1 : (P1 !!! Regidx Rs1 : mword 64) = pa_stk sp0 58).
    { rewrite /P1 upd_eq HN6s4. apply add_vec_zero_l. }
    assert (HP1s4 : (P1 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58)
      by (rewrite /P1 upd_ne; [exact HN6s4 | nz]).
    assert (HP1s0 : (P1 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P1 upd_ne; [exact HN6s0 | nz]).
    assert (HP1sp : sx_sp sp0 P1)
      by (rewrite /sx_sp /P1 upd_ne; [exact HN6sp | nz]).
    assert (Hpb46 : add_vec_int (mword_of_int (SX + 0x46) : mword 64) 2
                   = mword_of_int (SX + 0x48)) by pcw.
    iEval (rewrite Hpb46) in "Hpc".
    (* ===== +0x048 c.mv Rs3,s4 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (SX + 0x48)) Rs3 Rs4
              P1 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi048").
    iIntros (CIDb48 Hqb48) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P2 := <[Regidx Rs3 := regval_into_reg
                  (add_vec zero_reg (P1 !!! Regidx Rs4))]> P1).
    assert (HP2s3 : (P2 !!! Regidx Rs3 : mword 64) = pa_stk sp0 58).
    { rewrite /P2 upd_eq HP1s4. apply add_vec_zero_l. }
    assert (HP2s4 : (P2 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58)
      by (rewrite /P2 upd_ne; [exact HP1s4 | nz]).
    assert (HP2s0 : (P2 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P2 upd_ne; [exact HP1s0 | nz]).
    assert (HP2sp : sx_sp sp0 P2)
      by (rewrite /sx_sp /P2 upd_ne; [exact HP1sp | nz]).
    assert (HP2s1 : (P2 !!! Regidx Rs1 : mword 64) = pa_stk sp0 58)
      by (rewrite /P2 upd_ne; [exact HP1s1 | nz]).
    assert (Hpb48 : add_vec_int (mword_of_int (SX + 0x48) : mword 64) 2
                   = mword_of_int (SX + 0x4a)) by pcw.
    iEval (rewrite Hpb48) in "Hpc".
    (* ===== +0x04a c.li s2,0 ===== *)
    iApply (wp_cli_s_sconf (mword_of_int (SX + 0x4a)) Rs2
              (mword_of_int 0 : mword 6) (mword_of_int 0 : mword 64)
              P2 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi04a").
    iIntros (CIDb3 Hqb3) "Hcg Hpc".
    set (P3 := <[Regidx Rs2 := regval_into_reg (mword_of_int 0 : mword 64)]> P2).
    assert (HP3s2 : (P3 !!! Regidx Rs2 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /P3; apply upd_eq).
    assert (HP3s1 : (P3 !!! Regidx Rs1 : mword 64) = pa_stk sp0 58)
      by (rewrite /P3 upd_ne; [exact HP2s1 | nz]).
    assert (HP3s3 : (P3 !!! Regidx Rs3 : mword 64) = pa_stk sp0 58)
      by (rewrite /P3 upd_ne; [exact HP2s3 | nz]).
    assert (HP3s4 : (P3 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58)
      by (rewrite /P3 upd_ne; [exact HP2s4 | nz]).
    assert (HP3s0 : (P3 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P3 upd_ne; [exact HP2s0 | nz]).
    assert (HP3sp : sx_sp sp0 P3)
      by (rewrite /sx_sp /P3 upd_ne; [exact HP2sp | nz]).
    assert (Hpb4 : add_vec_int (mword_of_int (SX + 0x4a) : mword 64) 2
                   = mword_of_int (SX + 0x4c)) by pcw.
    iEval (rewrite Hpb4) in "Hpc".
    (* ===== +0x04c addi s5,s0,-480 : &uarg ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (SX + 0x4c)) Rs5 Rs0
              (mword_of_int 3616 : mword 12) P3 (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi04c").
    iIntros (CIDb5 Hqb5) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (P4 := <[Regidx Rs5 := regval_into_reg
                  (add_vec (P3 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3616 : mword 12)))]> P3).
    assert (HP4s5 : (P4 !!! Regidx Rs5 : mword 64) = pa_stk sp0 60).
    { rewrite /P4 upd_eq HP3s0. apply sx_uarg. }
    assert (HP4s1 : (P4 !!! Regidx Rs1 : mword 64) = pa_stk sp0 58)
      by (rewrite /P4 upd_ne; [exact HP3s1 | nz]).
    assert (HP4s2 : (P4 !!! Regidx Rs2 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /P4 upd_ne; [exact HP3s2 | nz]).
    assert (HP4s3 : (P4 !!! Regidx Rs3 : mword 64) = pa_stk sp0 58)
      by (rewrite /P4 upd_ne; [exact HP3s3 | nz]).
    assert (HP4s4 : (P4 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58)
      by (rewrite /P4 upd_ne; [exact HP3s4 | nz]).
    assert (HP4s0 : (P4 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P4 upd_ne; [exact HP3s0 | nz]).
    assert (HP4sp : sx_sp sp0 P4)
      by (rewrite /sx_sp /P4 upd_ne; [exact HP3sp | nz]).
    assert (Hpb6 : add_vec_int (mword_of_int (SX + 0x4c) : mword 64) 4
                   = mword_of_int (SX + 0x50)) by pcw.
    iEval (rewrite Hpb6) in "Hpc".
    (* ===== +0x050 c.lui s6,1 : PGSIZE ===== *)
    iApply (wp_clui_s_sconf (mword_of_int (SX + 0x50)) Rs6
              (sign_extend' 20 (mword_of_int 1 : mword 6))
              (mword_of_int 4096 : mword 64) P4 (K - 60)%nat b
              ltac:(nz) ltac:(rdok) ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi050").
    iIntros (CIDb7 Hqb7) "Hcg Hpc".
    set (P5 := <[Regidx Rs6 := regval_into_reg (mword_of_int 4096 : mword 64)]> P4).
    assert (HP5s6 : (P5 !!! Regidx Rs6 : mword 64) = (mword_of_int 4096 : mword 64))
      by (rewrite /P5; apply upd_eq).
    assert (HP5s1 : (P5 !!! Regidx Rs1 : mword 64) = pa_stk sp0 58)
      by (rewrite /P5 upd_ne; [exact HP4s1 | nz]).
    assert (HP5s2 : (P5 !!! Regidx Rs2 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /P5 upd_ne; [exact HP4s2 | nz]).
    assert (HP5s3 : (P5 !!! Regidx Rs3 : mword 64) = pa_stk sp0 58)
      by (rewrite /P5 upd_ne; [exact HP4s3 | nz]).
    assert (HP5s4 : (P5 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58)
      by (rewrite /P5 upd_ne; [exact HP4s4 | nz]).
    assert (HP5s5 : (P5 !!! Regidx Rs5 : mword 64) = pa_stk sp0 60)
      by (rewrite /P5 upd_ne; [exact HP4s5 | nz]).
    assert (HP5s0 : (P5 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P5 upd_ne; [exact HP4s0 | nz]).
    assert (HP5sp : sx_sp sp0 P5)
      by (rewrite /sx_sp /P5 upd_ne; [exact HP4sp | nz]).
    assert (Hpb8 : add_vec_int (mword_of_int (SX + 0x50) : mword 64) 2
                   = mword_of_int (SX + 0x52)) by pcw.
    iEval (rewrite Hpb8) in "Hpc".
    (* ===== +0x052 addi s7,zero,32 : MAXARG ===== *)
    iApply (wp_li4_s_sconf (mword_of_int (SX + 0x52)) Rs7
              (mword_of_int 32 : mword 12) (mword_of_int 32 : mword 64)
              P5 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi052").
    iIntros (CIDb9 Hqb9) "Hcg Hpc".
    set (P6 := <[Regidx Rs7 := regval_into_reg (mword_of_int 32 : mword 64)]> P5).
    assert (HP6s7 : (P6 !!! Regidx Rs7 : mword 64) = (mword_of_int 32 : mword 64))
      by (rewrite /P6; apply upd_eq).
    assert (HP6s1 : (P6 !!! Regidx Rs1 : mword 64) = pa_stk sp0 58)
      by (rewrite /P6 upd_ne; [exact HP5s1 | nz]).
    assert (HP6s2 : (P6 !!! Regidx Rs2 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /P6 upd_ne; [exact HP5s2 | nz]).
    assert (HP6s3 : (P6 !!! Regidx Rs3 : mword 64) = pa_stk sp0 58)
      by (rewrite /P6 upd_ne; [exact HP5s3 | nz]).
    assert (HP6s4 : (P6 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58)
      by (rewrite /P6 upd_ne; [exact HP5s4 | nz]).
    assert (HP6s5 : (P6 !!! Regidx Rs5 : mword 64) = pa_stk sp0 60)
      by (rewrite /P6 upd_ne; [exact HP5s5 | nz]).
    assert (HP6s6 : (P6 !!! Regidx Rs6 : mword 64) = (mword_of_int 4096 : mword 64))
      by (rewrite /P6 upd_ne; [exact HP5s6 | nz]).
    assert (HP6s0 : (P6 !!! Regidx Rs0 : mword 64) = sp0)
      by (rewrite /P6 upd_ne; [exact HP5s0 | nz]).
    assert (HP6sp : sx_sp sp0 P6)
      by (rewrite /sx_sp /P6 upd_ne; [exact HP5sp | nz]).
    assert (Hpb10 : add_vec_int (mword_of_int (SX + 0x52) : mword 64) 4
                    = mword_of_int (SX + 0x56)) by pcw.
    iEval (rewrite Hpb10) in "Hpc".
    (* ---- THE ZERO ROUND TRIP: memset's 256 bytes back to 32 words ---- *)
    iEval (change 256%nat with (8 * 32)%nat) in "Haz".
    iDestruct (sx_zeros_slots sp0 _ 58 32 sx_zb_zero sx_argv_slots_fit Hala
                 with "Haz") as "Hargv".
    (* THE THREADING CLAUSE, in ONE assert rather than eleven: every write
       this block makes is either to a register [sx_thr] already excludes or
       to a caller-saved one, so the chain of [upd_ne]s is the whole proof
       and [regne] discharges each side condition by whichever of the two
       reasons applies. *)
    assert (HP6thr : sx_thr m P6).
    { intros c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23.
      rewrite /P6 upd_ne; [| regne]. rewrite /P5 upd_ne; [| regne].
      rewrite /P4 upd_ne; [| regne]. rewrite /P3 upd_ne; [| regne].
      rewrite /P2 upd_ne; [| regne]. rewrite /P1 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hcsa6 c Hc).
      rewrite /N5 upd_ne; [| regne]. rewrite /N4 upd_ne; [| regne].
      rewrite /N3 upd_ne; [| regne]. rewrite /N2 upd_ne; [| regne].
      rewrite /N1 upd_ne; [| regne].
      exact (sx_thr2_thr m M HMthr c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23). }
    iSpecialize ("Hout" $! CIDb9 with "[%]"); [wp_next_chain |].
    iApply ("Hout" $! P6 with "[%] Hpc Hcg F3 F4 F5 F6 F7 F8 F9 Hargv").
    { split_and!;
        [ exact HP6sp | exact HP6thr | exact HP6s0 | exact HP6s1 | exact HP6s2
        | exact HP6s3 | exact HP6s4 | exact HP6s5 | exact HP6s6
        | exact HP6s7 ]. }
  Qed.


End SysExecSetup.

(* ===================================================================== *)
(*  THE kfree LOOP, +0x096 .. +0x0a0 and +0x0d4 .. +0x0de.                *)
(*                                                                        *)
(*  The same five instructions at two addresses, so it is ONE lemma taking *)
(*  the block's base offset and its own [instr] facts -- the move          *)
(*  [ProofKexecC.kxc_c_exit_m1] makes for kexec's three [-1] stubs.        *)
(*                                                                        *)
(*  THE TEST IS AT THE BOTTOM: [bne s4,s1] runs AFTER the increment, so    *)
(*  the load at the top is reached only at [k < 32] and the array is never *)
(*  read out of range.  Two exits, and the caller supplies both targets:   *)
(*  the [c.beqz] at [k = t < 32], where the cell holds memset's zero, and  *)
(*  the fall-through at [k = t = 32], where every slot has been freed.     *)
(* ===================================================================== *)
Section SysExecFree.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* ---- the address arithmetic of a block at a SYMBOLIC base ---- *)

  (* [pc + k] where the base is a variable, so [pcw]'s [vm_compute] is not
     available (its goal still mentions [base]).  ProofKexecC's [avi_moi],
     restated: a whole-function proof file is not a dependency any other one
     may take. *)
  Local Lemma sx_avi (z k : Z) :
    add_vec_int (mword_of_int z : mword 64) k = (mword_of_int (z + k) : mword 64).
  Proof.
    change (add_vec_int (mword_of_int z : mword 64) k)
      with (add_vec (mword_of_int z : mword 64) (mword_of_int k : mword 64)).
    apply bv_eq. rewrite add_vec64_unsigned !moi64_unsigned.
    rewrite bv_wrap_add_idemp_l bv_wrap_add_idemp_r. reflexivity.
  Qed.

  (* a zero displacement is the identity, which is what [c.ld a0,0(s1)] wants *)
  Local Lemma sx_off0 (x : mword 64) :
    add_vec x (sign_extend' 64 (mword_of_int 0 : mword 12)) = x.
  Proof.
    assert (Hz : (mword_of_int 0 : mword 12) = zeros' 12)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hz. apply add_vec_zeros_r.
  Qed.

  Local Lemma sx_zreg0 : (zero_reg : mword 64) = mword_of_int 0.
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  (* AN INSTRUCTION FACT IS NOT PERSISTENT -- [kernel_text] IS.  Every WP leaf
     CONSUMES its [instr], so a loop body cannot be handed one: it has to mint
     a fresh one per iteration off the (persistent) text.  A block lemma at a
     SYMBOLIC base therefore takes the five [kernel_text -*] implications as
     COQ premises, exactly the shape [CodeSysExec]'s generated [sxi_*] lemmas
     already have, and the caller passes its own by name. *)
  Definition sx_itxt (pc : mword 64) (c : bool) (i : instruction) : Prop :=
    ⊢ (kernel_text -∗ instr pc c i : iProp Σ).

  (* TWO SLOTS OF ONE FRAME ARE DISTINCT ADDRESSES, and the loop's exit test
     is the only place that needs it: [bne s1,s4] compares POINTERS, not an
     index.  It is unconditional in [sp] -- the whole frame spans 480 bytes,
     so no pair of slots can alias however [sp] is placed. *)
  Local Lemma sx_stk_ne (sp : mword 64) (a c : nat) :
    (a <= 60)%nat -> (c <= 60)%nat -> a <> c -> pa_stk sp a <> pa_stk sp c.
  Proof.
    intros Ha Hc Hne Heq.
    apply (f_equal bv_unsigned) in Heq.
    unfold pa_stk, add_vec_int in Heq.
    rewrite !add_vec64_unsigned !moi64_unsigned in Heq.
    rewrite !bv_wrap_add_idemp_r in Heq.
    assert (HM : bv_modulus 64 = 18446744073709551616%Z)
      by (vm_compute; reflexivity).
    unfold bv_wrap in Heq. rewrite HM in Heq.
    assert (Hd : (((bv_unsigned sp + - (8 * Z.of_nat a))
                   - (bv_unsigned sp + - (8 * Z.of_nat c)))
                  mod 18446744073709551616 = 0)%Z).
    { rewrite Zminus_mod Heq Z.sub_diag. apply Zmod_0_l. }
    replace ((bv_unsigned sp + - (8 * Z.of_nat a))
             - (bv_unsigned sp + - (8 * Z.of_nat c)))%Z
      with (8 * Z.of_nat c - 8 * Z.of_nat a)%Z in Hd by lia.
    apply Z.mod_divide in Hd; [| lia].
    destruct Hd as [q Hq]. lia.
  Qed.

  (* the cursor's step, and the end pointer: [argv + 8k] IS slot [58 - k],
     and [argv + 256] IS slot 26 -- one past argv[31], which is where [path]
     begins. *)
  Lemma sx_cursor (sp0 : mword 64) (k : nat) : (k < 32)%nat ->
    add_vec (pa_stk sp0 (58 - k))
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6)))
    = pa_stk sp0 (58 - S k).
  Proof.
    intro Hk.
    assert (Him : (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))
                   : mword 64) = mword_of_int 8)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Him.
    change (add_vec (pa_stk sp0 (58 - k)) (mword_of_int 8))
      with (pa_add (pa_stk sp0 (58 - k)) 8).
    rewrite (pa_stk_next sp0 (58 - k)%nat ltac:(lia)).
    f_equal. lia.
  Qed.

  (* the end pointer: [argv + 256] is slot 26, one past argv[31]. *)
  Lemma sx_argv_end (sp0 : mword 64) :
    pa_stk sp0 (58 - 32)%nat = pa_stk sp0 26.
  Proof. reflexivity. Qed.

  (* ---- the loop's own view of the argv array ---- *)

  (* The array between the free loop's cursor [k] and the first NULL [t]:
     below [k] the pages are gone and only the (stale) pointer words remain,
     between [k] and [t] each slot holds a live page, and from [t] up every
     slot still holds memset's zero.  The pure facts about the pointers ride
     as a COQ premise rather than as conjuncts -- they are what kexec's own
     contract already states about [avf], so restating them here would make
     the seam a re-derivation. *)
  Definition sx_argv_at (sp0 : mword 64) (k t : nat) (pg : nat -> mword 64)
      : iProp Σ :=
    (([∗ list] j ∈ seq 0 k, ∃ w : mword 64, (pa_stk sp0 (58 - j)) ↦₈[KT1] w) ∗
     ([∗ list] j ∈ seq k (t - k), (pa_stk sp0 (58 - j)) ↦₈[KT1] pg j) ∗
     ([∗ list] j ∈ seq t (32 - t),
        (pa_stk sp0 (58 - j)) ↦₈[KT1] (mword_of_int 0 : mword 64)))%I.

  (* the pages themselves, as the named byte runs kexec was handed and kfree
     wants back *)
  Definition sx_pages (pg : nat -> mword 64) (afun : nat -> nat -> bv 8)
      (k t : nat) : iProp Σ :=
    ([∗ list] j ∈ seq k (t - k),
       [∗ list] i ∈ seq 0 4096, pa_add (pg j) i ↦ₘ afun j i)%I.

  (* every slot back in the caller's hands, contents forgotten: what the
     epilogue's [bytes_own] carve is rebuilt from *)
  Definition sx_argv_free (sp0 : mword 64) : iProp Σ :=
    ([∗ list] j ∈ seq 0 32, ∃ w : mword 64, (pa_stk sp0 (58 - j)) ↦₈[KT1] w)%I.

  Local Lemma sx_ex_app (sp0 : mword 64) (t n : nat) :
    ([∗ list] j ∈ seq 0 t, ∃ w : mword 64, (pa_stk sp0 (58 - j)) ↦₈[KT1] w) -∗
    ([∗ list] j ∈ seq t n, ∃ w : mword 64, (pa_stk sp0 (58 - j)) ↦₈[KT1] w) -∗
    ([∗ list] j ∈ seq 0 (t + n), ∃ w : mword 64, (pa_stk sp0 (58 - j)) ↦₈[KT1] w).
  Proof. rewrite seq_app big_sepL_app. iIntros "A B". iSplitL "A"; done. Qed.

  (* both exits leave the cursor AT the first NULL -- the early one because
     that is what it tested, the fall-through because [t = 32] there. *)
  Lemma sx_argv_done (sp0 : mword 64) (t : nat) (pg : nat -> mword 64) :
    (t <= 32)%nat -> sx_argv_at sp0 t t pg ⊢ sx_argv_free sp0.
  Proof.
    intro Ht. rewrite /sx_argv_at /sx_argv_free Nat.sub_diag.
    iIntros "(H1 & _ & H3)".
    iAssert ([∗ list] j ∈ seq t (32 - t),
               ∃ w : mword 64, (pa_stk sp0 (58 - j)) ↦₈[KT1] w)%I
      with "[H3]" as "H3".
    { iApply (big_sepL_mono with "H3"). intros i j _. iIntros "H".
      iExists (mword_of_int 0 : mword 64). iExact "H". }
    iDestruct (sx_ex_app sp0 t (32 - t)%nat with "H1 H3") as "H".
    replace (t + (32 - t))%nat with 32%nat by lia. iExact "H".
  Qed.

  (* EVERY PIECE OF LIST SURGERY IS A STANDALONE LEMMA, and that is not a
     style choice: [rewrite]ing a [seq]/[big_sepL] equation inside the WP
     goal builds its congruence proof over the whole syscall-altitude
     context, which climbed past 11 GB with no plateau.  Proved here, where
     the goal is the predicate and nothing else, each is instant and the loop
     body sees only an [iDestruct]. *)

  (* peel the live cell at the cursor, with the wand that puts it back as a
     freed one *)
  Local Lemma sx_argv_peel (sp0 : mword 64) (k t : nat) (pg : nat -> mword 64) :
    (k < t)%nat ->
    sx_argv_at sp0 k t pg -∗
    (pa_stk sp0 (58 - k)) ↦₈[KT1] pg k ∗
    ((∃ w : mword 64, (pa_stk sp0 (58 - k)) ↦₈[KT1] w) -∗ sx_argv_at sp0 (S k) t pg).
  Proof.
    intro Hk. rewrite /sx_argv_at.
    rewrite (_ : (t - k)%nat = S (t - S k)%nat); [| lia].
    rewrite -cons_seq big_sepL_cons.
    iIntros "(Hlo & [Hcell Hmid] & Hhi)". iSplitL "Hcell"; [iExact "Hcell" |].
    iIntros "Hnew". rewrite seq_S big_sepL_app big_sepL_singleton.
    iSplitL "Hlo Hnew"; [iSplitL "Hlo"; [iExact "Hlo" | iExact "Hnew"] |].
    iSplitL "Hmid"; [iExact "Hmid" | iExact "Hhi"].
  Qed.

  (* the NULL at the cursor, with the wand that closes the loop out *)
  Local Lemma sx_argv_null (sp0 : mword 64) (t : nat) (pg : nat -> mword 64) :
    (t < 32)%nat ->
    sx_argv_at sp0 t t pg -∗
    (pa_stk sp0 (58 - t)) ↦₈[KT1] (mword_of_int 0 : mword 64) ∗
    ((pa_stk sp0 (58 - t)) ↦₈[KT1] (mword_of_int 0 : mword 64) -∗ sx_argv_free sp0).
  Proof.
    intro Ht. iIntros "H". rewrite /sx_argv_at.
    rewrite (_ : (32 - t)%nat = S (32 - S t)%nat); [| lia].
    rewrite -cons_seq big_sepL_cons.
    iDestruct "H" as "(Hlo & Hmid & [Hcell Hhi])".
    iSplitL "Hcell"; [iExact "Hcell" |].
    iIntros "Hcell".
    iApply (sx_argv_done sp0 t pg ltac:(lia)).
    rewrite /sx_argv_at.
    rewrite (_ : (32 - t)%nat = S (32 - S t)%nat); [| lia].
    rewrite -cons_seq big_sepL_cons.
    iSplitL "Hlo"; [iExact "Hlo" |].
    iSplitL "Hmid"; [iExact "Hmid" |].
    iSplitL "Hcell"; [iExact "Hcell" | iExact "Hhi"].
  Qed.

  Local Lemma sx_pages_peel (pg : nat -> mword 64) (afun : nat -> nat -> bv 8)
      (k t : nat) :
    (k < t)%nat ->
    sx_pages pg afun k t -∗
    ([∗ list] i ∈ seq 0 4096, pa_add (pg k) i ↦ₘ afun k i) ∗
    sx_pages pg afun (S k) t.
  Proof.
    intro Hk. rewrite /sx_pages.
    rewrite (_ : (t - k)%nat = S (t - S k)%nat); [| lia].
    rewrite -cons_seq big_sepL_cons. iIntros "[Hp Hr]".
    (* NOT [iIntros "[$ $]"]: framing a 4096-conjunct big-op normalises
       [seq 0 4096] into a literal list and does not come back. *)
    iSplitL "Hp"; [iExact "Hp" | iExact "Hr"].
  Qed.

  (* ---- the loop ---- *)

  (* THE EARLY EXIT, and it is the loop's own first two instructions: the
     cell at the cursor holds memset's zero, so every page below it has
     already been freed and the [c.beqz] is taken.  Reached from the head at
     [k = t], whatever the fuel, which is why it is a lemma of its own rather
     than the induction's base case. *)
  Lemma sx_free_exit `{CID0 : CpuId}
      (sp0 pj : mword 64)
      (K : nat) (eb b : bool) (lks : gset string)
      (pg : nat -> mword 64) (t : nat) (base ea : Z) (imm8 : mword 8)
      (M : regfile) :
    (t < 32)%nat ->
    add_vec (mword_of_int (SX + base + 2) : mword 64)
      (sign_extend' 64 (sign_extend' 13 (concat_vec imm8 ('b"0"))))
      = (mword_of_int (SX + ea) : mword 64) ->
    eq_vec (access_vec_dec (mword_of_int (SX + ea) : mword 64) 0) ('b"0") = true ->
    (M !!! Regidx Rs1 : mword 64) = pa_stk sp0 (58 - t)%nat ->
    sx_itxt (mword_of_int (SX + base) : mword 64) true
          (LOAD (mword_of_int 0 : mword 12, Regidx Rs1, Regidx Ra0, false, 8)) ->
    sx_itxt (mword_of_int (SX + base + 2) : mword 64) true
          (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg,
                  creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) ->
    kernel_text -∗
    pc_is (mword_of_int (SX + base) : mword 64) -∗
    sie_cap_gpr KT1 M (K - 60)%nat b pj -∗
    cpu_own 0 eb pj b lks -∗
    sx_argv_at sp0 t t pg -∗
    wp_next b pj (fun (CID : CpuId) =>
      ∀ (M' : regfile) (pcx : mword 64),
        ⌜pcx = (mword_of_int (SX + ea) : mword 64)
         \/ pcx = (mword_of_int (SX + base + 14) : mword 64)⌝ -∗
        ⌜forall c : mword 5, is_cs_idx c = true -> c <> Rs1 ->
           (M' !!! Regidx c : mword 64) = (M !!! Regidx c : mword 64)⌝ -∗
        pc_is pcx -∗
        sie_cap_gpr KT1 M' (K - 60)%nat b pj -∗
        cpu_own 0 eb pj b lks -∗
        sx_argv_free sp0 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Ht Hbeq Hbeqal HMs1 Hx0 Hx2.
    iIntros "#Htext Hpc Hcg Hcnt Harr Hout".
    iPoseProof (Hx0 with "Htext") as "Hi0".
    iPoseProof (Hx2 with "Htext") as "Hi2".
    iDestruct (sx_argv_null sp0 t pg ltac:(lia) with "Harr") as "[Hcell Hback]".
    (* ===== +base c.ld a0,0(s1) : memset's zero ===== *)
    assert (Hg1 : rget M Rs1 = (M !!! Regidx Rs1 : mword 64)) by (apply rget_ne; nz).
    assert (Hca : add_vec (rget M Rs1)
                    (sign_extend' 64 (mword_of_int 0 : mword 12))
                  = pa_stk sp0 (58 - t)%nat)
      by (rewrite Hg1 HMs1; apply sx_off0).
    iEval (rewrite -Hca) in "Hcell".
    iApply (wp_cld_s_sconf (mword_of_int (SX + base) : mword 64) Ra0 Rs1
              (mword_of_int 0 : mword 12) M (K - 60)%nat
              (mword_of_int 0 : mword 64) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0 Hcell").
    iIntros (CID1 Hq1) "Hcg Hpc Hcell".
    iEval (rewrite Hca) in "Hcell".
    set (M1 := <[Regidx Ra0 := regval_into_reg (mword_of_int 0 : mword 64)]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = (mword_of_int 0 : mword 64))
      by (rewrite /M1; apply upd_eq).
    assert (HM1cs : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 ->
              (M1 !!! Regidx c : mword 64) = (M !!! Regidx c : mword 64)).
    { intros c Hc _. rewrite /M1 upd_ne; [reflexivity |].
      apply not_eq_sym. apply is_cs_idx_true_neq;
        [vm_compute; reflexivity | exact Hc]. }
    iEval (rewrite (sx_avi (SX + base) 2)) in "Hpc".
    (* ===== +base+2 c.beqz a0 : TAKEN ===== *)
    assert (Hcmp : eq_vec (rget M1 Ra0) zero_reg = true).
    { rewrite rget_ne; [| nz]. rewrite HM1a0. apply eq_vec_true_iff.
      symmetry. exact sx_zreg0. }
    iApply (wp_cbeqz_taken_s_sconf (mword_of_int (SX + base + 2) : mword 64)
              imm8 (Cregidx (mword_of_int 2)) Ra0 M1 (K - 60)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
              ltac:(rewrite Hbeq; exact Hbeqal) with "Hcg Hpc Hi2").
    iIntros (CID2 Hq2). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Hbeq) in "Hpc".
    iSpecialize ("Hout" $! CID2 with "[%]"); [wp_next_chain |].
    iDestruct (cpu_own_transport CID0 CID2 0%nat eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply ("Hout" $! M1 _ with "[%] [%] Hpc Hcg Hcnt [Hcell Hback]").
    { left; reflexivity. }
    { exact HM1cs. }
    { iApply ("Hback" with "Hcell"). }
  Qed.

  (* Five instructions, at [SX + base]:
       +0   c.ld  a0,0(s1)
       +2   c.beqz a0,SX+ea          the array's NULL: every page is freed
       +4   jal   ra,kfree
       +8   c.addi s1,8
       +10  bne   s1,s4,SX+base      the back edge; falls through at [k = 32]
     The induction is on the FUEL [W] bounding [t - k]; the head is entered
     only at [k < 32], so the array is never read out of range. *)
  Lemma sx_free_loop `{CID0 : CpuId}
      (ga : gname) (sp0 pj : mword 64)
      (K : nat) (eb b : bool) (lks : gset string)
      (pg : nat -> mword 64) (afun : nat -> nat -> bv 8) (t : nat)
      (base ea : Z) (imm8 : mword 8) (jimm : mword 21) :
    (K_sys_exec <= K)%nat ->
    (t <= 32)%nat ->
    (forall j, (j < t)%nat ->
       pg j <> (mword_of_int 0 : mword 64) /\ page_valid (pg j)) ->
    locks_below lks "kmem" ->
    ret_pc (mword_of_int (SX + base + 8) : mword 64)
      = (mword_of_int (SX + base + 8) : mword 64) ->
    add_vec (mword_of_int (SX + base + 2) : mword 64)
      (sign_extend' 64 (sign_extend' 13 (concat_vec imm8 ('b"0"))))
      = (mword_of_int (SX + ea) : mword 64) ->
    eq_vec (access_vec_dec (mword_of_int (SX + ea) : mword 64) 0) ('b"0") = true ->
    add_vec (mword_of_int (SX + base + 4) : mword 64) (sign_extend' 64 jimm)
      = (mword_of_int KernelSyms.kfree : mword 64) ->
    add_vec (mword_of_int (SX + base + 10) : mword 64)
      (sign_extend' 64 (mword_of_int 8182 : mword 13))
      = (mword_of_int (SX + base) : mword 64) ->
    eq_vec (access_vec_dec (mword_of_int (SX + base) : mword 64) 0) ('b"0")
      = true ->
    sx_itxt (mword_of_int (SX + base) : mword 64) true
          (LOAD (mword_of_int 0 : mword 12, Regidx Rs1, Regidx Ra0, false, 8)) ->
    sx_itxt (mword_of_int (SX + base + 2) : mword 64) true
          (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg,
                  creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) ->
    sx_itxt (mword_of_int (SX + base + 4) : mword 64) false
          (JAL (jimm, Regidx Rra)) ->
    sx_itxt (mword_of_int (SX + base + 8) : mword 64) true
          (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx Rs1,
                  Regidx Rs1, ADDI)) ->
    sx_itxt (mword_of_int (SX + base + 10) : mword 64) false
          (BTYPE (mword_of_int 8182 : mword 13, Regidx Rs4, Regidx Rs1, BNE)) ->
    forall (W : nat) (M : regfile) (k : nat),
    (k <= t)%nat -> (k < 32)%nat -> (t - k <= W)%nat ->
    (M !!! Regidx Rs1 : mword 64) = pa_stk sp0 (58 - k)%nat ->
    (M !!! Regidx Rs4 : mword 64) = pa_stk sp0 26 ->
    kernel_text -∗
    kalloc_env ga None -∗
    pc_is (mword_of_int (SX + base) : mword 64) -∗
    sie_cap_gpr KT1 M (K - 60)%nat b pj -∗
    cpu_own 0 eb pj b lks -∗
    sx_argv_at sp0 k t pg -∗
    sx_pages pg afun k t -∗
    wp_next b pj (fun (CID : CpuId) =>
      ∀ (M' : regfile) (pcx : mword 64),
        ⌜pcx = (mword_of_int (SX + ea) : mword 64)
         \/ pcx = (mword_of_int (SX + base + 14) : mword 64)⌝ -∗
        ⌜forall c : mword 5, is_cs_idx c = true -> c <> Rs1 ->
           (M' !!! Regidx c : mword 64) = (M !!! Regidx c : mword 64)⌝ -∗
        pc_is pcx -∗
        sie_cap_gpr KT1 M' (K - 60)%nat b pj -∗
        cpu_own 0 eb pj b lks -∗
        sx_argv_free sp0 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Ht Hpg Hlb Hret Hbeq Hbeqal Hkf Hbk Hbkal Hx0 Hx2 Hx4 Hx8 Hx10.
    destruct (sx_kb K HK) as (Kkx & Kar & Kaa & Kfa & Kfs & K14 & K2 & K60 & Kpop).
    intro W. revert CID0.
    induction W as [| W IH]; intros CID0 M k Hkt Hk32 Hfuel HMs1 HMs4.
    { (* no fuel: [t - k = 0], so the cell at the cursor is memset's zero and
         the [c.beqz] is taken.  Not a vacuous case -- it is the EXIT. *)
      assert (Hkeqt : k = t) by lia. subst t.
      iIntros "#Htext #Hka Hpc Hcg Hcnt Harr Hpgs Hout".
      iApply (sx_free_exit (CID0 := CID0) sp0 pj K eb b lks pg k base ea
                imm8 M ltac:(lia) Hbeq Hbeqal HMs1 Hx0 Hx2
                with "Htext Hpc Hcg Hcnt Harr Hout"). }
    iIntros "#Htext #Hka Hpc Hcg Hcnt Harr Hpgs Hout".
    iPoseProof (Hx0 with "Htext") as "Hi0".
    iPoseProof (Hx2 with "Htext") as "Hi2".
    iPoseProof (Hx4 with "Htext") as "Hi4".
    iPoseProof (Hx8 with "Htext") as "Hi8".
    iPoseProof (Hx10 with "Htext") as "Hi10".
    destruct (Nat.eq_dec k t) as [Hkeq | Hkne].
    { (* the cell holds the NULL: the early exit, whatever the fuel *)
      subst t.
      iApply (sx_free_exit (CID0 := CID0) sp0 pj K eb b lks pg k base ea
                imm8 M ltac:(lia) Hbeq Hbeqal HMs1 Hx0 Hx2
                with "Htext Hpc Hcg Hcnt Harr Hout"). }
    (* ---- a live page: free it and go round ---- *)
    assert (Hklt : (k < t)%nat) by lia.
    destruct (Hpg k Hklt) as [Hpgnz Hpgv].
    iDestruct (sx_argv_peel sp0 k t pg Hklt with "Harr") as "[Hcell Hback]".
    iDestruct (sx_pages_peel pg afun k t Hklt with "Hpgs") as "[Hpage Hpgs]".
    (* ===== +base c.ld a0,0(s1) ===== *)
    assert (Hg1 : rget M Rs1 = (M !!! Regidx Rs1 : mword 64)) by (apply rget_ne; nz).
    assert (Hca : add_vec (rget M Rs1) (sign_extend' 64 (mword_of_int 0 : mword 12))
                  = pa_stk sp0 (58 - k)%nat)
      by (rewrite Hg1 HMs1; apply sx_off0).
    iEval (rewrite -Hca) in "Hcell".
    iApply (wp_cld_s_sconf (mword_of_int (SX + base) : mword 64) Ra0 Rs1
              (mword_of_int 0 : mword 12) M (K - 60)%nat (pg k) b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi0 Hcell").
    iIntros (CID1 Hq1) "Hcg Hpc Hcell".
    iEval (rewrite Hca) in "Hcell".
    set (M1 := <[Regidx Ra0 := regval_into_reg (pg k)]> M).
    assert (HM1a0 : (M1 !!! Regidx Ra0 : mword 64) = pg k)
      by (rewrite /M1; apply upd_eq).
    assert (HM1s1 : (M1 !!! Regidx Rs1 : mword 64) = pa_stk sp0 (58 - k)%nat)
      by (rewrite /M1 upd_ne; [exact HMs1 | nz]).
    assert (HM1s4 : (M1 !!! Regidx Rs4 : mword 64) = pa_stk sp0 26)
      by (rewrite /M1 upd_ne; [exact HMs4 | nz]).
    assert (HM1cs : forall c : mword 5, is_cs_idx c = true ->
              (M1 !!! Regidx c : mword 64) = (M !!! Regidx c : mword 64)).
    { intros c Hc. rewrite /M1 upd_ne; [reflexivity |].
      apply not_eq_sym. apply is_cs_idx_true_neq;
        [vm_compute; reflexivity | exact Hc]. }
    iEval (rewrite (sx_avi (SX + base) 2)) in "Hpc".
    (* ===== +base+2 c.beqz a0 : NOT taken, the page is live ===== *)
    assert (Hcmp : eq_vec (rget M1 Ra0) zero_reg = false).
    { rewrite rget_ne; [| nz]. rewrite HM1a0. apply eq_vec_false_iff.
      intro Hc. apply Hpgnz. rewrite Hc. exact sx_zreg0. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (SX + base + 2) : mword 64)
              imm8 (Cregidx (mword_of_int 2)) Ra0 M1 (K - 60)%nat b
              ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
              with "Hcg Hpc Hi2").
    iIntros (CID2 Hq2) "Hcg Hpc".
    iEval (rewrite (sx_avi (SX + base + 2) 2)) in "Hpc".
    rewrite (_ : (SX + base + 2 + 2)%Z = (SX + base + 4)%Z); [| lia].
    (* ===== +base+4 jal ra,kfree ===== *)
    iApply (wp_jal_s_sconf (mword_of_int (SX + base + 4) : mword 64) Rra jimm
              M1 (K - 60)%nat b ltac:(nz) ltac:(rdok)
              ltac:(rewrite Hkf; vm_compute; reflexivity)
              with "Hcg Hpc Hi4").
    iIntros (CID3 Hq3) "Hcg Hpc". iEval (rewrite Hkf) in "Hpc".
    set (M2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SX + base + 4) : mword 64) 4)]> M1).
    assert (HM2ra : (M2 !!! Regidx Rra : mword 64)
                    = (mword_of_int (SX + base + 8) : mword 64)).
    { rewrite /M2 upd_eq (sx_avi (SX + base + 4) 4).
      rewrite (_ : (SX + base + 4 + 4)%Z = (SX + base + 8)%Z); [reflexivity | lia]. }
    assert (HM2a0 : (M2 !!! Regidx Ra0 : mword 64) = pg k)
      by (rewrite /M2 upd_ne; [exact HM1a0 | nz]).
    assert (HM2s1 : (M2 !!! Regidx Rs1 : mword 64) = pa_stk sp0 (58 - k)%nat)
      by (rewrite /M2 upd_ne; [exact HM1s1 | nz]).
    assert (HM2s4 : (M2 !!! Regidx Rs4 : mword 64) = pa_stk sp0 26)
      by (rewrite /M2 upd_ne; [exact HM1s4 | nz]).
    assert (HM2cs : forall c : mword 5, is_cs_idx c = true ->
              (M2 !!! Regidx c : mword 64) = (M !!! Regidx c : mword 64)).
    { intros c Hc. rewrite /M2 upd_ne;
        [exact (HM1cs c Hc) |
         apply not_eq_sym; apply is_cs_idx_true_neq;
           [vm_compute; reflexivity | exact Hc]]. }
    iDestruct "Hka" as (γk) "(#Hlk & #Hav)".
    iDestruct (cpu_own_transport CID0 CID3 0%nat eb pj b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (bb_page_of_named (pg k) (afun k) with "Hpage") as "Hpage".
    iApply (Kfree.wp_kfree_sconf KT1 ga γk (mword_of_int KernelSyms.kmem)
              (mword_of_int (KernelSyms.kmem + 24)) M2 None 0%nat eb pj
              (K - 60)%nat b lks K14 eq_refl eq_refl sx_noff0 Hlb
              with "Hcg Hcnt Htext Hpc Hlk [Hpage] Hav").
    { rewrite /kfree_pre HM2a0. iSplitR; [iPureIntro; exact Hpgv |]. iExact "Hpage". }
    iIntros (CID4 Hq4 Mk) "Hcg Hcnt Hpc %Hcsk Hav2".
    iEval (rewrite HM2ra Hret) in "Hpc".
    (* ===== +base+8 c.addi s1,8 ===== *)
    iApply (wp_caddi_s_sconf (mword_of_int (SX + base + 8) : mword 64) Rs1
              (mword_of_int 8 : mword 6) Mk (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8").
    iIntros (CID5 Hq5) "Hcg Hpc".
    iEval (rewrite (sx_avi (SX + base + 8) 2)) in "Hpc".
    rewrite (_ : (SX + base + 8 + 2)%Z = (SX + base + 10)%Z); [| lia].
    set (M3 := <[Regidx Rs1 := regval_into_reg
                  (add_vec (rget Mk Rs1)
                     (sign_extend' 64 (sign_extend' 12 (mword_of_int 8 : mword 6))))]> Mk).
    assert (HM3s1 : (M3 !!! Regidx Rs1 : mword 64) = pa_stk sp0 (58 - S k)%nat).
    { rewrite /M3 upd_eq rget_ne; [| nz].
      rewrite (callee_saved_lookup Hcsk Rs1 ltac:(vm_compute; reflexivity)) HM2s1.
      apply sx_cursor. lia. }
    assert (HM3s4 : (M3 !!! Regidx Rs4 : mword 64) = pa_stk sp0 26).
    { rewrite /M3 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsk Rs4 ltac:(vm_compute; reflexivity)).
      exact HM2s4. }
    assert (HM3cs : forall c : mword 5, is_cs_idx c = true -> c <> Rs1 ->
              (M3 !!! Regidx c : mword 64) = (M !!! Regidx c : mword 64)).
    { intros c Hc Hcs. rewrite /M3 upd_ne; [| congruence].
      rewrite (callee_saved_lookup Hcsk c Hc). exact (HM2cs c Hc). }
    (* the freed cell joins the prefix *)
    iAssert (sx_argv_at sp0 (S k) t pg)%I with "[Hcell Hback]" as "Harr".
    { iApply "Hback". iExists (pg k). iExact "Hcell". }
    (* ===== +base+10 bne s1,s4 ===== *)
    destruct (Nat.eq_dec (S k) 32) as [Hend | Hgo].
    - (* the cursor reached [argv + 256]: fall through *)
      assert (Hs1eq : (M3 !!! Regidx Rs1 : mword 64) = (M3 !!! Regidx Rs4 : mword 64)).
      { rewrite HM3s1 HM3s4 Hend. reflexivity. }
      assert (Hcmpb : neq_vec (rget M3 Rs1) (rget M3 Rs4) = false).
      { rewrite !rget_ne; [| nz | nz]. unfold neq_vec. rewrite negb_false_iff.
        apply eq_vec_true_iff. exact Hs1eq. }
      iApply (wp_bne_fall_s_sconf (mword_of_int (SX + base + 10) : mword 64)
                (mword_of_int 8182 : mword 13) Rs4 Rs1 M3 (K - 60)%nat b
                ltac:(nz) ltac:(nz) Hcmpb with "Hcg Hpc Hi10").
      iIntros (CID6 Hq6) "Hcg Hpc".
      iEval (rewrite (sx_avi (SX + base + 10) 4)) in "Hpc".
      rewrite (_ : (SX + base + 10 + 4)%Z = (SX + base + 14)%Z); [| lia].
      iSpecialize ("Hout" $! CID6 with "[%]"); [wp_next_chain |].
      iDestruct (cpu_own_transport CID4 CID6 0%nat eb pj b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply ("Hout" $! M3 _ with "[%] [%] Hpc Hcg Hcnt [Harr]").
      { right; reflexivity. }
      { exact HM3cs. }
      { rewrite (_ : (S k) = t); [| lia].
        iApply (sx_argv_done sp0 t pg ltac:(lia) with "Harr"). }
    - (* another slot: the BACK EDGE *)
      assert (Hs1ne : (M3 !!! Regidx Rs1 : mword 64) <> (M3 !!! Regidx Rs4 : mword 64)).
      { rewrite HM3s1 HM3s4. apply sx_stk_ne; lia. }
      assert (Hcmpb : neq_vec (rget M3 Rs1) (rget M3 Rs4) = true).
      { rewrite !rget_ne; [| nz | nz]. unfold neq_vec. rewrite negb_true_iff.
        apply eq_vec_false_iff. exact Hs1ne. }
      iApply (wp_bne_taken_s_sconf (mword_of_int (SX + base + 10) : mword 64)
                (mword_of_int 8182 : mword 13) Rs4 Rs1 M3 (K - 60)%nat b
                ltac:(nz) ltac:(nz) Hcmpb
                ltac:(rewrite Hbk; exact Hbkal) with "Hcg Hpc Hi10").
      iIntros (CID6 Hq6). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Hbk) in "Hpc".
      iDestruct (cpu_own_transport CID4 CID6 0%nat eb pj b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      assert (Hcr : b = false \/ pj = zero_reg -> (CID6 : CPU) = (CID0 : CPU))
        by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CID6 b pj _ Hcr with "Hout") as "Hout".
      iApply (IH CID6 M3 (S k) ltac:(lia) ltac:(lia) ltac:(lia) HM3s1 HM3s4
                with "Htext [] Hpc Hcg Hcnt Harr Hpgs [Hout]").
      { iExists γk. iFrame "Hlk Hav". }
      { rewrite /wp_next. iIntros (CIDx) "%Hcx".
        iSpecialize ("Hout" $! CIDx with "[%]"); [exact Hcx |].
        iIntros (M' pcx) "%Hpcx %Hthr Hpc' Hcg' Hcnt' Harr'".
        iApply ("Hout" $! M' pcx with "[%] [%] Hpc' Hcg' Hcnt' Harr'").
        { exact Hpcx. }
        { intros c Hc Hcs. rewrite (Hthr c Hc Hcs). exact (HM3cs c Hc Hcs). } }
  Qed.

End SysExecFree.

(* ===================================================================== *)
(*  +0x056 .. +0x090 -- THE FILL LOOP.                                    *)
(*                                                                        *)
(*  One iteration is [fetchaddr(uargv + 8i, &uarg)], the NULL test that    *)
(*  breaks out, [kalloc()] into [argv[i]], and [fetchstr(uarg, argv[i],    *)
(*  PGSIZE)].  FIVE ways out and only ONE continuation to spend them on,   *)
(*  so the step publishes a DISJUNCTION (kexec.md's block-interface rule): *)
(*  the back edge at [S i], the break at +0x0b6, and [bad:] at +0x092 --   *)
(*  which the three failing callees and the [i = 32] fall-through of the   *)
(*  back-edge test all reach, differing only in where the array's first    *)
(*  NULL then is ([i] before the store, [S i] after it, 32 at the          *)
(*  fall-through).                                                        *)
(*                                                                        *)
(*  THE BREAK STATE IS THE HEAD STATE AT ANOTHER PC.  Nothing before the   *)
(*  [c.beqz] at +0x06e writes a callee-saved register or the array, so     *)
(*  [sx_body] is parameterised by its pc and serves both, and the          *)
(*  composition has nothing to reconcile at the break.                     *)
(*                                                                        *)
(*  THE NINE REGISTER EQUATIONS TRAVEL AS ONE PROPOSITION, [sx_regs], with *)
(*  two transport lemmas -- one for an instruction that writes a           *)
(*  caller-saved register, one for a call.  Nineteen instructions and      *)
(*  three calls would otherwise be ~250 near-identical [upd_ne] lines.     *)
(* ===================================================================== *)
Section SysExecLoop.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.
  Local Ltac csf := vm_compute; reflexivity.

  (* ---- the pure bookkeeping the array carries ---- *)

  (* what the loop knows about the arguments it has already copied in: each
     pointer is a live page and the bytes in it are a NUL-terminated string
     short enough for kexec's push.  This IS kexec's own argument premise,
     restricted to the prefix built so far. *)
  Definition sx_ok (pg : nat -> mword 64) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) (n : nat) : Prop :=
    forall j, (j < n)%nat ->
      pg j <> (mword_of_int 0 : mword 64) /\ page_valid (pg j) /\
      (alen j < 4096)%nat /\ bb_cstr (afun j) (alen j).

  (* what [bad:] still knows -- the string half is gone, because the page a
     failing [fetchstr] leaves in the array has nothing said about its bytes.
     The free loop wants exactly this much and no more. *)
  Definition sx_pgok (pg : nat -> mword 64) (n : nat) : Prop :=
    forall j, (j < n)%nat ->
      pg j <> (mword_of_int 0 : mword 64) /\ page_valid (pg j).

  Lemma sx_ok_pgok (pg : nat -> mword 64) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) (n : nat) :
    sx_ok pg alen afun n -> sx_pgok pg n.
  Proof.
    intros H j Hj. destruct (H j Hj) as (A & B & _ & _). split; assumption.
  Qed.

  (* extend a function at one index; below [i] nothing moves, which is all
     the transports below ask for. *)
  Definition sx_upd {A : Type} (f : nat -> A) (i : nat) (v : A) : nat -> A :=
    fun j => if Nat.eq_dec j i then v else f j.

  Lemma sx_upd_eq {A : Type} (f : nat -> A) (i : nat) (v : A) :
    sx_upd f i v i = v.
  Proof. rewrite /sx_upd. destruct (Nat.eq_dec i i); [reflexivity | lia]. Qed.

  Lemma sx_upd_lt {A : Type} (f : nat -> A) (i : nat) (v : A) (j : nat) :
    (j < i)%nat -> sx_upd f i v j = f j.
  Proof.
    intro Hj. rewrite /sx_upd. destruct (Nat.eq_dec j i); [lia | reflexivity].
  Qed.

  Lemma sx_ok_push (pg : nat -> mword 64) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) (i : nat) (p : mword 64) (k : nat)
      (f : nat -> bv 8) :
    sx_ok pg alen afun i ->
    p <> (mword_of_int 0 : mword 64) -> page_valid p ->
    (k < 4096)%nat -> bb_cstr f k ->
    sx_ok (sx_upd pg i p) (sx_upd alen i k) (sx_upd afun i f) (S i).
  Proof.
    intros Hok Hnz Hpv Hk Hcs j Hj.
    destruct (Nat.eq_dec j i) as [Heq | Hne].
    - subst j. rewrite !sx_upd_eq. split_and!; assumption.
    - rewrite (sx_upd_lt pg i p j ltac:(lia)) (sx_upd_lt alen i k j ltac:(lia))
              (sx_upd_lt afun i f j ltac:(lia)).
      exact (Hok j ltac:(lia)).
  Qed.

  Lemma sx_pgok_push (pg : nat -> mword 64) (i : nat) (p : mword 64) :
    sx_pgok pg i -> p <> (mword_of_int 0 : mword 64) -> page_valid p ->
    sx_pgok (sx_upd pg i p) (S i).
  Proof.
    intros Hok Hnz Hpv j Hj.
    destruct (Nat.eq_dec j i) as [Heq | Hne].
    - subst j. rewrite sx_upd_eq. split; assumption.
    - rewrite (sx_upd_lt pg i p j ltac:(lia)). exact (Hok j ltac:(lia)).
  Qed.

  (* ---- the array, as the FILL loop sees it: filled below [t], memset's
         zero from [t] up ---- *)
  Definition sx_argv0 (sp0 : mword 64) (t : nat) (pg : nat -> mword 64)
      : iProp Σ :=
    (([∗ list] j ∈ seq 0 t, (pa_stk sp0 (58 - j)) ↦₈[KT1] pg j) ∗
     ([∗ list] j ∈ seq t (32 - t),
        (pa_stk sp0 (58 - j)) ↦₈[KT1] (mword_of_int 0 : mword 64)))%I.

  (* the array MINUS the slot at the cursor *)
  Definition sx_argv_rest (sp0 : mword 64) (t : nat) (pg : nat -> mword 64)
      : iProp Σ :=
    (([∗ list] j ∈ seq 0 t, (pa_stk sp0 (58 - j)) ↦₈[KT1] pg j) ∗
     ([∗ list] j ∈ seq (S t) (31 - t),
        (pa_stk sp0 (58 - j)) ↦₈[KT1] (mword_of_int 0 : mword 64)))%I.

  Lemma sx_seq00 : seq 0 0 = @nil nat.
  Proof. reflexivity. Qed.

  (* the fill loop's view and the free loop's view are one predicate -- the
     free loop just starts with an empty freed prefix. *)
  Lemma sx_argv0_at (sp0 : mword 64) (t : nat) (pg : nat -> mword 64) :
    sx_argv0 sp0 t pg ⊢ sx_argv_at sp0 0 t pg.
  Proof.
    rewrite /sx_argv0 /sx_argv_at Nat.sub_0_r sx_seq00 big_sepL_nil.
    iIntros "[A B]". iSplitR; [done |].
    iSplitL "A"; [iExact "A" | iExact "B"].
  Qed.

  Lemma sx_argv0_open (sp0 : mword 64) (t : nat) (pg : nat -> mword 64) :
    (t < 32)%nat ->
    sx_argv0 sp0 t pg ⊢
    (pa_stk sp0 (58 - t)) ↦₈[KT1] (mword_of_int 0 : mword 64) ∗
    sx_argv_rest sp0 t pg.
  Proof.
    intro Ht. rewrite /sx_argv0 /sx_argv_rest.
    rewrite (_ : (32 - t)%nat = S (31 - t)%nat); [| lia].
    rewrite -cons_seq big_sepL_cons.
    iIntros "(Hmid & Hcell & Hhi)". iSplitL "Hcell"; [iExact "Hcell" |].
    iSplitL "Hmid"; [iExact "Hmid" | iExact "Hhi"].
  Qed.

  Lemma sx_argv0_shut (sp0 : mword 64) (t : nat) (pg : nat -> mword 64) :
    (t < 32)%nat ->
    (pa_stk sp0 (58 - t)) ↦₈[KT1] (mword_of_int 0 : mword 64) -∗
    sx_argv_rest sp0 t pg -∗ sx_argv0 sp0 t pg.
  Proof.
    intro Ht. iIntros "Hcell [Hmid Hhi]". rewrite /sx_argv0.
    rewrite (_ : (32 - t)%nat = S (31 - t)%nat); [| lia].
    rewrite -cons_seq big_sepL_cons.
    iSplitL "Hmid"; [iExact "Hmid" |].
    iSplitL "Hcell"; [iExact "Hcell" | iExact "Hhi"].
  Qed.

  Lemma sx_argv0_close (sp0 : mword 64) (t : nat) (pg pg' : nat -> mword 64) :
    (t < 32)%nat -> (forall j, (j < t)%nat -> pg' j = pg j) ->
    (pa_stk sp0 (58 - t)) ↦₈[KT1] pg' t -∗ sx_argv_rest sp0 t pg -∗
    sx_argv0 sp0 (S t) pg'.
  Proof.
    intros Ht Hag. iIntros "Hcell [Hmid Hhi]". rewrite /sx_argv0.
    iSplitR "Hhi".
    - rewrite seq_S big_sepL_app big_sepL_singleton.
      iSplitR "Hcell"; [| iExact "Hcell"].
      iApply (big_sepL_mono with "Hmid"). intros n j Hj.
      apply lookup_seq in Hj as [Hj0 Hlt]. subst j.
      rewrite (Hag (0 + n)%nat ltac:(lia)). done.
    - rewrite (_ : (32 - S t)%nat = (31 - t)%nat); [| lia]. iExact "Hhi".
  Qed.

  Lemma sx_pages_close (pg pg' : nat -> mword 64)
      (afun afun' : nat -> nat -> bv 8) (t : nat) :
    (forall j, (j < t)%nat -> pg' j = pg j) ->
    (forall j, (j < t)%nat -> afun' j = afun j) ->
    sx_pages pg afun 0 t -∗
    ([∗ list] i ∈ seq 0 4096, pa_add (pg' t) i ↦ₘ afun' t i) -∗
    sx_pages pg' afun' 0 (S t).
  Proof.
    intros Hp Ha. iIntros "Hold Hnew". rewrite /sx_pages !Nat.sub_0_r.
    (* [seq_S] must be aimed: a bare rewrite unifies with the INNER
       [seq 0 4096] first and peels the page's last byte instead. *)
    rewrite (seq_S t 0) big_sepL_app big_sepL_singleton.
    iSplitR "Hnew"; [| iExact "Hnew"].
    iApply (big_sepL_mono with "Hold"). intros n j Hj.
    apply lookup_seq in Hj as [Hj0 Hlt]. subst j.
    rewrite (Hp (0 + n)%nat ltac:(lia)) (Ha (0 + n)%nat ltac:(lia)). done.
  Qed.

  (* ---- everything the loop only CARRIES: the ten spill slots and the
         path buffer, split at the NUL argstr reported ---- *)
  Definition sx_carry (sp0 : mword 64) (m : regfile) (plen : nat)
      (pfun rest : nat -> bv 8) : iProp Σ :=
    ((pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
     (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
     (pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) ∗
     (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) ∗
     (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) ∗
     (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) ∗
     (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) ∗
     (pa_stk sp0 9) ↦₈[KT1] (m !!! Regidx Rs7 : mword 64) ∗
     (∃ w : mword 64, (pa_stk sp0 10) ↦₈[KT1] w) ∗
     ([∗ list] j ∈ seq 0 (S plen), pa_add (pa_stk sp0 26) j ↦ₘ[KT1] pfun j) ∗
     ([∗ list] j ∈ seq 0 (127 - plen)%nat,
        pa_add (pa_add (pa_stk sp0 26) (S plen)) j ↦ₘ[KT1] rest j))%I.

  (* ---- the nine register equations, as one transportable proposition ---- *)
  Definition sx_regs (sp0 : mword 64) (m M : regfile) (i : nat) : Prop :=
    sx_sp sp0 M /\ sx_thr m M /\
    (M !!! Regidx Rs0 : mword 64) = sp0 /\
    (M !!! Regidx Rs1 : mword 64) = pa_stk sp0 58 /\
    (M !!! Regidx Rs2 : mword 64) = (mword_of_int (Z.of_nat i) : mword 64) /\
    (M !!! Regidx Rs3 : mword 64) = pa_stk sp0 (58 - i)%nat /\
    (M !!! Regidx Rs4 : mword 64) = pa_stk sp0 58 /\
    (M !!! Regidx Rs5 : mword 64) = pa_stk sp0 60 /\
    (M !!! Regidx Rs6 : mword 64) = (mword_of_int 4096 : mword 64) /\
    (M !!! Regidx Rs7 : mword 64) = (mword_of_int 32 : mword 64).

  Lemma sxr_sp {sp0 : mword 64} {m M : regfile} {i : nat} :
    sx_regs sp0 m M i -> sx_sp sp0 M.
  Proof. intros (H&_&_&_&_&_&_&_&_&_). exact H. Qed.
  Lemma sxr_thr {sp0 : mword 64} {m M : regfile} {i : nat} :
    sx_regs sp0 m M i -> sx_thr m M.
  Proof. intros (_&H&_&_&_&_&_&_&_&_). exact H. Qed.
  Lemma sxr_s0 {sp0 : mword 64} {m M : regfile} {i : nat} :
    sx_regs sp0 m M i -> (M !!! Regidx Rs0 : mword 64) = sp0.
  Proof. intros (_&_&H&_&_&_&_&_&_&_). exact H. Qed.
  Lemma sxr_s1 {sp0 : mword 64} {m M : regfile} {i : nat} :
    sx_regs sp0 m M i -> (M !!! Regidx Rs1 : mword 64) = pa_stk sp0 58.
  Proof. intros (_&_&_&H&_&_&_&_&_&_). exact H. Qed.
  Lemma sxr_s2 {sp0 : mword 64} {m M : regfile} {i : nat} :
    sx_regs sp0 m M i ->
    (M !!! Regidx Rs2 : mword 64) = (mword_of_int (Z.of_nat i) : mword 64).
  Proof. intros (_&_&_&_&H&_&_&_&_&_). exact H. Qed.
  Lemma sxr_s3 {sp0 : mword 64} {m M : regfile} {i : nat} :
    sx_regs sp0 m M i -> (M !!! Regidx Rs3 : mword 64) = pa_stk sp0 (58 - i)%nat.
  Proof. intros (_&_&_&_&_&H&_&_&_&_). exact H. Qed.
  Lemma sxr_s4 {sp0 : mword 64} {m M : regfile} {i : nat} :
    sx_regs sp0 m M i -> (M !!! Regidx Rs4 : mword 64) = pa_stk sp0 58.
  Proof. intros (_&_&_&_&_&_&H&_&_&_). exact H. Qed.
  Lemma sxr_s5 {sp0 : mword 64} {m M : regfile} {i : nat} :
    sx_regs sp0 m M i -> (M !!! Regidx Rs5 : mword 64) = pa_stk sp0 60.
  Proof. intros (_&_&_&_&_&_&_&H&_&_). exact H. Qed.
  Lemma sxr_s6 {sp0 : mword 64} {m M : regfile} {i : nat} :
    sx_regs sp0 m M i ->
    (M !!! Regidx Rs6 : mword 64) = (mword_of_int 4096 : mword 64).
  Proof. intros (_&_&_&_&_&_&_&_&H&_). exact H. Qed.
  Lemma sxr_s7 {sp0 : mword 64} {m M : regfile} {i : nat} :
    sx_regs sp0 m M i ->
    (M !!! Regidx Rs7 : mword 64) = (mword_of_int 32 : mword 64).
  Proof. intros (_&_&_&_&_&_&_&_&_&H). exact H. Qed.

  (* an instruction that writes a CALLER-saved register moves nothing here *)
  Lemma sx_regs_tmp (sp0 : mword 64) (m M : regfile) (i : nat)
      (r : mword 5) (v : mword 64) :
    is_cs_idx r = false ->
    sx_regs sp0 m M i -> sx_regs sp0 m (<[Regidx r := v]> M) i.
  Proof.
    intros Hr (Hsp & Hthr & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7).
    assert (Hne : forall c : mword 5, is_cs_idx c = true -> Regidx r <> Regidx c)
      by (intros c Hc; exact (is_cs_idx_true_neq r c Hr Hc)).
    split_and!.
    - rewrite /sx_sp upd_ne; [exact Hsp | apply not_eq_sym, Hne; csf].
    - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23.
      rewrite upd_ne; [| apply not_eq_sym, Hne; exact Hc].
      exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23).
    - rewrite upd_ne; [exact H0 | apply not_eq_sym, Hne; csf].
    - rewrite upd_ne; [exact H1 | apply not_eq_sym, Hne; csf].
    - rewrite upd_ne; [exact H2 | apply not_eq_sym, Hne; csf].
    - rewrite upd_ne; [exact H3 | apply not_eq_sym, Hne; csf].
    - rewrite upd_ne; [exact H4 | apply not_eq_sym, Hne; csf].
    - rewrite upd_ne; [exact H5 | apply not_eq_sym, Hne; csf].
    - rewrite upd_ne; [exact H6 | apply not_eq_sym, Hne; csf].
    - rewrite upd_ne; [exact H7 | apply not_eq_sym, Hne; csf].
  Qed.

  (* ...and a CALL moves nothing here either *)
  Lemma sx_regs_call (sp0 : mword 64) (m M M' : regfile) (i : nat) :
    callee_saved M M' -> sx_regs sp0 m M i -> sx_regs sp0 m M' i.
  Proof.
    intros Hcs (Hsp & Hthr & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7).
    split_and!.
    - rewrite /sx_sp (callee_saved_lookup Hcs csp_rs1 ltac:(csf)). exact Hsp.
    - intros c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23.
      rewrite (callee_saved_lookup Hcs c Hc).
      exact (Hthr c Hc N2 N8 N9 N18 N19 N20 N21 N22 N23).
    - rewrite (callee_saved_lookup Hcs Rs0 ltac:(csf)). exact H0.
    - rewrite (callee_saved_lookup Hcs Rs1 ltac:(csf)). exact H1.
    - rewrite (callee_saved_lookup Hcs Rs2 ltac:(csf)). exact H2.
    - rewrite (callee_saved_lookup Hcs Rs3 ltac:(csf)). exact H3.
    - rewrite (callee_saved_lookup Hcs Rs4 ltac:(csf)). exact H4.
    - rewrite (callee_saved_lookup Hcs Rs5 ltac:(csf)). exact H5.
    - rewrite (callee_saved_lookup Hcs Rs6 ltac:(csf)). exact H6.
    - rewrite (callee_saved_lookup Hcs Rs7 ltac:(csf)). exact H7.
  Qed.

  (* what [bad:] needs: its own cursor, the array's base, and the frame *)
  Definition sx_bregs (sp0 : mword 64) (m M : regfile) : Prop :=
    sx_sp sp0 M /\ sx_thr m M /\
    (M !!! Regidx Rs0 : mword 64) = sp0 /\
    (M !!! Regidx Rs1 : mword 64) = pa_stk sp0 58 /\
    (M !!! Regidx Rs4 : mword 64) = pa_stk sp0 58.

  Lemma sx_regs_bregs (sp0 : mword 64) (m M : regfile) (i : nat) :
    sx_regs sp0 m M i -> sx_bregs sp0 m M.
  Proof.
    intros H. split_and!;
      [ exact (sxr_sp H) | exact (sxr_thr H) | exact (sxr_s0 H)
      | exact (sxr_s1 H) | exact (sxr_s4 H) ].
  Qed.

End SysExecLoop.

(* ===================================================================== *)
(*  THE TWO SEAM STATES.  [sie_cap_gpr] and [cpu_own] are HART-INDEXED, so *)
(*  a predicate that bundles them takes the hart as a parameter -- which   *)
(*  is what makes the published state land at the hart the iteration       *)
(*  ENDED on rather than the one it started on.  Their own section, so     *)
(*  that the step and the loop below can pin it per use with               *)
(*  [(CID0 := ...)].                                                      *)
(* ===================================================================== *)
Section SysExecState.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).

  (* ---- the loop's state, at its head (+0x056) and at the break (+0x0b6):
         one predicate, parameterised by the pc ---- *)
  Definition sx_body (γf : gname) (jp : nat) (pid : mword 32) (V : pprivate)
      (K : nat) (eb b : bool) (lks : gset string)
      (sp0 : mword 64) (m : regfile) (plen : nat) (pfun rest : nat -> bv 8)
      (uav : mword 64)
      (M : regfile) (P : uptd) (i : nat)
      (pg : nat -> mword 64) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (pcv : mword 64) : iProp Σ :=
    (⌜ (i < 32)%nat /\ uptd_ext (pv_upt V) P /\ sx_ok pg alen afun i /\
       sx_regs sp0 m M i ⌝ ∗
     pc_is pcv ∗
     sie_cap_gpr KT1 M (K - 60)%nat b (proc_addr jp) ∗
     cpu_own 0 eb (proc_addr jp) b lks ∗
     proc_priv γf (proc_addr jp) pid (upd_upt V P) ∗
     sx_carry sp0 m plen pfun rest ∗
     (pa_stk sp0 59) ↦₈[KT1] uav ∗
     (∃ w : mword 64, (pa_stk sp0 60) ↦₈[KT1] w) ∗
     sx_argv0 sp0 i pg ∗
     sx_pages pg afun 0 i)%I.

  (* ---- [bad:] at +0x092 ---- *)
  Definition sx_bad (γf : gname) (jp : nat) (pid : mword 32) (V : pprivate)
      (K : nat) (eb b : bool) (lks : gset string)
      (sp0 : mword 64) (m : regfile) (plen : nat) (pfun rest : nat -> bv 8)
      (uav : mword 64)
      (M : regfile) (P : uptd) (t : nat)
      (pg : nat -> mword 64) (afun : nat -> nat -> bv 8) : iProp Σ :=
    (⌜ (t <= 32)%nat /\ uptd_ext (pv_upt V) P /\ sx_pgok pg t /\
       sx_bregs sp0 m M ⌝ ∗
     pc_is (mword_of_int (SX + 0x92) : mword 64) ∗
     sie_cap_gpr KT1 M (K - 60)%nat b (proc_addr jp) ∗
     cpu_own 0 eb (proc_addr jp) b lks ∗
     proc_priv γf (proc_addr jp) pid (upd_upt V P) ∗
     sx_carry sp0 m plen pfun rest ∗
     (pa_stk sp0 59) ↦₈[KT1] uav ∗
     (∃ w : mword 64, (pa_stk sp0 60) ↦₈[KT1] w) ∗
     sx_argv0 sp0 t pg ∗
     sx_pages pg afun 0 t)%I.

  (* the two introduction rules, written once because the body reaches
     [bad:] from four places and the head from two *)
  Lemma sx_body_intro (γf : gname) (jp : nat) (pid : mword 32) (V : pprivate)
      (K : nat) (eb b : bool) (lks : gset string)
      (sp0 : mword 64) (m : regfile) (plen : nat) (pfun rest : nat -> bv 8)
      (uav : mword 64) (M : regfile) (P : uptd) (i : nat)
      (pg : nat -> mword 64) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (pcv : mword 64) :
    (i < 32)%nat -> uptd_ext (pv_upt V) P -> sx_ok pg alen afun i ->
    sx_regs sp0 m M i ->
    pc_is pcv -∗
    sie_cap_gpr KT1 M (K - 60)%nat b (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) b lks -∗
    proc_priv γf (proc_addr jp) pid (upd_upt V P) -∗
    sx_carry sp0 m plen pfun rest -∗
    (pa_stk sp0 59) ↦₈[KT1] uav -∗
    (∃ w : mword 64, (pa_stk sp0 60) ↦₈[KT1] w) -∗
    sx_argv0 sp0 i pg -∗
    sx_pages pg afun 0 i -∗
    sx_body γf jp pid V K eb b lks sp0 m plen pfun rest uav
            M P i pg alen afun pcv.
  Proof.
    intros H1 H2 H3 H4.
    iIntros "Hpc Hcg Hcnt Hpriv Hcarry F59 F60 Harr Hpgs". rewrite /sx_body.
    iSplitR; [iPureIntro; split_and!; assumption |].
    iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
    iSplitL "Hcnt"; [iExact "Hcnt" |]. iSplitL "Hpriv"; [iExact "Hpriv" |].
    iSplitL "Hcarry"; [iExact "Hcarry" |]. iSplitL "F59"; [iExact "F59" |].
    iSplitL "F60"; [iExact "F60" |].
    iSplitL "Harr"; [iExact "Harr" | iExact "Hpgs"].
  Qed.

  Lemma sx_bad_intro (γf : gname) (jp : nat) (pid : mword 32) (V : pprivate)
      (K : nat) (eb b : bool) (lks : gset string)
      (sp0 : mword 64) (m : regfile) (plen : nat) (pfun rest : nat -> bv 8)
      (uav : mword 64) (M : regfile) (P : uptd) (t : nat)
      (pg : nat -> mword 64) (afun : nat -> nat -> bv 8) :
    (t <= 32)%nat -> uptd_ext (pv_upt V) P -> sx_pgok pg t ->
    sx_bregs sp0 m M ->
    pc_is (mword_of_int (SX + 0x92) : mword 64) -∗
    sie_cap_gpr KT1 M (K - 60)%nat b (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) b lks -∗
    proc_priv γf (proc_addr jp) pid (upd_upt V P) -∗
    sx_carry sp0 m plen pfun rest -∗
    (pa_stk sp0 59) ↦₈[KT1] uav -∗
    (∃ w : mword 64, (pa_stk sp0 60) ↦₈[KT1] w) -∗
    sx_argv0 sp0 t pg -∗
    sx_pages pg afun 0 t -∗
    sx_bad γf jp pid V K eb b lks sp0 m plen pfun rest uav M P t pg afun.
  Proof.
    intros H1 H2 H3 H4.
    iIntros "Hpc Hcg Hcnt Hpriv Hcarry F59 F60 Harr Hpgs". rewrite /sx_bad.
    iSplitR; [iPureIntro; split_and!; assumption |].
    iSplitL "Hpc"; [iExact "Hpc" |]. iSplitL "Hcg"; [iExact "Hcg" |].
    iSplitL "Hcnt"; [iExact "Hcnt" |]. iSplitL "Hpriv"; [iExact "Hpriv" |].
    iSplitL "Hcarry"; [iExact "Hcarry" |]. iSplitL "F59"; [iExact "F59" |].
    iSplitL "F60"; [iExact "F60" |].
    iSplitL "Harr"; [iExact "Harr" | iExact "Hpgs"].
  Qed.

End SysExecState.

(* ===================================================================== *)
(*  THE BODY AND ITS INDUCTION.  Both take the hart as a LEMMA binder --   *)
(*  the loop reverts it, and the step is applied once per iteration at     *)
(*  whichever hart the previous one ended on.                             *)
(* ===================================================================== *)
Section SysExecStep.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.
  Local Ltac csf := vm_compute; reflexivity.

  (* ---- two arithmetic facts the body needs ---- *)

  Lemma sx_incr (i : nat) :
    add_vec (mword_of_int (Z.of_nat i) : mword 64)
      (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))
    = (mword_of_int (Z.of_nat (S i)) : mword 64).
  Proof.
    assert (Him : (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))
                   : mword 64) = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Him. apply bv_eq.
    rewrite add_vec64_unsigned !moi64_unsigned.
    rewrite bv_wrap_add_idemp_l bv_wrap_add_idemp_r. f_equal. lia.
  Qed.

  Lemma sx_moi_inj (a c : Z) :
    (0 <= a < 2 ^ 64)%Z -> (0 <= c < 2 ^ 64)%Z ->
    (mword_of_int a : mword 64) = (mword_of_int c : mword 64) -> a = c.
  Proof.
    intros Ha Hc Heq. apply (f_equal bv_unsigned) in Heq.
    rewrite !moi64_unsigned in Heq.
    assert (HM : (2 ^ 64)%Z = 18446744073709551616%Z) by (vm_compute; reflexivity).
    rewrite !bvw64_small in Heq; [exact Heq | lia | lia].
  Qed.

  Lemma sx_m32 : (mword_of_int 32 : mword 64) = mword_of_int (Z.of_nat 32).
  Proof. apply bv_eq; vm_compute; reflexivity. Qed.

  Lemma sx_moi_nat_inj (a c : nat) : (a <= 32)%nat -> (c <= 32)%nat ->
    (mword_of_int (Z.of_nat a) : mword 64) = (mword_of_int (Z.of_nat c) : mword 64) ->
    a = c.
  Proof.
    intros Ha Hc Heq.
    assert (Hz : Z.of_nat a = Z.of_nat c).
    { apply (sx_moi_inj (Z.of_nat a) (Z.of_nat c));
        [ change (2 ^ 64)%Z with 18446744073709551616%Z; lia
        | change (2 ^ 64)%Z with 18446744073709551616%Z; lia
        | exact Heq ]. }
    lia.
  Qed.

  (* ===================================================================== *)
  (*  ONE ITERATION, +0x056 .. +0x090.                                      *)
  (* ===================================================================== *)
  Lemma sx_step `{CID0 : CpuId}
      (γf γa : gname) (jp : nat) (pid : mword 32) (V : pprivate)
      (K : nat) (eb b : bool) (lks : gset string)
      (sp0 : mword 64) (m : regfile) (plen : nat) (pfun rest : nat -> bv 8)
      (uav : mword 64)
      (M : regfile) (P : uptd) (i : nat)
      (pg : nat -> mword 64) (alen : nat -> nat) (afun : nat -> nat -> bv 8) :
    (K_sys_exec <= K)%nat ->
    locks_below lks "kmem" ->
    kernel_text -∗
    kalloc_env γa None -∗
    sx_body γf jp pid V K eb b lks sp0 m plen pfun rest uav
            M P i pg alen afun (mword_of_int (SX + 0x56) : mword 64) -∗
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M' : regfile) (P' : uptd) (i' : nat)
        (pg' : nat -> mword 64) (alen' : nat -> nat)
        (afun' : nat -> nat -> bv 8),
        ((⌜i' = S i⌝ ∗
          sx_body γf jp pid V K eb b lks sp0 m plen pfun rest uav
                  M' P' i' pg' alen' afun'
                  (mword_of_int (SX + 0x56) : mword 64))
         ∨ sx_body γf jp pid V K eb b lks sp0 m plen pfun rest uav
                   M' P' i' pg' alen' afun'
                   (mword_of_int (SX + 0xb6) : mword 64)
         ∨ sx_bad γf jp pid V K eb b lks sp0 m plen pfun rest uav
                  M' P' i' pg' afun') -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlb.
    destruct (sx_kb K HK) as (Kkx & Kar & Kaa & Kfa & Kfs & K14 & K2 & K60 & Kpop).
    iIntros "#Htext #Hka Hst Hout".
    rewrite /sx_body.
    iDestruct "Hst" as "((%Hi32 & %Hext & %Hok & %HR) & Hpc & Hcg & Hcnt & Hpriv
                         & Hcarry & F59 & F60 & Harr & Hpgs)".
    iAssert (kalloc_env γa None) as "#Hka2"; [iExact "Hka" |].
    iDestruct "Hka2" as (γk) "(#Hlk & #Hav)".
    iPoseProof (sxi_056 with "Htext") as "Hi56".
    iPoseProof (sxi_05a with "Htext") as "Hi5a".
    iPoseProof (sxi_05c with "Htext") as "Hi5c".
    iPoseProof (sxi_060 with "Htext") as "Hi60".
    iPoseProof (sxi_062 with "Htext") as "Hi62".
    iPoseProof (sxi_066 with "Htext") as "Hi66".
    iPoseProof (sxi_06a with "Htext") as "Hi6a".
    iPoseProof (sxi_06e with "Htext") as "Hi6e".
    iPoseProof (sxi_070 with "Htext") as "Hi70".
    iPoseProof (sxi_074 with "Htext") as "Hi74".
    iPoseProof (sxi_076 with "Htext") as "Hi76".
    iPoseProof (sxi_07a with "Htext") as "Hi7a".
    iPoseProof (sxi_07c with "Htext") as "Hi7c".
    iPoseProof (sxi_07e with "Htext") as "Hi7e".
    iPoseProof (sxi_082 with "Htext") as "Hi82".
    iPoseProof (sxi_086 with "Htext") as "Hi86".
    iPoseProof (sxi_08a with "Htext") as "Hi8a".
    iPoseProof (sxi_08c with "Htext") as "Hi8c".
    iPoseProof (sxi_08e with "Htext") as "Hi8e".
    (* ===== +0x056 slli a0,s2,3 : 8*i ===== *)
    assert (Hg2 : rget M Rs2 = (M !!! Regidx Rs2 : mword 64))
      by (apply rget_ne; nz).
    assert (Hsl : shift_bits_left (rget M Rs2)
                    (subrange_vec_dec (mword_of_int 3 : mword 6)
                       (Z.sub log2_xlen 1) 0)
                  = (mword_of_int (Z.of_nat i * 8) : mword 64)).
    { rewrite Hg2 (sxr_s2 HR). apply ofile_slli3; lia. }
    iApply (wp_slli_s_sconf (mword_of_int (SX + 0x56) : mword 64) Ra0 Rs2
              (mword_of_int 3 : mword 6) (mword_of_int (Z.of_nat i * 8) : mword 64)
              M (K - 60)%nat b ltac:(nz) ltac:(rdok) Hsl with "Hcg Hpc Hi56").
    iIntros (CID1 Hq1) "Hcg Hpc".
    set (N1 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (Z.of_nat i * 8) : mword 64)]> M).
    assert (HR1 : sx_regs sp0 m N1 i)
      by (rewrite /N1; apply sx_regs_tmp; [csf | exact HR]).
    assert (Hp5a : add_vec_int (mword_of_int (SX + 0x56) : mword 64) 4
                   = mword_of_int (SX + 0x5a)) by pcw.
    iEval (rewrite Hp5a) in "Hpc".
    (* ===== +0x05a c.mv a1,s5 : &uarg ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (SX + 0x5a) : mword 64) Ra1 Rs5
              N1 (K - 60)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5a").
    iIntros (CID2 Hq2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N2 := <[Regidx Ra1 := regval_into_reg
                  (add_vec zero_reg (N1 !!! Regidx Rs5))]> N1).
    assert (HR2 : sx_regs sp0 m N2 i)
      by (rewrite /N2; apply sx_regs_tmp; [csf | exact HR1]).
    assert (HN2a1 : (N2 !!! Regidx Ra1 : mword 64) = pa_stk sp0 60).
    { rewrite /N2 upd_eq (sxr_s5 HR1). apply add_vec_zero_l. }
    assert (Hp5c : add_vec_int (mword_of_int (SX + 0x5a) : mword 64) 2
                   = mword_of_int (SX + 0x5c)) by pcw.
    iEval (rewrite Hp5c) in "Hpc".
    (* ===== +0x05c ld a5,-472(s0) : uargv ===== *)
    assert (Hg0 : rget N2 Rs0 = (N2 !!! Regidx Rs0 : mword 64))
      by (apply rget_ne; nz).
    assert (Hc59 : add_vec (rget N2 Rs0)
                     (sign_extend' 64 (mword_of_int 3624 : mword 12))
                   = pa_stk sp0 59)
      by (rewrite Hg0 (sxr_s0 HR2); apply sx_uargv).
    iEval (rewrite -Hc59) in "F59".
    iApply (wp_ld_s_sconf (mword_of_int (SX + 0x5c) : mword 64) Ra5 Rs0
              (mword_of_int 3624 : mword 12) N2 (K - 60)%nat uav b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi5c F59").
    iIntros (CID3 Hq3) "Hcg Hpc F59".
    iEval (rewrite Hc59) in "F59".
    set (N3 := <[Regidx Ra5 := regval_into_reg uav]> N2).
    assert (HR3 : sx_regs sp0 m N3 i)
      by (rewrite /N3; apply sx_regs_tmp; [csf | exact HR2]).
    assert (HN3a1 : (N3 !!! Regidx Ra1 : mword 64) = pa_stk sp0 60)
      by (rewrite /N3 upd_ne; [exact HN2a1 | nz]).
    assert (Hp60 : add_vec_int (mword_of_int (SX + 0x5c) : mword 64) 4
                   = mword_of_int (SX + 0x60)) by pcw.
    iEval (rewrite Hp60) in "Hpc".
    (* ===== +0x060 c.add a0,a5 : uargv + 8i ===== *)
    iApply (wp_cadd_s_sconf (mword_of_int (SX + 0x60) : mword 64) Ra0 Ra5
              N3 (K - 60)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi60").
    iIntros (CID4 Hq4) "Hcg Hpc".
    (* A WRITTEN VALUE SPELLED WITH [rget] IS PINNED TO THE HART THE
       INSTRUCTION WAS ISSUED AT, so normalise it to the hart-free [!!!]
       form INSIDE the hypothesis before naming the new map -- a [set] whose
       [rget] resolves at the ambient hart silently fails to fold. *)
    iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    set (N4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (N3 !!! Regidx Ra0) (N3 !!! Regidx Ra5))]> N3).
    assert (HR4 : sx_regs sp0 m N4 i)
      by (rewrite /N4; apply sx_regs_tmp; [csf | exact HR3]).
    assert (HN4a1 : (N4 !!! Regidx Ra1 : mword 64) = pa_stk sp0 60)
      by (rewrite /N4 upd_ne; [exact HN3a1 | nz]).
    assert (Hp62 : add_vec_int (mword_of_int (SX + 0x60) : mword 64) 2
                   = mword_of_int (SX + 0x62)) by pcw.
    iEval (rewrite Hp62) in "Hpc".
    (* ===== +0x062 jal ra,fetchaddr ===== *)
    assert (Htfa : add_vec (mword_of_int (SX + 0x62) : mword 64)
                     (sign_extend' 64 (mword_of_int 2085812 : mword 21))
                   = mword_of_int KernelSyms.fetchaddr) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (SX + 0x62) : mword 64) Rra
              (mword_of_int 2085812 : mword 21) N4 (K - 60)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htfa; vm_compute; reflexivity)
              with "Hcg Hpc Hi62").
    iIntros (CID5 Hq5) "Hcg Hpc". iEval (rewrite Htfa) in "Hpc".
    set (N5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SX + 0x62) : mword 64) 4)]> N4).
    assert (HR5 : sx_regs sp0 m N5 i)
      by (rewrite /N5; apply sx_regs_tmp; [csf | exact HR4]).
    assert (HN5a1 : (N5 !!! Regidx Ra1 : mword 64) = pa_stk sp0 60)
      by (rewrite /N5 upd_ne; [exact HN4a1 | nz]).
    assert (HN5ra : ret_pc (N5 !!! Regidx Rra : mword 64)
                    = (mword_of_int (SX + 0x66) : mword 64))
      by (rewrite /N5 upd_eq; pcw).
    iDestruct "F60" as (u0) "F60".
    iEval (rewrite -HN5a1) in "F60".
    iDestruct (cpu_own_transport CID0 CID5 0%nat eb (proc_addr jp) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Fetchaddr.wp_fetchaddr_sconf γa γf N5 (K - 60)%nat eb (proc_addr jp)
              pid (upd_upt V P) u0 b lks Kfa
              with "Hcg Hcnt Htext Hpc Hpriv Hka F60").
    iIntros (CID6 Hq6 mf Pa) "%Hcsa %Hexta Hcg Hcnt Hpc Hpriv Hfa".
    assert (Hupa : upd_upt (upd_upt V P) Pa = upd_upt V Pa) by reflexivity.
    iEval (rewrite Hupa) in "Hpriv".
    assert (Hexta' : uptd_ext (pv_upt V) Pa)
      by (apply (uptd_ext_trans (pv_upt V) P Pa); [exact Hext | exact Hexta]).
    assert (HR6 : sx_regs sp0 m mf i)
      by exact (sx_regs_call sp0 m N5 mf i Hcsa HR5).
    iEval (rewrite HN5ra) in "Hpc".
    iEval (rewrite HN5a1) in "Hfa".
    (* ===== +0x066 blt a0,zero,+0x92 ===== *)
    assert (Ht92 : add_vec (mword_of_int (SX + 0x66) : mword 64)
                     (sign_extend' 64 (mword_of_int 44 : mword 13))
                   = (mword_of_int (SX + 0x92) : mword 64)) by pcw.
    assert (Hgfa : rget mf Ra0 = (mf !!! Regidx Ra0 : mword 64))
      by (apply rget_ne; nz).
    rewrite /fetchaddr_post.
    iDestruct "Hfa" as "[[%Hfa1 F60] | [%Hfa2 F60]]".
    { (* fetchaddr FAILED before it wrote: [-1], the cell is untouched *)
      destruct Hfa1 as [Hm1 _].
      assert (Hcmp : zopz0zI_s (rget mf Ra0) zero_reg = true)
        by (rewrite Hgfa Hm1; exact sx_m1_neg).
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (SX + 0x66) : mword 64)
                (mword_of_int 44 : mword 13) Ra0 mf (K - 60)%nat b
                ltac:(nz) Hcmp ltac:(rewrite Ht92; vm_compute; reflexivity)
                with "Hcg Hpc Hi66").
      iIntros (CID7 Hq7). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Ht92) in "Hpc".
      iSpecialize ("Hout" $! CID7 with "[%]"); [wp_next_chain |].
      iDestruct (cpu_own_transport CID6 CID7 0%nat eb (proc_addr jp) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply ("Hout" $! mf Pa i pg alen afun). iRight. iRight.
      iApply (sx_bad_intro (CID0 := CID7) γf jp pid V K eb b lks sp0 m plen pfun rest uav
                mf Pa i pg afun ltac:(lia) Hexta'
                (sx_ok_pgok pg alen afun i Hok) (sx_regs_bregs sp0 m mf i HR6)
                with "Hpc Hcg Hcnt Hpriv Hcarry F59 [F60] Harr Hpgs").
      iExists u0. iExact "F60". }
    (* fetchaddr returned: 0 (it wrote) or -1 (it did not) *)
    destruct Hfa2 as [Hr Hfok].
    iDestruct "F60" as (u1) "F60".
    destruct Hr as [Hr0 | Hrm1]; last first.
    { (* -1 again: the same [bad:] *)
      assert (Hcmp : zopz0zI_s (rget mf Ra0) zero_reg = true)
        by (rewrite Hgfa Hrm1; exact sx_m1_neg).
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (SX + 0x66) : mword 64)
                (mword_of_int 44 : mword 13) Ra0 mf (K - 60)%nat b
                ltac:(nz) Hcmp ltac:(rewrite Ht92; vm_compute; reflexivity)
                with "Hcg Hpc Hi66").
      iIntros (CID7 Hq7). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Ht92) in "Hpc".
      iSpecialize ("Hout" $! CID7 with "[%]"); [wp_next_chain |].
      iDestruct (cpu_own_transport CID6 CID7 0%nat eb (proc_addr jp) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply ("Hout" $! mf Pa i pg alen afun). iRight. iRight.
      iApply (sx_bad_intro (CID0 := CID7) γf jp pid V K eb b lks sp0 m plen pfun rest uav
                mf Pa i pg afun ltac:(lia) Hexta'
                (sx_ok_pgok pg alen afun i Hok) (sx_regs_bregs sp0 m mf i HR6)
                with "Hpc Hcg Hcnt Hpriv Hcarry F59 [F60] Harr Hpgs").
      iExists u1. iExact "F60". }
    (* ---- the copy-in succeeded ---- *)
    assert (Hcmp : zopz0zI_s (rget mf Ra0) zero_reg = false).
    { rewrite Hgfa Hr0. apply sx_nonneg. lia. }
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (SX + 0x66) : mword 64)
              (mword_of_int 44 : mword 13) Ra0 mf (K - 60)%nat b
              ltac:(nz) Hcmp with "Hcg Hpc Hi66").
    iIntros (CID7 Hq7) "Hcg Hpc".
    assert (Hp6a : add_vec_int (mword_of_int (SX + 0x66) : mword 64) 4
                   = mword_of_int (SX + 0x6a)) by pcw.
    iEval (rewrite Hp6a) in "Hpc".
    (* ===== +0x06a ld a5,-480(s0) : uarg ===== *)
    assert (Hg0b : rget mf Rs0 = (mf !!! Regidx Rs0 : mword 64))
      by (apply rget_ne; nz).
    assert (Hc60 : add_vec (rget mf Rs0)
                     (sign_extend' 64 (mword_of_int 3616 : mword 12))
                   = pa_stk sp0 60)
      by (rewrite Hg0b (sxr_s0 HR6); apply sx_uarg).
    iEval (rewrite -Hc60) in "F60".
    iApply (wp_ld_s_sconf (mword_of_int (SX + 0x6a) : mword 64) Ra5 Rs0
              (mword_of_int 3616 : mword 12) mf (K - 60)%nat u1 b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi6a F60").
    iIntros (CID8 Hq8) "Hcg Hpc F60".
    iEval (rewrite Hc60) in "F60".
    set (Q1 := <[Regidx Ra5 := regval_into_reg u1]> mf).
    assert (HRq1 : sx_regs sp0 m Q1 i)
      by (rewrite /Q1; apply sx_regs_tmp; [csf | exact HR6]).
    assert (HQ1a5 : (Q1 !!! Regidx Ra5 : mword 64) = u1)
      by (rewrite /Q1; apply upd_eq).
    assert (Hp6e : add_vec_int (mword_of_int (SX + 0x6a) : mword 64) 4
                   = mword_of_int (SX + 0x6e)) by pcw.
    iEval (rewrite Hp6e) in "Hpc".
    (* ===== +0x06e c.beqz a5,+0x0b6 : the BREAK ===== *)
    assert (Htb6 : add_vec (mword_of_int (SX + 0x6e) : mword 64)
                     (sign_extend' 64 (sign_extend' 13
                        (concat_vec (mword_of_int 36 : mword 8) ('b"0"))))
                   = (mword_of_int (SX + 0xb6) : mword 64)) by pcw.
    assert (Hgq5 : rget Q1 Ra5 = (Q1 !!! Regidx Ra5 : mword 64))
      by (apply rget_ne; nz).
    destruct (decide (u1 = (mword_of_int 0 : mword 64))) as [Hu1z | Hu1nz].
    { (* the vector's terminating NULL: break out with [i] arguments *)
      assert (Hcmpb : eq_vec (rget Q1 Ra5) zero_reg = true).
      { rewrite Hgq5 HQ1a5 Hu1z. apply eq_vec_true_iff. symmetry. exact sx_zreg0. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (SX + 0x6e) : mword 64)
                (mword_of_int 36 : mword 8) (Cregidx (mword_of_int 7)) Ra5
                Q1 (K - 60)%nat b ltac:(csf) ltac:(nz) Hcmpb
                ltac:(rewrite Htb6; vm_compute; reflexivity)
                with "Hcg Hpc Hi6e").
      iIntros (CID9 Hq9). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htb6) in "Hpc".
      iSpecialize ("Hout" $! CID9 with "[%]"); [wp_next_chain |].
      iDestruct (cpu_own_transport CID6 CID9 0%nat eb (proc_addr jp) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply ("Hout" $! Q1 Pa i pg alen afun). iRight. iLeft.
      iApply (sx_body_intro (CID0 := CID9) γf jp pid V K eb b lks sp0 m plen pfun rest uav
                Q1 Pa i pg alen afun (mword_of_int (SX + 0xb6) : mword 64)
                Hi32 Hexta' Hok HRq1
                with "Hpc Hcg Hcnt Hpriv Hcarry F59 [F60] Harr Hpgs").
      iExists u1. iExact "F60". }
    (* ---- a real pointer: allocate a page for its string ---- *)
    assert (Hcmpb : eq_vec (rget Q1 Ra5) zero_reg = false).
    { rewrite Hgq5 HQ1a5. apply eq_vec_false_iff. intro Hc.
      apply Hu1nz. rewrite Hc. exact sx_zreg0. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (SX + 0x6e) : mword 64)
              (mword_of_int 36 : mword 8) (Cregidx (mword_of_int 7)) Ra5
              Q1 (K - 60)%nat b ltac:(csf) ltac:(nz) Hcmpb with "Hcg Hpc Hi6e").
    iIntros (CID9 Hq9) "Hcg Hpc".
    assert (Hp70 : add_vec_int (mword_of_int (SX + 0x6e) : mword 64) 2
                   = mword_of_int (SX + 0x70)) by pcw.
    iEval (rewrite Hp70) in "Hpc".
    (* ===== +0x070 jal ra,kalloc ===== *)
    assert (Htka : add_vec (mword_of_int (SX + 0x70) : mword 64)
                     (sign_extend' 64 (mword_of_int 2078454 : mword 21))
                   = mword_of_int KernelSyms.kalloc) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (SX + 0x70) : mword 64) Rra
              (mword_of_int 2078454 : mword 21) Q1 (K - 60)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htka; vm_compute; reflexivity)
              with "Hcg Hpc Hi70").
    iIntros (CID10 Hq10) "Hcg Hpc". iEval (rewrite Htka) in "Hpc".
    set (Q2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SX + 0x70) : mword 64) 4)]> Q1).
    assert (HRq2 : sx_regs sp0 m Q2 i)
      by (rewrite /Q2; apply sx_regs_tmp; [csf | exact HRq1]).
    assert (HQ2ra : ret_pc (Q2 !!! Regidx Rra : mword 64)
                    = (mword_of_int (SX + 0x74) : mword 64))
      by (rewrite /Q2 upd_eq; pcw).
    iDestruct (cpu_own_transport CID6 CID10 0%nat eb (proc_addr jp) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Kalloc.wp_kalloc_sconf KT1 γa γk
              (mword_of_int (KernelSyms.kmem + 24)) Q2 None 0%nat eb
              (proc_addr jp) (K - 60)%nat b lks K14 eq_refl sx_noff0 Hlb
              with "Hcg Hcnt Htext Hpc Hlk Hav").
    iIntros (CID11 Hq11 mr) "Hcg Hcnt Hpc %Hcsr Hkp".
    iEval (rewrite HQ2ra) in "Hpc".
    assert (HRr : sx_regs sp0 m mr i)
      by exact (sx_regs_call sp0 m Q2 mr i Hcsr HRq2).
    (* ===== +0x074 c.mv a1,a0 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (SX + 0x74) : mword 64) Ra1 Ra0
              mr (K - 60)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi74").
    iIntros (CID12 Hq12) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (Q3 := <[Regidx Ra1 := regval_into_reg
                  (add_vec zero_reg (mr !!! Regidx Ra0))]> mr).
    assert (HRq3 : sx_regs sp0 m Q3 i)
      by (rewrite /Q3; apply sx_regs_tmp; [csf | exact HRr]).
    assert (HQ3a1 : (Q3 !!! Regidx Ra1 : mword 64)
                    = (mr !!! Regidx Ra0 : mword 64))
      by (rewrite /Q3 upd_eq; apply add_vec_zero_l).
    assert (HQ3a0 : (Q3 !!! Regidx Ra0 : mword 64)
                    = (mr !!! Regidx Ra0 : mword 64))
      by (rewrite /Q3 upd_ne; [reflexivity | nz]).
    assert (Hp76 : add_vec_int (mword_of_int (SX + 0x74) : mword 64) 2
                   = mword_of_int (SX + 0x76)) by pcw.
    iEval (rewrite Hp76) in "Hpc".
    (* ===== +0x076 sd a0,0(s3) : argv[i] = the page ===== *)
    iDestruct (sx_argv0_open sp0 i pg ltac:(lia) with "Harr") as "[Hcell Hrest]".
    assert (Hg3 : rget Q3 Rs3 = (Q3 !!! Regidx Rs3 : mword 64))
      by (apply rget_ne; nz).
    assert (Hcs3 : add_vec (rget Q3 Rs3)
                     (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = pa_stk sp0 (58 - i)%nat)
      by (rewrite Hg3 (sxr_s3 HRq3); apply sx_off0).
    iEval (rewrite -Hcs3) in "Hcell".
    iApply (wp_sd_s_sconf (mword_of_int (SX + 0x76) : mword 64) Ra0 Rs3
              (mword_of_int 0 : mword 12) Q3 (K - 60)%nat
              (mword_of_int 0 : mword 64) b with "Hcg Hpc Hi76 Hcell").
    iIntros (CID13 Hq13) "Hcg Hpc Hcell".
    iEval (rewrite Hcs3) in "Hcell".
    iEval (rgne) in "Hcell". iEval (rewrite HQ3a0) in "Hcell".
    assert (Hgq0 : rget Q3 Ra0 = (Q3 !!! Regidx Ra0 : mword 64))
      by (apply rget_ne; nz).
    assert (Hp7a : add_vec_int (mword_of_int (SX + 0x76) : mword 64) 4
                   = mword_of_int (SX + 0x7a)) by pcw.
    iEval (rewrite Hp7a) in "Hpc".
    (* ===== +0x07a c.beqz a0,+0x92 ===== *)
    assert (Ht92b : add_vec (mword_of_int (SX + 0x7a) : mword 64)
                      (sign_extend' 64 (sign_extend' 13
                         (concat_vec (mword_of_int 12 : mword 8) ('b"0"))))
                    = (mword_of_int (SX + 0x92) : mword 64)) by pcw.
    destruct (decide ((mr !!! Regidx Ra0 : mword 64)
                      = (mword_of_int 0 : mword 64))) as [Hpz | Hpnz].
    { (* kalloc came back empty: the store put the zero back, so the array is
         exactly as it was and [bad:] frees the first [i] pages *)
      assert (Hcmpk : eq_vec (rget Q3 Ra0) zero_reg = true).
      { rewrite Hgq0 HQ3a0 Hpz. apply eq_vec_true_iff. symmetry. exact sx_zreg0. }
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (SX + 0x7a) : mword 64)
                (mword_of_int 12 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                Q3 (K - 60)%nat b ltac:(csf) ltac:(nz) Hcmpk
                ltac:(rewrite Ht92b; vm_compute; reflexivity)
                with "Hcg Hpc Hi7a").
      iIntros (CID14 Hq14). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Ht92b) in "Hpc".
      iEval (rewrite Hpz) in "Hcell".
      iDestruct (sx_argv0_shut sp0 i pg ltac:(lia) with "Hcell Hrest") as "Harr".
      iSpecialize ("Hout" $! CID14 with "[%]"); [wp_next_chain |].
      iDestruct (cpu_own_transport CID11 CID14 0%nat eb (proc_addr jp) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply ("Hout" $! Q3 Pa i pg alen afun). iRight. iRight.
      iApply (sx_bad_intro (CID0 := CID14) γf jp pid V K eb b lks sp0 m plen pfun rest uav
                Q3 Pa i pg afun ltac:(lia) Hexta'
                (sx_ok_pgok pg alen afun i Hok) (sx_regs_bregs sp0 m Q3 i HRq3)
                with "Hpc Hcg Hcnt Hpriv Hcarry F59 [F60] Harr Hpgs").
      iExists u1. iExact "F60". }
    (* ---- a real page ---- *)
    iDestruct "Hkp" as "[(%Hnull & %Hz & Hav2) | (%Hpv & Hpage & Hav2)]".
    { exfalso. apply Hpnz. rewrite Hnull. reflexivity. }
    assert (Hcmpk : eq_vec (rget Q3 Ra0) zero_reg = false).
    { rewrite Hgq0 HQ3a0. apply eq_vec_false_iff. intro Hc.
      apply Hpnz. rewrite Hc. exact sx_zreg0. }
    iApply (wp_cbeqz_fall_s_sconf (mword_of_int (SX + 0x7a) : mword 64)
              (mword_of_int 12 : mword 8) (Cregidx (mword_of_int 2)) Ra0
              Q3 (K - 60)%nat b ltac:(csf) ltac:(nz) Hcmpk with "Hcg Hpc Hi7a").
    iIntros (CID14 Hq14) "Hcg Hpc".
    assert (Hp7c : add_vec_int (mword_of_int (SX + 0x7a) : mword 64) 2
                   = mword_of_int (SX + 0x7c)) by pcw.
    iEval (rewrite Hp7c) in "Hpc".
    (* ===== +0x07c c.mv a2,s6 : PGSIZE ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (SX + 0x7c) : mword 64) Ra2 Rs6
              Q3 (K - 60)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7c").
    iIntros (CID15 Hq15) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (Q4 := <[Regidx Ra2 := regval_into_reg
                  (add_vec zero_reg (Q3 !!! Regidx Rs6))]> Q3).
    assert (HRq4 : sx_regs sp0 m Q4 i)
      by (rewrite /Q4; apply sx_regs_tmp; [csf | exact HRq3]).
    assert (HQ4a2 : (Q4 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 4096) : mword 64)).
    { rewrite /Q4 upd_eq (sxr_s6 HRq3) add_vec_zero_l.
      apply bv_eq; vm_compute; reflexivity. }
    assert (HQ4a1 : (Q4 !!! Regidx Ra1 : mword 64)
                    = (mr !!! Regidx Ra0 : mword 64))
      by (rewrite /Q4 upd_ne; [exact HQ3a1 | nz]).
    assert (Hp7e : add_vec_int (mword_of_int (SX + 0x7c) : mword 64) 2
                   = mword_of_int (SX + 0x7e)) by pcw.
    iEval (rewrite Hp7e) in "Hpc".
    (* ===== +0x07e ld a0,-480(s0) : uarg ===== *)
    assert (Hg0c : rget Q4 Rs0 = (Q4 !!! Regidx Rs0 : mword 64))
      by (apply rget_ne; nz).
    assert (Hc60b : add_vec (rget Q4 Rs0)
                      (sign_extend' 64 (mword_of_int 3616 : mword 12))
                    = pa_stk sp0 60)
      by (rewrite Hg0c (sxr_s0 HRq4); apply sx_uarg).
    iEval (rewrite -Hc60b) in "F60".
    iApply (wp_ld_s_sconf (mword_of_int (SX + 0x7e) : mword 64) Ra0 Rs0
              (mword_of_int 3616 : mword 12) Q4 (K - 60)%nat u1 b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi7e F60").
    iIntros (CID16 Hq16) "Hcg Hpc F60".
    iEval (rewrite Hc60b) in "F60".
    set (Q5 := <[Regidx Ra0 := regval_into_reg u1]> Q4).
    assert (HRq5 : sx_regs sp0 m Q5 i)
      by (rewrite /Q5; apply sx_regs_tmp; [csf | exact HRq4]).
    assert (HQ5a1 : (Q5 !!! Regidx Ra1 : mword 64)
                    = (mr !!! Regidx Ra0 : mword 64))
      by (rewrite /Q5 upd_ne; [exact HQ4a1 | nz]).
    assert (HQ5a2 : (Q5 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 4096) : mword 64))
      by (rewrite /Q5 upd_ne; [exact HQ4a2 | nz]).
    assert (Hp82 : add_vec_int (mword_of_int (SX + 0x7e) : mword 64) 4
                   = mword_of_int (SX + 0x82)) by pcw.
    iEval (rewrite Hp82) in "Hpc".
    (* ===== +0x082 jal ra,fetchstr ===== *)
    assert (Htfs : add_vec (mword_of_int (SX + 0x82) : mword 64)
                     (sign_extend' 64 (mword_of_int 2085854 : mword 21))
                   = mword_of_int KernelSyms.fetchstr) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (SX + 0x82) : mword 64) Rra
              (mword_of_int 2085854 : mword 21) Q5 (K - 60)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htfs; vm_compute; reflexivity)
              with "Hcg Hpc Hi82").
    iIntros (CID17 Hq17) "Hcg Hpc". iEval (rewrite Htfs) in "Hpc".
    set (Q6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SX + 0x82) : mword 64) 4)]> Q5).
    assert (HRq6 : sx_regs sp0 m Q6 i)
      by (rewrite /Q6; apply sx_regs_tmp; [csf | exact HRq5]).
    assert (HQ6ra : ret_pc (Q6 !!! Regidx Rra : mword 64)
                    = (mword_of_int (SX + 0x86) : mword 64))
      by (rewrite /Q6 upd_eq; pcw).
    assert (HQ6a1 : (Q6 !!! Regidx Ra1 : mword 64)
                    = (mr !!! Regidx Ra0 : mword 64))
      by (rewrite /Q6 upd_ne; [exact HQ5a1 | nz]).
    assert (HQ6a2 : (Q6 !!! Regidx Ra2 : mword 64)
                    = (mword_of_int (Z.of_nat 4096) : mword 64))
      by (rewrite /Q6 upd_ne; [exact HQ5a2 | nz]).
    iDestruct (bb_page_named (mr !!! Regidx Ra0) with "Hpage") as (fpg) "Hpg".
    iEval (rewrite -HQ6a1) in "Hpg".
    iDestruct (cpu_own_transport CID11 CID17 0%nat eb (proc_addr jp) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Fetchstr.wp_fetchstr_sconf KT0 γa γf Q6 (K - 60)%nat 0%nat eb
              (proc_addr jp) pid (upd_upt V Pa) 4096%nat fpg b lks
              sx_noff0 Kfs HQ6a2 sx_pgsize_lt Hlb
              with "Hcg Hcnt Htext Hpc Hpriv Hka Hpg").
    iIntros (CID18 Hq18 mg Ps bnew) "%Hcsg %Hexts Hcg Hcnt Hpc Hpriv Hpg %Hfr".
    assert (Hups : upd_upt (upd_upt V Pa) Ps = upd_upt V Ps) by reflexivity.
    iEval (rewrite Hups) in "Hpriv".
    assert (Hexts' : uptd_ext (pv_upt V) Ps)
      by (apply (uptd_ext_trans (pv_upt V) Pa Ps); [exact Hexta' | exact Hexts]).
    assert (HRg : sx_regs sp0 m mg i)
      by exact (sx_regs_call sp0 m Q6 mg i Hcsg HRq6).
    iEval (rewrite HQ6ra) in "Hpc".
    iEval (rewrite HQ6a1) in "Hpg".
    (* the page joins the array on BOTH paths out of the test below *)
    set (pg' := sx_upd pg i (mr !!! Regidx Ra0 : mword 64)).
    set (afun' := sx_upd afun i bnew).
    assert (Hpg'i : pg' i = (mr !!! Regidx Ra0 : mword 64))
      by (rewrite /pg'; apply sx_upd_eq).
    assert (Hafun'i : afun' i = bnew) by (rewrite /afun'; apply sx_upd_eq).
    assert (Hpg'lt : forall j, (j < i)%nat -> pg' j = pg j)
      by (intros j Hj; rewrite /pg'; apply sx_upd_lt; lia).
    assert (Hafun'lt : forall j, (j < i)%nat -> afun' j = afun j)
      by (intros j Hj; rewrite /afun'; apply sx_upd_lt; lia).
    iEval (rewrite -Hpg'i) in "Hcell".
    iDestruct (sx_argv0_close sp0 i pg pg' ltac:(lia) Hpg'lt
                 with "Hcell Hrest") as "Harr".
    iEval (rewrite -Hpg'i -Hafun'i) in "Hpg".
    iDestruct (sx_pages_close pg pg' afun afun' i Hpg'lt Hafun'lt
                 with "Hpgs Hpg") as "Hpgs".
    assert (Hpnz' : pg' i <> (mword_of_int 0 : mword 64))
      by (rewrite Hpg'i; exact Hpnz).
    assert (Hpv' : page_valid (pg' i)) by (rewrite Hpg'i; exact Hpv).
    (* ===== +0x086 blt a0,zero,+0x92 ===== *)
    assert (Ht92c : add_vec (mword_of_int (SX + 0x86) : mword 64)
                      (sign_extend' 64 (mword_of_int 12 : mword 13))
                    = (mword_of_int (SX + 0x92) : mword 64)) by pcw.
    assert (Hggm : rget mg Ra0 = (mg !!! Regidx Ra0 : mword 64))
      by (apply rget_ne; nz).
    destruct Hfr as [(kk & Hkk & Hcstr & Hrk) | Hm1]; last first.
    { (* fetchstr FAILED -- and the page is already IN the array, so the
         first NULL has moved up by one and [bad:] frees it too *)
      assert (Hcmpf : zopz0zI_s (rget mg Ra0) zero_reg = true)
        by (rewrite Hggm Hm1; exact sx_m1_neg).
      iApply (wp_blt_x0_taken_s_sconf (mword_of_int (SX + 0x86) : mword 64)
                (mword_of_int 12 : mword 13) Ra0 mg (K - 60)%nat b
                ltac:(nz) Hcmpf ltac:(rewrite Ht92c; vm_compute; reflexivity)
                with "Hcg Hpc Hi86").
      iIntros (CID19 Hq19). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Ht92c) in "Hpc".
      iSpecialize ("Hout" $! CID19 with "[%]"); [wp_next_chain |].
      iDestruct (cpu_own_transport CID18 CID19 0%nat eb (proc_addr jp) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply ("Hout" $! mg Ps (S i) pg' alen afun'). iRight. iRight.
      iApply (sx_bad_intro (CID0 := CID19) γf jp pid V K eb b lks sp0 m plen pfun rest uav
                mg Ps (S i) pg' afun' ltac:(lia) Hexts'
                (sx_pgok_push pg i (mr !!! Regidx Ra0 : mword 64)
                   (sx_ok_pgok pg alen afun i Hok) Hpnz Hpv)
                (sx_regs_bregs sp0 m mg i HRg)
                with "Hpc Hcg Hcnt Hpriv Hcarry F59 [F60] Harr Hpgs").
      iExists u1. iExact "F60". }
    (* ---- one more argument copied in ---- *)
    assert (Hcmpf : zopz0zI_s (rget mg Ra0) zero_reg = false).
    { rewrite Hggm Hrk. apply sx_nonneg.
      exact (sx_len_range kk 4096 Hkk sx_pgsize_lt). }
    iApply (wp_blt_x0_fall_s_sconf (mword_of_int (SX + 0x86) : mword 64)
              (mword_of_int 12 : mword 13) Ra0 mg (K - 60)%nat b
              ltac:(nz) Hcmpf with "Hcg Hpc Hi86").
    iIntros (CID19 Hq19) "Hcg Hpc".
    assert (Hp8a : add_vec_int (mword_of_int (SX + 0x86) : mword 64) 4
                   = mword_of_int (SX + 0x8a)) by pcw.
    iEval (rewrite Hp8a) in "Hpc".
    (* ===== +0x08a c.addi s2,1 ===== *)
    iApply (wp_caddi_s_sconf (mword_of_int (SX + 0x8a) : mword 64) Rs2
              (mword_of_int 1 : mword 6) mg (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8a").
    iIntros (CID20 Hq20) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R1 := <[Regidx Rs2 := regval_into_reg
                  (add_vec (mg !!! Regidx Rs2)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 1 : mword 6))))]> mg).
    assert (HR1s2 : (R1 !!! Regidx Rs2 : mword 64)
                    = (mword_of_int (Z.of_nat (S i)) : mword 64)).
    { rewrite /R1 upd_eq (sxr_s2 HRg). apply sx_incr. }
    assert (HR1s3 : (R1 !!! Regidx Rs3 : mword 64) = pa_stk sp0 (58 - i)%nat)
      by (rewrite /R1 upd_ne; [exact (sxr_s3 HRg) | nz]).
    assert (Hp8c : add_vec_int (mword_of_int (SX + 0x8a) : mword 64) 2
                   = mword_of_int (SX + 0x8c)) by pcw.
    iEval (rewrite Hp8c) in "Hpc".
    (* ===== +0x08c c.addi s3,8 ===== *)
    iApply (wp_caddi_s_sconf (mword_of_int (SX + 0x8c) : mword 64) Rs3
              (mword_of_int 8 : mword 6) R1 (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi8c").
    iIntros (CID21 Hq21) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (R2 := <[Regidx Rs3 := regval_into_reg
                  (add_vec (R1 !!! Regidx Rs3)
                     (sign_extend' 64
                        (sign_extend' 12 (mword_of_int 8 : mword 6))))]> R1).
    assert (HR2s3 : (R2 !!! Regidx Rs3 : mword 64) = pa_stk sp0 (58 - S i)%nat).
    { rewrite /R2 upd_eq HR1s3. apply sx_cursor. lia. }
    assert (HR2s2 : (R2 !!! Regidx Rs2 : mword 64)
                    = (mword_of_int (Z.of_nat (S i)) : mword 64))
      by (rewrite /R2 upd_ne; [exact HR1s2 | nz]).
    assert (HRR : sx_regs sp0 m R2 (S i)).
    { split_and!.
      - rewrite /sx_sp /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz].
        exact (sxr_sp HRg).
      - intros c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23.
        rewrite /R2 upd_ne; [| congruence]. rewrite /R1 upd_ne; [| congruence].
        exact (sxr_thr HRg c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23).
      - rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz].
        exact (sxr_s0 HRg).
      - rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz].
        exact (sxr_s1 HRg).
      - exact HR2s2.
      - exact HR2s3.
      - rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz].
        exact (sxr_s4 HRg).
      - rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz].
        exact (sxr_s5 HRg).
      - rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz].
        exact (sxr_s6 HRg).
      - rewrite /R2 upd_ne; [| nz]. rewrite /R1 upd_ne; [| nz].
        exact (sxr_s7 HRg). }
    assert (Hp8e : add_vec_int (mword_of_int (SX + 0x8c) : mword 64) 2
                   = mword_of_int (SX + 0x8e)) by pcw.
    iEval (rewrite Hp8e) in "Hpc".
    (* ===== +0x08e bne s2,s7 : the back edge, or out of slots ===== *)
    assert (Htbk : add_vec (mword_of_int (SX + 0x8e) : mword 64)
                     (sign_extend' 64 (mword_of_int 8136 : mword 13))
                   = (mword_of_int (SX + 0x56) : mword 64)) by pcw.
    assert (Hgr2 : rget R2 Rs2 = (R2 !!! Regidx Rs2 : mword 64))
      by (apply rget_ne; nz).
    assert (Hgr7 : rget R2 Rs7 = (R2 !!! Regidx Rs7 : mword 64))
      by (apply rget_ne; nz).
    assert (Hokpush : sx_ok pg' (sx_upd alen i kk) afun' (S i))
      by exact (sx_ok_push pg alen afun i (mr !!! Regidx Ra0 : mword 64) kk bnew
                  Hok Hpnz Hpv Hkk Hcstr).
    destruct (Nat.eq_dec (S i) 32) as [Hend | Hgo].
    { (* THE ARRAY IS FULL: the test falls through straight into [bad:], which
         is how gcc compiled the C's [i >= NELEM(argv)] -- so the break is
         reachable only below MAXARG, and that is where kexec's [na < MAXARG]
         premise comes from. *)
      assert (Hcmpn : neq_vec (rget R2 Rs2) (rget R2 Rs7) = false).
      { rewrite Hgr2 Hgr7 HR2s2 (sxr_s7 HRR). unfold neq_vec.
        rewrite negb_false_iff. apply eq_vec_true_iff.
        rewrite Hend. apply bv_eq; vm_compute; reflexivity. }
      iApply (wp_bne_fall_s_sconf (mword_of_int (SX + 0x8e) : mword 64)
                (mword_of_int 8136 : mword 13) Rs7 Rs2 R2 (K - 60)%nat b
                ltac:(nz) ltac:(nz) Hcmpn with "Hcg Hpc Hi8e").
      iIntros (CID22 Hq22) "Hcg Hpc".
      assert (Hp92 : add_vec_int (mword_of_int (SX + 0x8e) : mword 64) 4
                     = mword_of_int (SX + 0x92)) by pcw.
      iEval (rewrite Hp92) in "Hpc".
      iSpecialize ("Hout" $! CID22 with "[%]"); [wp_next_chain |].
      iDestruct (cpu_own_transport CID18 CID22 0%nat eb (proc_addr jp) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply ("Hout" $! R2 Ps (S i) pg' (sx_upd alen i kk) afun').
      iRight. iRight.
      iApply (sx_bad_intro (CID0 := CID22) γf jp pid V K eb b lks sp0 m plen pfun rest uav
                R2 Ps (S i) pg' afun' ltac:(lia) Hexts'
                (sx_ok_pgok pg' (sx_upd alen i kk) afun' (S i) Hokpush)
                (sx_regs_bregs sp0 m R2 (S i) HRR)
                with "Hpc Hcg Hcnt Hpriv Hcarry F59 [F60] Harr Hpgs").
      iExists u1. iExact "F60". }
    (* ---- the BACK EDGE ---- *)
    assert (Hcmpn : neq_vec (rget R2 Rs2) (rget R2 Rs7) = true).
    { rewrite Hgr2 Hgr7 HR2s2 (sxr_s7 HRR). unfold neq_vec.
      rewrite negb_true_iff. apply eq_vec_false_iff. intro Hc.
      rewrite sx_m32 in Hc.
      exact (Hgo (sx_moi_nat_inj (S i) 32 ltac:(lia) ltac:(lia) Hc)). }
    iApply (wp_bne_taken_s_sconf (mword_of_int (SX + 0x8e) : mword 64)
              (mword_of_int 8136 : mword 13) Rs7 Rs2 R2 (K - 60)%nat b
              ltac:(nz) ltac:(nz) Hcmpn
              ltac:(rewrite Htbk; vm_compute; reflexivity)
              with "Hcg Hpc Hi8e").
    iIntros (CID22 Hq22). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htbk) in "Hpc".
    iSpecialize ("Hout" $! CID22 with "[%]"); [wp_next_chain |].
    iDestruct (cpu_own_transport CID18 CID22 0%nat eb (proc_addr jp) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply ("Hout" $! R2 Ps (S i) pg' (sx_upd alen i kk) afun').
    iLeft. iSplitR; [iPureIntro; reflexivity |].
    iApply (sx_body_intro (CID0 := CID22) γf jp pid V K eb b lks sp0 m plen pfun rest uav
              R2 Ps (S i) pg' (sx_upd alen i kk) afun'
              (mword_of_int (SX + 0x56) : mword 64)
              ltac:(lia) Hexts' Hokpush HRR
              with "Hpc Hcg Hcnt Hpriv Hcarry F59 [F60] Harr Hpgs").
    iExists u1. iExact "F60".
  Qed.

  (* ===================================================================== *)
  (*  THE LOOP, by induction on the fuel [32 - i].                          *)
  (* ===================================================================== *)
  Lemma sx_loop `{CID0 : CpuId}
      (γf γa : gname) (jp : nat) (pid : mword 32) (V : pprivate)
      (K : nat) (eb b : bool) (lks : gset string)
      (sp0 : mword 64) (m : regfile) (plen : nat) (pfun rest : nat -> bv 8)
      (uav : mword 64) :
    (K_sys_exec <= K)%nat ->
    locks_below lks "kmem" ->
    forall (W : nat) (M : regfile) (P : uptd) (i : nat)
      (pg : nat -> mword 64) (alen : nat -> nat) (afun : nat -> nat -> bv 8),
    (32 - i <= W)%nat ->
    kernel_text -∗
    kalloc_env γa None -∗
    sx_body γf jp pid V K eb b lks sp0 m plen pfun rest uav
            M P i pg alen afun (mword_of_int (SX + 0x56) : mword 64) -∗
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M' : regfile) (P' : uptd) (i' : nat)
        (pg' : nat -> mword 64) (alen' : nat -> nat)
        (afun' : nat -> nat -> bv 8),
        (sx_body γf jp pid V K eb b lks sp0 m plen pfun rest uav
                 M' P' i' pg' alen' afun'
                 (mword_of_int (SX + 0xb6) : mword 64)
         ∨ sx_bad γf jp pid V K eb b lks sp0 m plen pfun rest uav
                  M' P' i' pg' afun') -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlb.
    intro W. revert CID0.
    induction W as [| W IH]; intros CID0 M P i pg alen afun Hfuel.
    { (* no fuel is not a case: the head is entered only at [i < 32] *)
      iIntros "#Htext #Hka Hst Hout". rewrite /sx_body.
      iDestruct "Hst" as "((%Hi32 & _) & _)". exfalso. lia. }
    iIntros "#Htext #Hka Hst Hout".
    iAssert (⌜(i < 32)%nat⌝)%I as "%Hi32".
    { rewrite /sx_body. iDestruct "Hst" as "((%H & _) & _)". iPureIntro. exact H. }
    iApply (sx_step (CID0 := CID0) γf γa jp pid V K eb b lks sp0 m plen
              pfun rest uav M P i pg alen afun HK Hlb
              with "Htext Hka Hst [Hout]").
    iIntros (CIDn Hqn M' P' i' pg' alen' afun') "[[%Hsi Hhead] | [Hbrk | Hbad]]".
    - (* the BACK EDGE, re-entered at the hart the iteration ended on *)
      assert (Hcr : b = false \/ proc_addr jp = zero_reg ->
                (CIDn : CPU) = (CID0 : CPU)) by wp_next_chain.
      iDestruct (wp_next_retarget CID0 CIDn b (proc_addr jp) _ Hcr
                   with "Hout") as "Hout".
      iApply (IH CIDn M' P' i' pg' alen' afun' ltac:(lia)
                with "Htext Hka Hhead Hout").
    - iSpecialize ("Hout" $! CIDn with "[%]"); [wp_next_chain |].
      iApply ("Hout" $! M' P' i' pg' alen' afun'). iLeft. iExact "Hbrk".
    - iSpecialize ("Hout" $! CIDn with "[%]"); [wp_next_chain |].
      iApply ("Hout" $! M' P' i' pg' alen' afun'). iRight. iExact "Hbad".
  Qed.

End SysExecStep.

(* ===================================================================== *)
(*  THE THREE TAILS.                                                      *)
(*                                                                        *)
(*  All three are [c.li a0,-1] or [c.mv a0,s2], the SAME seven [c.ldsp]    *)
(*  restoring s1..s7, and a jump to the epilogue -- so the seven loads are *)
(*  one lemma taking the block's base offset and its own [instr] facts,    *)
(*  and each tail is three lines around it.                               *)
(* ===================================================================== *)
Section SysExecReload.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.
  Local Ltac csf := vm_compute; reflexivity.

  (* the seven lazily-spilled callee-saved registers, at the values the
     epilogue's premises want them back at *)
  Definition sx_spill (sp0 : mword 64) (m : regfile) : iProp Σ :=
    ((pa_stk sp0 3) ↦₈[KT1] (m !!! Regidx Rs1 : mword 64) ∗
     (pa_stk sp0 4) ↦₈[KT1] (m !!! Regidx Rs2 : mword 64) ∗
     (pa_stk sp0 5) ↦₈[KT1] (m !!! Regidx Rs3 : mword 64) ∗
     (pa_stk sp0 6) ↦₈[KT1] (m !!! Regidx Rs4 : mword 64) ∗
     (pa_stk sp0 7) ↦₈[KT1] (m !!! Regidx Rs5 : mword 64) ∗
     (pa_stk sp0 8) ↦₈[KT1] (m !!! Regidx Rs6 : mword 64) ∗
     (pa_stk sp0 9) ↦₈[KT1] (m !!! Regidx Rs7 : mword 64))%I.

  (* what a reload step preserves: everything the epilogue reads except the
     seven registers it is putting back *)
  Definition sx_rlp (sp0 : mword 64) (m M N : regfile) : Prop :=
    sx_sp sp0 N /\ sx_thr m N /\
    (N !!! Regidx Rs0 : mword 64) = (M !!! Regidx Rs0 : mword 64) /\
    (N !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64).

  (* [s1..s7] are exactly the registers [sx_thr] already excludes, so a
     reload preserves it -- which is why the epilogue can take the threading
     clause as a premise rather than re-deriving it from the loads. *)
  Lemma sx_rlp_step (sp0 : mword 64) (m M N : regfile) (r : mword 5)
      (v : mword 64) :
    (r = Rs1 \/ r = Rs2 \/ r = Rs3 \/ r = Rs4 \/ r = Rs5 \/ r = Rs6 \/ r = Rs7) ->
    sx_rlp sp0 m M N -> sx_rlp sp0 m M (<[Regidx r := v]> N).
  Proof.
    intros Hr (Hsp & Hthr & H0 & Ha).
    split_and!.
    - rewrite /sx_sp upd_ne; [exact Hsp | destruct Hr as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; nz].
    - intros c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23.
      rewrite upd_ne;
        [exact (Hthr c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23) |
         destruct Hr as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; congruence].
    - rewrite upd_ne; [exact H0 | destruct Hr as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; nz].
    - rewrite upd_ne; [exact Ha | destruct Hr as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; nz].
  Qed.

  (* +base .. +base+12: [ld s1..s7] off the pushed sp *)
  Lemma sx_reload `{CID0 : CpuId} (sp0 : mword 64) (m M : regfile) (K : nat)
      (b : bool) (pj : mword 64) (base : Z) :
    sx_sp sp0 M -> sx_thr m M ->
    sx_itxt (mword_of_int (SX + base) : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 57 : mword 6) ('b"000")),
             sp, Regidx Rs1, false, 8)) ->
    sx_itxt (mword_of_int (SX + base + 2) : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 56 : mword 6) ('b"000")),
             sp, Regidx Rs2, false, 8)) ->
    sx_itxt (mword_of_int (SX + base + 4) : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 55 : mword 6) ('b"000")),
             sp, Regidx Rs3, false, 8)) ->
    sx_itxt (mword_of_int (SX + base + 6) : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 54 : mword 6) ('b"000")),
             sp, Regidx Rs4, false, 8)) ->
    sx_itxt (mword_of_int (SX + base + 8) : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 53 : mword 6) ('b"000")),
             sp, Regidx Rs5, false, 8)) ->
    sx_itxt (mword_of_int (SX + base + 10) : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 52 : mword 6) ('b"000")),
             sp, Regidx Rs6, false, 8)) ->
    sx_itxt (mword_of_int (SX + base + 12) : mword 64) true
      (LOAD (zero_extend' 12 (concat_vec (mword_of_int 51 : mword 6) ('b"000")),
             sp, Regidx Rs7, false, 8)) ->
    kernel_text -∗
    pc_is (mword_of_int (SX + base) : mword 64) -∗
    sie_cap_gpr KT1 M (K - 60)%nat b pj -∗
    sx_spill sp0 m -∗
    wp_next b pj (fun (CID : CpuId) =>
      ∀ M' : regfile,
        ⌜ sx_rlp sp0 m M M' /\
          (M' !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64) /\
          (M' !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64) /\
          (M' !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64) /\
          (M' !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64) /\
          (M' !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64) /\
          (M' !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64) /\
          (M' !!! Regidx Rs7 : mword 64) = (m !!! Regidx Rs7 : mword 64) ⌝ -∗
        pc_is (mword_of_int (SX + base + 14) : mword 64) -∗
        sie_cap_gpr KT1 M' (K - 60)%nat b pj -∗
        sx_spill sp0 m -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hsp Hthr Hx0 Hx2 Hx4 Hx6 Hx8 Hx10 Hx12.
    iIntros "#Htext Hpc Hcg Hsp Hout".
    iPoseProof (Hx0 with "Htext") as "Hi0".
    iPoseProof (Hx2 with "Htext") as "Hi2".
    iPoseProof (Hx4 with "Htext") as "Hi4".
    iPoseProof (Hx6 with "Htext") as "Hi6".
    iPoseProof (Hx8 with "Htext") as "Hi8".
    iPoseProof (Hx10 with "Htext") as "Hi10".
    iPoseProof (Hx12 with "Htext") as "Hi12".
    rewrite /sx_spill.
    iDestruct "Hsp" as "(P3 & P4 & P5 & P6 & P7 & P8 & P9)".
    assert (HR0 : sx_rlp sp0 m M M)
      by (split_and!; [exact Hsp | exact Hthr | reflexivity | reflexivity]).
    (* ===== +base ld s1 ===== *)
    assert (Hc3 : add_vec (M !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 57 : mword 6) ('b"000")))
                  = pa_stk sp0 3) by (rewrite (proj1 HR0); apply sx_frm3).
    iApply (wp_cldsp_s_sconf (mword_of_int (SX + base) : mword 64)
              (mword_of_int 57 : mword 6) Rs1 M (K - 60)%nat
              (m !!! Regidx Rs1 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi0 [P3]").
    { iEval (rewrite Hc3). iExact "P3". }
    iIntros (CID1 Hq1) "Hcg Hpc P3". iEval (rewrite Hc3) in "P3".
    set (A1 := <[Regidx Rs1 := regval_into_reg (m !!! Regidx Rs1 : mword 64)]> M).
    assert (HR1 : sx_rlp sp0 m M A1)
      by (rewrite /A1; apply sx_rlp_step; [tauto | exact HR0]).
    assert (HA1s1 : (A1 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /A1; apply upd_eq).
    iEval (rewrite (sx_avi (SX + base) 2)) in "Hpc".
    (* ===== +base+2 ld s2 ===== *)
    assert (Hc4 : add_vec (A1 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 56 : mword 6) ('b"000")))
                  = pa_stk sp0 4) by (rewrite (proj1 HR1); apply sx_frm4).
    iApply (wp_cldsp_s_sconf (mword_of_int (SX + base + 2) : mword 64)
              (mword_of_int 56 : mword 6) Rs2 A1 (K - 60)%nat
              (m !!! Regidx Rs2 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi2 [P4]").
    { iEval (rewrite Hc4). iExact "P4". }
    iIntros (CID2 Hq2) "Hcg Hpc P4". iEval (rewrite Hc4) in "P4".
    set (A2 := <[Regidx Rs2 := regval_into_reg (m !!! Regidx Rs2 : mword 64)]> A1).
    assert (HR2 : sx_rlp sp0 m M A2)
      by (rewrite /A2; apply sx_rlp_step; [tauto | exact HR1]).
    assert (HA2s1 : (A2 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /A2 upd_ne; [exact HA1s1 | nz]).
    assert (HA2s2 : (A2 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /A2; apply upd_eq).
    iEval (rewrite (sx_avi (SX + base + 2) 2)) in "Hpc".
    rewrite (_ : (SX + base + 2 + 2)%Z = (SX + base + 4)%Z); [| lia].
    (* ===== +base+4 ld s3 ===== *)
    assert (Hc5 : add_vec (A2 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 55 : mword 6) ('b"000")))
                  = pa_stk sp0 5) by (rewrite (proj1 HR2); apply sx_frm5).
    iApply (wp_cldsp_s_sconf (mword_of_int (SX + base + 4) : mword 64)
              (mword_of_int 55 : mword 6) Rs3 A2 (K - 60)%nat
              (m !!! Regidx Rs3 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi4 [P5]").
    { iEval (rewrite Hc5). iExact "P5". }
    iIntros (CID3 Hq3) "Hcg Hpc P5". iEval (rewrite Hc5) in "P5".
    set (A3 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3 : mword 64)]> A2).
    assert (HR3 : sx_rlp sp0 m M A3)
      by (rewrite /A3; apply sx_rlp_step; [tauto | exact HR2]).
    assert (HA3s1 : (A3 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2s1 | nz]).
    assert (HA3s2 : (A3 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /A3 upd_ne; [exact HA2s2 | nz]).
    assert (HA3s3 : (A3 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /A3; apply upd_eq).
    iEval (rewrite (sx_avi (SX + base + 4) 2)) in "Hpc".
    rewrite (_ : (SX + base + 4 + 2)%Z = (SX + base + 6)%Z); [| lia].
    (* ===== +base+6 ld s4 ===== *)
    assert (Hc6 : add_vec (A3 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 54 : mword 6) ('b"000")))
                  = pa_stk sp0 6) by (rewrite (proj1 HR3); apply sx_frm6).
    iApply (wp_cldsp_s_sconf (mword_of_int (SX + base + 6) : mword 64)
              (mword_of_int 54 : mword 6) Rs4 A3 (K - 60)%nat
              (m !!! Regidx Rs4 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi6 [P6]").
    { iEval (rewrite Hc6). iExact "P6". }
    iIntros (CID4 Hq4) "Hcg Hpc P6". iEval (rewrite Hc6) in "P6".
    set (A4 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4 : mword 64)]> A3).
    assert (HR4 : sx_rlp sp0 m M A4)
      by (rewrite /A4; apply sx_rlp_step; [tauto | exact HR3]).
    assert (HA4s1 : (A4 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /A4 upd_ne; [exact HA3s1 | nz]).
    assert (HA4s2 : (A4 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /A4 upd_ne; [exact HA3s2 | nz]).
    assert (HA4s3 : (A4 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /A4 upd_ne; [exact HA3s3 | nz]).
    assert (HA4s4 : (A4 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
      by (rewrite /A4; apply upd_eq).
    iEval (rewrite (sx_avi (SX + base + 6) 2)) in "Hpc".
    rewrite (_ : (SX + base + 6 + 2)%Z = (SX + base + 8)%Z); [| lia].
    (* ===== +base+8 ld s5 ===== *)
    assert (Hc7 : add_vec (A4 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 53 : mword 6) ('b"000")))
                  = pa_stk sp0 7) by (rewrite (proj1 HR4); apply sx_frm7).
    iApply (wp_cldsp_s_sconf (mword_of_int (SX + base + 8) : mword 64)
              (mword_of_int 53 : mword 6) Rs5 A4 (K - 60)%nat
              (m !!! Regidx Rs5 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi8 [P7]").
    { iEval (rewrite Hc7). iExact "P7". }
    iIntros (CID5 Hq5) "Hcg Hpc P7". iEval (rewrite Hc7) in "P7".
    set (A5 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5 : mword 64)]> A4).
    assert (HR5 : sx_rlp sp0 m M A5)
      by (rewrite /A5; apply sx_rlp_step; [tauto | exact HR4]).
    assert (HA5s1 : (A5 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4s1 | nz]).
    assert (HA5s2 : (A5 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4s2 | nz]).
    assert (HA5s3 : (A5 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4s3 | nz]).
    assert (HA5s4 : (A5 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
      by (rewrite /A5 upd_ne; [exact HA4s4 | nz]).
    assert (HA5s5 : (A5 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64))
      by (rewrite /A5; apply upd_eq).
    iEval (rewrite (sx_avi (SX + base + 8) 2)) in "Hpc".
    rewrite (_ : (SX + base + 8 + 2)%Z = (SX + base + 10)%Z); [| lia].
    (* ===== +base+10 ld s6 ===== *)
    assert (Hc8 : add_vec (A5 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 52 : mword 6) ('b"000")))
                  = pa_stk sp0 8) by (rewrite (proj1 HR5); apply sx_frm8).
    iApply (wp_cldsp_s_sconf (mword_of_int (SX + base + 10) : mword 64)
              (mword_of_int 52 : mword 6) Rs6 A5 (K - 60)%nat
              (m !!! Regidx Rs6 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi10 [P8]").
    { iEval (rewrite Hc8). iExact "P8". }
    iIntros (CID6 Hq6) "Hcg Hpc P8". iEval (rewrite Hc8) in "P8".
    set (A6 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6 : mword 64)]> A5).
    assert (HR6 : sx_rlp sp0 m M A6)
      by (rewrite /A6; apply sx_rlp_step; [tauto | exact HR5]).
    assert (HA6s1 : (A6 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /A6 upd_ne; [exact HA5s1 | nz]).
    assert (HA6s2 : (A6 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /A6 upd_ne; [exact HA5s2 | nz]).
    assert (HA6s3 : (A6 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /A6 upd_ne; [exact HA5s3 | nz]).
    assert (HA6s4 : (A6 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
      by (rewrite /A6 upd_ne; [exact HA5s4 | nz]).
    assert (HA6s5 : (A6 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64))
      by (rewrite /A6 upd_ne; [exact HA5s5 | nz]).
    assert (HA6s6 : (A6 !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64))
      by (rewrite /A6; apply upd_eq).
    iEval (rewrite (sx_avi (SX + base + 10) 2)) in "Hpc".
    rewrite (_ : (SX + base + 10 + 2)%Z = (SX + base + 12)%Z); [| lia].
    (* ===== +base+12 ld s7 ===== *)
    assert (Hc9 : add_vec (A6 !!! Regidx csp_rs1 : mword 64)
                    (zero_extend' 64 (concat_vec (mword_of_int 51 : mword 6) ('b"000")))
                  = pa_stk sp0 9) by (rewrite (proj1 HR6); apply sx_frm9).
    iApply (wp_cldsp_s_sconf (mword_of_int (SX + base + 12) : mword 64)
              (mword_of_int 51 : mword 6) Rs7 A6 (K - 60)%nat
              (m !!! Regidx Rs7 : mword 64) b ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi12 [P9]").
    { iEval (rewrite Hc9). iExact "P9". }
    iIntros (CID7 Hq7) "Hcg Hpc P9". iEval (rewrite Hc9) in "P9".
    set (A7 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7 : mword 64)]> A6).
    assert (HR7 : sx_rlp sp0 m M A7)
      by (rewrite /A7; apply sx_rlp_step; [tauto | exact HR6]).
    assert (HA7s1 : (A7 !!! Regidx Rs1 : mword 64) = (m !!! Regidx Rs1 : mword 64))
      by (rewrite /A7 upd_ne; [exact HA6s1 | nz]).
    assert (HA7s2 : (A7 !!! Regidx Rs2 : mword 64) = (m !!! Regidx Rs2 : mword 64))
      by (rewrite /A7 upd_ne; [exact HA6s2 | nz]).
    assert (HA7s3 : (A7 !!! Regidx Rs3 : mword 64) = (m !!! Regidx Rs3 : mword 64))
      by (rewrite /A7 upd_ne; [exact HA6s3 | nz]).
    assert (HA7s4 : (A7 !!! Regidx Rs4 : mword 64) = (m !!! Regidx Rs4 : mword 64))
      by (rewrite /A7 upd_ne; [exact HA6s4 | nz]).
    assert (HA7s5 : (A7 !!! Regidx Rs5 : mword 64) = (m !!! Regidx Rs5 : mword 64))
      by (rewrite /A7 upd_ne; [exact HA6s5 | nz]).
    assert (HA7s6 : (A7 !!! Regidx Rs6 : mword 64) = (m !!! Regidx Rs6 : mword 64))
      by (rewrite /A7 upd_ne; [exact HA6s6 | nz]).
    assert (HA7s7 : (A7 !!! Regidx Rs7 : mword 64) = (m !!! Regidx Rs7 : mword 64))
      by (rewrite /A7; apply upd_eq).
    iEval (rewrite (sx_avi (SX + base + 12) 2)) in "Hpc".
    rewrite (_ : (SX + base + 12 + 2)%Z = (SX + base + 14)%Z); [| lia].
    iSpecialize ("Hout" $! CID7 with "[%]"); [wp_next_chain |].
    iApply ("Hout" $! A7 with "[%] Hpc Hcg [P3 P4 P5 P6 P7 P8 P9]").
    { split_and!;
        [ exact HR7 | exact HA7s1 | exact HA7s2 | exact HA7s3 | exact HA7s4
        | exact HA7s5 | exact HA7s6 | exact HA7s7 ]. }
    rewrite /sx_spill.
    iSplitL "P3"; [iExact "P3" |]. iSplitL "P4"; [iExact "P4" |].
    iSplitL "P5"; [iExact "P5" |]. iSplitL "P6"; [iExact "P6" |].
    iSplitL "P7"; [iExact "P7" |]. iSplitL "P8"; [iExact "P8" | iExact "P9"].
  Qed.

  (* ---- the frame, opened for the reload and closed for the epilogue ---- *)

  Lemma sx_carry_open (sp0 : mword 64) (m : regfile) (plen : nat)
      (pfun rest : nat -> bv 8) :
    sx_carry sp0 m plen pfun rest -∗
    (pa_stk sp0 1) ↦₈[KT1] (m !!! Regidx Rra : mword 64) ∗
    (pa_stk sp0 2) ↦₈[KT1] (m !!! Regidx Rs0 : mword 64) ∗
    sx_spill sp0 m ∗
    (∃ w : mword 64, (pa_stk sp0 10) ↦₈[KT1] w) ∗
    ([∗ list] j ∈ seq 0 (S plen), pa_add (pa_stk sp0 26) j ↦ₘ[KT1] pfun j) ∗
    ([∗ list] j ∈ seq 0 (127 - plen)%nat,
       pa_add (pa_add (pa_stk sp0 26) (S plen)) j ↦ₘ[KT1] rest j).
  Proof.
    rewrite /sx_carry /sx_spill.
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & Hp & Hs)".
    iSplitL "H1"; [iExact "H1" |]. iSplitL "H2"; [iExact "H2" |].
    iSplitR "H10 Hp Hs".
    { iSplitL "H3"; [iExact "H3" |]. iSplitL "H4"; [iExact "H4" |].
      iSplitL "H5"; [iExact "H5" |]. iSplitL "H6"; [iExact "H6" |].
      iSplitL "H7"; [iExact "H7" |]. iSplitL "H8"; [iExact "H8" | iExact "H9"]. }
    iSplitL "H10"; [iExact "H10" |].
    iSplitL "Hp"; [iExact "Hp" | iExact "Hs"].
  Qed.

  Lemma sx_rest_build (sp0 : mword 64) (m : regfile) (plen : nat)
      (pfun rest : nat -> bv 8) (uav : mword 64) :
    (plen < 128)%nat ->
    sx_spill sp0 m -∗
    (∃ w : mword 64, (pa_stk sp0 10) ↦₈[KT1] w) -∗
    ([∗ list] j ∈ seq 0 (S plen), pa_add (pa_stk sp0 26) j ↦ₘ[KT1] pfun j) -∗
    ([∗ list] j ∈ seq 0 (127 - plen)%nat,
       pa_add (pa_add (pa_stk sp0 26) (S plen)) j ↦ₘ[KT1] rest j) -∗
    (pa_stk sp0 59) ↦₈[KT1] uav -∗
    (∃ w : mword 64, (pa_stk sp0 60) ↦₈[KT1] w) -∗
    sx_argv_free sp0 -∗
    sx_rest sp0.
  Proof.
    intro Hplen. rewrite /sx_spill /sx_rest /sx_argv_free.
    iIntros "(H3 & H4 & H5 & H6 & H7 & H8 & H9) H10 Hp Hs F59 F60 Ha".
    iDestruct (sx_buf_join (pa_stk sp0 26) pfun rest plen Hplen with "Hp Hs") as "Hpb".
    change 256%nat with (8 * 32)%nat.
    iDestruct (slotsn_bytes_own (KTR := KT1) sp0 58 32 ltac:(lia) with "Ha") as "[_ Hab]".
    iSplitL "H3"; [iExists (m !!! Regidx Rs1 : mword 64); iExact "H3" |].
    iSplitL "H4"; [iExists (m !!! Regidx Rs2 : mword 64); iExact "H4" |].
    iSplitL "H5"; [iExists (m !!! Regidx Rs3 : mword 64); iExact "H5" |].
    iSplitL "H6"; [iExists (m !!! Regidx Rs4 : mword 64); iExact "H6" |].
    iSplitL "H7"; [iExists (m !!! Regidx Rs5 : mword 64); iExact "H7" |].
    iSplitL "H8"; [iExists (m !!! Regidx Rs6 : mword 64); iExact "H8" |].
    iSplitL "H9"; [iExists (m !!! Regidx Rs7 : mword 64); iExact "H9" |].
    iSplitL "H10"; [iExact "H10" |].
    iSplitL "F59"; [iExists uav; iExact "F59" |].
    iSplitL "F60"; [iExact "F60" |].
    iSplitL "Hpb"; [iExact "Hpb" | iExact "Hab"].
  Qed.

  (* THE ALIGNMENT FACTS ARE READ BACK OFF THE ARRAY, not threaded: a word
     points-to carries its own alignment, and [slotsn_bytes_own (KTR := KT1)] hands the
     whole run's out.  The round trip through [bytes_own_slotsn (KTR := KT1)] is what
     makes the extraction non-consuming. *)
  Lemma sx_argv_ala (sp0 : mword 64) :
    sx_argv_free sp0 ⊢ ⌜sx_ala sp0⌝ ∗ sx_argv_free sp0.
  Proof.
    rewrite /sx_argv_free. iIntros "H".
    iDestruct (slotsn_bytes_own (KTR := KT1) sp0 58 32 ltac:(lia) with "H") as "[%Hal Hb]".
    iSplitR; [iPureIntro; exact Hal |].
    iApply (bytes_own_slotsn (KTR := KT1) sp0 58 32 ltac:(lia) Hal with "Hb").
  Qed.

End SysExecReload.

(* ===================================================================== *)
(*  +0x092 .. +0x0b4 / +0x0f4 .. -- [bad:], THE -1 EXIT.                  *)
(*                                                                        *)
(*  [s4 = argv + 256], the free loop, and then the SAME three lines at    *)
(*  two addresses: the loop's early exit lands at +0x0f4 and its          *)
(*  fall-through at +0x0a4, and the only difference is that the second    *)
(*  has to [c.j] to the epilogue while the first is already next to it.   *)
(* ===================================================================== *)
Section SysExecBadTail.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.
  Local Ltac csf := vm_compute; reflexivity.

  (* [argv + 256] is slot 26, one past argv[31] *)
  Lemma sx_argv_end2 (sp0 : mword 64) :
    add_vec (pa_stk sp0 58) (sign_extend' 64 (mword_of_int 256 : mword 12))
    = pa_stk sp0 26.
  Proof.
    assert (Him : (sign_extend' 64 (mword_of_int 256 : mword 12) : mword 64)
                  = mword_of_int 256) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Him. unfold pa_stk, add_vec_int. apply bv_eq.
    rewrite !add_vec64_unsigned !moi64_unsigned.
    rewrite !bv_wrap_add_idemp_r !bv_wrap_add_idemp_l. f_equal. lia.
  Qed.

  Lemma sx_bad_tail `{CID0 : CpuId}
      (γf γa : gname) (jp : nat) (pid : mword 32) (V : pprivate)
      (K : nat) (eb b : bool) (lks : gset string)
      (sp0 : mword 64) (m : regfile) (plen : nat) (pfun rest : nat -> bv 8)
      (uav : mword 64) (M : regfile) (P : uptd) (t : nat)
      (pg : nat -> mword 64) (afun : nat -> nat -> bv 8) :
    (K_sys_exec <= K)%nat ->
    locks_below lks "kmem" ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    (plen < 128)%nat ->
    sx_alp sp0 ->
    kernel_text -∗
    kalloc_env γa None -∗
    sx_bad γf jp pid V K eb b lks sp0 m plen pfun rest uav M P t pg afun -∗
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        ⌜uptd_ext (pv_upt V) P⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
        cpu_own 0 eb (proc_addr jp) b lks -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv γf (proc_addr jp) pid (upd_upt V P) -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlb Hsp0 Hplen Halp.
    destruct (sx_kb K HK) as (Kkx & Kar & Kaa & Kfa & Kfs & K14 & K2 & K60 & Kpop).
    iIntros "#Htext #Hka Hst Hout".
    rewrite /sx_bad.
    iDestruct "Hst" as "((%Ht32 & %Hext & %Hpgok & %HB) & Hpc & Hcg & Hcnt &
                         Hpriv & Hcarry & F59 & F60 & Harr & Hpgs)".
    destruct HB as (Hsp & Hthr & Hs0 & Hs1 & Hs4).
    iDestruct (sx_carry_open sp0 m plen pfun rest with "Hcarry")
      as "(Hf1 & Hf2 & Hspill & F10 & Hpb & Hps)".
    iPoseProof (sxi_092 with "Htext") as "Hi92".
    (* ===== +0x092 addi s4,s4,256 : the array's end ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (SX + 0x92) : mword 64) Rs4 Rs4
              (mword_of_int 256 : mword 12) M (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi92").
    iIntros (CID1 Hq1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N1 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (M !!! Regidx Rs4)
                     (sign_extend' 64 (mword_of_int 256 : mword 12)))]> M).
    assert (HN1s4 : (N1 !!! Regidx Rs4 : mword 64) = pa_stk sp0 26)
      by (rewrite /N1 upd_eq Hs4; apply sx_argv_end2).
    assert (HN1s1 : (N1 !!! Regidx Rs1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N1 upd_ne; [exact Hs1 | nz]).
    assert (HN1sp : sx_sp sp0 N1)
      by (rewrite /sx_sp /N1 upd_ne; [exact Hsp | nz]).
    assert (HN1thr : sx_thr m N1).
    { intros c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23.
      rewrite /N1 upd_ne; [| congruence].
      exact (Hthr c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23). }
    assert (Hp96 : add_vec_int (mword_of_int (SX + 0x92) : mword 64) 4
                   = mword_of_int (SX + 0x96)) by pcw.
    iEval (rewrite Hp96) in "Hpc".
    (* ===== +0x096 .. +0x0a0 THE FREE LOOP ===== *)
    iDestruct (sx_argv0_at sp0 t pg with "Harr") as "Harr".
    iDestruct (cpu_own_transport CID0 CID1 0%nat eb (proc_addr jp) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (sx_free_loop (CID0 := CID1) γa sp0 (proc_addr jp) K eb b lks
              pg afun t 0x96 0xf4 (mword_of_int 46 : mword 8)
              (mword_of_int 2078180 : mword 21)
              HK Ht32 Hpgok Hlb ltac:(pcw) ltac:(pcw) ltac:(csf) ltac:(pcw)
              ltac:(pcw) ltac:(csf)
              sxi_096 sxi_098 sxi_09a sxi_09e sxi_0a0
              32%nat N1 0%nat ltac:(lia) ltac:(lia) ltac:(lia) HN1s1 HN1s4
              with "Htext Hka Hpc Hcg Hcnt Harr Hpgs").
    iIntros (CID2 Hq2 M2 pcx) "%Hpcx %Hthr2 Hpc Hcg Hcnt Harr".
    assert (HM2sp : sx_sp sp0 M2)
      by (rewrite /sx_sp (Hthr2 csp_rs1 ltac:(csf) ltac:(nz)); exact HN1sp).
    assert (HM2thr : sx_thr m M2).
    { intros c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23.
      rewrite (Hthr2 c Hc D9).
      exact (HN1thr c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23). }
    iDestruct (sx_argv_ala sp0 with "Harr") as "[%Hala Harr]".
    destruct Hpcx as [Hpe | Hpf].
    - (* the early exit at +0x0f4: [-1], reload, and the epilogue is next *)
      iEval (rewrite Hpe) in "Hpc".
      iPoseProof (sxi_0f4 with "Htext") as "Hif4".
      iApply (wp_cli_s_sconf (mword_of_int (SX + 0xf4) : mword 64) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                M2 (K - 60)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc Hif4").
      iIntros (CID3 Hq3) "Hcg Hpc".
      set (M3 := <[Regidx Ra0 := regval_into_reg
                    (mword_of_int (-1) : mword 64)]> M2).
      assert (HM3a0 : (M3 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
        by (rewrite /M3; apply upd_eq).
      assert (HM3sp : sx_sp sp0 M3)
        by (rewrite /sx_sp /M3 upd_ne; [exact HM2sp | nz]).
      assert (HM3thr : sx_thr m M3).
      { intros c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23.
        rewrite /M3 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq;
                               [csf | exact Hc]].
        exact (HM2thr c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23). }
      assert (Hpf6 : add_vec_int (mword_of_int (SX + 0xf4) : mword 64) 2
                     = mword_of_int (SX + 0xf6)) by pcw.
      iEval (rewrite Hpf6) in "Hpc".
      iApply (sx_reload (CID0 := CID3) sp0 m M3 K b (proc_addr jp) 0xf6
                HM3sp HM3thr sxi_0f6 sxi_0f8 sxi_0fa sxi_0fc sxi_0fe sxi_100
                sxi_102 with "Htext Hpc Hcg Hspill").
      iIntros (CID4 Hq4 M4) "%HRL Hpc Hcg Hspill".
      destruct HRL as ((HM4sp & HM4thr & _ & HM4a0) & E1 & E2 & E3 & E4 & E5 & E6 & E7).
      iDestruct (sx_rest_build sp0 m plen pfun rest uav Hplen
                   with "Hspill F10 Hpb Hps F59 F60 Harr") as "Hrest".
      iApply (sx_epilogue (CID0 := CID4) m M4 sp0 K b (proc_addr jp)
                K60 Kpop Hsp0 HM4sp HM4thr E1 E2 E3 E4 E5 E6 E7 Halp Hala
                with "Hcg Htext Hpc Hf1 Hf2 Hrest [Hout Hcnt Hpriv]").
      iIntros (CID5) "%Hq5". iIntros (mf) "%Hcsf %Hfa0 Hcg Hpc".
      iSpecialize ("Hout" $! CID5 with "[%]"); [wp_next_chain |].
      iDestruct (cpu_own_transport CID2 CID5 0%nat eb (proc_addr jp) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply ("Hout" $! mf with "[%] [%] [%] Hcg Hcnt Hpc Hpriv").
      { exact Hcsf. }
      { rewrite Hfa0 HM4a0. exact HM3a0. }
      { exact Hext. }
    - (* the fall-through at +0x0a4: the same, plus a [c.j] to the epilogue *)
      iEval (rewrite Hpf) in "Hpc".
      rewrite (_ : (SX + 0x96 + 14)%Z = (SX + 0xa4)%Z); [| lia].
      iPoseProof (sxi_0a4 with "Htext") as "Hia4".
      iPoseProof (sxi_0b4 with "Htext") as "Hib4".
      iApply (wp_cli_s_sconf (mword_of_int (SX + 0xa4) : mword 64) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                M2 (K - 60)%nat b ltac:(nz) ltac:(rdok) ltac:(pcw)
                with "Hcg Hpc Hia4").
      iIntros (CID3 Hq3) "Hcg Hpc".
      set (M3 := <[Regidx Ra0 := regval_into_reg
                    (mword_of_int (-1) : mword 64)]> M2).
      assert (HM3a0 : (M3 !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64))
        by (rewrite /M3; apply upd_eq).
      assert (HM3sp : sx_sp sp0 M3)
        by (rewrite /sx_sp /M3 upd_ne; [exact HM2sp | nz]).
      assert (HM3thr : sx_thr m M3).
      { intros c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23.
        rewrite /M3 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq;
                               [csf | exact Hc]].
        exact (HM2thr c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23). }
      assert (Hpa6 : add_vec_int (mword_of_int (SX + 0xa4) : mword 64) 2
                     = mword_of_int (SX + 0xa6)) by pcw.
      iEval (rewrite Hpa6) in "Hpc".
      iApply (sx_reload (CID0 := CID3) sp0 m M3 K b (proc_addr jp) 0xa6
                HM3sp HM3thr sxi_0a6 sxi_0a8 sxi_0aa sxi_0ac sxi_0ae sxi_0b0
                sxi_0b2 with "Htext Hpc Hcg Hspill").
      iIntros (CID4 Hq4 M4) "%HRL Hpc Hcg Hspill".
      destruct HRL as ((HM4sp & HM4thr & _ & HM4a0) & E1 & E2 & E3 & E4 & E5 & E6 & E7).
      rewrite (_ : (SX + 0xa6 + 14)%Z = (SX + 0xb4)%Z); [| lia].
      (* ===== +0x0b4 c.j +0x104 ===== *)
      assert (Htj : add_vec (mword_of_int (SX + 0xb4) : mword 64)
                      (sign_extend' 64 (sign_extend' 21
                         (concat_vec (mword_of_int 40 : mword 11) ('b"0"))))
                    = (mword_of_int (SX + 0x104) : mword 64)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (SX + 0xb4) : mword 64)
                (sign_extend' 21 (concat_vec (mword_of_int 40 : mword 11) ('b"0")))
                M4 (K - 60)%nat b ltac:(rewrite Htj; vm_compute; reflexivity)
                with "Hcg Hpc Hib4").
      iIntros (CID5 Hq5). iApply bi.later_intro. iIntros "Hcg Hpc".
      iEval (rewrite Htj) in "Hpc".
      iDestruct (sx_rest_build sp0 m plen pfun rest uav Hplen
                   with "Hspill F10 Hpb Hps F59 F60 Harr") as "Hrest".
      iApply (sx_epilogue (CID0 := CID5) m M4 sp0 K b (proc_addr jp)
                K60 Kpop Hsp0 HM4sp HM4thr E1 E2 E3 E4 E5 E6 E7 Halp Hala
                with "Hcg Htext Hpc Hf1 Hf2 Hrest [Hout Hcnt Hpriv]").
      iIntros (CID6) "%Hq6". iIntros (mf) "%Hcsf %Hfa0 Hcg Hpc".
      iSpecialize ("Hout" $! CID6 with "[%]"); [wp_next_chain |].
      iDestruct (cpu_own_transport CID2 CID6 0%nat eb (proc_addr jp) b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply ("Hout" $! mf with "[%] [%] [%] Hcg Hcnt Hpc Hpriv").
      { exact Hcsf. }
      { rewrite Hfa0 HM4a0. exact HM3a0. }
      { exact Hext. }
  Qed.

End SysExecBadTail.

(* ===================================================================== *)
(*  +0x0ce .. +0x0f2 -- THE SUCCESS TAIL.                                 *)
(*                                                                        *)
(*  [s2 = ret], the second free loop, and the return.  Unlike [bad:] this  *)
(*  one has no branch to reconcile: BOTH of the free loop's exits land at  *)
(*  +0x0e2, because its early-exit target and its fall-through address     *)
(*  coincide.                                                             *)
(* ===================================================================== *)
Section SysExecSuccTail.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.
  Local Ltac csf := vm_compute; reflexivity.

  Lemma sx_succ_tail `{CID0 : CpuId}
      (γf γa : gname) (jp : nat) (pid : mword 32) (W : pprivate)
      (K : nat) (eb b : bool) (lks : gset string)
      (sp0 : mword 64) (m : regfile) (plen : nat) (pfun rest : nat -> bv 8)
      (uav rv : mword 64) (M : regfile) (t : nat)
      (pg : nat -> mword 64) (afun : nat -> nat -> bv 8) :
    (K_sys_exec <= K)%nat ->
    locks_below lks "kmem" ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    (plen < 128)%nat ->
    sx_alp sp0 ->
    (t <= 32)%nat ->
    sx_pgok pg t ->
    sx_sp sp0 M -> sx_thr m M ->
    (M !!! Regidx Rs0 : mword 64) = sp0 ->
    (M !!! Regidx Rs1 : mword 64) = pa_stk sp0 58 ->
    (M !!! Regidx Rs4 : mword 64) = pa_stk sp0 58 ->
    (M !!! Regidx Ra0 : mword 64) = rv ->
    kernel_text -∗
    kalloc_env γa None -∗
    pc_is (mword_of_int (SX + 0xce) : mword 64) -∗
    sie_cap_gpr KT1 M (K - 60)%nat b (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) b lks -∗
    proc_priv γf (proc_addr jp) pid W -∗
    sx_carry sp0 m plen pfun rest -∗
    (pa_stk sp0 59) ↦₈[KT1] uav -∗
    (∃ w : mword 64, (pa_stk sp0 60) ↦₈[KT1] w) -∗
    sx_argv0 sp0 t pg -∗
    sx_pages pg afun 0 t -∗
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = rv⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
        cpu_own 0 eb (proc_addr jp) b lks -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv γf (proc_addr jp) pid W -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlb Hsp0 Hplen Halp Ht32 Hpgok Hsp Hthr Hs0 Hs1 Hs4 Ha0.
    destruct (sx_kb K HK) as (Kkx & Kar & Kaa & Kfa & Kfs & K14 & K2 & K60 & Kpop).
    iIntros "#Htext #Hka Hpc Hcg Hcnt Hpriv Hcarry F59 F60 Harr Hpgs Hout".
    iDestruct (sx_carry_open sp0 m plen pfun rest with "Hcarry")
      as "(Hf1 & Hf2 & Hspill & F10 & Hpb & Hps)".
    iPoseProof (sxi_0ce with "Htext") as "Hice".
    iPoseProof (sxi_0d0 with "Htext") as "Hid0".
    (* ===== +0x0ce c.mv s2,a0 : keep the return value ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (SX + 0xce) : mword 64) Rs2 Ra0
              M (K - 60)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hice").
    iIntros (CID1 Hq1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N1 := <[Regidx Rs2 := regval_into_reg
                  (add_vec zero_reg (M !!! Regidx Ra0))]> M).
    assert (HN1s2 : (N1 !!! Regidx Rs2 : mword 64) = rv)
      by (rewrite /N1 upd_eq Ha0; apply add_vec_zero_l).
    assert (HN1sp : sx_sp sp0 N1)
      by (rewrite /sx_sp /N1 upd_ne; [exact Hsp | nz]).
    assert (HN1s1 : (N1 !!! Regidx Rs1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N1 upd_ne; [exact Hs1 | nz]).
    assert (HN1s4 : (N1 !!! Regidx Rs4 : mword 64) = pa_stk sp0 58)
      by (rewrite /N1 upd_ne; [exact Hs4 | nz]).
    assert (HN1thr : sx_thr m N1).
    { intros c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23.
      rewrite /N1 upd_ne; [| congruence].
      exact (Hthr c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23). }
    assert (Hpd0 : add_vec_int (mword_of_int (SX + 0xce) : mword 64) 2
                   = mword_of_int (SX + 0xd0)) by pcw.
    iEval (rewrite Hpd0) in "Hpc".
    (* ===== +0x0d0 addi s4,s4,256 ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (SX + 0xd0) : mword 64) Rs4 Rs4
              (mword_of_int 256 : mword 12) N1 (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hid0").
    iIntros (CID2 Hq2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N2 := <[Regidx Rs4 := regval_into_reg
                  (add_vec (N1 !!! Regidx Rs4)
                     (sign_extend' 64 (mword_of_int 256 : mword 12)))]> N1).
    assert (HN2s4 : (N2 !!! Regidx Rs4 : mword 64) = pa_stk sp0 26)
      by (rewrite /N2 upd_eq HN1s4; apply sx_argv_end2).
    assert (HN2s1 : (N2 !!! Regidx Rs1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N2 upd_ne; [exact HN1s1 | nz]).
    assert (HN2s2 : (N2 !!! Regidx Rs2 : mword 64) = rv)
      by (rewrite /N2 upd_ne; [exact HN1s2 | nz]).
    assert (HN2sp : sx_sp sp0 N2)
      by (rewrite /sx_sp /N2 upd_ne; [exact HN1sp | nz]).
    assert (HN2thr : sx_thr m N2).
    { intros c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23.
      rewrite /N2 upd_ne; [| congruence].
      exact (HN1thr c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23). }
    assert (Hpd4 : add_vec_int (mword_of_int (SX + 0xd0) : mword 64) 4
                   = mword_of_int (SX + 0xd4)) by pcw.
    iEval (rewrite Hpd4) in "Hpc".
    (* ===== +0x0d4 .. +0x0de THE FREE LOOP ===== *)
    iDestruct (sx_argv0_at sp0 t pg with "Harr") as "Harr".
    iDestruct (cpu_own_transport CID0 CID2 0%nat eb (proc_addr jp) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (sx_free_loop (CID0 := CID2) γa sp0 (proc_addr jp) K eb b lks
              pg afun t 0xd4 0xe2 (mword_of_int 6 : mword 8)
              (mword_of_int 2078118 : mword 21)
              HK Ht32 Hpgok Hlb ltac:(pcw) ltac:(pcw) ltac:(csf) ltac:(pcw)
              ltac:(pcw) ltac:(csf)
              sxi_0d4 sxi_0d6 sxi_0d8 sxi_0dc sxi_0de
              32%nat N2 0%nat ltac:(lia) ltac:(lia) ltac:(lia) HN2s1 HN2s4
              with "Htext Hka Hpc Hcg Hcnt Harr Hpgs").
    iIntros (CID3 Hq3 M3 pcx) "%Hpcx %Hthr3 Hpc Hcg Hcnt Harr".
    (* BOTH exits are +0x0e2 *)
    assert (Hpce : pcx = (mword_of_int (SX + 0xe2) : mword 64)).
    { destruct Hpcx as [-> | ->]; [reflexivity |].
      rewrite (_ : (SX + 0xd4 + 14)%Z = (SX + 0xe2)%Z); [reflexivity | lia]. }
    iEval (rewrite Hpce) in "Hpc".
    assert (HM3sp : sx_sp sp0 M3)
      by (rewrite /sx_sp (Hthr3 csp_rs1 ltac:(csf) ltac:(nz)); exact HN2sp).
    assert (HM3s2 : (M3 !!! Regidx Rs2 : mword 64) = rv)
      by (rewrite (Hthr3 Rs2 ltac:(csf) ltac:(nz)); exact HN2s2).
    assert (HM3thr : sx_thr m M3).
    { intros c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23.
      rewrite (Hthr3 c Hc D9).
      exact (HN2thr c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23). }
    iDestruct (sx_argv_ala sp0 with "Harr") as "[%Hala Harr]".
    iPoseProof (sxi_0e2 with "Htext") as "Hie2".
    iPoseProof (sxi_0f2 with "Htext") as "Hif2".
    (* ===== +0x0e2 c.mv a0,s2 ===== *)
    iApply (wp_cmv_s_sconf (mword_of_int (SX + 0xe2) : mword 64) Ra0 Rs2
              M3 (K - 60)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hie2").
    iIntros (CID4 Hq4) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (M4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M3 !!! Regidx Rs2))]> M3).
    assert (HM4a0 : (M4 !!! Regidx Ra0 : mword 64) = rv)
      by (rewrite /M4 upd_eq HM3s2; apply add_vec_zero_l).
    assert (HM4sp : sx_sp sp0 M4)
      by (rewrite /sx_sp /M4 upd_ne; [exact HM3sp | nz]).
    assert (HM4thr : sx_thr m M4).
    { intros c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23.
      rewrite /M4 upd_ne; [| apply not_eq_sym; apply is_cs_idx_true_neq;
                             [csf | exact Hc]].
      exact (HM3thr c Hc D2 D8 D9 D18 D19 D20 D21 D22 D23). }
    assert (Hpe4 : add_vec_int (mword_of_int (SX + 0xe2) : mword 64) 2
                   = mword_of_int (SX + 0xe4)) by pcw.
    iEval (rewrite Hpe4) in "Hpc".
    (* ===== +0x0e4 .. +0x0f0 the reload ===== *)
    iApply (sx_reload (CID0 := CID4) sp0 m M4 K b (proc_addr jp) 0xe4
              HM4sp HM4thr sxi_0e4 sxi_0e6 sxi_0e8 sxi_0ea sxi_0ec sxi_0ee
              sxi_0f0 with "Htext Hpc Hcg Hspill").
    iIntros (CID5 Hq5 M5) "%HRL Hpc Hcg Hspill".
    destruct HRL as ((HM5sp & HM5thr & _ & HM5a0) & E1 & E2 & E3 & E4 & E5 & E6 & E7).
    rewrite (_ : (SX + 0xe4 + 14)%Z = (SX + 0xf2)%Z); [| lia].
    (* ===== +0x0f2 c.j +0x104 ===== *)
    assert (Htj : add_vec (mword_of_int (SX + 0xf2) : mword 64)
                    (sign_extend' 64 (sign_extend' 21
                       (concat_vec (mword_of_int 9 : mword 11) ('b"0"))))
                  = (mword_of_int (SX + 0x104) : mword 64)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (SX + 0xf2) : mword 64)
              (sign_extend' 21 (concat_vec (mword_of_int 9 : mword 11) ('b"0")))
              M5 (K - 60)%nat b ltac:(rewrite Htj; vm_compute; reflexivity)
              with "Hcg Hpc Hif2").
    iIntros (CID6 Hq6). iApply bi.later_intro. iIntros "Hcg Hpc".
    iEval (rewrite Htj) in "Hpc".
    iDestruct (sx_rest_build sp0 m plen pfun rest uav Hplen
                 with "Hspill F10 Hpb Hps F59 F60 Harr") as "Hrest".
    iApply (sx_epilogue (CID0 := CID6) m M5 sp0 K b (proc_addr jp)
              K60 Kpop Hsp0 HM5sp HM5thr E1 E2 E3 E4 E5 E6 E7 Halp Hala
              with "Hcg Htext Hpc Hf1 Hf2 Hrest [Hout Hcnt Hpriv]").
    iIntros (CID7) "%Hq7". iIntros (mf) "%Hcsf %Hfa0 Hcg Hpc".
    iSpecialize ("Hout" $! CID7 with "[%]"); [wp_next_chain |].
    iDestruct (cpu_own_transport CID3 CID7 0%nat eb (proc_addr jp) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply ("Hout" $! mf with "[%] [%] Hcg Hcnt Hpc Hpriv").
    { exact Hcsf. }
    { rewrite Hfa0 HM5a0. exact HM4a0. }
  Qed.

End SysExecSuccTail.

(* ===================================================================== *)
(*  +0x0b6 .. +0x0cc -- THE BREAK, AND THE CALL TO kexec.                 *)
(*                                                                        *)
(*  [argv[i] = 0] is a no-op on the resource (memset already put it        *)
(*  there); what the six instructions really do is compute the two         *)
(*  pointers kexec is called with.  The work is the ARRAY'S CHANGE OF      *)
(*  VIEW: the fill loop carries it as -- filled below [i], memset's zero   *)
(*  above -- and kexec's contract wants [S na] cells ending in a NULL,     *)
(*  plus whatever is left over.  [sx_argv_kx] is that one equivalence, and *)
(*  it is what makes [avf := sx_avf pg i] -- the pointers with a zero      *)
(*  written at [i] -- the vector kexec is handed.                          *)
(* ===================================================================== *)
Section SysExecBreak.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.
  Local Ltac csf := vm_compute; reflexivity.

  (* the argument vector kexec is handed: the [i] pointers the loop filled,
     with the terminating NULL at [i] *)
  Definition sx_avf (pg : nat -> mword 64) (i : nat) : nat -> mword 64 :=
    sx_upd pg i (mword_of_int 0 : mword 64).

  Lemma sx_avf_lt (pg : nat -> mword 64) (i j : nat) :
    (j < i)%nat -> sx_avf pg i j = pg j.
  Proof. intro Hj. rewrite /sx_avf. apply sx_upd_lt. exact Hj. Qed.

  Lemma sx_avf_eq (pg : nat -> mword 64) (i : nat) :
    sx_avf pg i i = (mword_of_int 0 : mword 64).
  Proof. rewrite /sx_avf. apply sx_upd_eq. Qed.

  (* THE CHANGE OF VIEW.  Both sides own the same 32 cells; the loop counts
     them from the array's base and kexec counts them from its argument
     pointer, and the NULL is the one cell they disagree about naming. *)
  Lemma sx_argv_kx (sp0 : mword 64) (i : nat) (pg : nat -> mword 64) :
    (i < 32)%nat ->
    sx_argv0 sp0 i pg ⊣⊢
    (([∗ list] j ∈ seq 0 (S i),
        pa_add (pa_stk sp0 58) (8 * j) ↦₈[KT1] sx_avf pg i j) ∗
     ([∗ list] j ∈ seq (S i) (31 - i),
        (pa_stk sp0 (58 - j)) ↦₈[KT1] (mword_of_int 0 : mword 64)))%I.
  Proof.
    intro Hi.
    assert (Haddr : forall f : nat -> mword 64,
      ([∗ list] j ∈ seq 0 (S i), pa_add (pa_stk sp0 58) (8 * j) ↦₈[KT1] f j)
      ⊣⊢ ([∗ list] j ∈ seq 0 (S i), (pa_stk sp0 (58 - j)) ↦₈[KT1] f j)).
    { intro f. apply big_sepL_proper. intros n j Hj.
      apply lookup_seq in Hj as [Hj0 Hlt]. subst j.
      rewrite (pa_stk_addn sp0 58 (0 + n)%nat ltac:(lia)). reflexivity. }
    rewrite (Haddr (sx_avf pg i)).
    rewrite /sx_argv0.
    rewrite (_ : (32 - i)%nat = S (31 - i)%nat); [| lia].
    rewrite -(cons_seq (31 - i)%nat i) big_sepL_cons.
    rewrite (seq_S i 0) big_sepL_app big_sepL_singleton.
    rewrite (_ : (0 + i)%nat = i); [| lia].
    rewrite sx_avf_eq.
    assert (Hlo : ([∗ list] j ∈ seq 0 i, (pa_stk sp0 (58 - j)) ↦₈[KT1] pg j)
                  ⊣⊢ ([∗ list] j ∈ seq 0 i, (pa_stk sp0 (58 - j)) ↦₈[KT1] sx_avf pg i j)).
    { apply big_sepL_proper. intros n j Hj.
      apply lookup_seq in Hj as [Hj0 Hlt]. subst j.
      rewrite (sx_avf_lt pg i (0 + n)%nat ltac:(lia)). reflexivity. }
    rewrite Hlo. iSplit.
    - iIntros "(A & B & Cc)". iSplitR "Cc"; [| iExact "Cc"].
      iSplitL "A"; [iExact "A" | iExact "B"].
    - iIntros "((A & B) & Cc)". iSplitL "A"; [iExact "A" |].
      iSplitL "B"; [iExact "B" | iExact "Cc"].
  Qed.

  Lemma sx_pages_ext (pg pg' : nat -> mword 64) (afun : nat -> nat -> bv 8)
      (t : nat) :
    (forall j, (j < t)%nat -> pg' j = pg j) ->
    sx_pages pg afun 0 t ⊣⊢ sx_pages pg' afun 0 t.
  Proof.
    intro Hag. rewrite /sx_pages !Nat.sub_0_r.
    apply big_sepL_proper. intros n j Hj.
    apply lookup_seq in Hj as [Hj0 Hlt]. subst j.
    rewrite (Hag (0 + n)%nat ltac:(lia)). reflexivity.
  Qed.

  (* [argv + 8i] again, this time built the other way round: the machine
     adds the scaled index TO the base, and [pa_stk_addn] is stated the
     other way.  Going through commutativity rather than re-deriving the
     wrap normalisation is not a style choice -- the nested [bv_wrap] the
     direct route leaves behind cannot be flattened once the OUTER
     [bv_wrap_add_idemp_r] has consumed its context. *)
  Lemma sx_addv_comm (x y : mword 64) : add_vec x y = add_vec y x.
  Proof. apply bv_eq. rewrite !add_vec64_unsigned. f_equal. lia. Qed.

  Lemma sx_scaled (sp0 : mword 64) (i : nat) : (i < 32)%nat ->
    add_vec (mword_of_int (Z.of_nat i * 8) : mword 64) (pa_stk sp0 58)
    = pa_stk sp0 (58 - i)%nat.
  Proof.
    intro Hi.
    assert (He : (mword_of_int (Z.of_nat i * 8) : mword 64)
                 = mword_of_int (Z.of_nat (8 * i))) by (f_equal; lia).
    rewrite sx_addv_comm He.
    change (add_vec (pa_stk sp0 58) (mword_of_int (Z.of_nat (8 * i))))
      with (pa_add (pa_stk sp0 58) (8 * i)%nat).
    rewrite (pa_stk_addn sp0 58 i ltac:(lia)). reflexivity.
  Qed.

  Lemma sx_break `{CID0 : CpuId}
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (γa γf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used : gset Z)
      (dqb dqs : dfrac)
      (pid : mword 32) (V : pprivate)
      (K : nat) (eb b : bool) (lks : gset string)
      (sp0 : mword 64) (m : regfile) (plen : nat) (pfun rest : nat -> bv 8)
      (uav : mword 64) (M : regfile) (P : uptd) (i : nat)
      (pg : nat -> mword 64) (alen : nat -> nat) (afun : nat -> nat -> bv 8) :
    (K_sys_exec <= K)%nat ->
    locks_below lks "kmem" ->
    sp0 = (m !!! Regidx csp_rs1 : mword 64) ->
    (plen < 128)%nat -> bb_cstr pfun plen ->
    sx_alp sp0 ->
    dev = icfg_dev -> nib = icfg_nib -> g = icfg_log -> inodestart = icfg_ist ->
    dev = ROOTDEV -> (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    (jp < NPROC)%nat -> gs !! jp = Some gl ->
    b = true -> eb = true ->
    kernel_text -∗
    fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
              cov logstart inodestart nib dev -∗
    kalloc_env γa None -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    bslots bn 3 -∗
    iref_slots 2 -∗
    sx_body γf jp pid V K eb b lks sp0 m plen pfun rest uav
            M P i pg alen afun (mword_of_int (SX + 0xb6) : mword 64) -∗
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
        ⌜callee_saved m mf⌝ -∗
        ⌜kexec_ok (upd_upt V P) V' (mf !!! Regidx Ra0) entry spv szv' i alen⌝ -∗
        ⌜used' ⊆ used⌝ -∗
        ⌜uptd_ext (pv_upt V) P⌝ -∗
        sie_cap_gpr KT1 mf K b (proc_addr jp) -∗
        cpu_own 0 eb (proc_addr jp) b lks -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
        sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
        bitmap_res gfs bmapstart cov logstart size used' -∗
        bslots bn 3 -∗
        iref_slots 2 -∗
        proc_priv γf (proc_addr jp) pid V' -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hlb Hsp0 Hplen Hpcstr Halp Hdev Hnib Hg Hist Hroot Hnib0
           Hlg Hsize Hbm0 Hbmc Hbml Hist0 Hcb Hireg Hjp Hgl Hbt Hebt.
    destruct (sx_kb K HK) as (Kkx & Kar & Kaa & Kfa & Kfs & K14 & K2 & K60 & Kpop).
    iIntros "#Htext #Hfab #Hka Hbmp Hisp Hbmr Hbs Hir Hst".
    rewrite /sx_body.
    iDestruct "Hst" as "((%Hi32 & %Hext & %Hok & %HR) & Hpc & Hcg & Hcnt &
                         Hpriv & Hcarry & F59 & F60 & Harr & Hpgs)".
    iIntros "Hout".
    iDestruct (sx_carry_open sp0 m plen pfun rest with "Hcarry")
      as "(Hf1 & Hf2 & Hspill & F10 & Hpb & Hps)".
    iPoseProof (sxi_0b6 with "Htext") as "Hib6".
    iPoseProof (sxi_0ba with "Htext") as "Hiba".
    iPoseProof (sxi_0be with "Htext") as "Hibe".
    iPoseProof (sxi_0c0 with "Htext") as "Hic0".
    iPoseProof (sxi_0c2 with "Htext") as "Hic2".
    iPoseProof (sxi_0c6 with "Htext") as "Hic6".
    iPoseProof (sxi_0ca with "Htext") as "Hica".
    (* ===== +0x0b6 addiw a5,s2,0 : argc, in int ===== *)
    iApply (wp_addiw_s_sconf (mword_of_int (SX + 0xb6) : mword 64) Ra5 Rs2
              (mword_of_int 0 : mword 12) M (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hib6").
    iIntros (CID1 Hq1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N1 := <[Regidx Ra5 := regval_into_reg
                  (sign_extend' 64 (subrange_vec_dec
                     (add_vec (M !!! Regidx Rs2)
                        (sign_extend' 64 (mword_of_int 0 : mword 12))) 31 0))]> M).
    assert (HR1 : sx_regs sp0 m N1 i)
      by (rewrite /N1; apply sx_regs_tmp; [csf | exact HR]).
    assert (HN1a5 : (N1 !!! Regidx Ra5 : mword 64)
                    = (mword_of_int (Z.of_nat i) : mword 64)).
    { rewrite /N1 upd_eq (sxr_s2 HR). apply w32_sextw_moi. lia. }
    assert (Hpba : add_vec_int (mword_of_int (SX + 0xb6) : mword 64) 4
                   = mword_of_int (SX + 0xba)) by pcw.
    iEval (rewrite Hpba) in "Hpc".
    (* ===== +0x0ba addi a1,s0,-464 : argv ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (SX + 0xba) : mword 64) Ra1 Rs0
              (mword_of_int 3632 : mword 12) N1 (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hiba").
    iIntros (CID2 Hq2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N2 := <[Regidx Ra1 := regval_into_reg
                  (add_vec (N1 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3632 : mword 12)))]> N1).
    assert (HR2 : sx_regs sp0 m N2 i)
      by (rewrite /N2; apply sx_regs_tmp; [csf | exact HR1]).
    assert (HN2a1 : (N2 !!! Regidx Ra1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N2 upd_eq (sxr_s0 HR1); apply sx_argv).
    assert (HN2a5 : (N2 !!! Regidx Ra5 : mword 64)
                    = (mword_of_int (Z.of_nat i) : mword 64))
      by (rewrite /N2 upd_ne; [exact HN1a5 | nz]).
    assert (Hpbe : add_vec_int (mword_of_int (SX + 0xba) : mword 64) 4
                   = mword_of_int (SX + 0xbe)) by pcw.
    iEval (rewrite Hpbe) in "Hpc".
    (* ===== +0x0be c.slli a5,3 ===== *)
    iApply (wp_cslli_s_sconf (mword_of_int (SX + 0xbe) : mword 64) (Regidx Ra5)
              Ra5 (mword_of_int 3 : mword 6) N2 (K - 60)%nat b
              eq_refl ltac:(nz) ltac:(rdok) with "Hcg Hpc Hibe").
    iIntros (CID3 Hq3) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N3 := <[Regidx Ra5 := regval_into_reg
                  (shift_bits_left (N2 !!! Regidx Ra5)
                     (subrange_vec_dec (mword_of_int 3 : mword 6)
                        (Z.sub log2_xlen 1) 0))]> N2).
    assert (HR3 : sx_regs sp0 m N3 i)
      by (rewrite /N3; apply sx_regs_tmp; [csf | exact HR2]).
    assert (HN3a5 : (N3 !!! Regidx Ra5 : mword 64)
                    = (mword_of_int (Z.of_nat i * 8) : mword 64)).
    { rewrite /N3 upd_eq HN2a5. apply ofile_slli3; lia. }
    assert (HN3a1 : (N3 !!! Regidx Ra1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N3 upd_ne; [exact HN2a1 | nz]).
    assert (Hpc0 : add_vec_int (mword_of_int (SX + 0xbe) : mword 64) 2
                   = mword_of_int (SX + 0xc0)) by pcw.
    iEval (rewrite Hpc0) in "Hpc".
    (* ===== +0x0c0 c.add a5,a1 : &argv[i] ===== *)
    iApply (wp_cadd_s_sconf (mword_of_int (SX + 0xc0) : mword 64) Ra5 Ra1
              N3 (K - 60)%nat b ltac:(nz) ltac:(rdok) with "Hcg Hpc Hic0").
    iIntros (CID4 Hq4) "Hcg Hpc". iEval (rgne) in "Hcg". iEval (rgne) in "Hcg".
    set (N4 := <[Regidx Ra5 := regval_into_reg
                  (add_vec (N3 !!! Regidx Ra5) (N3 !!! Regidx Ra1))]> N3).
    assert (HR4 : sx_regs sp0 m N4 i)
      by (rewrite /N4; apply sx_regs_tmp; [csf | exact HR3]).
    assert (HN4a5 : (N4 !!! Regidx Ra5 : mword 64) = pa_stk sp0 (58 - i)%nat).
    { rewrite /N4 upd_eq HN3a5 HN3a1. apply sx_scaled. lia. }
    assert (HN4a1 : (N4 !!! Regidx Ra1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N4 upd_ne; [exact HN3a1 | nz]).
    assert (Hpc2 : add_vec_int (mword_of_int (SX + 0xc0) : mword 64) 2
                   = mword_of_int (SX + 0xc2)) by pcw.
    iEval (rewrite Hpc2) in "Hpc".
    (* ===== +0x0c2 sd zero,0(a5) : argv[i] = 0 -- already zero ===== *)
    iDestruct (sx_argv0_open sp0 i pg ltac:(lia) with "Harr") as "[Hcell Hrest]".
    assert (Hga5 : rget N4 Ra5 = (N4 !!! Regidx Ra5 : mword 64))
      by (apply rget_ne; nz).
    assert (Hca5 : add_vec (rget N4 Ra5)
                     (sign_extend' 64 (mword_of_int 0 : mword 12))
                   = pa_stk sp0 (58 - i)%nat)
      by (rewrite Hga5 HN4a5; apply sx_off0).
    iEval (rewrite -Hca5) in "Hcell".
    iApply (wp_sd_zero_s_sconf (mword_of_int (SX + 0xc2) : mword 64) Ra5
              (mword_of_int 0 : mword 12) N4 (K - 60)%nat
              (mword_of_int 0 : mword 64) b with "Hcg Hpc Hic2 Hcell").
    iIntros (CID5 Hq5) "Hcg Hpc Hcell".
    iEval (rewrite Hca5 sx_zreg0) in "Hcell".
    iDestruct (sx_argv0_shut sp0 i pg ltac:(lia) with "Hcell Hrest") as "Harr".
    assert (Hpc6 : add_vec_int (mword_of_int (SX + 0xc2) : mword 64) 4
                   = mword_of_int (SX + 0xc6)) by pcw.
    iEval (rewrite Hpc6) in "Hpc".
    (* ===== +0x0c6 addi a0,s0,-208 : path ===== *)
    iApply (wp_addi4_s_sconf (mword_of_int (SX + 0xc6) : mword 64) Ra0 Rs0
              (mword_of_int 3888 : mword 12) N4 (K - 60)%nat b
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hic6").
    iIntros (CID6 Hq6) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N5 := <[Regidx Ra0 := regval_into_reg
                  (add_vec (N4 !!! Regidx Rs0)
                     (sign_extend' 64 (mword_of_int 3888 : mword 12)))]> N4).
    assert (HR5 : sx_regs sp0 m N5 i)
      by (rewrite /N5; apply sx_regs_tmp; [csf | exact HR4]).
    assert (HN5a0 : (N5 !!! Regidx Ra0 : mword 64) = pa_stk sp0 26)
      by (rewrite /N5 upd_eq (sxr_s0 HR4); apply sx_path).
    assert (HN5a1 : (N5 !!! Regidx Ra1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N5 upd_ne; [exact HN4a1 | nz]).
    assert (Hpca : add_vec_int (mword_of_int (SX + 0xc6) : mword 64) 4
                   = mword_of_int (SX + 0xca)) by pcw.
    iEval (rewrite Hpca) in "Hpc".
    (* ===== +0x0ca jal ra,kexec ===== *)
    assert (Htkx : add_vec (mword_of_int (SX + 0xca) : mword 64)
                     (sign_extend' 64 (mword_of_int 2093916 : mword 21))
                   = mword_of_int KernelSyms.kexec) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (SX + 0xca) : mword 64) Rra
              (mword_of_int 2093916 : mword 21) N5 (K - 60)%nat b
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htkx; vm_compute; reflexivity)
              with "Hcg Hpc Hica").
    iIntros (CID7 Hq7) "Hcg Hpc". iEval (rewrite Htkx) in "Hpc".
    set (N6 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (SX + 0xca) : mword 64) 4)]> N5).
    assert (HR6 : sx_regs sp0 m N6 i)
      by (rewrite /N6; apply sx_regs_tmp; [csf | exact HR5]).
    assert (HN6a0 : (N6 !!! Regidx Ra0 : mword 64) = pa_stk sp0 26)
      by (rewrite /N6 upd_ne; [exact HN5a0 | nz]).
    assert (HN6a1 : (N6 !!! Regidx Ra1 : mword 64) = pa_stk sp0 58)
      by (rewrite /N6 upd_ne; [exact HN5a1 | nz]).
    assert (HN6ra : ret_pc (N6 !!! Regidx Rra : mword 64)
                    = (mword_of_int (SX + 0xce) : mword 64))
      by (rewrite /N6 upd_eq; pcw).
    (* the array, in kexec's spelling *)
    rewrite (sx_argv_kx sp0 i pg ltac:(lia)).
    iDestruct "Harr" as "[Havf Hhi]".
    iEval (rewrite -HN6a1) in "Havf".
    rewrite (sx_pages_ext pg (sx_avf pg i) afun i
               ltac:(intros j Hj; apply sx_avf_lt; lia)).
    iEval (rewrite /sx_pages Nat.sub_0_r) in "Hpgs".
    iEval (rewrite -HN6a0) in "Hpb".
    iDestruct (cpu_own_transport CID0 CID7 0%nat eb (proc_addr jp) b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Kexec.wp_kexec_sconf gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl
              γa γf cov logstart bmapstart inodestart nib size dev used
              plen pfun i (sx_avf pg i) alen (fun _ => 4096%nat) afun
              pid (upd_upt V P) dqb dqs (DfracOwn 1) N6 (K - 60)%nat eb b lks
              Kkx Hdev Hnib Hg Hist Hroot Hnib0 Hlg Hsize Hbm0 Hbmc Hbml Hist0
              Hcb Hireg Hpcstr ltac:(lia)
              ltac:(intros j Hj; rewrite (sx_avf_lt pg i j Hj);
                    exact (proj1 (Hok j Hj)))
              (sx_avf_eq pg i) ltac:(unfold MAXARG; lia)
              ltac:(intros j Hj; exact (proj1 (proj2 (proj2 (Hok j Hj)))))
              ltac:(intros j Hj; exact (proj2 (proj2 (proj2 (Hok j Hj)))))
              ltac:(intros j Hj; pose proof (proj1 (proj2 (proj2 (Hok j Hj))));
                    lia)
              Hjp Hgl Hbt Hebt
              with "Hcg Hcnt Htext Hpc Hfab Hka Hbmp Hisp Hbmr Hpriv
                    Hpb Havf Hpgs Hbs Hir").
    iIntros (CID8 Hq8 mf used' V' entry spv szv') "%Hcsf %Hkok Hcg Hcnt Hpc
             Hbmp Hisp %Husub Hbmr Hka2 Hpriv Hpb Havf Hpgs Hbs Hir".
    iEval (rewrite HN6ra) in "Hpc".
    iEval (rewrite HN6a0) in "Hpb".
    iEval (rewrite HN6a1) in "Havf".
    assert (HRf : sx_regs sp0 m mf i)
      by exact (sx_regs_call sp0 m N6 mf i Hcsf HR6).
    (* the array, back in the loop's spelling *)
    iAssert (sx_pages (sx_avf pg i) afun 0 i)%I with "[Hpgs]" as "Hpgs".
    { rewrite /sx_pages Nat.sub_0_r. iExact "Hpgs". }
    rewrite -(sx_pages_ext pg (sx_avf pg i) afun i
                ltac:(intros j Hj; apply sx_avf_lt; lia)).
    iAssert (sx_argv0 sp0 i pg) with "[Havf Hhi]" as "Harr".
    { rewrite (sx_argv_kx sp0 i pg ltac:(lia)).
      iSplitL "Havf"; [iExact "Havf" | iExact "Hhi"]. }
    iApply (sx_succ_tail (CID0 := CID8) γf γa jp pid V' K eb b lks sp0 m plen
              pfun rest uav (mf !!! Regidx Ra0 : mword 64) mf i pg afun
              HK Hlb Hsp0 Hplen Halp ltac:(lia) (sx_ok_pgok pg alen afun i Hok)
              (sxr_sp HRf) (sxr_thr HRf) (sxr_s0 HRf) (sxr_s1 HRf) (sxr_s4 HRf)
              eq_refl
              with "Htext Hka Hpc Hcg Hcnt Hpriv [Hf1 Hf2 Hspill F10 Hpb Hps]
                    F59 F60 Harr Hpgs [Hout Hbmp Hisp Hbmr Hbs Hir]").
    { rewrite /sx_carry /sx_spill.
      iDestruct "Hspill" as "(P3 & P4 & P5 & P6 & P7 & P8 & P9)".
      iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "P3"; [iExact "P3" |]. iSplitL "P4"; [iExact "P4" |].
      iSplitL "P5"; [iExact "P5" |]. iSplitL "P6"; [iExact "P6" |].
      iSplitL "P7"; [iExact "P7" |]. iSplitL "P8"; [iExact "P8" |].
      iSplitL "P9"; [iExact "P9" |]. iSplitL "F10"; [iExact "F10" |].
      iSplitL "Hpb"; [iExact "Hpb" | iExact "Hps"]. }
    iIntros (CID9) "%Hq9". iIntros (mg) "%Hcsg %Hga0 Hcg Hcnt Hpc Hpriv".
    iSpecialize ("Hout" $! CID9 with "[%]"); [wp_next_chain |].
    iApply ("Hout" $! mg used' V' entry spv szv'
             with "[%] [%] [%] [%] Hcg Hcnt Hpc Hbmp Hisp Hbmr Hbs Hir Hpriv").
    { exact Hcsg. }
    { rewrite Hga0. exact Hkok. }
    { exact Husub. }
    { exact Hext. }
  Qed.

End SysExecBreak.

(* ===================================================================== *)
(*  THE COMPOSITION.                                                      *)
(*                                                                        *)
(*  head -> setup -> the fill loop -> {break -> kexec -> the success tail  *)
(*  | bad:}.  Every seam is a state predicate the two sides already agree  *)
(*  on, so all this file does is pin the interrupt index, hand the frame   *)
(*  from one block's spelling to the next's, and turn each of the two      *)
(*  returns into the contract's [sys_exec_post].                          *)
(*                                                                        *)
(*  PINNING [b] IS THE FIRST STEP.  The contract takes [eb = true] and     *)
(*  leaves [b] free; at depth 0 the SIE eighth in [sie_cap_gpr] and        *)
(*  [cpu_own]'s own index agree, so [b = eb = true] -- and [cpu_own]'s     *)
(*  depth then pins [lks = ∅], which is every lock-order goal the eight    *)
(*  callees raise.  Do it before anything else or the FS layer's [wp_next  *)
(*  true] contracts look unreachable.                                      *)
(* ===================================================================== *)
Section SysExecWhole.
  Context `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs3 := (mword_of_int 19 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Rs5 := (mword_of_int 21 : mword 5).
  Notation Rs6 := (mword_of_int 22 : mword 5).
  Notation Rs7 := (mword_of_int 23 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  (* [ProofFiledup.sie_b_agree], restated: a whole-function proof file is
     not a dependency any other one may take. *)
  Local Lemma sie_b_agree (m : regfile) (n K0 : nat) (eb b : bool)
      (p : mword 64) (lks : gset string) :
    sie_cap_gpr KT1 m K0 b p -∗ cpu_own n eb p b lks -∗
    ⌜ b = match n with O => eb | S _ => false end ⌝.
  Proof.
    iIntros "Hcg Hcnt". destruct b.
    - iDestruct "Hcnt" as "%Hb". destruct Hb as (-> & -> & _). done.
    - destruct n as [|n']; [ | done ].
      iDestruct "Hcnt" as "[_ Hint]".
      iDestruct "Hcg" as "(_ & _ & (_ & _ & Harm & _) & _)".
      iDestruct (ghost_var_agree with "Harm Hint") as %Heq.
      destruct eb; [ exfalso | done ].
      apply (f_equal (@bv_unsigned _)) in Heq. vm_compute in Heq. discriminate.
  Qed.

  Lemma wp_sys_exec_sconf
      (γf : gname) (γa : gname)
      (gs : list gname) (j : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (dqb dqs : dfrac)
      (v0 v1 : mword 64)
      (pid : mword 32) (V : pprivate)
      (m : regfile) (K : nat) (eb : bool)
      (b : bool) (lks : gset string) :
      wp_sys_exec_sconf_body γf γa gs j gl gu gd gk pd pav pu bn g gfs gi
                             cn gtl cov logstart bmapstart inodestart nib
                             size dev used dqb dqs v0 v1 pid V m K eb b lks.
  Proof.
    cbv beta zeta delta [wp_sys_exec_sconf_body].
    intros HK Hdev Hnib Hg Hist Hroot Hnib0 Hlg Hsize Hbm0 Hbmc Hbml Hist0
           Hcb Hireg Hjp Hgl Hebt Harg0 Harg1.
    subst eb.
    iIntros "Hcg Hcnt Htcx Hccx #Htext #Hdata Hpc #Hfab Hbmp Hisp Hbmr
             Hbs #Hka Hir Hpriv Hcont".
    (* ---- the interrupt index, and the held-lock set ---- *)
    iDestruct (sie_b_agree m 0%nat K true b (proc_addr j) lks
                 with "Hcg Hcnt") as %Hb.
    cbn in Hb. subst b.
    iDestruct (cpu_own_zero_empty true (proc_addr j) true lks
                 with "Hcnt") as "[%Hlks Hcnt]".
    subst lks.
    pose proof (locks_below_empty "kmem") as Hlb.
    set (sp0 := (m !!! Regidx csp_rs1 : mword 64)).
    (* ===== +0x000 .. +0x026 : the prologue ===== *)
    iApply (sx_head γf γa j pid V v0 v1 m K true true ∅
              HK Harg0 Harg1 Hlb with "Hcg Hcnt Htext Hdata Hpc Hpriv Hka").
    iIntros (CID1 Hq1 M P' plen pfun rst v59 v60) "[Hm1 | Hft]".
    { (* ---- argstr failed: -1, and the block never moved ---- *)
      iDestruct "Hm1" as "((%Hcs & %Hext & %Ha0) & Hcg & Hcnt & Hpc & Hpriv)".
      iSpecialize ("Hcont" $! CID1 with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! M used P'
               with "[%] [%] Hcg Hcnt Htcx Hccx Hpc Hbmp Hisp [%] Hbmr Hbs Hka
                     Hir [Hpriv]").
      { exact Hcs. }
      { exact Hext. }
      { reflexivity. }
      { rewrite /sys_exec_post.
        iExists (upd_upt V P'), 0%nat, (fun _ => 0%nat),
                (mword_of_int 0 : mword 64), (mword_of_int 0 : mword 64),
                (mword_of_int 0 : mword 64).
        iSplitR; [iPureIntro; left; split; [exact Ha0 | reflexivity] |].
        iExact "Hpriv". } }
    (* ---- the path is in: run the rest of the function ---- *)
    iDestruct "Hft" as "((%Hsp & %Hs0 & %Hthr2 & %Hext & %Hplen & %Hpcstr &
                          %Halp & %Hala) & Hpc & Hcg & Hcnt & Hpriv & F1 & F2 &
                         F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & Hpre & Hsuf &
                         Hab & F59 & F60)".
    (* ===== +0x028 .. +0x054 : the lazy spills and memset ===== *)
    iApply (sx_setup (CID0 := CID1) m M sp0 K true (proc_addr j)
              HK eq_refl Hsp Hs0 Hthr2 Hala
              with "Hcg Htext Hpc F3 F4 F5 F6 F7 F8 F9 Hab").
    iIntros (CID2 Hq2 M2) "%Hst2 Hpc Hcg S3 S4 S5 S6 S7 S8 S9 Hargv".
    destruct Hst2 as (H2sp & H2thr & H2s0 & H2s1 & H2s2 & H2s3 & H2s4 & H2s5 &
                      H2s6 & H2s7).
    iDestruct (cpu_own_transport CID1 CID2 0%nat true (proc_addr j) true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iAssert (sx_carry sp0 m plen pfun rst)
      with "[F1 F2 S3 S4 S5 S6 S7 S8 S9 F10 Hpre Hsuf]" as "Hcarry".
    { rewrite /sx_carry.
      iSplitL "F1"; [iExact "F1" |]. iSplitL "F2"; [iExact "F2" |].
      iSplitL "S3"; [iExact "S3" |]. iSplitL "S4"; [iExact "S4" |].
      iSplitL "S5"; [iExact "S5" |]. iSplitL "S6"; [iExact "S6" |].
      iSplitL "S7"; [iExact "S7" |]. iSplitL "S8"; [iExact "S8" |].
      iSplitL "S9"; [iExact "S9" |]. iSplitL "F10"; [iExact "F10" |].
      iSplitL "Hpre"; [iExact "Hpre" | iExact "Hsuf"]. }
    (* the array is empty, so the three index-keyed functions are arbitrary *)
    assert (HR0 : sx_regs sp0 m M2 0%nat).
    { split_and!;
        [ exact H2sp | exact H2thr | exact H2s0 | exact H2s1 | exact H2s2
        | exact H2s3 | exact H2s4 | exact H2s5 | exact H2s6 | exact H2s7 ]. }
    iAssert (sx_body γf j pid V K true true ∅ sp0 m plen pfun rst v59
               M2 P' 0%nat (fun _ => (mword_of_int 0 : mword 64))
               (fun _ => 0%nat) (fun _ _ => (mword_of_int 0 : mword 8))
               (mword_of_int (SX + 0x56) : mword 64))
      with "[Hpc Hcg Hcnt Hpriv Hcarry F59 F60 Hargv]" as "Hbody".
    { iApply (sx_body_intro (CID0 := CID2) γf j pid V K true true ∅ sp0 m
                plen pfun rst v59 M2 P' 0%nat
                (fun _ => (mword_of_int 0 : mword 64)) (fun _ => 0%nat)
                (fun _ _ => (mword_of_int 0 : mword 8))
                (mword_of_int (SX + 0x56) : mword 64)
                ltac:(lia) Hext ltac:(intros q Hq; lia) HR0
                with "Hpc Hcg Hcnt Hpriv Hcarry F59 [F60] [Hargv] []").
      { iExists v60. iExact "F60". }
      { rewrite /sx_argv0 sx_seq00 big_sepL_nil.
        iSplitR; [done | iExact "Hargv"]. }
      { rewrite /sx_pages sx_seq00 big_sepL_nil. done. } }
    (* ===== +0x056 .. +0x090 : the fill loop ===== *)
    iApply (sx_loop (CID0 := CID2) γf γa j pid V K true true ∅ sp0 m plen
              pfun rst v59 HK Hlb 32%nat M2 P' 0%nat
              (fun _ => (mword_of_int 0 : mword 64)) (fun _ => 0%nat)
              (fun _ _ => (mword_of_int 0 : mword 8)) ltac:(lia)
              with "Htext Hka Hbody").
    iIntros (CID3 Hq3 M3 P3 i3 pg3 al3 af3) "[Hbrk | Hbad]".
    - (* ---- the break: argv[i] = 0, then kexec ---- *)
      iApply (sx_break (CID0 := CID3) gs j gl gu gd gk pd pav pu bn g gfs gi
                cn gtl γa γf cov logstart bmapstart inodestart nib size dev
                used dqb dqs pid V K true true ∅ sp0 m plen pfun rst v59
                M3 P3 i3 pg3 al3 af3
                HK Hlb eq_refl Hplen Hpcstr Halp Hdev Hnib Hg Hist Hroot Hnib0
                Hlg Hsize Hbm0 Hbmc Hbml Hist0 Hcb Hireg Hjp Hgl eq_refl eq_refl
                with "Htext Hfab Hka Hbmp Hisp Hbmr Hbs Hir Hbrk").
      iIntros (CID4 Hq4 mf used' V' entry spv szv')
        "%Hcs %Hkok %Husub %Hext3 Hcg Hcnt Hpc Hbmp Hisp Hbmr Hbs Hir Hpriv".
      iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf used' P3
               with "[%] [%] Hcg Hcnt Htcx Hccx Hpc Hbmp Hisp [%] Hbmr Hbs Hka
                     Hir [Hpriv]").
      { exact Hcs. }
      { exact Hext3. }
      { exact Husub. }
      { rewrite /sys_exec_post.
        iExists V', i3, al3, entry, spv, szv'.
        iSplitR; [iPureIntro; exact Hkok |]. iExact "Hpriv". }
    - (* ---- [bad:]: free what was allocated and return -1 ---- *)
      iApply (sx_bad_tail (CID0 := CID3) γf γa j pid V K true true ∅ sp0 m
                plen pfun rst v59 M3 P3 i3 pg3 af3
                HK Hlb eq_refl Hplen Halp with "Htext Hka Hbad").
      iIntros (CID4 Hq4 mf) "%Hcs %Ha0 %Hext3 Hcg Hcnt Hpc Hpriv".
      iSpecialize ("Hcont" $! CID4 with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf used P3
               with "[%] [%] Hcg Hcnt Htcx Hccx Hpc Hbmp Hisp [%] Hbmr Hbs Hka
                     Hir [Hpriv]").
      { exact Hcs. }
      { exact Hext3. }
      { reflexivity. }
      { rewrite /sys_exec_post.
        iExists (upd_upt V P3), 0%nat, (fun _ => 0%nat),
                (mword_of_int 0 : mword 64), (mword_of_int 0 : mword 64),
                (mword_of_int 0 : mword 64).
        iSplitR; [iPureIntro; left; split; [exact Ha0 | reflexivity] |].
        iExact "Hpriv". }
  Qed.

End SysExecWhole.

End SysExecProof.
