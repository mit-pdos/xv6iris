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
   wrote.  [bytes_own_slotsn] would give the words back EXISTENTIALLY and
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
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import LockRank.
Require Import CpuOwn.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import SchedCtx.
Require Import WpUart.
Require Import DiskPtsto DiskInv.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import BitmapInv.
Require Import ByteBuf.
Require Import PathElems.
Require Import DinodeEnc.
Require Import InodeInv.
Require Import InodeLock.
Require Import SleepLock.
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
Require Import UmCovered.
Require Import FileInvDefs.
Require Import ProcInv.
Require Import VcGen.
Require Import SpecIput.
Require Import SpecDirlink.
Require Import SpecNamex.
Require Import SpecArgaddr.
Require Import SpecArgstr.
Require Import SpecFetchaddr.
Require Import SpecFetchstr.
Require Import SpecKalloc.
Require Import SpecKfree.
Require Import SpecMemset.
Require Import SpecKexec.
Require Import CodeSysExec.
Require Import SpecSysExec.
From Kernel Require KernelSyms.
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
  unfold K_sys_exec, K_kexec, argstr_stack, argaddr_stack, fetchaddr_stack,
         fetchstr_stack.
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
    ([∗ list] j ∈ seq 0 8, pa_add a j ↦ₘ zb) ⊢ a ↦₈ (mword_of_int 0 : mword 64).
  Proof.
    intros Hzb Hal. iIntros "H".
    iApply (word_pointsto_intro _ _ _ Hal).
    iApply (big_sepL_mono with "H"). intros i j Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite (Hzb i Hlt). done.
  Qed.

  Lemma sx_zeros_slots (sp : mword 64) (zb : bv 8) (k n : nat) :
    (forall j, (j < 8)%nat -> nth_byte (mword_of_int 0 : mword 64) j = zb) ->
    (n <= S k)%nat ->
    (forall i, (i < n)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp (k - i))) 8 = true) ->
    ([∗ list] j ∈ seq 0 (8 * n), pa_add (pa_stk sp k) j ↦ₘ zb) ⊢
    [∗ list] i ∈ seq 0 n, pa_stk sp (k - i) ↦₈ (mword_of_int 0 : mword 64).
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
    stack_own sp0 60 -∗
    ⌜sx_alp sp0⌝ ∗ ⌜sx_ala sp0⌝ ∗
    (∃ w : mword 64, (pa_stk sp0 1) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 2) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 3) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 4) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 5) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 6) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 7) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 8) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 9) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 10) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 59) ↦₈ w) ∗
    (∃ w : mword 64, (pa_stk sp0 60) ↦₈ w) ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 26) 128 ∗
    bytes_own (DfracOwn 1) (pa_stk sp0 58) 256.
  Proof.
    iIntros "H". rewrite stack_own_slots. cbn [seq].
    iDestruct "H" as "(S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28 & S29 & S30 & S31 & S32 & S33 & S34 & S35 & S36 & S37 & S38 & S39 & S40 & S41 & S42 & S43 & S44 & S45 & S46 & S47 & S48 & S49 & S50 & S51 & S52 & S53 & S54 & S55 & S56 & S57 & S58 & S59 & S60 & _)".
    change 128%nat with (8 * 16)%nat. change 256%nat with (8 * 32)%nat.
    iDestruct (slotsn_bytes_own sp0 26 16 ltac:(lia)
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
    iDestruct (slotsn_bytes_own sp0 58 32 ltac:(lia)
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
    (pa_stk sp0 1) ↦₈ v1 -∗
    (pa_stk sp0 2) ↦₈ v2 -∗
    (pa_stk sp0 3) ↦₈ v3 -∗
    (pa_stk sp0 4) ↦₈ v4 -∗
    (pa_stk sp0 5) ↦₈ v5 -∗
    (pa_stk sp0 6) ↦₈ v6 -∗
    (pa_stk sp0 7) ↦₈ v7 -∗
    (pa_stk sp0 8) ↦₈ v8 -∗
    (pa_stk sp0 9) ↦₈ v9 -∗
    (pa_stk sp0 10) ↦₈ v10 -∗
    (pa_stk sp0 59) ↦₈ v59 -∗
    (pa_stk sp0 60) ↦₈ v60 -∗
    bytes_own (DfracOwn 1) (pa_stk sp0 26) 128 -∗
    bytes_own (DfracOwn 1) (pa_stk sp0 58) 256 -∗
    stack_own sp0 60.
  Proof.
    intros Halp Hala. iIntros "S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S59 S60 Hpb Hab".
    change 128%nat with (8 * 16)%nat. change 256%nat with (8 * 32)%nat.
    iDestruct (bytes_own_slotsn sp0 26 16 ltac:(lia) Halp with "Hpb") as "Hp".
    iDestruct (bytes_own_slotsn sp0 58 32 ltac:(lia) Hala with "Hab") as "Ha".
    cbn [seq].
    iDestruct "Hp" as "(P26 & P25 & P24 & P23 & P22 & P21 & P20 & P19 & P18 & P17 & P16 & P15 & P14 & P13 & P12 & P11 & _)".
    iDestruct "Ha" as "(A58 & A57 & A56 & A55 & A54 & A53 & A52 & A51 & A50 & A49 & A48 & A47 & A46 & A45 & A44 & A43 & A42 & A41 & A40 & A39 & A38 & A37 & A36 & A35 & A34 & A33 & A32 & A31 & A30 & A29 & A28 & A27 & _)".
    rewrite stack_own_slots. cbn [seq].
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
    bytes_own (DfracOwn 1) a N ⊢
    ∃ f : nat -> bv 8, [∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ f j.
  Proof. rewrite /bytes_own. exact (bb_any_named a N). Qed.

  Lemma sx_name_bytes (a : mword 64) (N : nat) (f : nat -> bv 8) :
    ([∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ f j) ⊢ bytes_own (DfracOwn 1) a N.
  Proof. rewrite /bytes_own. exact (bb_named_any a N f). Qed.

  Lemma sx_buf_split (a : mword 64) (f : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 128, pa_add a j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ f j)
    ∗ ([∗ list] j ∈ seq 0 (127 - k)%nat,
         pa_add (pa_add a (S k)) j ↦ₘ f (S k + j)%nat).
  Proof.
    intro Hk.
    replace 128%nat with (S k + (127 - k))%nat by lia.
    rewrite (bb_split a (S k) (127 - k)%nat f). iIntros "[$ $]".
  Qed.

  Lemma sx_buf_join (a : mword 64) (f : nat -> bv 8) (k : nat) :
    (k < 128)%nat ->
    ([∗ list] j ∈ seq 0 (S k), pa_add a j ↦ₘ f j) -∗
    ([∗ list] j ∈ seq 0 (127 - k)%nat,
       pa_add (pa_add a (S k)) j ↦ₘ f (S k + j)%nat) -∗
    bytes_own (DfracOwn 1) a 128.
  Proof.
    intro Hk. iIntros "H1 H2".
    iDestruct (sx_name_bytes a (S k) f with "H1") as "B1".
    iDestruct (sx_name_bytes (pa_add a (S k)) (127 - k)%nat
                 (fun j => f (S k + j)%nat) with "H2") as "B2".
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
  Context `{!riscvGS Σ, !sieG Σ}.

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
    ((∃ w : mword 64, (pa_stk sp0 3) ↦₈ w) ∗
    ((∃ w : mword 64, (pa_stk sp0 4) ↦₈ w) ∗
    ((∃ w : mword 64, (pa_stk sp0 5) ↦₈ w) ∗
    ((∃ w : mword 64, (pa_stk sp0 6) ↦₈ w) ∗
    ((∃ w : mword 64, (pa_stk sp0 7) ↦₈ w) ∗
    ((∃ w : mword 64, (pa_stk sp0 8) ↦₈ w) ∗
    ((∃ w : mword 64, (pa_stk sp0 9) ↦₈ w) ∗
    ((∃ w : mword 64, (pa_stk sp0 10) ↦₈ w) ∗
    ((∃ w : mword 64, (pa_stk sp0 59) ↦₈ w) ∗
    ((∃ w : mword 64, (pa_stk sp0 60) ↦₈ w) ∗
     bytes_own (DfracOwn 1) (pa_stk sp0 26) 128 ∗
     bytes_own (DfracOwn 1) (pa_stk sp0 58) 256))))))))))%I.

  Lemma sx_rest_join (sp0 v1 v2 : mword 64) :
    sx_alp sp0 -> sx_ala sp0 ->
    (pa_stk sp0 1) ↦₈ v1 -∗ (pa_stk sp0 2) ↦₈ v2 -∗ sx_rest sp0 -∗
    stack_own sp0 60.
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
    sie_cap_gpr M (K - 60) b pj -∗
    kernel_text -∗ pc_is (mword_of_int (SX + 0x104)) -∗
    (pa_stk sp0 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
    (pa_stk sp0 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
    sx_rest sp0 -∗
    wp_next b pj (fun (CIDx : CpuId) =>
      ∀ mf : regfile,
        ⌜callee_saved m mf⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (M !!! Regidx Ra0 : mword 64)⌝ -∗
        sie_cap_gpr mf K b pj -∗
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
                    (Fetchstr : FETCHSTR) (Kexec : KEXEC) (Kfree : KFREE).

(* ===================================================================== *)
(*  +0x000 .. +0x026 -- THE PROLOGUE, argaddr and argstr.                 *)
(*                                                                        *)
(*  Owns the FIRST of the three [-1] exits, and it is the odd one: s1..s7 *)
(*  are not spilled until +0x28, so this path reloads nothing and goes    *)
(*  straight to the epilogue with every callee-saved register still at    *)
(*  its entry value.                                                      *)
(* ===================================================================== *)
Section SysExecHead.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !irefslotG Σ}.
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
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ)
      (b : bool) (lks : gset string) :
    (K_sys_exec <= K)%nat ->
    pv_tf V !! tf_arg_idx 0 = Some v0 ->
    pv_tf V !! tf_arg_idx 1 = Some v1 ->
    locks_below lks "kmem" ->
    sie_cap_gpr m K b (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) C b lks -∗
    kernel_text -∗ kernel_data -∗ pc_is (mword_of_int SX : mword 64) -∗
    proc_priv γf (proc_addr jp) pid V -∗
    kalloc_env γa None -∗
    (* ---- THE -1 EXIT: argstr failed, and nothing has been spilled ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (P' : uptd),
        ⌜callee_saved m mf⌝ -∗
        ⌜uptd_ext (pv_upt V) P'⌝ -∗
        ⌜(mf !!! Regidx Ra0 : mword 64) = (mword_of_int (-1) : mword 64)⌝ -∗
        sie_cap_gpr mf K b (proc_addr jp) -∗
        cpu_own 0 eb (proc_addr jp) C b lks -∗
        pc_is (ret_pc (m !!! Regidx Rra : mword 64)) -∗
        proc_priv γf (proc_addr jp) pid (upd_upt V P') -∗
        WP (Loop : expr riscv_lang)) -∗
    (* ---- THE FALL-THROUGH at +0x028, with the path copied in ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M : regfile) (P' : uptd) (plen : nat) (pfun : nat -> bv 8)
        (rest : nat -> bv 8) (v59 v60 : mword 64),
        ⌜ sx_sp (m !!! Regidx csp_rs1 : mword 64) M /\
          (M !!! Regidx Rs0 : mword 64) = (m !!! Regidx csp_rs1 : mword 64) /\
          sx_thr2 m M ⌝ -∗
        ⌜ uptd_ext (pv_upt V) P' /\ (plen < 128)%nat /\ bb_cstr pfun plen ⌝ -∗
        ⌜ sx_alp (m !!! Regidx csp_rs1 : mword 64) /\
          sx_ala (m !!! Regidx csp_rs1 : mword 64) ⌝ -∗
        pc_is (mword_of_int (SX + 0x28) : mword 64) -∗
        sie_cap_gpr M (K - 60)%nat b (proc_addr jp) -∗
        cpu_own 0 eb (proc_addr jp) C b lks -∗
        proc_priv γf (proc_addr jp) pid (upd_upt V P') -∗
        (* the frame: ra and s0 spilled, s1..s7 and slot 10 still free,
           the path buffer holding its NUL-terminated string, the argv
           array untouched, and the two out-parameter cells *)
        (pa_stk (m !!! Regidx csp_rs1) 1) ↦₈ (m !!! Regidx Rra : mword 64) -∗
        (pa_stk (m !!! Regidx csp_rs1) 2) ↦₈ (m !!! Regidx Rs0 : mword 64) -∗
        (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 3) ↦₈ w) -∗
        (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 4) ↦₈ w) -∗
        (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 5) ↦₈ w) -∗
        (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 6) ↦₈ w) -∗
        (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 7) ↦₈ w) -∗
        (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 8) ↦₈ w) -∗
        (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 9) ↦₈ w) -∗
        (∃ w : mword 64, (pa_stk (m !!! Regidx csp_rs1) 10) ↦₈ w) -∗
        ([∗ list] j ∈ seq 0 (S plen),
           pa_add (pa_stk (m !!! Regidx csp_rs1) 26) j ↦ₘ pfun j) -∗
        ([∗ list] j ∈ seq 0 (127 - plen)%nat,
           pa_add (pa_add (pa_stk (m !!! Regidx csp_rs1) 26) (S plen)) j ↦ₘ rest j) -∗
        bytes_own (DfracOwn 1) (pa_stk (m !!! Regidx csp_rs1) 58) 256 -∗
        (pa_stk (m !!! Regidx csp_rs1) 59) ↦₈ v59 -∗
        (pa_stk (m !!! Regidx csp_rs1) 60) ↦₈ v60 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Harg0 Harg1 Hlb.
    destruct (sx_kb K HK) as (Kkx & Kar & Kaa & Kfa & Kfs & K14 & K2 & K60 & Kpop).
    set (sp0 := m !!! Regidx csp_rs1).
    iIntros "Hcg Hcnt #Htext #Hdata Hpc Hpriv #Hka Hm1 Hout".
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
                     (sign_extend' 64 (mword_of_int 2086150 : mword 21))
                   = mword_of_int KernelSyms.argaddr) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (SX + 0xe)) Rra
              (mword_of_int 2086150 : mword 21) M4 (K - 60)%nat b
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
    iDestruct (proc_priv_tf with "Hpriv") as "(Htfc & Htfp & Hprivback)".
    iEval (rewrite -HM5a1) in "F59".
    iDestruct (cpu_own_transport CID0 CID7 0%nat eb (proc_addr jp) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Argaddr.wp_argaddr_sconf M5 (K - 60)%nat 0%nat eb (proc_addr jp) C
              1%nat (ud_tfp (pv_upt V)) (pv_tf V) v1 u59 (DfracOwn (1/4)) b lks
              sx_arg1_lt ltac:(rewrite HM5a0; reflexivity) Harg1 sx_noff0 Kaa
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
                     (sign_extend' 64 (mword_of_int 2086164 : mword 21))
                   = mword_of_int KernelSyms.argstr) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (SX + 0x1c)) Rra
              (mword_of_int 2086164 : mword 21) M9 (K - 60)%nat b
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
    iDestruct (cpu_own_transport CID8 CID12 0%nat eb (proc_addr jp) C b
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Argstr.wp_argstr_sconf γa γf M10 (K - 60)%nat 0%nat eb
              (proc_addr jp) C 0%nat v0 pid V 128%nat bf b lks
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
      iDestruct (cpu_own_transport CID13 CID16 0%nat eb (proc_addr jp) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hout" $! CID16 with "[%]"); [wp_next_chain |].
      iApply ("Hout" $! M13 P' k bnew (fun j => bnew (S k + j)%nat) v1 u60
              with "[%] [%] [%] Hpc Hcg Hcnt Hpriv F1 F2 F3 F4 F5 F6 F7 F8 F9
                    F10 Hpre Hsuf Hab F59 F60").
      { split_and!; [exact HM13sp | exact HM13s0 | exact HM13thr]. }
      { split_and!; [exact Hext | exact Hklt | exact Hkstr]. }
      { split_and!; [exact Halp | exact Hala]. }
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
                Halp Hala with "Hcg Htext Hpc F1 F2 Hrest [Hcnt Hpriv Hm1]").
      iIntros (CID17) "%Hq17". iIntros (mf) "%Hcsf %Hfa0 Hcg Hpc".
      iDestruct (cpu_own_transport CID13 CID17 0%nat eb (proc_addr jp) C b
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hm1" $! CID17 with "[%]"); [wp_next_chain |].
      iApply ("Hm1" $! mf P' with "[%] [%] [%] Hcg Hcnt Hpc Hpriv").
      { exact Hcsf. }
      { exact Hext. }
      { rewrite Hfa0. exact HM13a0. }
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
  Context `{!riscvGS Σ, !sieG Σ}.
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
    sie_cap_gpr M (K - 60)%nat b pj -∗
    kernel_text -∗ pc_is (mword_of_int (SX + 0x28) : mword 64) -∗
    (∃ w : mword 64, (pa_stk sp0 3) ↦₈ w) -∗
    (∃ w : mword 64, (pa_stk sp0 4) ↦₈ w) -∗
    (∃ w : mword 64, (pa_stk sp0 5) ↦₈ w) -∗
    (∃ w : mword 64, (pa_stk sp0 6) ↦₈ w) -∗
    (∃ w : mword 64, (pa_stk sp0 7) ↦₈ w) -∗
    (∃ w : mword 64, (pa_stk sp0 8) ↦₈ w) -∗
    (∃ w : mword 64, (pa_stk sp0 9) ↦₈ w) -∗
    bytes_own (DfracOwn 1) (pa_stk sp0 58) 256 -∗
    wp_next b pj (fun (CID : CpuId) =>
      ∀ M' : regfile,
        ⌜ sx_sp sp0 M' /\
          (M' !!! Regidx Rs0 : mword 64) = sp0 /\
          (M' !!! Regidx Rs1 : mword 64) = pa_stk sp0 58 /\
          (M' !!! Regidx Rs2 : mword 64) = (mword_of_int 0 : mword 64) /\
          (M' !!! Regidx Rs3 : mword 64) = pa_stk sp0 58 /\
          (M' !!! Regidx Rs4 : mword 64) = pa_stk sp0 58 /\
          (M' !!! Regidx Rs5 : mword 64) = pa_stk sp0 60 /\
          (M' !!! Regidx Rs6 : mword 64) = (mword_of_int 4096 : mword 64) /\
          (M' !!! Regidx Rs7 : mword 64) = (mword_of_int 32 : mword 64) ⌝ -∗
        pc_is (mword_of_int (SX + 0x56) : mword 64) -∗
        sie_cap_gpr M' (K - 60)%nat b pj -∗
        (* the seven spill slots, at the values the epilogue reloads *)
        (pa_stk sp0 3) ↦₈ (m !!! Regidx Rs1 : mword 64) -∗
        (pa_stk sp0 4) ↦₈ (m !!! Regidx Rs2 : mword 64) -∗
        (pa_stk sp0 5) ↦₈ (m !!! Regidx Rs3 : mword 64) -∗
        (pa_stk sp0 6) ↦₈ (m !!! Regidx Rs4 : mword 64) -∗
        (pa_stk sp0 7) ↦₈ (m !!! Regidx Rs5 : mword 64) -∗
        (pa_stk sp0 8) ↦₈ (m !!! Regidx Rs6 : mword 64) -∗
        (pa_stk sp0 9) ↦₈ (m !!! Regidx Rs7 : mword 64) -∗
        (* argv, zeroed, as thirty-two WORDS *)
        ([∗ list] i ∈ seq 0 32,
           (pa_stk sp0 (58 - i)) ↦₈ (mword_of_int 0 : mword 64)) -∗
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
                     (sign_extend' 64 (mword_of_int 2078996 : mword 21))
                   = mword_of_int KernelSyms.memset) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (SX + 0x42)) Rra
              (mword_of_int 2078996 : mword 21) N4 (K - 60)%nat b
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
    iApply (Memset.wp_memset_sconf N5 (K - 60)%nat 256%nat
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
    iSpecialize ("Hout" $! CIDb9 with "[%]"); [wp_next_chain |].
    iApply ("Hout" $! P6 with "[%] Hpc Hcg F3 F4 F5 F6 F7 F8 F9 Hargv").
    { split_and!;
        [ exact HP6sp | exact HP6s0 | exact HP6s1 | exact HP6s2 | exact HP6s3
        | exact HP6s4 | exact HP6s5 | exact HP6s6 | exact HP6s7 ]. }
  Qed.


End SysExecSetup.

End SysExecProof.
