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
