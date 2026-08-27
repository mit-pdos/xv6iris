(* ProofKexecTail.v -- the part of kexec's phase A that phase B ALSO needs:
   the frame/seam algebra over kexec's 68-slot frame, and the two blocks at
   the bottom of the function that more than one phase branches into.

   ---- THIS FILE EXISTS FOR THE BUILD GRAPH, NOT FOR THE PROOF -----------

   Every line below was in ProofKexecA.v, and ProofKexecB.v reached it by
   requiring that file outright.  Nothing requires either proof file in turn
   -- they are both leaves -- so that edge bought nothing and cost the one
   thing a leaf can still cost: it put A and B IN SERIES on the build's
   critical path, when they have no proof-level reason to be.

   What B actually consumed from A was:

     * six pieces of top-level frame/seam vocabulary -- [kxc_frameA6] and its
       weakening, [kxc_mid_split] / [kxc_mid_join], [kxc_elf_slots_of_stack] /
       [kxc_stack_of_elf_slots], and [kxc_sie_b_agree] -- not one of which
       mentions a functor argument, or indeed anything about phase A; and

     * ONE lemma from inside the functor: [kxc_bad64], the short-read /
       bad-magic tail at +0x064.  B's own [bad:] tail at +0x31c restores s6
       and jumps to +0x064, i.e. it lands in the middle of a block phase A had
       already proved.  That single [iApply] is the whole reason [KexecBProof]
       had to take all seven of phase A's functor arguments.

   So the split is along the line the proof already drew.  The functor here is
   [KexecTailProof]; phase A opens it as [T] and phase B as [A], and each names
   the same seven modules it named before.  [kxc_bad64] drags in with it
   [kxc_exit_m1] (the [-1] return it ends on) and the three single-slot icache
   accessors [kxa_esc_acc] / [kxa_bs3_split] / [kxa_bs3_join]
   that it and phase A's body share -- those are the only other residents of
   the functor part, and phase A reaches them as [T.kxa_*] now.

   NOTHING BELOW CHANGED except the two module names and the [T.] qualifier on
   phase A's nine call sites; the statements, the proofs and the section
   structure are the originals.  In particular [Section KexecAExit] is still a
   separate section from [Section KexecABad], and both are separate from phase
   A's body: [kxc_exit_m1] and [kxc_bad64] are each applied at the hart their
   caller's [c.j] resumed on, and a sibling lemma in the SAME section would
   resolve its [CpuId] through the section variable by name.  The reason is
   recorded in full above [Section KexecABody] in ProofKexecA.v, where the
   applications are.  It is a constraint on the section, not on the file, so
   do not collapse these two sections into one on the grounds that the file
   boundary now separates them from their callers.

   Read ProofKexecA.v's header for the frame map, the register conventions and
   the reasoning about the buffers; it is still the entry point for this
   proof.  claude-notes/projects/kexec.md is the worklist. *)

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
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import HartTp.
Require Import WpNext.
Require Import WpMmodeLeafBase.
Require Import RiscvExtras.
Require Import StackOwn.
Require Import StackBytes.
Require Import CalleeSaved.
Require Import KernelRvcDecode.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpSconfAlu WpSconfMem WpSconfCtl.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SleepLock.   (* [is_sleeplock]: the nightly dead-import sweep re-pointed the chain that used to carry it *)
Require Import WpLock.
Require Import KernelDataInv.
Require Import SpecPanic.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import FsCrash.
Require Import InodeRegion.
Require Import IcacheEscrow.
Require Import ByteBuf.
Require Import ElfEnc.
Require Import ProcGeom.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KallocInv.
Require Import KvmSpec.
Require Import ProcInv.
(* Names the nightly dead-import sweep stopped delivering transitively. *)
Require Import DinodeEnc.
Require Import InodeLock.
Require Import SchedCtx.
Require Import DiskInv.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import UmCovered.
Require Import FileInvDefs.
Require Import SpecIput.
Require Import SpecKexec.
Require Import KexecOkQ.
Require Import SpecMyproc.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecReadi.
Require Import SpecIunlockput.
Require Import SpecNamei.
Require Import SpecNameiTr.   (* [inode_held_at]: the +0x032 seam's inum *)
Require Import SpecProcFreepagetable.
Require Import ProofKexecParts.
Require Import CodeKexec.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import FsCfg.   (* [fscfg]: the fs configuration is AMBIENT *)
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KXA := KernelSyms.kexec (only parsing).

(* ===================================================================== *)
(*  THE MAGIC WORD.                                                       *)
(* ===================================================================== *)
(* [lui a5,0x464c4 ; addi a5,a5,1407] builds [ELF_MAGIC] in a5, and the
   [beq] at +0x060 compares it against the SIGN-EXTENDED word the [lw] at
   +0x054 delivered.  0x464C457F has bit 31 clear, so the sign extension is
   the identity and the register comparison IS [eh_magic_ok].  Stated at the
   Z tier so the [beq]'s [eq_vec] side condition is one [vm_compute] over a
   closed term once the field's value is known. *)
Lemma kxc_magic_word :
  add_vec (luival (mword_of_int 287940 : mword 20))
          (sign_extend' 64 (mword_of_int 1407 : mword 12))
  = (mword_of_int ELF_MAGIC : mword 64).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  THE FRAME ALGEBRA phase A needs on top of ProofKexecParts'.           *)
(* ===================================================================== *)

(* A [stack_own] chunk based at slot [j], enumerated by ABSOLUTE slot index
   and ASCENDING -- [StackOwn.stack_own_slots] with [pa_stk_assoc] folded
   in.  This is the one bridge between the epilogue's currency
   ([stack_own]) and the carves' ([∗ list] over slot indices), and it is an
   [⊣⊢], so both directions of every regrouping below are one rewrite. *)
Section KexecAFrame.
  Context `{!riscvGS Σ, FSC : fscfg}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma kxc_slots_asc (sp0 : mword 64) (n j : nat) :
    stack_own (KTR := KT1) (pa_stk sp0 j) n ⊣⊢
    ([∗ list] i ∈ seq 1 n,
       ∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 (j + i)) (DfracOwn 1) w)%I.
  Proof.
    rewrite (stack_own_slots (KTR := KT1)).
    apply big_sepL_proper. intros k i _.
    by rewrite pa_stk_assoc.
  Qed.

  (* the eight elf slots, in the DESCENDING order [kxc_slots_elf] wants.
     Eight conjuncts, so the reordering is eight lines rather than a
     permutation lemma over [big_sepL] (whose [Φ] would have to be given
     explicitly -- durable-notes' big-op rule). *)
  Lemma kxc_elf_slots_of_stack (sp0 : mword 64) :
    stack_own (KTR := KT1) (pa_stk sp0 46) 8 ⊢
    [∗ list] i ∈ seq 0 8, ∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 (54 - i)) (DfracOwn 1) w.
  Proof.
    rewrite (kxc_slots_asc sp0 8 46). cbn [seq big_opL].
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _)".
    cbn [Nat.add Nat.sub].
    iFrame "H8 H7 H6 H5 H4 H3 H2 H1".
  Qed.

  Lemma kxc_stack_of_elf_slots (sp0 : mword 64) :
    ([∗ list] i ∈ seq 0 8, ∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 (54 - i)) (DfracOwn 1) w)
    ⊢ stack_own (KTR := KT1) (pa_stk sp0 46) 8.
  Proof.
    rewrite (kxc_slots_asc sp0 8 46). cbn [seq big_opL Nat.add Nat.sub].
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _)".
    iFrame "H8 H7 H6 H5 H4 H3 H2 H1".
  Qed.

  (* ---- the five top slots (64..68), individually ---- *)
  Lemma kxc_top5_of_stack (sp0 : mword 64) :
    stack_own (KTR := KT1) (pa_stk sp0 63) 5 ⊢
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 64) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 65) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 66) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 67) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 68) (DfracOwn 1) w).
  Proof.
    rewrite (kxc_slots_asc sp0 5 63). cbn [seq big_opL Nat.add].
    iIntros "(H1 & H2 & H3 & H4 & H5 & _)". iFrame.
  Qed.

  Lemma kxc_stack_of_top5 (sp0 : mword 64) (w64 w65 w66 w67 w68 : mword 64) :
    word_pointsto (KTR := KT1) (pa_stk sp0 64) (DfracOwn 1) w64 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 65) (DfracOwn 1) w65 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 66) (DfracOwn 1) w66 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 67) (DfracOwn 1) w67 -∗
    word_pointsto (KTR := KT1) (pa_stk sp0 68) (DfracOwn 1) w68 -∗
    stack_own (KTR := KT1) (pa_stk sp0 63) 5.
  Proof.
    iIntros "H1 H2 H3 H4 H5".
    rewrite (kxc_slots_asc sp0 5 63). cbn [seq big_opL Nat.add].
    iSplitL "H1"; [by iExists w64 |].
    iSplitL "H2"; [by iExists w65 |].
    iSplitL "H3"; [by iExists w66 |].
    iSplitL "H4"; [by iExists w67 |].
    iSplitL "H5"; [by iExists w68 |]. done.
  Qed.

  (* ---- slots 1..13, individually: the prologue's four plus the nine
         lazily-spilled ones [ProofKexecParts.kxc_frame] takes existentially ---- *)
  Lemma kxc_slots13_of_stack (sp0 : mword 64) :
    stack_own (KTR := KT1) sp0 13 ⊢
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 12) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (KTR := KT1) (pa_stk sp0 13) (DfracOwn 1) w).
  Proof.
    rewrite (stack_own_slots (KTR := KT1)). cbn [seq big_opL].
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12
              & H13 & _)".
    (* A bare [iFrame] here still pays a GOAL-side search over this
       13-conjunct existential tuple (optimization.md #3): 4.5 s for what an
       explicit, positionally-matched split does for free, because each
       hypothesis is already exactly one conjunct's witness -- [iExact] does
       not need to find that out by trying the rest. *)
    iSplitL "H1"; [iExact "H1" |].
    iSplitL "H2"; [iExact "H2" |].
    iSplitL "H3"; [iExact "H3" |].
    iSplitL "H4"; [iExact "H4" |].
    iSplitL "H5"; [iExact "H5" |].
    iSplitL "H6"; [iExact "H6" |].
    iSplitL "H7"; [iExact "H7" |].
    iSplitL "H8"; [iExact "H8" |].
    iSplitL "H9"; [iExact "H9" |].
    iSplitL "H10"; [iExact "H10" |].
    iSplitL "H11"; [iExact "H11" |].
    iSplitL "H12"; [iExact "H12" | iExact "H13"].
  Qed.

  (* ---- 496(sp) is slot 6, at the c.sdsp / c.ldsp encoding.  Used twice:
         +0x032 spills s4 there and +0x070 reloads it. ---- *)
  Lemma kxc_slot6_sp (X : mword 64) :
    add_vec (pa_stk X 68)
      (zero_extend' 64 (concat_vec (mword_of_int 62 : mword 6) ('b"000")))
    = pa_stk X 6.
  Proof.
    change 68%nat with (6 + 62)%nat.
    rewrite -(pa_stk_assoc X 6 62).
    apply stk_pop. apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* ---- THE OTHER EIGHT LAZILY-SPILLED SLOTS, same template as
     [kxc_slot6_sp] -- phase C's shared [-1] tail (+0x1d6) reloads all nine
     of s3..s11 from their spill slots in one run (+0x1e0 .. +0x1f0), unlike
     [kxc_bad64] which only ever reloads slot 6 on its own. ---- *)
  Lemma kxc_slot5_sp (X : mword 64) :
    add_vec (pa_stk X 68)
      (zero_extend' 64 (concat_vec (mword_of_int 63 : mword 6) ('b"000")))
    = pa_stk X 5.
  Proof.
    change 68%nat with (5 + 63)%nat.
    rewrite -(pa_stk_assoc X 5 63).
    apply stk_pop. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma kxc_slot7_sp (X : mword 64) :
    add_vec (pa_stk X 68)
      (zero_extend' 64 (concat_vec (mword_of_int 61 : mword 6) ('b"000")))
    = pa_stk X 7.
  Proof.
    change 68%nat with (7 + 61)%nat.
    rewrite -(pa_stk_assoc X 7 61).
    apply stk_pop. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma kxc_slot8_sp (X : mword 64) :
    add_vec (pa_stk X 68)
      (zero_extend' 64 (concat_vec (mword_of_int 60 : mword 6) ('b"000")))
    = pa_stk X 8.
  Proof.
    change 68%nat with (8 + 60)%nat.
    rewrite -(pa_stk_assoc X 8 60).
    apply stk_pop. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma kxc_slot9_sp (X : mword 64) :
    add_vec (pa_stk X 68)
      (zero_extend' 64 (concat_vec (mword_of_int 59 : mword 6) ('b"000")))
    = pa_stk X 9.
  Proof.
    change 68%nat with (9 + 59)%nat.
    rewrite -(pa_stk_assoc X 9 59).
    apply stk_pop. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma kxc_slot10_sp (X : mword 64) :
    add_vec (pa_stk X 68)
      (zero_extend' 64 (concat_vec (mword_of_int 58 : mword 6) ('b"000")))
    = pa_stk X 10.
  Proof.
    change 68%nat with (10 + 58)%nat.
    rewrite -(pa_stk_assoc X 10 58).
    apply stk_pop. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma kxc_slot11_sp (X : mword 64) :
    add_vec (pa_stk X 68)
      (zero_extend' 64 (concat_vec (mword_of_int 57 : mword 6) ('b"000")))
    = pa_stk X 11.
  Proof.
    change 68%nat with (11 + 57)%nat.
    rewrite -(pa_stk_assoc X 11 57).
    apply stk_pop. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma kxc_slot12_sp (X : mword 64) :
    add_vec (pa_stk X 68)
      (zero_extend' 64 (concat_vec (mword_of_int 56 : mword 6) ('b"000")))
    = pa_stk X 12.
  Proof.
    change 68%nat with (12 + 56)%nat.
    rewrite -(pa_stk_assoc X 12 56).
    apply stk_pop. apply bv_eq; vm_compute; reflexivity.
  Qed.

  Lemma kxc_slot13_sp (X : mword 64) :
    add_vec (pa_stk X 68)
      (zero_extend' 64 (concat_vec (mword_of_int 55 : mword 6) ('b"000")))
    = pa_stk X 13.
  Proof.
    change 68%nat with (13 + 55)%nat.
    rewrite -(pa_stk_assoc X 13 55).
    apply stk_pop. apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* ---- THE ELF BUFFER, borrowed as 64 NAMED bytes and given back. ----

     ONE accessor rather than two lemmas, for [ByteBuf.bb_word_acc]'s
     reason: the per-slot 8-alignment facts are what the rebuild needs and a
     byte run no longer carries them, so they have to be captured BEFORE the
     split.  readi's destination is the named form, hence the [∃ f]. *)
  Lemma kxc_elf_acc (sp0 : mword 64) :
    stack_own (KTR := KT1) (pa_stk sp0 46) 8 ⊢
    (∃ f : nat -> bv 8,
       [∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ[KT1] f j) ∗
    (∀ g : nat -> bv 8,
       ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ[KT1] g j) -∗
       stack_own (KTR := KT1) (pa_stk sp0 46) 8).
  Proof.
    iIntros "H".
    iDestruct (kxc_elf_slots_of_stack with "H") as "H".
    iDestruct (kxc_slots_elf sp0 with "H") as "[%Hal Hb]".
    iSplitL "Hb".
    - iApply (bb_any_named (KTR := KT1) (pa_stk sp0 54) 64). rewrite /bytes_own /byte_any.
      iExact "Hb".
    - iIntros (g) "Hg".
      iApply kxc_stack_of_elf_slots.
      iApply (kxc_bytes_elf sp0 Hal).
      rewrite /bytes_own. iApply (bb_named_any (KTR := KT1) with "Hg").
  Qed.

  (* ---- the first four bytes of a named run ARE the 4-byte cell the [lw]
         at +0x054 reads, and giving the cell back gives the bytes back.
         [ElfEnc.le_at_nth_byte] at m := 32 is the whole content; the
         alignment comes off the elf buffer's own slot (slot 54). ---- *)
  Lemma kxc_seq_split_4 (N : nat) : (4 <= N)%nat -> seq 0 N = seq 0 4 ++ seq 4 (N - 4).
  Proof.
    intro H. rewrite -(seq_app 4 (N - 4) 0). f_equal. lia.
  Qed.

  Lemma kxc_word4_of_named (a : Arch.pa) (g : nat -> bv 8) :
    is_aligned_paddr (Physaddr a) 4 = true ->
    ([∗ list] j ∈ seq 0 4, pa_add a j ↦ₘ[KT1] g j) ⊢
    word4_pointsto (KTR := KT1) a (DfracOwn 1) (Z_to_bv 32 (le_at g 0 4)).
  Proof.
    intro Hal. iIntros "H".
    iApply (word4_pointsto_intro (KTR := KT1) a (DfracOwn 1) _ Hal).
    iApply (big_sepL_impl with "H"). iIntros "!>" (i j Hij) "Hb".
    assert (Hj : (j < 4)%nat).
    { apply lookup_seq in Hij. lia. }
    rewrite (le_at_nth_byte 32 g 0 4 j ltac:(lia) Hj).
    cbn [Nat.add]. iExact "Hb".
  Qed.

  Lemma kxc_named_of_word4 (a : Arch.pa) (g : nat -> bv 8) :
    word4_pointsto (KTR := KT1) a (DfracOwn 1) (Z_to_bv 32 (le_at g 0 4)) ⊢
    [∗ list] j ∈ seq 0 4, pa_add a j ↦ₘ[KT1] g j.
  Proof.
    rewrite (word4_pointsto_unfold (KTR := KT1)). iIntros "[_ H]".
    iApply (big_sepL_impl with "H"). iIntros "!>" (i j Hij) "Hb".
    assert (Hj : (j < 4)%nat).
    { apply lookup_seq in Hij. lia. }
    assert (Hw : (8 * Z.of_nat 4 <= Z.of_N 32)%Z) by lia.
    iEval (rewrite (le_at_nth_byte 32 g 0 4 j Hw Hj); cbn [Nat.add]) in "Hb".
    iExact "Hb".
  Qed.

  (* ---- the 50-slot middle (14..63) as ustack | elf | ph+2 ---- *)
  Lemma kxc_mid_split (sp0 : mword 64) :
    stack_own (KTR := KT1) (pa_stk sp0 13) 50 ⊢
    stack_own (KTR := KT1) (pa_stk sp0 13) 33 ∗ stack_own (KTR := KT1) (pa_stk sp0 46) 8 ∗
    stack_own (KTR := KT1) (pa_stk sp0 54) 9.
  Proof.
    iIntros "H".
    iEval (change 50%nat with (33 + 17)%nat;
           rewrite (stack_own_app (KTR := KT1)) (pa_stk_assoc sp0 13 33)) in "H".
    iDestruct "H" as "[$ H]".
    iEval (change 17%nat with (8 + 9)%nat;
           rewrite (stack_own_app (KTR := KT1)) (pa_stk_assoc sp0 46 8)) in "H".
    iDestruct "H" as "[$ $]".
  Qed.

  Lemma kxc_mid_join (sp0 : mword 64) :
    stack_own (KTR := KT1) (pa_stk sp0 13) 33 -∗ stack_own (KTR := KT1) (pa_stk sp0 46) 8 -∗
    stack_own (KTR := KT1) (pa_stk sp0 54) 9 -∗ stack_own (KTR := KT1) (pa_stk sp0 13) 50.
  Proof.
    iIntros "A B C".
    iEval (change 50%nat with (33 + 17)%nat;
           rewrite (stack_own_app (KTR := KT1)) (pa_stk_assoc sp0 13 33)).
    iSplitL "A"; [iExact "A" |].
    iEval (change 17%nat with (8 + 9)%nat;
           rewrite (stack_own_app (KTR := KT1)) (pa_stk_assoc sp0 46 8)).
    iSplitL "B"; [iExact "B" | iExact "C"].
  Qed.

  (* the named run splits at 4 and rejoins -- stated as ENTAILMENTS, not as a
     [rewrite] on [seq 0 64]: inside the proofmode that rewrite has to match a
     [seq] under a [big_opL] and does not. *)
  Lemma kxc_named_split4 (a : Arch.pa) (g : nat -> bv 8) (N : nat) :
    (4 <= N)%nat ->
    ([∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] g j) ⊢
    ([∗ list] j ∈ seq 0 4, pa_add a j ↦ₘ[KT1] g j) ∗
    ([∗ list] j ∈ seq 4 (N - 4), pa_add a j ↦ₘ[KT1] g j).
  Proof.
    intro H. rewrite (kxc_seq_split_4 N H) big_sepL_app. iIntros "[$ $]".
  Qed.

  Lemma kxc_named_join4 (a : Arch.pa) (g : nat -> bv 8) (N : nat) :
    (4 <= N)%nat ->
    ([∗ list] j ∈ seq 0 4, pa_add a j ↦ₘ[KT1] g j) -∗
    ([∗ list] j ∈ seq 4 (N - 4), pa_add a j ↦ₘ[KT1] g j) -∗
    ([∗ list] j ∈ seq 0 N, pa_add a j ↦ₘ[KT1] g j).
  Proof.
    intro H. iIntros "A B".
    rewrite (kxc_seq_split_4 N H) big_sepL_app. iSplitL "A"; [iExact "A" | iExact "B"].
  Qed.

End KexecAFrame.

(* ===================================================================== *)
(*  The two s0-RELATIVE spill addresses phase A writes.                   *)
(*  [sd rs,-N(s0)] is [add_vec s0 (sign_extend' 64 (mword_of_int          *)
(*  (4096-N) : mword 12))], and [s0] is [sp0], so the slot is [N/8].       *)
(* ===================================================================== *)
Lemma kxc_path_slot (X : mword 64) :     (* sd a0,-528(s0) : path -> slot 66 *)
  add_vec X (sign_extend' 64 (mword_of_int 3568 : mword 12)) = pa_stk X 66.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kxc_argv_slot (X : mword 64) :     (* sd a1,-512(s0) : argv -> slot 64 *)
  add_vec X (sign_extend' 64 (mword_of_int 3584 : mword 12)) = pa_stk X 64.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* [addi s0,sp,544] undoes the prologue's push, at the c.addi4spn encoding. *)
Lemma kxc_s0_of_sp (X : mword 64) :
  add_vec (pa_stk X 68)
    (sign_extend' 64 (caddi4spn_imm (mword_of_int 136 : mword 8))) = X.
Proof. apply stk_pop. apply bv_eq; vm_compute; reflexivity. Qed.

Section KexecA.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, FSC : fscfg}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).

  Local Ltac regne := reg_ne_side.

  (* =================================================================== *)
  (*  THE FRAME AS PHASE A PRESENTS IT.                                   *)
  (*                                                                      *)
  (*  [ProofKexecParts.kxc_frame] with the five TOP slots (64..68) pulled  *)
  (*  out, because two of them are pinned: slot 66 holds the spilled path  *)
  (*  and slot 64 the spilled argv, and every later phase reads them       *)
  (*  ([ld ...,-528(s0)] / [ld ...,-512(s0)]).  Slots 14..63 -- the three  *)
  (*  buffers, [off], and one unused word -- stay as ONE [stack_own]       *)
  (*  chunk; see the file header for why that, and not the three carves,   *)
  (*  is the right currency at a block seam.                              *)
  (* =================================================================== *)
  Definition kxc_frameA (sp0 ra0 s00 s10 s20 pv av : mword 64) : iProp Σ :=
    (word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) s10 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) s20 ∗
     (∃ w5, word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5) ∗
     (∃ w6, word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6) ∗
     (∃ w7, word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) w7) ∗
     (∃ w8, word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) w8) ∗
     (∃ w9, word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) w9) ∗
     (∃ w10, word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) w10) ∗
     (∃ w11, word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) w11) ∗
     (∃ w12, word_pointsto (KTR := KT1) (pa_stk sp0 12) (DfracOwn 1) w12) ∗
     (∃ w13, word_pointsto (KTR := KT1) (pa_stk sp0 13) (DfracOwn 1) w13) ∗
     stack_own (KTR := KT1) (pa_stk sp0 13) 50 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 64) (DfracOwn 1) av ∗
     (∃ w65, word_pointsto (KTR := KT1) (pa_stk sp0 65) (DfracOwn 1) w65) ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 66) (DfracOwn 1) pv ∗
     (∃ w67, word_pointsto (KTR := KT1) (pa_stk sp0 67) (DfracOwn 1) w67) ∗
     (∃ w68, word_pointsto (KTR := KT1) (pa_stk sp0 68) (DfracOwn 1) w68))%I.

  (* ... and the SAME frame with slot 6 PINNED.  s4 is spilled there at
     +0x032 and reloaded at +0x070 / +0x0d0 / ..., so from the +0x032 seam
     onward every block has to know WHICH value it will get back --
     [ProofKexecParts.kxc_frame_at]'s reason, at the one slot phase A
     writes. *)
  Definition kxc_frameA6 (sp0 ra0 s00 s10 s20 pv av w6 : mword 64) : iProp Σ :=
    (word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) s10 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) s20 ∗
     (∃ w5, word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5) ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6 ∗
     (∃ w7, word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) w7) ∗
     (∃ w8, word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) w8) ∗
     (∃ w9, word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) w9) ∗
     (∃ w10, word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) w10) ∗
     (∃ w11, word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) w11) ∗
     (∃ w12, word_pointsto (KTR := KT1) (pa_stk sp0 12) (DfracOwn 1) w12) ∗
     (∃ w13, word_pointsto (KTR := KT1) (pa_stk sp0 13) (DfracOwn 1) w13) ∗
     stack_own (KTR := KT1) (pa_stk sp0 13) 50 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 64) (DfracOwn 1) av ∗
     (∃ w65, word_pointsto (KTR := KT1) (pa_stk sp0 65) (DfracOwn 1) w65) ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 66) (DfracOwn 1) pv ∗
     (∃ w67, word_pointsto (KTR := KT1) (pa_stk sp0 67) (DfracOwn 1) w67) ∗
     (∃ w68, word_pointsto (KTR := KT1) (pa_stk sp0 68) (DfracOwn 1) w68))%I.

  Lemma kxc_frameA6_weaken (sp0 ra0 s00 s10 s20 pv av w6 : mword 64) :
    kxc_frameA6 sp0 ra0 s00 s10 s20 pv av w6 -∗
    kxc_frameA sp0 ra0 s00 s10 s20 pv av.
  Proof.
    rewrite /kxc_frameA6 /kxc_frameA.
    iIntros "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 &
              A13 & Arest & A64 & A65 & A66 & A67 & A68)".
    iFrame "A1 A2 A3 A4 A5 A7 A8 A9 A10 A11 A12 A13 Arest A64 A65 A66 A67 A68".
    by iExists w6.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  ...AND THE SAME FRAME WITH THE ELF BUFFER NAMED (N-5.2B).           *)
  (*                                                                      *)
  (*  [kxc_frameA6] hands slots 14..63 across the +0x090 seam as ONE       *)
  (*  [stack_own] chunk, which FORGETS what readi just wrote into          *)
  (*  [struct elfhdr elf] -- phase A's own header says so ("the buffer's   *)
  (*  contents are existential at every seam anyway"), and phase B then    *)
  (*  re-carves the same eight slots and names them itself.  That is       *)
  (*  exactly one byte-run too many for a client that wants to say WHICH   *)
  (*  header the walk read, so this variant carves them ONCE, in phase A,  *)
  (*  and carries the name across.  Nothing else moves: the two halves     *)
  (*  around it are [kxc_mid_split]'s own, and the alignment facts a byte  *)
  (*  run cannot carry ride as a pure conjunct (the same data              *)
  (*  [ProofKexecSeam.kxc_elf_take] used to produce).                      *)
  (*                                                                      *)
  (*  [kxc_frameA6x_fold] is the way back, and it is what phase A's own    *)
  (*  [bad:] tail takes: [T.kxc_bad64] wants the landed frame.             *)
  (* ------------------------------------------------------------------ *)
  Definition kxc_frameA6x (sp0 ra0 s00 s10 s20 pv av w6 : mword 64)
      (ef : nat -> bv 8) : iProp Σ :=
    (⌜forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true⌝ ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 2) (DfracOwn 1) s00 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 3) (DfracOwn 1) s10 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 4) (DfracOwn 1) s20 ∗
     (∃ w5, word_pointsto (KTR := KT1) (pa_stk sp0 5) (DfracOwn 1) w5) ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 6) (DfracOwn 1) w6 ∗
     (∃ w7, word_pointsto (KTR := KT1) (pa_stk sp0 7) (DfracOwn 1) w7) ∗
     (∃ w8, word_pointsto (KTR := KT1) (pa_stk sp0 8) (DfracOwn 1) w8) ∗
     (∃ w9, word_pointsto (KTR := KT1) (pa_stk sp0 9) (DfracOwn 1) w9) ∗
     (∃ w10, word_pointsto (KTR := KT1) (pa_stk sp0 10) (DfracOwn 1) w10) ∗
     (∃ w11, word_pointsto (KTR := KT1) (pa_stk sp0 11) (DfracOwn 1) w11) ∗
     (∃ w12, word_pointsto (KTR := KT1) (pa_stk sp0 12) (DfracOwn 1) w12) ∗
     (∃ w13, word_pointsto (KTR := KT1) (pa_stk sp0 13) (DfracOwn 1) w13) ∗
     stack_own (KTR := KT1) (pa_stk sp0 13) 33 ∗
     ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ[KT1] ef j) ∗
     stack_own (KTR := KT1) (pa_stk sp0 54) 9 ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 64) (DfracOwn 1) av ∗
     (∃ w65, word_pointsto (KTR := KT1) (pa_stk sp0 65) (DfracOwn 1) w65) ∗
     word_pointsto (KTR := KT1) (pa_stk sp0 66) (DfracOwn 1) pv ∗
     (∃ w67, word_pointsto (KTR := KT1) (pa_stk sp0 67) (DfracOwn 1) w67) ∗
     (∃ w68, word_pointsto (KTR := KT1) (pa_stk sp0 68) (DfracOwn 1) w68))%I.

  Lemma kxc_frameA6x_fold (sp0 ra0 s00 s10 s20 pv av w6 : mword 64)
      (ef : nat -> bv 8) :
    kxc_frameA6x sp0 ra0 s00 s10 s20 pv av w6 ef -∗
    kxc_frameA6 sp0 ra0 s00 s10 s20 pv av w6.
  Proof.
    rewrite /kxc_frameA6x /kxc_frameA6.
    iIntros "(%Hal & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 &
              A12 & A13 & Aust & Aelf & Aph & A64 & A65 & A66 & A67 & A68)".
    iAssert (stack_own (KTR := KT1) (pa_stk sp0 46) 8) with "[Aelf]" as "Aelf".
    { iApply kxc_stack_of_elf_slots. iApply (kxc_bytes_elf sp0 Hal).
      rewrite /bytes_own. iApply (bb_named_any with "Aelf"). }
    iDestruct (kxc_mid_join sp0 with "Aust Aelf Aph") as "Amid".
    iFrame "A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 Amid A64 A65 A66 A67 A68".
  Qed.

  (* THE EXIT MOVE: phase A's frame is [ProofKexecParts.kxc_frame], which is
     what [kxc_epi_frame] consumes.  The five top slots go back into the
     [stack_own] chunk ([50 + 5 = 55]) and the two pinned ones lose their
     values -- the epilogue reads none of slots 14..68. *)
  Lemma kxc_frameA_epi (sp0 ra0 s00 s10 s20 pv av : mword 64) :
    kxc_frameA sp0 ra0 s00 s10 s20 pv av -∗
    kxc_frame sp0 ra0 s00 s10 s20.
  Proof.
    rewrite /kxc_frameA /kxc_frame.
    iIntros "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 &
              A13 & Arest & A64 & (%w65 & A65) & A66 & (%w67 & A67) &
              (%w68 & A68))".
    iFrame "A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13".
    iDestruct (kxc_stack_of_top5 sp0 av w65 pv w67 w68
                 with "A64 A65 A66 A67 A68") as "Atop".
    change 55%nat with (50 + 5)%nat.
    rewrite (stack_own_app (KTR := KT1)) (pa_stk_assoc sp0 13 50).
    iFrame "Arest Atop".
  Qed.

  (* =================================================================== *)
  (*  [b] IS [true].                                                      *)
  (*  ProofFileclose's [sie_b_agree] verbatim (itself ProofFiledup's): the *)
  (*  SIE eighth inside [sie_cap_gpr] and the [cpu_hart] cells inside      *)
  (*  [cpu_own] are two presentations of the same bit.  kexec enters at    *)
  (*  [n = 0] with [eb = true], so this pins [b := true] and every parking *)
  (*  callee below chains at the literal [true].                          *)
  (* =================================================================== *)
  Lemma kxc_sie_b_agree (m : regfile) (n K0 : nat) (eb b : bool)
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

  (* =================================================================== *)
  (*  +0x000 .. +0x01c -- THE PROLOGUE.  (statement below)                *)
  (*                                                                      *)
  (*  Nine instructions, no call, no branch: push 544, spill ra/s0/s1/s2   *)
  (*  into slots 1..4, set the frame pointer, keep the path in s2, and     *)
  (*  spill both arguments to slots 66 and 64.  Its output is exactly      *)
  (*  [kxc_frameA] plus the register facts the rest of phase A reads.      *)
  (* =================================================================== *)
  Lemma kxc_prologue (m : regfile) (K : nat) (b : bool) (p : mword 64)
      (sp0 ra0 s00 s10 s20 pv av : mword 64) :
    (68 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Ra0 = pv ->
    m !!! Regidx Ra1 = av ->
    sie_cap_gpr KT1 m K b p -∗
    kernel_text -∗
    pc_is (mword_of_int KXA : mword 64) -∗
    wp_next b p (fun (CID : CpuId) =>
      ∀ M : regfile,
        ⌜ M !!! Regidx csp_rs1 = pa_stk sp0 68 /\
          M !!! Regidx Rs0 = sp0 /\
          M !!! Regidx Rs2 = pv /\
          M !!! Regidx Ra0 = pv /\
          M !!! Regidx Ra1 = av /\
          (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
             r <> Rs0 -> r <> Rs2 -> M !!! Regidx r = m !!! Regidx r) ⌝ -∗
        sie_cap_gpr KT1 M (K - 68)%nat b p -∗
        pc_is (mword_of_int (KXA + 0x020) : mword 64) -∗
        kxc_frameA sp0 ra0 s00 s10 s20 pv av -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hra Hs0 Hs1 Hs2 Ha0 Ha1.
    iIntros "Hcg #Htext Hpc Hcont".
    (* ---- +0x000: addi sp,sp,-544 (BASE-encoded) ---- *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (mword_of_int 3552 : mword 12))
                    = pa_stk (m !!! Regidx csp_rs1) 68)
      by apply kxc_push_544.
    iApply (wp_addi_sp_push4_s_sconf (mword_of_int KXA)
              (mword_of_int 3552 : mword 12) m K 68 b HK Hpush
              with "Hcg Hpc []").
    { iApply (kxc_000 with "Htext"). }
    iIntros (CID1 Hs1c) "Hcg Hframe Hpc".
    set (T1 := <[Regidx csp_rs1 := regval_into_reg
                  (add_vec (m !!! Regidx csp_rs1)
                     (sign_extend' 64 (mword_of_int 3552 : mword 12)))]> m).
    change (<[Regidx csp_rs1 := regval_into_reg
              (add_vec (m !!! Regidx csp_rs1)
                 (sign_extend' 64 (mword_of_int 3552 : mword 12)))]> m) with T1.
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T1 upd_eq Hpush Hsp; reflexivity).
    iEval (rewrite Hsp) in "Hframe".
    assert (Hp004 : add_vec_int (mword_of_int KXA : mword 64) 4
                    = mword_of_int (KXA + 0x004)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp004) in "Hpc".
    (* ---- peel the 68-slot frame: slots 1..13, 14..63, 64..68 ---- *)
    change 68%nat with (13 + 55)%nat.
    rewrite (stack_own_app (KTR := KT1)).
    iDestruct "Hframe" as "[Hf13 Hf55]".
    iDestruct (kxc_slots13_of_stack sp0 with "Hf13")
      as "((%v1 & Hb1) & (%v2 & Hb2) & (%v3 & Hb3) & (%v4 & Hb4) & Hb5 & Hb6 &
           Hb7 & Hb8 & Hb9 & Hb10 & Hb11 & Hb12 & Hb13)".
    iEval (change 55%nat with (50 + 5)%nat;
           rewrite (stack_own_app (KTR := KT1)) (pa_stk_assoc sp0 13 50)) in "Hf55".
    iDestruct "Hf55" as "[Hmid Htop]".
    iDestruct (kxc_top5_of_stack sp0 with "Htop")
      as "((%v64 & Hb64) & Hb65 & (%v66 & Hb66) & Hb67 & Hb68)".
    (* ---- +0x004: sd ra,536(sp) -> slot 1 ---- *)
    assert (Hpa1 : add_vec (rget T1 csp_rs1)
                     (sign_extend' 64 (mword_of_int 536 : mword 12))
                   = pa_stk sp0 1).
    { rewrite (rget_ne T1 csp_rs1 ltac:(vm_compute; discriminate)) HT1sp.
      apply kxc_frm1. }
    assert (Hv1 : rget T1 Rra = ra0).
    { rewrite (rget_ne T1 Rra ltac:(vm_compute; discriminate)).
      rewrite /T1 upd_ne; [exact Hra | vm_compute; discriminate]. }
    iEval (rewrite -Hpa1) in "Hb1".
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0x004)) Rra csp_rs1
              (mword_of_int 536 : mword 12) T1 (K - 68)%nat v1 b
              with "Hcg Hpc [] Hb1").
    { iApply (kxc_004 with "Htext"). }
    iIntros (CID2 Hs2c) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1 Hv1) in "Hb1".
    assert (Hp008 : add_vec_int (mword_of_int (KXA + 0x004) : mword 64) 4
                    = mword_of_int (KXA + 0x008)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp008) in "Hpc".
    (* ---- +0x008: sd s0,528(sp) -> slot 2 ---- *)
    assert (Hpa2 : add_vec (rget T1 csp_rs1)
                     (sign_extend' 64 (mword_of_int 528 : mword 12))
                   = pa_stk sp0 2).
    { rewrite (rget_ne T1 csp_rs1 ltac:(vm_compute; discriminate)) HT1sp.
      apply kxc_frm2. }
    assert (Hv2 : rget T1 Rs0 = s00).
    { rewrite (rget_ne T1 Rs0 ltac:(vm_compute; discriminate)).
      rewrite /T1 upd_ne; [exact Hs0 | vm_compute; discriminate]. }
    iEval (rewrite -Hpa2) in "Hb2".
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0x008)) Rs0 csp_rs1
              (mword_of_int 528 : mword 12) T1 (K - 68)%nat v2 b
              with "Hcg Hpc [] Hb2").
    { iApply (kxc_008 with "Htext"). }
    iIntros (CID3 Hs3c) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2 Hv2) in "Hb2".
    assert (Hp00c : add_vec_int (mword_of_int (KXA + 0x008) : mword 64) 4
                    = mword_of_int (KXA + 0x00c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp00c) in "Hpc".
    (* ---- +0x00c: sd s1,520(sp) -> slot 3 ---- *)
    assert (Hpa3 : add_vec (rget T1 csp_rs1)
                     (sign_extend' 64 (mword_of_int 520 : mword 12))
                   = pa_stk sp0 3).
    { rewrite (rget_ne T1 csp_rs1 ltac:(vm_compute; discriminate)) HT1sp.
      apply kxc_frm3. }
    assert (Hv3 : rget T1 Rs1 = s10).
    { rewrite (rget_ne T1 Rs1 ltac:(vm_compute; discriminate)).
      rewrite /T1 upd_ne; [exact Hs1 | vm_compute; discriminate]. }
    iEval (rewrite -Hpa3) in "Hb3".
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0x00c)) Rs1 csp_rs1
              (mword_of_int 520 : mword 12) T1 (K - 68)%nat v3 b
              with "Hcg Hpc [] Hb3").
    { iApply (kxc_00c with "Htext"). }
    iIntros (CID4 Hs4c) "Hcg Hpc Hb3".
    iEval (rewrite Hpa3 Hv3) in "Hb3".
    assert (Hp010 : add_vec_int (mword_of_int (KXA + 0x00c) : mword 64) 4
                    = mword_of_int (KXA + 0x010)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp010) in "Hpc".
    (* ---- +0x010: sd s2,512(sp) -> slot 4 ---- *)
    assert (Hpa4 : add_vec (rget T1 csp_rs1)
                     (sign_extend' 64 (mword_of_int 512 : mword 12))
                   = pa_stk sp0 4).
    { rewrite (rget_ne T1 csp_rs1 ltac:(vm_compute; discriminate)) HT1sp.
      apply kxc_frm4. }
    assert (Hv4 : rget T1 Rs2 = s20).
    { rewrite (rget_ne T1 Rs2 ltac:(vm_compute; discriminate)).
      rewrite /T1 upd_ne; [exact Hs2 | vm_compute; discriminate]. }
    iEval (rewrite -Hpa4) in "Hb4".
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0x010)) Rs2 csp_rs1
              (mword_of_int 512 : mword 12) T1 (K - 68)%nat v4 b
              with "Hcg Hpc [] Hb4").
    { iApply (kxc_010 with "Htext"). }
    iIntros (CID5 Hs5c) "Hcg Hpc Hb4".
    iEval (rewrite Hpa4 Hv4) in "Hb4".
    assert (Hp014 : add_vec_int (mword_of_int (KXA + 0x010) : mword 64) 4
                    = mword_of_int (KXA + 0x014)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp014) in "Hpc".
    (* ---- +0x014: c.addi4spn s0,sp,544 -- s0 := sp0 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KXA + 0x014))
              (Cregidx (mword_of_int 0)) (mword_of_int 136 : mword 8) Rs0
              T1 (K - 68)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc []").
    { iApply (kxc_014 with "Htext"). }
    iIntros (CID6 Hs6c) "Hcg Hpc".
    set (T2 := <[Regidx Rs0 := regval_into_reg
                  (add_vec (T1 !!! Regidx csp_rs1)
                     (sign_extend' 64 (caddi4spn_imm (mword_of_int 136 : mword 8))))]> T1).
    change (<[Regidx Rs0 := regval_into_reg
              (add_vec (T1 !!! Regidx csp_rs1)
                 (sign_extend' 64 (caddi4spn_imm (mword_of_int 136 : mword 8))))]> T1)
      with T2.
    assert (HT2s0 : T2 !!! Regidx Rs0 = sp0).
    { rewrite /T2 upd_eq HT1sp. apply kxc_s0_of_sp. }
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T2 upd_ne; [exact HT1sp | vm_compute; discriminate]).
    assert (HT2a0 : T2 !!! Regidx Ra0 = pv).
    { rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [exact Ha0 | vm_compute; discriminate]. }
    assert (HT2a1 : T2 !!! Regidx Ra1 = av).
    { rewrite /T2 upd_ne; [| vm_compute; discriminate].
      rewrite /T1 upd_ne; [exact Ha1 | vm_compute; discriminate]. }
    assert (Hp016 : add_vec_int (mword_of_int (KXA + 0x014) : mword 64) 2
                    = mword_of_int (KXA + 0x016)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp016) in "Hpc".
    (* ---- +0x016: c.mv s2,a0 -- s2 := path ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x016)) Rs2 Ra0
              T2 (K - 68)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_016 with "Htext"). }
    iIntros (CID7 Hs7c) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (T3 := <[Regidx Rs2 := regval_into_reg
                  (add_vec zero_reg (T2 !!! Regidx Ra0))]> T2).
    assert (HT3s2 : T3 !!! Regidx Rs2 = pv).
    { rewrite /T3 upd_eq HT2a0. apply add_vec_zero_l. }
    assert (HT3s0 : T3 !!! Regidx Rs0 = sp0)
      by (rewrite /T3 upd_ne; [exact HT2s0 | vm_compute; discriminate]).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T3 upd_ne; [exact HT2sp | vm_compute; discriminate]).
    assert (HT3a0 : T3 !!! Regidx Ra0 = pv)
      by (rewrite /T3 upd_ne; [exact HT2a0 | vm_compute; discriminate]).
    assert (HT3a1 : T3 !!! Regidx Ra1 = av)
      by (rewrite /T3 upd_ne; [exact HT2a1 | vm_compute; discriminate]).
    assert (Hp018 : add_vec_int (mword_of_int (KXA + 0x016) : mword 64) 2
                    = mword_of_int (KXA + 0x018)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp018) in "Hpc".
    (* ---- +0x018: sd a0,-528(s0) -- spill the path into slot 66 ---- *)
    assert (Hpa66 : add_vec (rget T3 Rs0)
                      (sign_extend' 64 (mword_of_int 3568 : mword 12))
                    = pa_stk sp0 66).
    { rewrite (rget_ne T3 Rs0 ltac:(vm_compute; discriminate)) HT3s0.
      apply kxc_path_slot. }
    assert (Hv66 : rget T3 Ra0 = pv)
      by (rewrite (rget_ne T3 Ra0 ltac:(vm_compute; discriminate)); exact HT3a0).
    iEval (rewrite -Hpa66) in "Hb66".
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0x018)) Ra0 Rs0
              (mword_of_int 3568 : mword 12) T3 (K - 68)%nat v66 b
              with "Hcg Hpc [] Hb66").
    { iApply (kxc_018 with "Htext"). }
    iIntros (CID8 Hs8c) "Hcg Hpc Hb66".
    iEval (rewrite Hpa66 Hv66) in "Hb66".
    assert (Hp01c : add_vec_int (mword_of_int (KXA + 0x018) : mword 64) 4
                    = mword_of_int (KXA + 0x01c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp01c) in "Hpc".
    (* ---- +0x01c: sd a1,-512(s0) -- spill argv into slot 64 ---- *)
    assert (Hpa64 : add_vec (rget T3 Rs0)
                      (sign_extend' 64 (mword_of_int 3584 : mword 12))
                    = pa_stk sp0 64).
    { rewrite (rget_ne T3 Rs0 ltac:(vm_compute; discriminate)) HT3s0.
      apply kxc_argv_slot. }
    assert (Hv64 : rget T3 Ra1 = av)
      by (rewrite (rget_ne T3 Ra1 ltac:(vm_compute; discriminate)); exact HT3a1).
    iEval (rewrite -Hpa64) in "Hb64".
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0x01c)) Ra1 Rs0
              (mword_of_int 3584 : mword 12) T3 (K - 68)%nat v64 b
              with "Hcg Hpc [] Hb64").
    { iApply (kxc_01c with "Htext"). }
    iIntros (CID9 Hs9c) "Hcg Hpc Hb64".
    iEval (rewrite Hpa64 Hv64) in "Hb64".
    assert (Hp020 : add_vec_int (mword_of_int (KXA + 0x01c) : mword 64) 4
                    = mword_of_int (KXA + 0x020)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp020) in "Hpc".
    (* ---- hand over ---- *)
    assert (HT3thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs2 -> T3 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns2.
      rewrite /T3 upd_ne; [| regne].
      rewrite /T2 upd_ne; [| regne].
      rewrite /T1 upd_ne; [| regne].
      reflexivity. }
    iSpecialize ("Hcont" $! CID9 with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! T3 with "[%] Hcg Hpc").
    { split_and!; [exact HT3sp | exact HT3s0 | exact HT3s2 | exact HT3a0
                  | exact HT3a1 | exact HT3thr]. }
    rewrite /kxc_frameA.
    iFrame "Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12 Hb13 Hmid
            Hb64 Hb65 Hb66 Hb67 Hb68".
  Qed.

End KexecA.

(* ===================================================================== *)
(*  THE SEAM AT +0x032.                                                   *)
(* ===================================================================== *)
(* Phase A is two halves and this is the state they meet in.  Stated ONCE,
   as a named [iProp], so the two cannot disagree -- the half that produces
   it ([kxc_a1], +0x000 .. +0x030) and the half that consumes it
   ([kxc_a2], +0x032 .. +0x08e) are both written over this name.

   IT IS RELATIVE TO ITS OWN ENTRY MAP [M32], not to kexec's entry map [m]
   (convention 1 in claude-notes/projects/kexec.md): the frame is pushed, s0
   is the frame pointer, s1 is the running process and s2 the path, so a
   premise tying [M32] to [m] would be false.  What relates the two is the
   last pure conjunct -- the callee-saved registers this stretch has NOT
   written still agree with [m], which is what lets the epilogue's
   [callee_saved] obligation close from downstream ([ProofKexecParts.kxc_epi]'s
   [Hthr]).

   [proc_priv] travels WHOLE (convention 2): namei's [p_cwd] cell, its
   [cwd_ref] and the [p_pid] quarter every one of begin_op / namei / ilock /
   readi / iunlockput / end_op needs are all inside it, and
   [ProcInv.proc_priv_cwd_pid] yields exactly those three at once -- so each
   half opens it at its top and closes it (with
   [ProofKexecParts.kxc_upd_cwd_id]) before its exits.

   [SpecKexec.fs_fabric] is NOT here: it is persistent, so it is carried by
   whoever needs it rather than threaded.

   THE PATH BUFFER IS AT [dqpv] AND THE ARGUMENT STRINGS AT [dqas], the two
   fractions [wp_kexec_sconf_body] takes them at.  Both are only READ here --
   the path goes to namei and to safestrcpy, each argument to strlen and to
   copyout -- and all four of those callees are dfrac-generic on their source,
   so the fraction goes straight through.  What this bundle still holds WHOLE
   is what kexec WRITES: the frame slots, the new table, and [proc_priv]. *)
Section KexecASeam.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.  (* NB: icacheG + icfg come from
              [fileG] -- see the header.  A standalone [!icacheG Σ] beside
              [!fileG Σ] is a SECOND instance and [ProcInv.cwd_ref] then does
              not match [SpecNamei]'s [inode_held]. *)
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  (* [inode_held] IS [inode_held_at] with the inum forgotten, so the walk
     publishes the sharper form by ∃-introduction and no landed contract
     grows a premise.  N-5.2B's whole cost at this seam. *)
  Lemma inode_held_zi (v : mword 64) :
    inode_held v ⊢ ∃ z : Z, inode_held_at v z.
  Proof.
    rewrite /inode_held /inode_held_at. iIntros "H".
    iDestruct "H" as (k q inum) "(%Hv & %Hk & %Hlt & Hr)".
    iExists (bv_unsigned inum), k, q, inum.
    iSplit; [done |]. iSplit; [done |]. iSplit; [done |]. iSplit; [done |].
    iExact "Hr".
  Qed.

  Definition kxc_at_a2
      (jp : nat)
      (bn : bio_names) (g : log_names)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa dqpv dqas : dfrac)
      (m M32 : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (sp0 ra0 s00 s10 s20 pv av ipv : mword 64)
      (* THE INUM THE WALK RETURNED (N-5.2B).  [inode_held] hides it behind
         an existential, which is enough for a client that only means to
         [ilock] the thing -- but not for one that holds a CONTENTS pin at a
         named inum and has to redeem it against this very inode's payload.
         [SpecNameiTr.inode_held_at] is [inode_held] with that one equation
         exposed, and the landed walk publishes it by [∃]-introduction
         ([inode_held_zi] below), so no landed contract asks for more. *)
      (zi : Z)
      (n1 : nat) : iProp Σ :=
    let pj := proc_addr jp in
    (* ---- the register state at [pc_is (kexec + 0x32)] ---- *)
    (⌜ M32 !!! Regidx csp_rs1 = pa_stk sp0 68 /\
       M32 !!! Regidx Rs0 = sp0 /\
       M32 !!! Regidx Rs1 = pj /\
       M32 !!! Regidx Rs2 = pv /\
       M32 !!! Regidx Ra0 = ipv /\
       ipv <> (zero_reg : mword 64) /\
       (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
          r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> M32 !!! Regidx r = m !!! Regidx r) ⌝ ∗
     pc_is (mword_of_int (KXA + 0x032) : mword 64) ∗
     sie_cap_gpr KT1 M32 (K - 68)%nat b pj ∗
     cpu_own 0 eb pj b lks ∗
     trap_csrs_ext KT1 eb ∗
     cpu_claim_ext eb pj ∗
     (* ---- the open log transaction, and what namei left of its budget.
            [iput_units <= n1] AND NOT AN INTERVAL IN THE PATH LENGTH: the
            walk is priced by [SpecNamex.walk_need], which is 4 whatever the
            depth, so what crosses this seam is the one fact the closing
            iunlockput needs.  Spelling it as the counted contract's
            [MAXOPBLOCKS - (L+1)*iput_units <= n1] is what used to cap kexec
            at one path element -- see SpecKexec.v's header. ---- *)
     ⌜ (iput_units <= n1)%nat ⌝ ∗
     log_op g n1 ∗
     (* ---- the inode namei returned, and the slot it came out of ---- *)
     inode_held_at ipv zi ∗
     iref_slots 1 ∗
     (* ---- the fs environment kexec threads.  The block bitmap is the
            PERSISTENT [BitmapInv.bitmap_inv] now, so nothing about the free
            pool crosses this seam -- the ledger that used to ride here
            ([used1 ⊆ used]) has no statement left to make. ---- *)
     bitmap_inv fsc_fs bmapstart cov logstart size ∗
     bslots 3 ∗
     sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) ∗
     sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) ∗
     kalloc_env ga None ∗
     (* ---- the process, WHOLE (convention 2) ---- *)
     proc_priv gf pj pidv V ∗
     (* ---- the caller's buffers.  THE PATH IS FULL; see the header. ---- *)
     ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) ∗
     ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) ∗
     ([∗ list] i ∈ seq 0 na,
        [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) ∗
     (* ---- the frame: slots 1..4 pinned, 5..13 lazy, 14..63 one chunk,
            64 = argv, 66 = path ---- *)
     kxc_frameA sp0 ra0 s00 s10 s20 pv av)%I.

End KexecASeam.

(* ===================================================================== *)
(*  THE EXIT, FROM THE LANDED RELATION TO THE GENERIC ONE (N-5.2B §13.3)  *)
(*                                                                        *)
(*  Every phase lemma of this cone relays kexec's exit at [kexec_ok_q Q].  *)
(*  A caller holding the LANDED, [kexec_ok]-shaped continuation converts   *)
(*  with this one wand: the generic relation implies the landed one        *)
(*  ([KexecOkQ.kexec_ok_q_weaken]) and the hypothesis sits to the LEFT of  *)
(*  a wand, so implication runs the right way.                            *)
(*                                                                        *)
(*  STATED AT THE FULL SHAPE, NOT OVER AN ABSTRACTED TAIL.  A version      *)
(*  with the sixteen wands packed into a [T : regfile -> pprivate ->       *)
(*  iProp] is prettier and does not terminate: [iSpecialize] then has to   *)
(*  solve [?T mf V'] against a tail containing [proc_priv], i.e. against a *)
(*  4096-conjunct trapframe big-op, which is durable-notes' measured       *)
(*  non-terminating case.  Spelling the tail keeps the unification         *)
(*  first-order.                                                          *)
(* ===================================================================== *)
Section KexecExitQ.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ}.
  Context `{GEN : GenId}.

  Notation Ra0 := (mword_of_int 10 : mword 5).

  Lemma kxc_exit_qgen `{CIDx : CpuId}
      (Q : mword 64 -> Prop)
      (pj : mword 64) (ga gf : gname) (bmapstart inodestart : Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa dqpv dqas : dfrac)
      (m : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (ra0 pv av : mword 64) :
    wp_next (CID0 := CIDx) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (V' : pprivate) (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K b pj -∗
          cpu_own 0 eb pj b lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb pj -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          kalloc_env ga None -∗
          proc_priv gf pj pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
          bslots 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    wp_next (CID0 := CIDx) true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (V' : pprivate) (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok_q Q V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K b pj -∗
          cpu_own 0 eb pj b lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb pj -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          kalloc_env ga None -∗
          proc_priv gf pj pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
          bslots 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)).
  Proof.
    rewrite /wp_next. iIntros "H" (CID Hcr).
    iSpecialize ("H" $! CID with "[%]"); [exact Hcr |].
    iIntros (mf V' entry spv szv')
            "%Hcs %Hok Hsie Hcnt Htc Hcl Hpc Hbm Hin Hka Hpriv Hpath Hargv
             Hargs Hbs Hirs".
    iApply ("H" $! mf V' entry spv szv' with
             "[%] [%] Hsie Hcnt Htc Hcl Hpc Hbm Hin Hka Hpriv Hpath Hargv
              Hargs Hbs Hirs");
      [exact Hcs | exact (kexec_ok_q_weaken _ _ _ _ _ _ _ _ _ Hok)].
  Qed.


  (* ...and the way the opaque exit is OPENED (N-5.2B §13.4).  The unfolding
     wand is persistent, so a block with two [-1] tails can spend it twice;
     [KEX] itself is linear and whichever tail runs consumes it.  Stated at
     [fun _ => _] because the exit body names no hart. *)
  Lemma kxc_exit_open `{CIDx : CpuId} (pj : mword 64)
      (KEX E : CpuId -> iProp Σ) :
    □ (∀ CX : CpuId, KEX CX -∗ E CX) -∗
    wp_next (CID0 := CIDx) true pj KEX -∗
    wp_next (CID0 := CIDx) true pj E.
  Proof.
    rewrite /wp_next. iIntros "#Hw H" (CID Hcr).
    iSpecialize ("H" $! CID with "[%]"); [exact Hcr |]. by iApply "Hw".
  Qed.

End KexecExitQ.


(* ===================================================================== *)
(*  THE BLOCKS AT THE BOTTOM, SHARED BY PHASE A AND PHASE B.              *)
(*  Functor-bound because [kxc_bad64] calls iunlockput and end_op.        *)
(* ===================================================================== *)
Module KexecTailProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                      (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                      (EndOp : END_OP).
Section KexecAExit.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.  (* NB: icacheG + icfg come from
              [fileG] -- see the header.  A standalone [!icacheG Σ] beside
              [!fileG Σ] is a SECOND instance and [ProcInv.cwd_ref] then does
              not match [SpecNamei]'s [inode_held]. *)
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac regne := reg_ne_side.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* =================================================================== *)
  (*  The single-slot accessors out of the icache's persistent families    *)
  (*  that are not already shared -- the sleeplock family's is             *)
  (*  [IcacheEscrow.ic_sleeplocks_lookup].                                 *)
  (* =================================================================== *)
  Lemma kxa_esc_acc (gi : gname)
      (cov : gset Z) (logstart : Z) (k : nat) : (k < NINODE)%nat ->
    (ic_escrows fsc_ic fsc_fs gi cov logstart -∗ ic_escrow fsc_ic fsc_fs gi cov logstart k
     : iProp Σ).
  Proof.
    iIntros (Hk) "H". rewrite /ic_escrows.
    assert (Hl : seq 0 NINODE !! k = Some k) by (rewrite lookup_seq; lia).
    iDestruct (big_sepL_lookup _ _ k k Hl with "H") as "$".
  Qed.

  Lemma kxa_bs3_split :
    (bslots 3 : iProp Σ) -∗ bslot ∗ bslots 2.
  Proof.
    rewrite /bslot. change 3%nat with (1 + 2)%nat. rewrite bslots_op.
    iIntros "$".
  Qed.

  Lemma kxa_bs3_join :
    (bslot : iProp Σ) -∗ bslots 2 -∗ bslots 3.
  Proof.
    iIntros "A B". rewrite /bslot. change 3%nat with (1 + 2)%nat.
    rewrite bslots_op. iFrame.
  Qed.

  (* =================================================================== *)
  (*  [fs_fabric]'s CONSTRUCTOR.                                          *)
  (*                                                                      *)
  (*  BELONGS NEXT TO [fs_fabric]'s definition in SpecKexec.v, right      *)
  (*  after its [Persistent] instance -- it lives here only because this  *)
  (*  is a file phase A and phase B's call sites can require without      *)
  (*  touching a Spec file, and [fs_fabric]'s own header already says its *)
  (*  home is a shared file once a second contract wants it (promote on   *)
  (*  the second consumer).  MOVE IT to SpecKexec.v when that happens.    *)
  (*                                                                      *)
  (*  Both of [T.kxc_bad64]'s call sites in ProofKexecA.v hand its        *)
  (*  [fs_fabric] premise over as a [[]]-bullet closed with [rewrite      *)
  (*  /fs_fabric; iFrame "<the same thirteen names>"].  [fs_fabric]        *)
  (*  unfolds to a flat 13-conjunct [∗] (IcacheEscrow's arms, BioInv's    *)
  (*  ctx's, the crash seam, the era cert, the itable pair, the two       *)
  (*  icache families, [ireg_inv], [procs_inv] -- a big-op of [is_lock]   *)
  (*  over every proc -- and the disk fabric), and a NAMED [iFrame] still *)
  (*  pays a GOAL-side search over that whole bundle (optimization.md's   *)
  (*  icache-files entry, "#3"): 107.7 s and 90.6 s, two single sentences *)
  (*  inside kexec's whole-function proof, where [Qed]'s term-size law    *)
  (*  charges the search once per surviving proof step.  Assembled HERE,  *)
  (*  where the context is exactly the thirteen pieces and nothing else,  *)
  (*  the same search is a no-op; a caller then writes one [iApply].      *)
  (* =================================================================== *)
  Lemma fs_fabric_mk gs gu gd gk pd pav pu bn g gi gtl
      cov logstart inodestart nib dev :
    (* the fabric's last conjunct (durable-disk B''-tx), FIRST in the wand
       chain so a caller writes it as one [[%]] slot *)
    ⌜g = icfg_log⌝ -∗
    kernel_data -∗
    panic_env -∗
    bio_ctx bn (fs_view fsc_fs gd dev cov) -∗
    log_ctx g bn fsc_fs cov logstart dev -∗
    fs_crash_seam cov logstart -∗
    gen_cert -∗
    is_itable2 gtl fsc_ic fsc_fs gi cov logstart nib dev -∗
    itable_inv -∗
    ic_escrows fsc_ic fsc_fs gi cov logstart -∗
    ic_sleeplocks fsc_ic -∗
    ireg_inv gi fsc_fs inodestart nib -∗
    ireg_open -∗
    procs_inv gs -∗
    dev_inv gu gd -∗
    disk_geom gd pd pav pu -∗
    is_lock gk d_lock "virtio_disk"%string (disk_res gd pd pav pu) -∗
    fs_fabric gs gu gd gk pd pav pu bn g gi gtl
              cov logstart inodestart nib dev.
  Proof.
    iIntros "%Hclogf Hkd Hpenv Hbio Hlogc Hcrash Hcert Hitab Hitinv Hesc Hslks Hireg Hropen
             Hprocs Hdevi Hdgeom Hdlock".
    rewrite /fs_fabric.
    iSplitL "Hkd"; [iExact "Hkd" |].
    iSplitL "Hpenv"; [iExact "Hpenv" |].
    iSplitL "Hbio"; [iExact "Hbio" |].
    iSplitL "Hlogc"; [iExact "Hlogc" |].
    iSplitL "Hcrash"; [iExact "Hcrash" |].
    iSplitL "Hcert"; [iExact "Hcert" |].
    iSplitL "Hitab"; [iExact "Hitab" |].
    iSplitL "Hitinv"; [iExact "Hitinv" |].
    iSplitL "Hesc"; [iExact "Hesc" |].
    iSplitL "Hslks"; [iExact "Hslks" |].
    iSplitL "Hireg"; [iExact "Hireg" |].
    iSplitL "Hropen"; [iExact "Hropen" |].
    iSplitL "Hprocs"; [iExact "Hprocs" |].
    iSplitL "Hdevi"; [iExact "Hdevi" |].
    iSplitL "Hdgeom"; [iExact "Hdgeom" |].
    iSplitL "Hdlock"; [iExact "Hdlock" |].
    iPureIntro; exact Hclogf.
  Qed.

  (* =================================================================== *)
  (*  THE SHARED [-1] EXIT, at +0x072.                                    *)
  (*                                                                      *)
  (*  Both of phase A's [bad:] entries end identically: a0 = -1, the frame *)
  (*  in [ProofKexecParts.kxc_frame] shape, and the epilogue.  The         *)
  (*  contract's failure arm is [V' = V] and it is free -- nothing before  *)
  (*  the commit block touched the process.                               *)
  (* =================================================================== *)
  Lemma kxc_exit_m1
      (Q : mword 64 -> Prop)
      (pj : mword 64) (bn : bio_names) (ga gf : gname)
      (bmapstart inodestart : Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa dqpv dqas : dfrac)
      (m Mt : regfile) (K : nat) (eb : bool) (b : bool) (lks : gset string)
      (sp0 ra0 s00 s10 s20 pv av : mword 64) :
    (68 <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 68 ->
    Mt !!! Regidx Ra0 = (mword_of_int (-1) : mword 64) ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (K - 68)%nat b pj -∗
    cpu_own 0 eb pj b lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb pj -∗
    kernel_text -∗
    pc_is (mword_of_int (KXA + 0x072) : mword 64) -∗
    kxc_frame sp0 ra0 s00 s10 s20 -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    kalloc_env ga None -∗
    proc_priv gf pj pidv V -∗
    ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
    ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
    ([∗ list] i ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
    bslots 3 -∗
    iref_slots 2 -∗
    wp_next true pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok_q Q V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K b pj -∗
          cpu_own 0 eb pj b lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb pj -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          kalloc_env ga None -∗
          proc_priv gf pj pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
          bslots 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hra Hs0 Hs1 Hs2 Hmtsp Hmta0 Hthr.
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc Hframe Hbm Hins #Hka Hpriv Hpath Hargv
             Hargs Hbs Hirs Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    iApply (kxc_epi_frame m Mt K sp0 ra0 s00 s10 s20 pj b
              HK Hsp Hra Hs0 Hs1 Hs2 Hmtsp Hthr
              with "Hcg Htext Hpc Hframe").
    iIntros (CIDe Hse mf) "%Hcs %Hpres Hcg Hpc".
    iDestruct (cpu_own_transport CID0 CIDe 0%nat eb pj b Hse
                 with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDe eb pj
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDe eb pj
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iSpecialize ("Hcont" $! CIDe with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf V (mword_of_int 0 : mword 64)
              (mword_of_int 0 : mword 64) (mword_of_int 0 : mword 64)
              with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc Hbm Hins Hka Hpriv Hpath
                    Hargv Hargs Hbs Hirs").
    - exact Hcs.
    - left. split; [| reflexivity].
      rewrite (Hpres Ra0 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
      exact Hmta0.
  Qed.


End KexecAExit.

(* A THIRD SECTION, for [kxc_epi]'s reason again: [kxc_bad64] applies
   [kxc_exit_m1] at the hart the [c.ldsp] at +0x070 resumed on, and a
   same-Section sibling would resolve its [CpuId] through the section
   variable by name. *)
Section KexecABad.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.  (* NB: icacheG + icfg come from
              [fileG] -- see the header.  A standalone [!icacheG Σ] beside
              [!fileG Σ] is a SECOND instance and [ProcInv.cwd_ref] then does
              not match [SpecNamei]'s [inode_held]. *)
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Rs4 := (mword_of_int 20 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).
  Notation Ra2 := (mword_of_int 12 : mword 5).
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra4 := (mword_of_int 14 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac regne := reg_ne_side.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* =================================================================== *)
  (*  +0x064 .. +0x070 -- THE SHORT-READ / BAD-MAGIC TAIL.                *)
  (*                                                                      *)
  (*    mv a0,s4 ; jal iunlockput ; jal end_op ; li a0,-1 ;               *)
  (*    ld s4,496(sp) ; fall into the epilogue                            *)
  (*                                                                      *)
  (*  Reached from BOTH of [kxc_a2]'s tests -- the [bne a0,64] at +0x050  *)
  (*  and the [beq a4,a5] at +0x060 -- so it is one lemma, not two        *)
  (*  copies.  It closes the open inode (iunlockput) and the log          *)
  (*  transaction (end_op) and then takes [kxc_exit_m1].                  *)
  (*                                                                      *)
  (*  SLOT 6 HOLDS THE ENTRY s4 and the [ld] puts it back, which is what  *)
  (*  makes [callee_saved]'s s4 conjunct hold at the return.              *)
  (* =================================================================== *)
  Lemma kxc_bad64
      (Q : mword 64 -> Prop)
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gi : gname)
      (gtl : gname) (gil gisl : gname) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (* [gy]: the GENERATION the caller's share names (SpecIlock v5 /
         fs-icache 17.6 (5)).  It rides through the deposit and pins the
         [ity_shot] SpecIunlockput now demands. *)
      (k : nat) (qi sq : Qp) (gy : gname) (inum : mword 32)
      (dn : dinode) (bm : blkmap)
      (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa dqpv dqas : dfrac)
      (m Mt : regfile) (K : nat) (eb : bool) (lks : gset string)
      (sp0 ra0 s00 s10 s20 pv av : mword 64) :
    (K_kexec <= K)%nat ->
    (k < NINODE)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    IBLOCK inum inodestart ∈ cov ->
    ~ (IBLOCK inum inodestart ∈ log_region_set logstart) ->
    bv_unsigned inum < 16 * Z.of_nat nib ->
    cov_below cov size ->
    (iput_units <= n2)%nat ->
    (jp < NPROC)%nat ->
    gs !! jp = Some gl ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 68 ->
    Mt !!! Regidx Rs4 = ientry k ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 -> r <> Rs0 ->
        r <> Rs1 -> r <> Rs2 -> r <> Rs4 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr KT1 Mt (K - 68)%nat eb (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) eb lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jp) -∗
    kernel_text -∗
    pc_is (mword_of_int (KXA + 0x064) : mword 64) -∗
    fs_fabric gs gu gd gk pd pav pu bn g gi gtl
              cov logstart inodestart nib dev -∗
    is_sleeplock_gen gil gisl (i_lock (ientry k)) "inode"%string (ic_tok fsc_ic k) (slh_tok (icfg_isl k)) -∗
    (* ---- the open inode: exactly SpecIunlockput's input ---- *)
    sleeplocked_q gisl sq (i_lock (ientry k)) pidv -∗
    ic_tx_dep fsc_ic k sq dev inum gy -∗
    i_dev (ientry k) ↦₄{DfracOwn (1/2)} dev -∗
    i_inum (ientry k) ↦₄{DfracOwn (1/2)} inum -∗
    i_valid (ientry k) ↦₄ valid_word true -∗
    ic_loaded fsc_fs gi cov logstart k inum dn bm -∗
    (* the parked record's type witness -- SpecIunlockput's new premise
       (SpecIlock v5's postcondition supplies it at the same [gy]) *)
    ity_shot gy (di_type dn) -∗
    (* ...AND THE INUM'S FREEZE TOKEN, [SpecIunlockput]'s new premise since
       iclaim-ledger.md §3.9 (RULING A-prime): the payload's A-custody
       conjunct, relayed from the caller's own ilock. *)
    ifreeze_off (bv_unsigned inum) -∗
    inode_ref_short k (qi + sq)%Qp qi dev inum -∗
    (* its PROVENANCE UNIT (item 7a-wire): iunlockput's iput spends it. *)
    runit_any (bv_unsigned inum) -∗
    (* ---- and the rest of kexec's state ---- *)
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_inv fsc_fs bmapstart cov logstart size -∗
    kalloc_env ga None -∗
    proc_priv gf (proc_addr jp) pidv V -∗
    ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
    ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
    ([∗ list] i ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
    bslots 3 -∗
    iref_slots 1 -∗
    log_opb g n2 -∗
    kxc_frameA6 sp0 ra0 s00 s10 s20 pv av (m !!! Regidx Rs4) -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok_q Q V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K eb (proc_addr jp) -∗
          cpu_own 0 eb (proc_addr jp) eb lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jp) -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
          bslots 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hibc Hibl Hib Hcovb Hn2
           Hjp Hgs Hsp Hra Hs0 Hs1 Hs2 Hmtsp Hmts4 Hthr.
    
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc #Hfab #Hslkk Hslkd Hdep Hidev
             Hiinum Hivalid Hload Hity Hfrz Hkeep Hru Hbm Hins #Hbits #Hka Hpriv Hpath Hargv
             Hargs Hbs Hirs Hlog Hframe Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    (* depth 0 with interrupts on forces the held set empty, so iunlockput's
       order premise needs no hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iDestruct "Hfab" as "(#Hkd & #Hpenv & #Hbio & #Hlogc & #Hcrash & #Hcert & #Hitab & #Hitinv &
                          #Hesc & #Hslks & #Hireg & #Hropen & #Hprocs & #Hdevi & #Hdgeom &
                          #Hdlock & %Hclogf)".
    iDestruct (kxa_esc_acc gi cov logstart k Hk with "Hesc") as "#Hesck".
    iDestruct (proc_priv_bare_cref gf (proc_addr jp) pidv V with "Hpriv")
      as "(Hppid & Hcref & Hpvbk)".
    (* ---- +0x064: c.mv a0,s4 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x064)) Ra0 Rs4
              Mt (K - 68)%nat eb ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_064 with "Htext"). }
    iIntros (CIDa Hsa) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B1 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (Mt !!! Regidx Rs4))]> Mt).
    assert (HB1a0 : B1 !!! Regidx Ra0 = ientry k).
    { rewrite /B1 upd_eq Hmts4. apply add_vec_zero_l. }
    assert (HB1sp : B1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B1 upd_ne; [exact Hmtsp | nz]).
    assert (Hpp066 : add_vec_int (mword_of_int (KXA + 0x064) : mword 64) 2
                     = mword_of_int (KXA + 0x066)) by pcw.
    iEval (rewrite Hpp066) in "Hpc".
    (* ---- +0x066: jal ra,iunlockput ---- *)
    assert (Htiu : add_vec (mword_of_int (KXA + 0x066) : mword 64)
                     (sign_extend' 64 (mword_of_int 2092080 : mword 21))
                   = mword_of_int KernelSyms.iunlockput) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x066)) Rra
              (mword_of_int 2092080 : mword 21) B1 (K - 68)%nat eb
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htiu; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_066 with "Htext"). }
    iIntros (CIDj1 Hsj1) "Hcg Hpc". iEval (rewrite Htiu) in "Hpc".
    set (B2 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x066) : mword 64) 4)]> B1).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x066) : mword 64) 4)]> B1) with B2.
    assert (HB2ra : B2 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x066) : mword 64) 4)
      by (rewrite /B2; apply upd_eq).
    assert (HB2a0 : B2 !!! Regidx Ra0 = ientry k)
      by (rewrite /B2 upd_ne; [exact HB1a0 | nz]).
    assert (HB2sp : B2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B2 upd_ne; [exact HB1sp | nz]).
    iDestruct (cpu_own_transport CID0 CIDj1 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CIDj1 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CIDj1 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iApply (Iunlockput.wp_iunlockput_tx_sconf gs jp gl gu gd gk pd pav pu bn g
              gi gtl gil gisl cov logstart bmapstart inodestart nib size dev
              k qi sq gy inum dn bm n2 pidv (DfracOwn (1/4)) dqb dqs
              B2 (K - 68)%nat eb eb lks V
              ltac:(lia) Hk Hlg Hsz Hbm0 Hbmc
              Hbml Hins0 Hibc Hibl Hib Hcovb Hn2 Hjp Hgs HB2a0 ltac:(lkbelow) Hclogf
              with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc Hitab Hitinv Hesck
                    Hireg Hropen Hslkk Hslkd Hdep Hidev Hiinum Hivalid Hload
                    Hity Hfrz [$Hkeep $Hru] Hbm Hins Hbits Hppid Hprocs Hdevi Hdgeom Hdlock Hbs
                    Hlog").
    all: try lkbelow.
    iIntros (CIDu Hsu M1 n3) "%Hcsu Hcg Hcnt Hextc Hclmc Hpc Hppid Hbm Hins
             Hbs %Hn3 Hlog Hirs1".
    assert (Hpc6a : ret_pc (B2 !!! Regidx Rra) = mword_of_int (KXA + 0x06a))
      by (rewrite HB2ra; pcw).
    iEval (rewrite Hpc6a) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcsu csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HB2sp. }
    (* ---- +0x06a: jal ra,end_op ---- *)
    assert (Hteo : add_vec (mword_of_int (KXA + 0x06a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2094286 : mword 21))
                   = mword_of_int KernelSyms.end_op) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x06a)) Rra
              (mword_of_int 2094286 : mword 21) M1 (K - 68)%nat eb
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Hteo; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_06a with "Htext"). }
    iIntros (CIDj2 Hsj2) "Hcg Hpc". iEval (rewrite Hteo) in "Hpc".
    set (B3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x06a) : mword 64) 4)]> M1).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x06a) : mword 64) 4)]> M1) with B3.
    assert (HB3ra : B3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x06a) : mword 64) 4)
      by (rewrite /B3; apply upd_eq).
    assert (HB3sp : B3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B3 upd_ne; [exact HM1sp | nz]).
    iDestruct (cpu_own_transport CIDu CIDj2 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDu CIDj2 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDu CIDj2 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iApply (EndOp.wp_end_op_sconf gs jp gl gu gd gk pd pav pu bn g fsc_fs
              cov logstart dev n3 pidv (DfracOwn (1/4)) B3 (K - 68)%nat
              eb eb lks V ltac:(lia) Hlg Hjp Hgs
              with "Hcg Hcnt Hextc Hclmc Htext Hkd Hpc Hpenv Hbio Hlogc Hcrash Hcert Hppid
                    Hprocs Hdevi Hdgeom Hdlock Hlog").
    all: try lkbelow.
    iIntros (CIDe Hse M2) "%Hcse Hcg Hcnt Hextc Hclmc Hpc Hppid".
    assert (Hpc6e : ret_pc (B3 !!! Regidx Rra) = mword_of_int (KXA + 0x06e))
      by (rewrite HB3ra; pcw).
    iEval (rewrite Hpc6e) in "Hpc".
    assert (HM2sp : M2 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcse csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HB3sp. }
    (* ---- +0x06e: c.li a0,-1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KXA + 0x06e)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              M2 (K - 68)%nat eb ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_06e with "Htext"). }
    iIntros (CIDl Hsl) "Hcg Hpc".
    set (B4 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (-1) : mword 64)]> M2).
    assert (HB4sp : B4 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B4 upd_ne; [exact HM2sp | nz]).
    assert (Hpp070 : add_vec_int (mword_of_int (KXA + 0x06e) : mword 64) 2
                     = mword_of_int (KXA + 0x070)) by pcw.
    iEval (rewrite Hpp070) in "Hpc".
    (* ---- +0x070: c.ldsp s4,496(sp) -- slot 6 back into s4 ---- *)
    rewrite /kxc_frameA6.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9 &
                            Hf10 & Hf11 & Hf12 & Hf13 & Hmid & Hf64 & Hf65 &
                            Hf66 & Hf67 & Hf68)".
    assert (Hpa6 : add_vec (B4 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 62 : mword 6)
                                                  ('b"000")))
                   = pa_stk sp0 6) by (rewrite HB4sp; apply kxc_slot6_sp).
    iEval (rewrite -Hpa6) in "Hf6".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXA + 0x070)) (mword_of_int 62 : mword 6)
              Rs4 B4 (K - 68)%nat (m !!! Regidx Rs4) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf6").
    { iApply (kxc_070 with "Htext"). }
    iIntros (CIDd Hsd) "Hcg Hpc Hf6". iEval (rewrite Hpa6) in "Hf6".
    set (B5 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> B4).
    assert (Hpp072 : add_vec_int (mword_of_int (KXA + 0x070) : mword 64) 2
                     = mword_of_int (KXA + 0x072)) by pcw.
    iEval (rewrite Hpp072) in "Hpc".
    (* ---- the register facts the epilogue needs ---- *)
    assert (HB5sp : B5 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B5 upd_ne; [exact HB4sp | nz]).
    assert (HB5a0 : B5 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64)).
    { rewrite /B5 upd_ne; [| nz]. rewrite /B4; apply upd_eq. }
    assert (HB5thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> B5 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2.
      destruct (decide (r = Rs4)) as [-> | Ns4].
      - rewrite /B5 upd_eq. reflexivity.
      - rewrite /B5 upd_ne; [| congruence].
        rewrite /B4 upd_ne; [| regne].
        rewrite (callee_saved_lookup Hcse r Hr).
        rewrite /B3 upd_ne; [| regne].
        rewrite (callee_saved_lookup Hcsu r Hr).
        rewrite /B2 upd_ne; [| regne].
        rewrite /B1 upd_ne; [| regne].
        exact (Hthr r Hr Nsp Ns0 Ns1 Ns2 Ns4). }
    (* ---- close the process back up and take the shared exit ---- *)
    (* the block goes back at the [V] it left at -- nothing wrote [p->cwd] --
       so there is no [upd_cwd] to normalise away any more. *)
    iDestruct ("Hpvbk" with "Hppid Hcref") as "Hpriv".
    iDestruct (cpu_own_transport CIDe CIDd 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CIDe CIDd eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CIDe CIDd eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iAssert (iref_slots 2) with "[Hirs Hirs1]" as "Hirs2".
    { change 2%nat with (1 + 1)%nat. rewrite iref_slots_op.
      iSplitL "Hirs"; [iExact "Hirs" | iExact "Hirs1"]. }
    iAssert (kxc_frame sp0 ra0 s00 s10 s20)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12 Hf13 Hmid
             Hf64 Hf65 Hf66 Hf67 Hf68]" as "Hfr".
    { rewrite /kxc_frame.
      iSplitL "Hf1"; [iExact "Hf1" |].
      iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |].
      iSplitL "Hf4"; [iExact "Hf4" |].
      iSplitL "Hf5"; [iExact "Hf5" |].
      iSplitL "Hf6"; [by iExists (m !!! Regidx Rs4) |].
      iSplitL "Hf7"; [iExact "Hf7" |].
      iSplitL "Hf8"; [iExact "Hf8" |].
      iSplitL "Hf9"; [iExact "Hf9" |].
      iSplitL "Hf10"; [iExact "Hf10" |].
      iSplitL "Hf11"; [iExact "Hf11" |].
      iSplitL "Hf12"; [iExact "Hf12" |].
      iSplitL "Hf13"; [iExact "Hf13" |].
      iDestruct "Hf65" as (w65) "Hf65".
      iDestruct "Hf67" as (w67) "Hf67".
      iDestruct "Hf68" as (w68) "Hf68".
      iDestruct (kxc_stack_of_top5 sp0 av w65 pv w67 w68
                   with "Hf64 Hf65 Hf66 Hf67 Hf68") as "Htop".
      change 55%nat with (50 + 5)%nat.
      rewrite (stack_own_app (KTR := KT1)) (pa_stk_assoc sp0 13 50).
      iSplitL "Hmid"; [iExact "Hmid" | iExact "Htop"]. }
    iApply (kxc_exit_m1 Q (proc_addr jp) bn ga gf bmapstart
              inodestart plen pfun na avf alen aslen afun pidv V
              dqb dqs dqa dqpv dqas m B5 K eb eb lks sp0 ra0 s00 s10 s20 pv av
              ltac:(lia)
              Hsp Hra Hs0 Hs1 Hs2 HB5sp HB5a0 HB5thr
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hfr Hbm Hins Hka Hpriv Hpath Hargv
                    Hargs Hbs Hirs2").
    iIntros (CIDf Hsf mf V' entry spv szv') "%Hcs2 %Hok Hcg Hcnt Hextc Hclmc Hpc
             Hbm Hins Hka2 Hpriv Hpath Hargv Hargs Hbs Hirs".
    iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
    iApply ("Hcont" $! mf V' entry spv szv'
              with "[%] [%] Hcg Hcnt Hextc Hclmc Hpc Hbm Hins Hka2 Hpriv Hpath
                    Hargv Hargs Hbs Hirs").
    - exact Hcs2.
    - exact Hok.
  Qed.

End KexecABad.

End KexecTailProof.

(* ===================================================================== *)
(*  PHASE C's SHARED [-1] TAIL, +0x1d6 .. +0x1f2.                         *)
(*                                                                        *)
(*  A second functor, wrapping [KexecTailProof] with one more module      *)
(*  ([PFP], proc_freepagetable's contract) that [kxc_exit_m1] itself does *)
(*  not need.  Keeping it a SEPARATE functor -- rather than adding [PFP]  *)
(*  to [KexecTailProof]'s own parameter list -- means phase A/B's existing*)
(*  instantiations (which have no [PFP] to hand) are untouched; phase C's *)
(*  own proof file opens this one instead, exactly as B3 opens B2's [A].  *)
(* ===================================================================== *)
Module KexecTailProofC (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                       (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                       (EndOp : END_OP) (PFP : PROC_FREEPAGETABLE).

Module T := KexecTailProof Myproc BeginOp Namei Ilock Readi Iunlockput EndOp.

Section KexecCBad.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ, !irefslotG Σ, !pavG Σ}.
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
  Notation Rs8 := (mword_of_int 24 : mword 5).
  Notation Rs9 := (mword_of_int 25 : mword 5).
  Notation Rs10 := (mword_of_int 26 : mword 5).
  Notation Rs11 := (mword_of_int 27 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).
  Notation Ra1 := (mword_of_int 11 : mword 5).

  Local Ltac regne := reg_ne_side.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.

  (* A local copy of [ProofKexecSeam.kxc_cs_cases] -- see that lemma's header
     for why a block ESTABLISHING a threading clause (rather than discharging
     one) needs the plain enumeration.  [ProofKexecSeam.v] REQUIRES this file,
     so importing it here is not an option; the fix the design doc records
     (hoist to [CalleeSaved.v]) is a 548-dependent-file cone and not owed by
     this one lemma -- promote on the next consumer that actually needs the
     recompile, per durable-notes' rule. *)
  Local Lemma kxc_cs_cases9 (r : mword 5) :
    is_cs_idx r = true ->
    r = csp_rs1 \/ r = Rs0 \/ r = Rs1 \/ r = Rs2 \/
    r = Rs3 \/ r = Rs4 \/ r = Rs5 \/ r = Rs6 \/
    r = Rs7 \/ r = Rs8 \/ r = Rs9 \/ r = Rs10 \/ r = Rs11.
  Proof.
    assert (Hsp : (mword_of_int 2 : mword 5) = csp_rs1)
      by (apply bv_eq; vm_compute; reflexivity).
    unfold is_cs_idx. cbn [existsb]. intro H.
    repeat match goal with
    | H : orb _ _ = true |- _ => apply orb_true_iff in H; destruct H as [H | H]
    end;
    first [ discriminate
          | apply bool_decide_eq_true_1 in H; rewrite ?Hsp in H; tauto ].
  Qed.

  (* =================================================================== *)
  (*  +0x1d6 .. +0x1f2 -- THE SECOND SHARED [-1] TAIL.  SIX PATHS reach it *)
  (*  (see claude-notes/projects/kexec.md's phase C design): the           *)
  (*  fall-through when uvmalloc's first call in phase C returns 0, the     *)
  (*  two two-instruction stubs at +0x358/+0x35c, and three branches inside *)
  (*  the argv loop (stack overflow, copyout failure, MAXARG).  Every path  *)
  (*  arrives with [s8] holding the size to free and [s6] the second       *)
  (*  table's root -- exactly [proc_freepagetable]'s two arguments -- and   *)
  (*  the frame's nine lazily-spilled slots untouched since phase B first   *)
  (*  spilled them.  Unlike [T.kxc_bad64] (only ever reloads slot 6), this  *)
  (*  reloads all NINE, because none of s3..s11 is read again after this.  *)
  (*  The inode is already closed by +0x1ae, so there is no iunlockput/     *)
  (*  end_op to do first -- this reaches [T.kxc_exit_m1] directly. *)
  (* =================================================================== *)
  Lemma kxc_bad_1d6
      (Q : mword 64 -> Prop)
      (jp : nat)
      (ga gf : gname) (bn : bio_names)
      (bmapstart inodestart : Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa dqpv dqas : dfrac)
      (m Mt : regfile) (K : nat) (eb : bool) (lks : gset string)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (P : uptd) (szf w13 : mword 64) :
    (K_kexec <= K)%nat ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 68 ->
    (* [s8], not [s3], since XV6_REV 7d258aa: the argv/ustack region's
       register allocation moved this live range (see the file header). *)
    Mt !!! Regidx Rs8 = szf ->
    Mt !!! Regidx Rs6 = page_base P.(ud_root) ->
    (* s11 is no longer reloaded in this epilogue (its spill/restore pair
       narrowed to the phdr loop at XV6_REV 7d258aa), so the caller has to
       say it still holds its entry value. *)
    Mt !!! Regidx Rs11 = m !!! Regidx Rs11 ->
    um_below szf P.(ud_um) ->
    um_covered szf P.(ud_um) ->
    sie_cap_gpr KT1 Mt (K - 68)%nat eb (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) eb lks -∗
    trap_csrs_ext KT1 eb -∗
    cpu_claim_ext eb (proc_addr jp) -∗
    kernel_text -∗
    pc_is (mword_of_int (KXA + 0x1d6) : mword 64) -∗
    proc_pt P -∗
    kalloc_env ga None -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    proc_priv gf (proc_addr jp) pidv V -∗
    ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
    ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
    ([∗ list] i ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
    bslots 3 -∗
    iref_slots 2 -∗
    (* SLOT 13 IS [w13], NOT [m !!! Regidx Rs11], at XV6_REV 7d258aa: on the
       phnum = 0 arm s11 is never spilled, so the slot keeps whatever it held
       on entry.  Nothing reads it -- the reload that used to is gone. *)
    kxc_frame_at sp0 ra0 s00 s10 s20
      (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
      (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
      (m !!! Regidx Rs9) (m !!! Regidx Rs10) w13 -∗
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok_q Q V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr KT1 mf K eb (proc_addr jp) -∗
          cpu_own 0 eb (proc_addr jp) eb lks -∗
          trap_csrs_ext KT1 eb -∗
          cpu_claim_ext eb (proc_addr jp) -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ[KT1]{dqpv} pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈[KT1]{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ{dqas} afun i j) -∗
          bslots 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hra Hs0 Hs1 Hs2 Hmtsp Hmts3 Hmts6 Hmts11 Hbelow Hcov.
    
    iIntros "Hcg Hcnt Hextc Hclmc #Htext Hpc Hpt #Hka Hbm Hins Hpriv Hpath Hargv
             Hargs Hbs Hirs Hframe Hcont".
    iDestruct (cpu_own_eb_agree with "Hcg Hcnt") as %Hebb.
    (* depth 0 forces the held set empty, so proc_freepagetable's order
       premise needs no hypothesis of this lemma's own. *)
    iDestruct (cpu_own_zero_empty with "Hcnt") as "[%Hlkempty Hcnt]".
    iDestruct (proc_pt_wf_get with "Hpt") as %Hwf.
    pose proof (proc_pt_covered_maxsz P szf Hwf Hcov) as Hmax.
    (* ---- +0x1d6: c.mv a1,s3 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x1d6)) Ra1 Rs8
              Mt (K - 68)%nat eb ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_1d6 with "Htext"). }
    iIntros (CID1 Hsc1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B1 := <[Regidx Ra1 := regval_into_reg
                  (add_vec zero_reg (Mt !!! Regidx Rs8))]> Mt).
    assert (HB1a1 : B1 !!! Regidx Ra1 = szf).
    { rewrite /B1 upd_eq Hmts3. apply add_vec_zero_l. }
    assert (HB1sp : B1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B1 upd_ne; [exact Hmtsp | nz]).
    assert (HB1s6 : B1 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /B1 upd_ne; [exact Hmts6 | nz]).
    assert (Hpp1d8 : add_vec_int (mword_of_int (KXA + 0x1d6) : mword 64) 2
                     = mword_of_int (KXA + 0x1d8)) by pcw.
    iEval (rewrite Hpp1d8) in "Hpc".
    (* ---- +0x1d8: c.mv a0,s6 ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x1d8)) Ra0 Rs6
              B1 (K - 68)%nat eb ltac:(nz) ltac:(rdok)
              with "Hcg Hpc []").
    { iApply (kxc_1d8 with "Htext"). }
    iIntros (CID2 Hsc2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (B2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (B1 !!! Regidx Rs6))]> B1).
    assert (HB2a0 : B2 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /B2 upd_eq HB1s6. apply add_vec_zero_l. }
    assert (HB2a1 : B2 !!! Regidx Ra1 = szf)
      by (rewrite /B2 upd_ne; [exact HB1a1 | nz]).
    assert (HB2sp : B2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B2 upd_ne; [exact HB1sp | nz]).
    assert (Hpp1da : add_vec_int (mword_of_int (KXA + 0x1d8) : mword 64) 2
                     = mword_of_int (KXA + 0x1da)) by pcw.
    iEval (rewrite Hpp1da) in "Hpc".
    (* ---- +0x1da: jal ra,proc_freepagetable ---- *)
    assert (Htpfp : add_vec (mword_of_int (KXA + 0x1da) : mword 64)
                     (sign_extend' 64 (mword_of_int 2085078 : mword 21))
                   = mword_of_int KernelSyms.proc_freepagetable) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x1da)) Rra
              (mword_of_int 2085078 : mword 21) B2 (K - 68)%nat eb
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htpfp; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_1da with "Htext"). }
    iIntros (CID3 Hsc3) "Hcg Hpc". iEval (rewrite Htpfp) in "Hpc".
    set (B3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x1da) : mword 64) 4)]> B2).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x1da) : mword 64) 4)]> B2) with B3.
    assert (HB3ra : B3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x1da) : mword 64) 4)
      by (rewrite /B3; apply upd_eq).
    assert (HB3a0 : B3 !!! Regidx Ra0 = page_base P.(ud_root))
      by (rewrite /B3 upd_ne; [exact HB2a0 | nz]).
    assert (HB3a1 : B3 !!! Regidx Ra1 = szf)
      by (rewrite /B3 upd_ne; [exact HB2a1 | nz]).
    assert (HB3sp : B3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B3 upd_ne; [exact HB2sp | nz]).
    iDestruct (cpu_own_transport CID0 CID3 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID0 CID3 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID0 CID3 eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iApply (PFP.wp_proc_freepagetable_sconf ga B3 P (K - 68)%nat eb
              (proc_addr jp) 0%nat eb lks
              ltac:(lia) ltac:(lia) HB3a0
              ltac:(rewrite HB3a1 uint_unsigned; exact Hmax)
              ltac:(rewrite HB3a1; exact Hbelow)
              ltac:(lkbelow)
              with "Hcg Hcnt Htext Hpc Hpt Hka").
    iIntros (CID4 Hsc4 M1) "Hcg Hcnt Hpc %Hcs1".
    assert (Hpc1de : ret_pc (B3 !!! Regidx Rra) = mword_of_int (KXA + 0x1de))
      by (rewrite HB3ra; pcw).
    iEval (rewrite Hpc1de) in "Hpc".
    assert (HM1sp : M1 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcs1 csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HB3sp. }
    (* s11 is callee-saved across proc_freepagetable and is not written
       anywhere in this phase, so its entry value survives to the epilogue --
       which is what pays for the reload gcc dropped at XV6_REV 7d258aa. *)
    assert (HM1s11 : M1 !!! Regidx Rs11 = m !!! Regidx Rs11).
    { rewrite (callee_saved_lookup Hcs1 Rs11 ltac:(vm_compute; reflexivity)).
      rewrite /B3 upd_ne; [| nz]. rewrite /B2 upd_ne; [| nz].
      rewrite /B1 upd_ne; [| nz]. exact Hmts11. }
    (* ---- +0x1de: c.li a0,-1 ---- *)
    iApply (wp_cli_s_sconf (mword_of_int (KXA + 0x1de)) Ra0
              (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
              M1 (K - 68)%nat eb ltac:(nz) ltac:(rdok)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_1de with "Htext"). }
    iIntros (CID5 Hsc5) "Hcg Hpc".
    set (B4 := <[Regidx Ra0 := regval_into_reg
                  (mword_of_int (-1) : mword 64)]> M1).
    assert (HB4sp : B4 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B4 upd_ne; [exact HM1sp | nz]).
    assert (HB4a0 : B4 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by (rewrite /B4; apply upd_eq).
    assert (Hpp1e0 : add_vec_int (mword_of_int (KXA + 0x1de) : mword 64) 2
                     = mword_of_int (KXA + 0x1e0)) by pcw.
    iEval (rewrite Hpp1e0) in "Hpc".
    (* ---- +0x1e0 .. +0x1f0: reload s3..s11 from their spill slots ---- *)
    rewrite /kxc_frame_at.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 & Hf9 &
                            Hf10 & Hf11 & Hf12 & Hf13 & Hrest)".
    (* ---- +0x1e0: c.ldsp s3,504(sp) -- slot 5 back into s3 ---- *)
    assert (Hpa5 : add_vec (B4 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 63 : mword 6) ('b"000")))
                   = pa_stk sp0 5) by (rewrite HB4sp; apply kxc_slot5_sp).
    iEval (rewrite -Hpa5) in "Hf5".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXA + 0x1e0)) (mword_of_int 63 : mword 6)
              Rs3 B4 (K - 68)%nat (m !!! Regidx Rs3) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf5").
    { iApply (kxc_1e0 with "Htext"). }
    iIntros (CID6 Hs7c) "Hcg Hpc Hf5". iEval (rewrite Hpa5) in "Hf5".
    set (B5 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> B4).
    assert (Hpp1e2 : add_vec_int (mword_of_int (KXA + 0x1e0) : mword 64) 2
                     = mword_of_int (KXA + 0x1e2)) by pcw.
    iEval (rewrite Hpp1e2) in "Hpc".
    assert (HB5sp : B5 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B5 upd_ne; [exact HB4sp | nz]).
    assert (HB5a0 : B5 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by (rewrite /B5 upd_ne; [exact HB4a0 | nz]).
    (* ---- +0x1e2: c.ldsp s4,496(sp) -- slot 6 back into s4 ---- *)
    assert (Hpa6 : add_vec (B5 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 62 : mword 6) ('b"000")))
                   = pa_stk sp0 6) by (rewrite HB5sp; apply kxc_slot6_sp).
    iEval (rewrite -Hpa6) in "Hf6".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXA + 0x1e2)) (mword_of_int 62 : mword 6)
              Rs4 B5 (K - 68)%nat (m !!! Regidx Rs4) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf6").
    { iApply (kxc_1e2 with "Htext"). }
    iIntros (CID7 Hs8c) "Hcg Hpc Hf6". iEval (rewrite Hpa6) in "Hf6".
    set (B6 := <[Regidx Rs4 := regval_into_reg (m !!! Regidx Rs4)]> B5).
    assert (Hpp1e4 : add_vec_int (mword_of_int (KXA + 0x1e2) : mword 64) 2
                     = mword_of_int (KXA + 0x1e4)) by pcw.
    iEval (rewrite Hpp1e4) in "Hpc".
    assert (HB6sp : B6 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B6 upd_ne; [exact HB5sp | nz]).
    assert (HB6a0 : B6 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by (rewrite /B6 upd_ne; [exact HB5a0 | nz]).
    (* ---- +0x1e4: c.ldsp s5,488(sp) -- slot 7 back into s5 ---- *)
    assert (Hpa7 : add_vec (B6 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 61 : mword 6) ('b"000")))
                   = pa_stk sp0 7) by (rewrite HB6sp; apply kxc_slot7_sp).
    iEval (rewrite -Hpa7) in "Hf7".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXA + 0x1e4)) (mword_of_int 61 : mword 6)
              Rs5 B6 (K - 68)%nat (m !!! Regidx Rs5) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf7").
    { iApply (kxc_1e4 with "Htext"). }
    iIntros (CID8 Hs9c) "Hcg Hpc Hf7". iEval (rewrite Hpa7) in "Hf7".
    set (B7 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5)]> B6).
    assert (Hpp1e6 : add_vec_int (mword_of_int (KXA + 0x1e4) : mword 64) 2
                     = mword_of_int (KXA + 0x1e6)) by pcw.
    iEval (rewrite Hpp1e6) in "Hpc".
    assert (HB7sp : B7 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B7 upd_ne; [exact HB6sp | nz]).
    assert (HB7a0 : B7 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by (rewrite /B7 upd_ne; [exact HB6a0 | nz]).
    (* ---- +0x1e6: c.ldsp s6,480(sp) -- slot 8 back into s6 ---- *)
    assert (Hpa8 : add_vec (B7 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 60 : mword 6) ('b"000")))
                   = pa_stk sp0 8) by (rewrite HB7sp; apply kxc_slot8_sp).
    iEval (rewrite -Hpa8) in "Hf8".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXA + 0x1e6)) (mword_of_int 60 : mword 6)
              Rs6 B7 (K - 68)%nat (m !!! Regidx Rs6) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf8").
    { iApply (kxc_1e6 with "Htext"). }
    iIntros (CID9 Hs10c) "Hcg Hpc Hf8". iEval (rewrite Hpa8) in "Hf8".
    set (B8 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> B7).
    assert (Hpp1e8 : add_vec_int (mword_of_int (KXA + 0x1e6) : mword 64) 2
                     = mword_of_int (KXA + 0x1e8)) by pcw.
    iEval (rewrite Hpp1e8) in "Hpc".
    assert (HB8sp : B8 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B8 upd_ne; [exact HB7sp | nz]).
    assert (HB8a0 : B8 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by (rewrite /B8 upd_ne; [exact HB7a0 | nz]).
    (* ---- +0x1e8: c.ldsp s7,472(sp) -- slot 9 back into s7 ---- *)
    assert (Hpa9 : add_vec (B8 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 59 : mword 6) ('b"000")))
                   = pa_stk sp0 9) by (rewrite HB8sp; apply kxc_slot9_sp).
    iEval (rewrite -Hpa9) in "Hf9".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXA + 0x1e8)) (mword_of_int 59 : mword 6)
              Rs7 B8 (K - 68)%nat (m !!! Regidx Rs7) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf9").
    { iApply (kxc_1e8 with "Htext"). }
    iIntros (CID10 Hs11c) "Hcg Hpc Hf9". iEval (rewrite Hpa9) in "Hf9".
    set (B9 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> B8).
    assert (Hpp1ea : add_vec_int (mword_of_int (KXA + 0x1e8) : mword 64) 2
                     = mword_of_int (KXA + 0x1ea)) by pcw.
    iEval (rewrite Hpp1ea) in "Hpc".
    assert (HB9sp : B9 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B9 upd_ne; [exact HB8sp | nz]).
    assert (HB9a0 : B9 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by (rewrite /B9 upd_ne; [exact HB8a0 | nz]).
    (* ---- +0x1ea: c.ldsp s8,464(sp) -- slot 10 back into s8 ---- *)
    assert (Hpa10 : add_vec (B9 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 58 : mword 6) ('b"000")))
                   = pa_stk sp0 10) by (rewrite HB9sp; apply kxc_slot10_sp).
    iEval (rewrite -Hpa10) in "Hf10".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXA + 0x1ea)) (mword_of_int 58 : mword 6)
              Rs8 B9 (K - 68)%nat (m !!! Regidx Rs8) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf10").
    { iApply (kxc_1ea with "Htext"). }
    iIntros (CID11 Hs12c) "Hcg Hpc Hf10". iEval (rewrite Hpa10) in "Hf10".
    set (B10 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8)]> B9).
    assert (Hpp1ec : add_vec_int (mword_of_int (KXA + 0x1ea) : mword 64) 2
                     = mword_of_int (KXA + 0x1ec)) by pcw.
    iEval (rewrite Hpp1ec) in "Hpc".
    assert (HB10sp : B10 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B10 upd_ne; [exact HB9sp | nz]).
    assert (HB10a0 : B10 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by (rewrite /B10 upd_ne; [exact HB9a0 | nz]).
    (* ---- +0x1ec: c.ldsp s9,456(sp) -- slot 11 back into s9 ---- *)
    assert (Hpa11 : add_vec (B10 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 57 : mword 6) ('b"000")))
                   = pa_stk sp0 11) by (rewrite HB10sp; apply kxc_slot11_sp).
    iEval (rewrite -Hpa11) in "Hf11".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXA + 0x1ec)) (mword_of_int 57 : mword 6)
              Rs9 B10 (K - 68)%nat (m !!! Regidx Rs9) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf11").
    { iApply (kxc_1ec with "Htext"). }
    iIntros (CID12 Hs13c) "Hcg Hpc Hf11". iEval (rewrite Hpa11) in "Hf11".
    set (B11 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9)]> B10).
    assert (Hpp1ee : add_vec_int (mword_of_int (KXA + 0x1ec) : mword 64) 2
                     = mword_of_int (KXA + 0x1ee)) by pcw.
    iEval (rewrite Hpp1ee) in "Hpc".
    assert (HB11sp : B11 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B11 upd_ne; [exact HB10sp | nz]).
    assert (HB11a0 : B11 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by (rewrite /B11 upd_ne; [exact HB10a0 | nz]).
    (* ---- +0x1ee: c.ldsp s10,448(sp) -- slot 12 back into s10 ---- *)
    assert (Hpa12 : add_vec (B11 !!! Regidx csp_rs1)
                     (zero_extend' 64 (concat_vec (mword_of_int 56 : mword 6) ('b"000")))
                   = pa_stk sp0 12) by (rewrite HB11sp; apply kxc_slot12_sp).
    iEval (rewrite -Hpa12) in "Hf12".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXA + 0x1ee)) (mword_of_int 56 : mword 6)
              Rs10 B11 (K - 68)%nat (m !!! Regidx Rs10) eb (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc [] Hf12").
    { iApply (kxc_1ee with "Htext"). }
    iIntros (CID13 Hs14c) "Hcg Hpc Hf12". iEval (rewrite Hpa12) in "Hf12".
    set (B12 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10)]> B11).
    assert (Hpp1f0 : add_vec_int (mword_of_int (KXA + 0x1ee) : mword 64) 2
                     = mword_of_int (KXA + 0x1f0)) by pcw.
    iEval (rewrite Hpp1f0) in "Hpc".
    assert (HB12sp : B12 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /B12 upd_ne; [exact HB11sp | nz]).
    assert (HB12a0 : B12 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by (rewrite /B12 upd_ne; [exact HB11a0 | nz]).
    (* THE s11 RELOAD IS GONE FROM THIS EPILOGUE at XV6_REV 7d258aa.  gcc
       narrowed s11's live range to the phdr loop: the reload now sits at
       +0x1a2, on the loop's exit edge, and every path that reaches here has
       already passed it (or never spilled s11 at all, on the phnum = 0 arm).
       So s11 holds [m !!! Regidx Rs11] on arrival and the threading clause
       below takes it from the caller's [Hmts11] instead of from a reload. *)
    set (B13 := B12).
    assert (HB13sp : B13 !!! Regidx csp_rs1 = pa_stk sp0 68) by exact HB12sp.
    assert (HB13a0 : B13 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
      by exact HB12a0.
    (* ---- +0x1f0: c.j +0x72 -- into the shared epilogue ---- *)
    assert (Htgt72 : add_vec (mword_of_int (KXA + 0x1f0) : mword 64)
              (sign_extend' 64 (sign_extend' 21 (concat_vec
                 (mword_of_int 1857 : mword 11) ('b"0"))))
            = mword_of_int (KXA + 0x072)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (KXA + 0x1f0))
              (sign_extend' 21 (concat_vec (mword_of_int 1857 : mword 11)
                                           ('b"0")))
              B13 (K - 68)%nat eb
              ltac:(rewrite Htgt72; vm_compute; reflexivity)
              with "Hcg Hpc []").
    { iApply (kxc_1f0 with "Htext"). }
    iIntros (CIDj Hscj). iNext. iIntros "Hcg Hpc".
    iEval (rewrite Htgt72) in "Hpc".
    (* ---- the threading clause: all NINE slots came back from THIS block's
       own reload, not from an external premise -- [kxc_cs_cases9] lands the
       symbolic [r] on the one register each case is really about. ---- *)
    assert (HB13thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> B13 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2.
      destruct (kxc_cs_cases9 r Hr)
        as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
           [-> | [-> | ->]]]]]]]]]]]];
        try (exfalso; congruence).
      - rewrite /B13. rewrite /B12 upd_ne; [| nz]. rewrite /B11 upd_ne; [| nz]. rewrite /B10 upd_ne; [| nz]. rewrite /B9 upd_ne; [| nz]. rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_ne; [| nz]. rewrite /B6 upd_ne; [| nz]. rewrite /B5; apply upd_eq.
      - rewrite /B13. rewrite /B12 upd_ne; [| nz]. rewrite /B11 upd_ne; [| nz]. rewrite /B10 upd_ne; [| nz]. rewrite /B9 upd_ne; [| nz]. rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_ne; [| nz]. rewrite /B6; apply upd_eq.
      - rewrite /B13. rewrite /B12 upd_ne; [| nz]. rewrite /B11 upd_ne; [| nz]. rewrite /B10 upd_ne; [| nz]. rewrite /B9 upd_ne; [| nz]. rewrite /B8 upd_ne; [| nz]. rewrite /B7; apply upd_eq.
      - rewrite /B13. rewrite /B12 upd_ne; [| nz]. rewrite /B11 upd_ne; [| nz]. rewrite /B10 upd_ne; [| nz]. rewrite /B9 upd_ne; [| nz]. rewrite /B8; apply upd_eq.
      - rewrite /B13. rewrite /B12 upd_ne; [| nz]. rewrite /B11 upd_ne; [| nz]. rewrite /B10 upd_ne; [| nz]. rewrite /B9; apply upd_eq.
      - rewrite /B13. rewrite /B12 upd_ne; [| nz]. rewrite /B11 upd_ne; [| nz]. rewrite /B10; apply upd_eq.
      - rewrite /B13. rewrite /B12 upd_ne; [| nz]. rewrite /B11; apply upd_eq.
      - rewrite /B13. rewrite /B12; apply upd_eq.
      - (* s11: NOT reloaded here since XV6_REV 7d258aa -- untouched all the
           way down to [Mt], where the caller's [Hmts11] pins it. *)
        rewrite /B13.
        rewrite /B12 upd_ne; [| nz]. rewrite /B11 upd_ne; [| nz].
        rewrite /B10 upd_ne; [| nz]. rewrite /B9 upd_ne; [| nz].
        rewrite /B8 upd_ne; [| nz]. rewrite /B7 upd_ne; [| nz].
        rewrite /B6 upd_ne; [| nz]. rewrite /B5 upd_ne; [| nz].
        rewrite /B4 upd_ne; [| nz]. exact HM1s11. }
    (* ---- reassemble [kxc_frame]: the reload only moved register CONTENTS,
       the frame's memory cells are exactly what [kxc_frame_at] handed in ---- *)
    iAssert (kxc_frame sp0 ra0 s00 s10 s20)
      with "[Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hf9 Hf10 Hf11 Hf12 Hf13 Hrest]"
      as "Hfr".
    { rewrite /kxc_frame.
      iSplitL "Hf1"; [iExact "Hf1" |].
      iSplitL "Hf2"; [iExact "Hf2" |].
      iSplitL "Hf3"; [iExact "Hf3" |].
      iSplitL "Hf4"; [iExact "Hf4" |].
      iSplitL "Hf5"; [by iExists (m !!! Regidx Rs3) |].
      iSplitL "Hf6"; [by iExists (m !!! Regidx Rs4) |].
      iSplitL "Hf7"; [by iExists (m !!! Regidx Rs5) |].
      iSplitL "Hf8"; [by iExists (m !!! Regidx Rs6) |].
      iSplitL "Hf9"; [by iExists (m !!! Regidx Rs7) |].
      iSplitL "Hf10"; [by iExists (m !!! Regidx Rs8) |].
      iSplitL "Hf11"; [by iExists (m !!! Regidx Rs9) |].
      iSplitL "Hf12"; [by iExists (m !!! Regidx Rs10) |].
      (* slot 13 carries [w13] now, not [m !!! Regidx Rs11] *)
      iSplitL "Hf13"; [by iExists w13 |].
      iExact "Hrest". }
    (* ---- hand the caller's exit continuation, and [Hcnt], across to the
       hart the jump resumed on -- both are still anchored where they were
       last established (the section's [CID0] for [Hcont], [CID3] for
       [Hcnt]), and [T.kxc_exit_m1]'s own implicit hart is unified from
       whichever it is applied with (durable-notes' "CHAINING TWO HALVES"). *)
    assert (Hcr : true = false \/ proc_addr jp = zero_reg ->
                   (CIDj : CPU) = (CID0 : CPU)) by wp_next_chain.
    iDestruct (wp_next_retarget CID0 CIDj true (proc_addr jp) _ Hcr
                 with "Hcont") as "Hcont".
    iDestruct (cpu_own_transport CID4 CIDj 0%nat eb (proc_addr jp) eb
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct (trap_csrs_ext_transport CID3 CIDj eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hextc") as "Hextc".
    iDestruct (cpu_claim_ext_transport CID3 CIDj eb (proc_addr jp)
                 ltac:(try rewrite Hebb; wp_next_chain) with "Hclmc") as "Hclmc".
    iApply (T.kxc_exit_m1 Q (proc_addr jp) bn ga gf bmapstart
              inodestart plen pfun na avf alen aslen afun pidv V
              dqb dqs dqa dqpv dqas m B13 K eb eb lks sp0 ra0 s00 s10 s20 pv av
              ltac:(lia) Hsp Hra Hs0 Hs1 Hs2 HB13sp HB13a0 HB13thr
              with "Hcg Hcnt Hextc Hclmc Htext Hpc Hfr Hbm Hins Hka Hpriv Hpath Hargv
                    Hargs Hbs Hirs Hcont").
  Qed.

End KexecCBad.

End KexecTailProofC.
