(* ProofKexecA.v -- PHASE A of kexec: [kexec+0x000] .. [kexec+0x08e], i.e.
   the prologue, myproc / begin_op / namei / ilock / readi, the ELF magic
   test, and the two [bad:] tails that are reachable from them.

     +0x000  addi sp,sp,-544          } BASE-encoded: 544 is past c.addi16sp's
     +0x004  sd   ra,536(sp)          } +-512 and 536 past c.sdsp's 504 --
     +0x008  sd   s0,528(sp)          } kexec is the only function in the tree
     +0x00c  sd   s1,520(sp)          } of which that is true (kexec.md).
     +0x010  sd   s2,512(sp)          } slots 1,2,3,4 = ra,s0,s1,s2
     +0x014  addi s0,sp,544           s0 = sp0
     +0x016  mv   s2,a0               s2 = path
     +0x018  sd   a0,-528(s0)         spill path  -> slot 66
     +0x01c  sd   a1,-512(s0)         spill argv  -> slot 64
     +0x020  jal  myproc              -> a0 = pj
     +0x024  mv   s1,a0
     +0x026  jal  begin_op            -> log_op g MAXOPBLOCKS
     +0x02a  mv   a0,s2
     +0x02c  jal  namei               -> a0 = ip, or 0
     +0x030  beqz a0, +0x88           namei failed
     +0x032  sd   s4,496(sp)          LAZY spill of s4 -> slot 6
     +0x034  mv   s4,a0               s4 = ip
     +0x036  jal  ilock
     +0x03a  li   a4,64               n    = 64
     +0x03e  li   a3,0                off  = 0
     +0x040  addi a2,s0,-432          dst  = &elf = pa_stk sp0 54
     +0x044  li   a1,0                user = 0     <- readi's KERNEL arm
     +0x046  mv   a0,s4
     +0x048  jal  readi
     +0x04c  li   a5,64
     +0x050  bne  a0,a5, +0x64        short read -> bad
     +0x054  lw   a4,-432(s0)         elf.magic
     +0x058  lui  a5,0x464c4
     +0x05c  addi a5,a5,1407          a5 = 0x464c457f = ELF_MAGIC
     +0x060  beq  a4,a5, +0x90        magic ok -> PHASE B
     [+0x064 bad:]  mv a0,s4 ; jal iunlockput ; jal end_op ; li a0,-1 ;
                    ld s4,496(sp) ; fall into the epilogue
     [+0x072 epilogue -- ProofKexecParts.kxc_epi_frame]
     [+0x088 namei-null tail:]  jal end_op ; li a0,-1 ; j +0x72

   ---- STATUS -----------------------------------------------------------

   PROVEN HERE: the frame algebra, [kxc_prologue] (+0x000..+0x01c),
   [kxc_exit_m1] (the shared -1 exit at +0x072), the seam [kxc_at_a2], and
   [kxc_a1] -- +0x000 .. +0x030 INCLUDING the namei-null tail at +0x088,
   which closes kexec's own failure arm.  No [admit] / [Admitted] / [Axiom].

   NOT YET WRITTEN: [kxc_a2] (+0x032 .. +0x08e, owning the +0x064 tail) and
   [kxc_phaseA].  Everything they need that is not mechanical is proved
   below: [kxc_slot6_sp] (496(sp), for the s4 spill and its reload),
   [kxc_elf_acc] (the elf buffer borrowed as 64 NAMED bytes for readi and
   given back), [kxc_word4_of_named] / [kxc_named_of_word4] (the [lw] at
   +0x054), [kxc_seq_split_4], and [kxc_exit_m1] itself.

   TWO THINGS THAT MAKE [kxc_a2] SMALLER THAN IT LOOKS, and both are worth
   knowing before writing it:

   * NEITHER COMPARISON NEEDS BIT-LEVEL REASONING.  The [bne a0,64] at
     +0x050 and the [beq a4,a5] at +0x060 are BLIND case splits: both arms
     are handled (fall through to +0x090, or take the +0x064 tail), and
     neither seam has to say WHY.  In particular the +0x090 state does NOT
     need [ElfEnc.eh_magic_ok] -- kexec's contract says nothing about the
     file being a valid ELF, so nothing downstream consumes it -- and it
     does not need [tot = 64] either, because the buffer's contents are
     existential at every seam anyway.  Splitting on
     [destruct (eq_vec ...) eqn:E] and using the fall/taken leaf pair is the
     whole of it.
   * THE OPEN INODE TRAVELS AS ONE BUNDLE (kexec.md convention 4): what
     ilock produces and iunlockput consumes is [sleeplocked], [sl_pid],
     [ic_deposit], the two 1/2 identity cells, [i_valid], [ic_loaded] and
     the retained [inode_ref_short].  readi peels [ic_loaded] into
     [inode_meta] / [inode_map] / [inode_blocks] and hands them back
     LITERALLY unchanged, so the re-assembly re-uses the pure conjuncts
     verbatim (ProofFileread.v ~:1995).

   ---- WHAT TO DO FIRST IN EVERY PHASE LEMMA (adopted; B, C and D too) ----

   PIN [b = eb = true] BEFORE ANYTHING ELSE, with [kxc_sie_b_agree] below
   (ProofFileclose's / ProofIput's [sie_b_agree], verbatim):

       iDestruct (kxc_sie_b_agree m 0%nat K eb b pj C with "Hcg Hcnt") as %Ho.
       subst eb. cbn in Ho. subst b.

   [sie_cap_gpr]'s SIE eighth and [cpu_own]'s [cpu_hart] are two
   presentations of the same bit, so at [n = 0] this reads [b = eb] straight
   off the precondition and kexec's [eb = true] premise then pins it.  It is
   not a convenience: every parking callee (namei, ilock, readi, end_op)
   publishes [wp_next TRUE], and [WpNext.wp_next_chain] cannot produce the
   [pj = zero_reg] disjunct from a SYMBOLIC [b] -- so without this step the
   very first [cpu_own_transport] after namei is unprovable, and
   [wp_kexec_sconf_body]'s own [wp_next b pj] could never be closed.

   ---- ESCALATION: [ProcInv.cwd_ref] AND [SpecNamei] ARE AT DIFFERENT
        [icacheG] INSTANCES ------------------------------------------------

   [FileInvDefs.fileG] BUNDLES [icacheG] and [icfg] as field instances
   ([file_icacheG ::], [file_icfg ::]).  So a context that binds BOTH
   [!fileG Σ] and a standalone [!icacheG Σ] / [ICFG : icfg] -- which is
   exactly what SpecNamei.v:90-93 does, and what SpecKexec.v copied -- has
   TWO [icacheG]s, and durable-notes.md's second typeclass trap is live:

     * [ProcInv.cwd_ref] (ProcInv.v:613) elaborates its [inode_held] through
       [fileG] (ProcInv's own Context has no standalone [icacheG]);
     * [SpecNamei]'s [inode_held cwdv] premise elaborates through the
       standalone one.

   The two print IDENTICALLY and do not unify: machine-checked, the wand
   [cwd_ref v -∗ inode_held v] fails with "iFrame: cannot frame (cwd_ref v)"
   in a context binding both, and closes by [iIntros "$"] in a context
   binding only [fileG].  kexec is the FIRST caller to hand a process's
   working-directory reference to namei, which is why this has never fired.

   THE FIX IS SpecNamei.v's (and then SpecNamex / SpecNameiparent /
   SpecKexec, and any Spec in that chain that binds both): DROP the
   standalone [ICFG : icfg, !icacheG Σ] and let [!fileG Σ] supply them --
   durable-notes' recorded remedy, and the same edit the kfork chain and
   fileread already took.  It changes the [Module Type] binder lists, so it
   is a Spec-level change and not this file's to make.

   WHAT THIS FILE DOES INSTEAD, and why it is exactly the post-fix shape:
   the two proof Sections below bind [!fileG Σ] and NOT [!icacheG Σ] /
   [ICFG].  Every [icacheG] in sight is then [file_icacheG], [cwd_ref]
   matches [inode_held], and the callee contracts (whose Module Type
   Parameters quantify over ALL [icacheG]) are instantiated at that one.
   So [kxc_a1] is proved TODAY and will need no edit once the Specs are
   fixed.  What CANNOT be built until they are is the capstone: discharging
   [KEXEC]'s Parameter requires the body at an ARBITRARY standalone
   [icacheG], and at a mismatched one [wp_kexec_sconf_body] is not merely
   unprovable but incoherent -- it asks for FS invariants at one icache and
   a process whose cwd reference is at another.

   ---- THE SEAM, AND HOW IT DIFFERS FROM THE BRIEF ------------------------

   [kxc_at_a2] carries the frame's slots 14..63 as ONE [stack_own] chunk
   rather than as the three pre-made [bytes_own] carves.  That is a
   deliberate simplification and it is the better currency at a block
   boundary: the epilogue ([ProofKexecParts.kxc_epi_frame], through
   [kxc_frame]) wants [stack_own (pa_stk sp0 13) 55] BACK, so a seam stated
   in bytes would have to be re-slotted at every exit -- and re-slotting
   needs the per-slot alignment facts, which a byte run does not carry.
   Whichever half wants a buffer carves it itself, at the one place it is
   used, with [ProofKexecParts.kxc_slots_elf] / [kxc_slots_ph] /
   [kxc_slots_ustack] over [kxc_slots_asc] below.  Nothing is lost: the
   chunk determines the three carves and they do not determine it. *)
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
Require Import RiscvExtras.
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
Require Import WpSconfAlu WpSconfMem WpSconfCtl WpSconfBtype.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import WpLock.
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
Require Import ProcInv.
Require Import DiskPtsto.
Require Import BioInv.
Require Import FsBlocks LogInv.
Require Import BitmapInv.
Require Import DirentEnc.
Require Import PathElems.
Require Import InodeInv.
Require Import IrefSlots.
Require Import IcacheRef.
Require Import IcacheInv.
Require Import KallocInv.
Require Import KvmSpec.
Require Import ProcInv.
Require Import FileInvDefs.
Require Import SpecIput.
Require Import SpecKexec.
Require Import SpecMyproc.
Require Import SpecBeginOp.
Require Import SpecEndOp.
Require Import SpecIlock.
Require Import SpecReadi.
Require Import SpecIunlockput.
Require Import SpecDirlink.
Require Import SpecNamei.
Require Import ProofKexecParts.
Require Import CodeKexec.
From Kernel Require KernelSyms.
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
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma kxc_slots_asc (sp0 : mword 64) (n j : nat) :
    stack_own (pa_stk sp0 j) n ⊣⊢
    ([∗ list] i ∈ seq 1 n,
       ∃ w : mword 64, word_pointsto (pa_stk sp0 (j + i)) (DfracOwn 1) w)%I.
  Proof.
    rewrite stack_own_slots.
    apply big_sepL_proper. intros k i _.
    by rewrite pa_stk_assoc.
  Qed.

  (* the eight elf slots, in the DESCENDING order [kxc_slots_elf] wants.
     Eight conjuncts, so the reordering is eight lines rather than a
     permutation lemma over [big_sepL] (whose [Φ] would have to be given
     explicitly -- durable-notes' big-op rule). *)
  Lemma kxc_elf_slots_of_stack (sp0 : mword 64) :
    stack_own (pa_stk sp0 46) 8 ⊢
    [∗ list] i ∈ seq 0 8, ∃ w : mword 64, word_pointsto (pa_stk sp0 (54 - i)) (DfracOwn 1) w.
  Proof.
    rewrite (kxc_slots_asc sp0 8 46). cbn [seq big_opL].
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _)".
    cbn [Nat.add Nat.sub].
    iFrame "H8 H7 H6 H5 H4 H3 H2 H1".
  Qed.

  Lemma kxc_stack_of_elf_slots (sp0 : mword 64) :
    ([∗ list] i ∈ seq 0 8, ∃ w : mword 64, word_pointsto (pa_stk sp0 (54 - i)) (DfracOwn 1) w)
    ⊢ stack_own (pa_stk sp0 46) 8.
  Proof.
    rewrite (kxc_slots_asc sp0 8 46). cbn [seq big_opL Nat.add Nat.sub].
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _)".
    iFrame "H8 H7 H6 H5 H4 H3 H2 H1".
  Qed.

  (* ---- the five top slots (64..68), individually ---- *)
  Lemma kxc_top5_of_stack (sp0 : mword 64) :
    stack_own (pa_stk sp0 63) 5 ⊢
    (∃ w : mword 64, word_pointsto (pa_stk sp0 64) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 65) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 66) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 67) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 68) (DfracOwn 1) w).
  Proof.
    rewrite (kxc_slots_asc sp0 5 63). cbn [seq big_opL Nat.add].
    iIntros "(H1 & H2 & H3 & H4 & H5 & _)". iFrame.
  Qed.

  Lemma kxc_stack_of_top5 (sp0 : mword 64) (w64 w65 w66 w67 w68 : mword 64) :
    word_pointsto (pa_stk sp0 64) (DfracOwn 1) w64 -∗
    word_pointsto (pa_stk sp0 65) (DfracOwn 1) w65 -∗
    word_pointsto (pa_stk sp0 66) (DfracOwn 1) w66 -∗
    word_pointsto (pa_stk sp0 67) (DfracOwn 1) w67 -∗
    word_pointsto (pa_stk sp0 68) (DfracOwn 1) w68 -∗
    stack_own (pa_stk sp0 63) 5.
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
    stack_own sp0 13 ⊢
    (∃ w : mword 64, word_pointsto (pa_stk sp0 1) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 2) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 3) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 4) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 5) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 6) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 7) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 8) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 9) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 10) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 11) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 12) (DfracOwn 1) w) ∗
    (∃ w : mword 64, word_pointsto (pa_stk sp0 13) (DfracOwn 1) w).
  Proof.
    rewrite stack_own_slots. cbn [seq big_opL].
    iIntros "(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12
              & H13 & _)".
    iFrame.
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

  (* ---- THE ELF BUFFER, borrowed as 64 NAMED bytes and given back. ----

     ONE accessor rather than two lemmas, for [ByteBuf.bb_word_acc]'s
     reason: the per-slot 8-alignment facts are what the rebuild needs and a
     byte run no longer carries them, so they have to be captured BEFORE the
     split.  readi's destination is the named form, hence the [∃ f]. *)
  Lemma kxc_elf_acc (sp0 : mword 64) :
    stack_own (pa_stk sp0 46) 8 ⊢
    (∃ f : nat -> bv 8,
       [∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ f j) ∗
    (∀ g : nat -> bv 8,
       ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ g j) -∗
       stack_own (pa_stk sp0 46) 8).
  Proof.
    iIntros "H".
    iDestruct (kxc_elf_slots_of_stack with "H") as "H".
    iDestruct (kxc_slots_elf sp0 with "H") as "[%Hal Hb]".
    iSplitL "Hb".
    - iApply (bb_any_named (pa_stk sp0 54) 64). rewrite /bytes_own /byte_any.
      iExact "Hb".
    - iIntros (g) "Hg".
      iApply kxc_stack_of_elf_slots.
      iApply (kxc_bytes_elf sp0 Hal).
      rewrite /bytes_own. iApply (bb_named_any with "Hg").
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
    ([∗ list] j ∈ seq 0 4, pa_add a j ↦ₘ g j) ⊢
    word4_pointsto a (DfracOwn 1) (Z_to_bv 32 (le_at g 0 4)).
  Proof.
    intro Hal. iIntros "H".
    iApply (word4_pointsto_intro a (DfracOwn 1) _ Hal).
    iApply (big_sepL_impl with "H"). iIntros "!>" (i j Hij) "Hb".
    assert (Hj : (j < 4)%nat).
    { apply lookup_seq in Hij. lia. }
    rewrite (le_at_nth_byte 32 g 0 4 j ltac:(lia) Hj).
    cbn [Nat.add]. iExact "Hb".
  Qed.

  Lemma kxc_named_of_word4 (a : Arch.pa) (g : nat -> bv 8) :
    word4_pointsto a (DfracOwn 1) (Z_to_bv 32 (le_at g 0 4)) ⊢
    [∗ list] j ∈ seq 0 4, pa_add a j ↦ₘ g j.
  Proof.
    rewrite word4_pointsto_unfold. iIntros "[_ H]".
    iApply (big_sepL_impl with "H"). iIntros "!>" (i j Hij) "Hb".
    assert (Hj : (j < 4)%nat).
    { apply lookup_seq in Hij. lia. }
    assert (Hw : (8 * Z.of_nat 4 <= Z.of_N 32)%Z) by lia.
    iEval (rewrite (le_at_nth_byte 32 g 0 4 j Hw Hj); cbn [Nat.add]) in "Hb".
    iExact "Hb".
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
  Context `{!riscvGS Σ, !sieG Σ}.
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
    (word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
     word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 ∗
     word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 ∗
     word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 ∗
     (∃ w5, word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5) ∗
     (∃ w6, word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6) ∗
     (∃ w7, word_pointsto (pa_stk sp0 7) (DfracOwn 1) w7) ∗
     (∃ w8, word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8) ∗
     (∃ w9, word_pointsto (pa_stk sp0 9) (DfracOwn 1) w9) ∗
     (∃ w10, word_pointsto (pa_stk sp0 10) (DfracOwn 1) w10) ∗
     (∃ w11, word_pointsto (pa_stk sp0 11) (DfracOwn 1) w11) ∗
     (∃ w12, word_pointsto (pa_stk sp0 12) (DfracOwn 1) w12) ∗
     (∃ w13, word_pointsto (pa_stk sp0 13) (DfracOwn 1) w13) ∗
     stack_own (pa_stk sp0 13) 50 ∗
     word_pointsto (pa_stk sp0 64) (DfracOwn 1) av ∗
     (∃ w65, word_pointsto (pa_stk sp0 65) (DfracOwn 1) w65) ∗
     word_pointsto (pa_stk sp0 66) (DfracOwn 1) pv ∗
     (∃ w67, word_pointsto (pa_stk sp0 67) (DfracOwn 1) w67) ∗
     (∃ w68, word_pointsto (pa_stk sp0 68) (DfracOwn 1) w68))%I.

  (* ... and the SAME frame with slot 6 PINNED.  s4 is spilled there at
     +0x032 and reloaded at +0x070 / +0x0d0 / ..., so from the +0x032 seam
     onward every block has to know WHICH value it will get back --
     [ProofKexecParts.kxc_frame_at]'s reason, at the one slot phase A
     writes. *)
  Definition kxc_frameA6 (sp0 ra0 s00 s10 s20 pv av w6 : mword 64) : iProp Σ :=
    (word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
     word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 ∗
     word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 ∗
     word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 ∗
     (∃ w5, word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5) ∗
     word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6 ∗
     (∃ w7, word_pointsto (pa_stk sp0 7) (DfracOwn 1) w7) ∗
     (∃ w8, word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8) ∗
     (∃ w9, word_pointsto (pa_stk sp0 9) (DfracOwn 1) w9) ∗
     (∃ w10, word_pointsto (pa_stk sp0 10) (DfracOwn 1) w10) ∗
     (∃ w11, word_pointsto (pa_stk sp0 11) (DfracOwn 1) w11) ∗
     (∃ w12, word_pointsto (pa_stk sp0 12) (DfracOwn 1) w12) ∗
     (∃ w13, word_pointsto (pa_stk sp0 13) (DfracOwn 1) w13) ∗
     stack_own (pa_stk sp0 13) 50 ∗
     word_pointsto (pa_stk sp0 64) (DfracOwn 1) av ∗
     (∃ w65, word_pointsto (pa_stk sp0 65) (DfracOwn 1) w65) ∗
     word_pointsto (pa_stk sp0 66) (DfracOwn 1) pv ∗
     (∃ w67, word_pointsto (pa_stk sp0 67) (DfracOwn 1) w67) ∗
     (∃ w68, word_pointsto (pa_stk sp0 68) (DfracOwn 1) w68))%I.

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
    rewrite stack_own_app (pa_stk_assoc sp0 13 50).
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
      (p : mword 64) (C : iProp Σ) :
    sie_cap_gpr m K0 b p -∗ cpu_own n eb p C b -∗
    ⌜ b = match n with O => eb | S _ => false end ⌝.
  Proof.
    iIntros "Hcg Hcnt". destruct b.
    - iDestruct "Hcnt" as "[%Hb _]". destruct Hb as [-> ->]. done.
    - destruct n as [|n']; [ | done ].
      iDestruct "Hcnt" as "[[_ Hint] _]".
      iDestruct "Hcg" as "(_ & _ & (_ & _ & Harm) & _)".
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
    sie_cap_gpr m K b p -∗
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
        sie_cap_gpr M (K - 68)%nat b p -∗
        pc_is (mword_of_int (KXA + 0x20) : mword 64) -∗
        kxc_frameA sp0 ra0 s00 s10 s20 pv av -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hsp Hra Hs0 Hs1 Hs2 Ha0 Ha1.
    iIntros "Hcg #Htext Hpc Hcont".
    iPoseProof (kxc_000 with "Htext") as "Hi000".
    iPoseProof (kxc_004 with "Htext") as "Hi004".
    iPoseProof (kxc_008 with "Htext") as "Hi008".
    iPoseProof (kxc_00c with "Htext") as "Hi00c".
    iPoseProof (kxc_010 with "Htext") as "Hi010".
    iPoseProof (kxc_014 with "Htext") as "Hi014".
    iPoseProof (kxc_016 with "Htext") as "Hi016".
    iPoseProof (kxc_018 with "Htext") as "Hi018".
    iPoseProof (kxc_01c with "Htext") as "Hi01c".
    (* ---- +0x000: addi sp,sp,-544 (BASE-encoded) ---- *)
    assert (Hpush : add_vec (m !!! Regidx csp_rs1)
                      (sign_extend' 64 (mword_of_int 3552 : mword 12))
                    = pa_stk (m !!! Regidx csp_rs1) 68)
      by apply kxc_push_544.
    iApply (wp_addi_sp_push4_s_sconf (mword_of_int KXA)
              (mword_of_int 3552 : mword 12) m K 68 b HK Hpush
              with "Hcg Hpc Hi000 [-]").
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
                    = mword_of_int (KXA + 0x4)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp004) in "Hpc".
    (* ---- peel the 68-slot frame: slots 1..13, 14..63, 64..68 ---- *)
    change 68%nat with (13 + 55)%nat.
    rewrite stack_own_app.
    iDestruct "Hframe" as "[Hf13 Hf55]".
    iDestruct (kxc_slots13_of_stack sp0 with "Hf13")
      as "((%v1 & Hb1) & (%v2 & Hb2) & (%v3 & Hb3) & (%v4 & Hb4) & Hb5 & Hb6 &
           Hb7 & Hb8 & Hb9 & Hb10 & Hb11 & Hb12 & Hb13)".
    iEval (change 55%nat with (50 + 5)%nat;
           rewrite stack_own_app (pa_stk_assoc sp0 13 50)) in "Hf55".
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
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0x4)) Rra csp_rs1
              (mword_of_int 536 : mword 12) T1 (K - 68)%nat v1 b
              with "Hcg Hpc Hi004 Hb1 [-]").
    iIntros (CID2 Hs2c) "Hcg Hpc Hb1".
    iEval (rewrite Hpa1 Hv1) in "Hb1".
    assert (Hp008 : add_vec_int (mword_of_int (KXA + 0x4) : mword 64) 4
                    = mword_of_int (KXA + 0x8)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0x8)) Rs0 csp_rs1
              (mword_of_int 528 : mword 12) T1 (K - 68)%nat v2 b
              with "Hcg Hpc Hi008 Hb2 [-]").
    iIntros (CID3 Hs3c) "Hcg Hpc Hb2".
    iEval (rewrite Hpa2 Hv2) in "Hb2".
    assert (Hp00c : add_vec_int (mword_of_int (KXA + 0x8) : mword 64) 4
                    = mword_of_int (KXA + 0xc)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0xc)) Rs1 csp_rs1
              (mword_of_int 520 : mword 12) T1 (K - 68)%nat v3 b
              with "Hcg Hpc Hi00c Hb3 [-]").
    iIntros (CID4 Hs4c) "Hcg Hpc Hb3".
    iEval (rewrite Hpa3 Hv3) in "Hb3".
    assert (Hp010 : add_vec_int (mword_of_int (KXA + 0xc) : mword 64) 4
                    = mword_of_int (KXA + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0x10)) Rs2 csp_rs1
              (mword_of_int 512 : mword 12) T1 (K - 68)%nat v4 b
              with "Hcg Hpc Hi010 Hb4 [-]").
    iIntros (CID5 Hs5c) "Hcg Hpc Hb4".
    iEval (rewrite Hpa4 Hv4) in "Hb4".
    assert (Hp014 : add_vec_int (mword_of_int (KXA + 0x10) : mword 64) 4
                    = mword_of_int (KXA + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp014) in "Hpc".
    (* ---- +0x014: c.addi4spn s0,sp,544 -- s0 := sp0 ---- *)
    iApply (wp_caddi4spn_s_sconf (mword_of_int (KXA + 0x14))
              (Cregidx (mword_of_int 0)) (mword_of_int 136 : mword 8) Rs0
              T1 (K - 68)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rdok) with "Hcg Hpc Hi014 [-]").
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
    assert (Hp016 : add_vec_int (mword_of_int (KXA + 0x14) : mword 64) 2
                    = mword_of_int (KXA + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hp016) in "Hpc".
    (* ---- +0x016: c.mv s2,a0 -- s2 := path ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x16)) Rs2 Ra0
              T2 (K - 68)%nat b ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi016 [-]").
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
    assert (Hp018 : add_vec_int (mword_of_int (KXA + 0x16) : mword 64) 2
                    = mword_of_int (KXA + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0x18)) Ra0 Rs0
              (mword_of_int 3568 : mword 12) T3 (K - 68)%nat v66 b
              with "Hcg Hpc Hi018 Hb66 [-]").
    iIntros (CID8 Hs8c) "Hcg Hpc Hb66".
    iEval (rewrite Hpa66 Hv66) in "Hb66".
    assert (Hp01c : add_vec_int (mword_of_int (KXA + 0x18) : mword 64) 4
                    = mword_of_int (KXA + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply (wp_sd_s_sconf (mword_of_int (KXA + 0x1c)) Ra1 Rs0
              (mword_of_int 3584 : mword 12) T3 (K - 68)%nat v64 b
              with "Hcg Hpc Hi01c Hb64 [-]").
    iIntros (CID9 Hs9c) "Hcg Hpc Hb64".
    iEval (rewrite Hpa64 Hv64) in "Hb64".
    assert (Hp020 : add_vec_int (mword_of_int (KXA + 0x1c) : mword 64) 4
                    = mword_of_int (KXA + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
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
    iApply ("Hcont" $! T3 with "[%] Hcg Hpc [-]").
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

   THE PATH BUFFER IS AT FULL OWNERSHIP, not at [dqa].  That is the file
   header's escalation: [SpecNamei] demands the whole buffer and
   [wp_kexec_sconf_body] offers a fraction, so the +0x02c call cannot be
   stated at [dqa].  When SpecKexec.v is fixed, this line is already right. *)
Section KexecASeam.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !iregG Σ}.  (* NB: icacheG + icfg come from
              [fileG] -- see the header.  A standalone [!icacheG Σ] beside
              [!fileG Σ] is a SECOND instance and [ProcInv.cwd_ref] then does
              not match [SpecNamei]'s [inode_held]. *)
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Notation Rra := (mword_of_int 1 : mword 5).
  Notation Rs0 := (mword_of_int 8 : mword 5).
  Notation Rs1 := (mword_of_int 9 : mword 5).
  Notation Rs2 := (mword_of_int 18 : mword 5).
  Notation Ra0 := (mword_of_int 10 : mword 5).

  Definition kxc_at_a2
      (jp : nat)
      (bn : bio_names) (g : log_names) (gfs : fs_names)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (used used1 : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M32 : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (sp0 ra0 s00 s10 s20 pv av ipv : mword 64)
      (n1 : nat) : iProp Σ :=
    let pj := proc_addr jp in
    let L := length (path_elems (bview plen pfun)) in
    (* ---- the register state at [pc_is (kexec + 0x32)] ---- *)
    (⌜ M32 !!! Regidx csp_rs1 = pa_stk sp0 68 /\
       M32 !!! Regidx Rs0 = sp0 /\
       M32 !!! Regidx Rs1 = pj /\
       M32 !!! Regidx Rs2 = pv /\
       M32 !!! Regidx Ra0 = ipv /\
       ipv <> (zero_reg : mword 64) /\
       (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
          r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> M32 !!! Regidx r = m !!! Regidx r) ⌝ ∗
     pc_is (mword_of_int (KXA + 0x32) : mword 64) ∗
     sie_cap_gpr M32 (K - 68)%nat b pj ∗
     cpu_own 0 eb pj C b ∗
     (* ---- the open log transaction, and what namei left of its budget ---- *)
     ⌜ ((MAXOPBLOCKS - (L + 1) * iput_units)%nat <= n1)%nat /\
       (n1 <= MAXOPBLOCKS)%nat ⌝ ∗
     log_op g n1 ∗
     (* ---- the inode namei returned, and the slot it came out of ---- *)
     inode_held ipv ∗
     iref_slots 1 ∗
     (* ---- the fs environment kexec threads ---- *)
     ⌜ used1 ⊆ used ⌝ ∗
     bitmap_res gfs bmapstart cov logstart size used1 ∗
     bslots bn 3 ∗
     sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) ∗
     sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) ∗
     kalloc_env ga None ∗
     (* ---- the process, WHOLE (convention 2) ---- *)
     proc_priv gf pj pidv V ∗
     (* ---- the caller's buffers.  THE PATH IS FULL; see the header. ---- *)
     ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) ∗
     ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) ∗
     ([∗ list] i ∈ seq 0 na,
        [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) ∗
     (* ---- the frame: slots 1..4 pinned, 5..13 lazy, 14..63 one chunk,
            64 = argv, 66 = path ---- *)
     kxc_frameA sp0 ra0 s00 s10 s20 pv av)%I.

End KexecASeam.

(* ===================================================================== *)
(*  PHASE A's TWO HALVES.                                                 *)
(* ===================================================================== *)
Module KexecAProof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                   (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                   (EndOp : END_OP).

Section KexecAExit.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !iregG Σ}.  (* NB: icacheG + icfg come from
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
  (*  THE SHARED [-1] EXIT, at +0x072.                                    *)
  (*                                                                      *)
  (*  Both of phase A's [bad:] entries end identically: a0 = -1, the frame *)
  (*  in [ProofKexecParts.kxc_frame] shape, and the epilogue.  The         *)
  (*  contract's failure arm is [V' = V] and it is free -- nothing before  *)
  (*  the commit block touched the process.                               *)
  (* =================================================================== *)
  Lemma kxc_exit_m1
      (pj : mword 64) (bn : bio_names) (gfs : fs_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z)
      (size : Z) (used used' : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m Mt : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (sp0 ra0 s00 s10 s20 pv av : mword 64) :
    (68 <= K)%nat ->
    used' ⊆ used ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    Mt !!! Regidx csp_rs1 = pa_stk sp0 68 ->
    Mt !!! Regidx Ra0 = (mword_of_int (-1) : mword 64) ->
    (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
        r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> Mt !!! Regidx r = m !!! Regidx r) ->
    sie_cap_gpr Mt (K - 68)%nat b pj -∗
    cpu_own 0 eb pj C b -∗
    kernel_text -∗
    pc_is (mword_of_int (KXA + 0x72) : mword 64) -∗
    kxc_frame sp0 ra0 s00 s10 s20 -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used' -∗
    kalloc_env ga None -∗
    proc_priv gf pj pidv V -∗
    ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
    ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
    ([∗ list] i ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
    bslots bn 3 -∗
    iref_slots 2 -∗
    wp_next b pj (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used2 : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr mf K b pj -∗
          cpu_own 0 eb pj C b -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          ⌜used2 ⊆ used⌝ -∗
          bitmap_res gfs bmapstart cov logstart size used2 -∗
          kalloc_env ga None -∗
          proc_priv gf pj pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
          bslots bn 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hused Hsp Hra Hs0 Hs1 Hs2 Hmtsp Hmta0 Hthr.
    iIntros "Hcg Hcnt #Htext Hpc Hframe Hbm Hins Hbits #Hka Hpriv Hpath Hargv
             Hargs Hbs Hirs Hcont".
    iApply (kxc_epi_frame m Mt K sp0 ra0 s00 s10 s20 pj b
              HK Hsp Hra Hs0 Hs1 Hs2 Hmtsp Hthr
              with "Hcg Htext Hpc Hframe [-]").
    iIntros (CIDe Hse mf) "%Hcs %Hpres Hcg Hpc".
    iDestruct (cpu_own_transport CID0 CIDe 0%nat eb pj C b Hse
                 with "Hcnt") as "Hcnt".
    iSpecialize ("Hcont" $! CIDe with "[%]"); [exact Hse |].
    iApply ("Hcont" $! mf used' V (mword_of_int 0 : mword 64)
              (mword_of_int 0 : mword 64) (mword_of_int 0 : mword 64)
              with "[%] [%] Hcg Hcnt Hpc Hbm Hins [%] Hbits Hka Hpriv Hpath
                    Hargv Hargs Hbs Hirs").
    - exact Hcs.
    - left. split; [| reflexivity].
      rewrite (Hpres Ra0 ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz) ltac:(nz)).
      exact Hmta0.
    - exact Hused.
  Qed.


End KexecAExit.

(* A SEPARATE SECTION, and it has to be: [kxc_exit_m1] is applied at the
   hart the [c.j] at +0x08e (resp. the fall-through at +0x070) resumed on,
   not at the section hart.  A SIBLING lemma in the same Section resolves
   its [CpuId] through the section variable BY NAME, so [sie_cap_gpr] in
   its premise would mean the ENTRY hart and the application fails with
   "cannot instantiate (P -* Q) with P" printing the SAME TERM TWICE
   (durable-notes.md).  Closing the section first generalises it, and the
   application then resolves [CID] from the caller's own hypotheses. *)
Section KexecABody.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !iregG Σ}.  (* NB: icacheG + icfg come from
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
  (*  +0x000 .. +0x030, PLUS the namei-null tail at +0x088.               *)
  (* =================================================================== *)
  Lemma kxc_a1
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname)
      (pd pav pu : mword 64)
      (bn : bio_names)
      (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname)
      (ga : gname) (gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32)
      (used : gset Z)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64)
      (alen : nat -> nat) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate)
      (dqb dqs dqa : dfrac)
      (m : regfile) (K : nat) (eb : bool) (C : iProp Σ) (b : bool)
      (sp0 ra0 s00 s10 s20 pv av : mword 64) :
    let L := length (path_elems (bview plen pfun)) in
    (K_kexec <= K)%nat ->
    dev = icfg_dev ->
    nib = icfg_nib ->
    dev = ROOTDEV ->
    (0 < nib)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    bb_cstr pfun plen ->
    (Z.of_nat plen < 2 ^ 31)%Z ->
    ((L + 1) * iput_units + iput_units <= MAXOPBLOCKS)%nat ->
    (jp < NPROC)%nat ->
    gs !! jp = Some gl ->
    eb = true ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    m !!! Regidx Ra0 = pv ->
    m !!! Regidx Ra1 = av ->
    sie_cap_gpr m K b (proc_addr jp) -∗
    cpu_own 0 eb (proc_addr jp) C b -∗
    kernel_text -∗ pc_is (mword_of_int KXA : mword 64) -∗
    panic_wp_any -∗
    fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
              cov logstart inodestart nib dev -∗
    kalloc_env ga None -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used -∗
    proc_priv gf (proc_addr jp) pidv V -∗
    ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
    ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
    ([∗ list] i ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
    bslots bn 3 -∗
    iref_slots 2 -∗
    (* ---- kexec's OWN continuation: the +0x088 tail closes the -1 arm ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr mf K b (proc_addr jp) -∗
          cpu_own 0 eb (proc_addr jp) C b -∗
          pc_is (ret_pc ra0) -∗
          sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
          sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
          ⌜used' ⊆ used⌝ -∗
          bitmap_res gfs bmapstart cov logstart size used' -∗
          kalloc_env ga None -∗
          proc_priv gf (proc_addr jp) pidv V' -∗
          ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
          ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
          ([∗ list] i ∈ seq 0 na,
             [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
          bslots bn 3 -∗
          iref_slots 2 -∗
          WP (Loop : expr riscv_lang)) -∗
    (* ---- and the FALL-THROUGH: the state at +0x032 ---- *)
    wp_next b (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (M32 : regfile) (used1 : gset Z) (ipv : mword 64) (n1 : nat),
        kxc_at_a2 jp bn g gfs ga gf cov logstart bmapstart inodestart size
                  used used1 plen pfun na avf aslen afun pidv V dqb dqs dqa
                  m M32 K eb C b sp0 ra0 s00 s10 s20 pv av ipv n1 -∗
        WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros L HK Hdev Hnib Hroot Hnib0 Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb
           Hiregb Hcstr Hplen Hbudget Hjp Hgs Heb Hsp Hra Hs0 Hs1 Hs2 Ha0 Ha1.
    unfold K_kexec in HK.
    iIntros "Hcg Hcnt #Htext Hpc #Hpanic #Hfab #Hka Hbm Hins Hbits Hpriv
             Hpath Hargv Hargs Hbs Hirs Hcont Hcont32".
    (* ---- b = eb = true (see the header) ---- *)
    iDestruct (kxc_sie_b_agree m 0%nat K eb b (proc_addr jp) C with "Hcg Hcnt") as %Houtb.
    subst eb. cbn in Houtb. subst b.
    iDestruct "Hfab" as "(#Hbio & #Hlogc & #Hcrash & #Hcert & #Hitab & #Hitinv &
                          #Hesc & #Hslks & #Hireg & #Hprocs & #Hdevi & #Hdgeom &
                          #Hdlock)".
    (* ---- open the process's private block ONCE (convention 2) ---- *)
    iDestruct (proc_priv_cwd_pid gf (proc_addr jp) pidv V with "Hpriv")
      as "(Hcwd & Hcref & Hppid & Hpvbk)".
    (* ---- +0x000 .. +0x01c ---- *)
    iApply (kxc_prologue m K true (proc_addr jp) sp0 ra0 s00 s10 s20 pv av
              ltac:(lia) Hsp Hra Hs0 Hs1 Hs2 Ha0 Ha1 with "Hcg Htext Hpc [-]").
    iIntros (CIDp Hsp1 M1) "%HM1 Hcg Hpc Hframe".
    destruct HM1 as (HM1sp & HM1s0 & HM1s2 & HM1a0 & HM1a1 & HM1thr).
    (* ---- +0x020: jal ra,myproc ---- *)
    iPoseProof (kxc_020 with "Htext") as "Hi020".
    assert (Htmp : add_vec (mword_of_int (KXA + 0x20) : mword 64)
                     (sign_extend' 64 (mword_of_int 2085418 : mword 21))
                   = mword_of_int KernelSyms.myproc) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x20)) Rra
              (mword_of_int 2085418 : mword 21) M1 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htmp; vm_compute; reflexivity)
              with "Hcg Hpc Hi020 [-]").
    iIntros (CIDj1 Hsj1) "Hcg Hpc". iEval (rewrite Htmp) in "Hpc".
    set (N1 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x20) : mword 64) 4)]> M1).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x20) : mword 64) 4)]> M1) with N1.
    assert (HN1ra : N1 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x20) : mword 64) 4)
      by (rewrite /N1; apply upd_eq).
    iDestruct (cpu_own_transport CID0 CIDj1 0%nat true (proc_addr jp) C true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (Myproc.wp_myproc_sconf N1 (K - 68)%nat 0%nat true (proc_addr jp) C true
              ltac:(vm_compute; reflexivity) ltac:(lia)
              with "Hcg Hcnt Htext Hpc [-]").
    iIntros (CIDm Hsm ms M2) "%Hmsf Hcg Hcnt Hpc %Hmp".
    destruct Hmp as (Hcsm & Hm2a0).
    assert (Hpc24 : ret_pc (N1 !!! Regidx Rra) = mword_of_int (KXA + 0x24))
      by (rewrite HN1ra; pcw).
    iEval (rewrite Hpc24) in "Hpc".
    (* ---- +0x024: c.mv s1,a0 -- s1 := p ---- *)
    iPoseProof (kxc_024 with "Htext") as "Hi024".
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x24)) Rs1 Ra0
              M2 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi024 [-]").
    iIntros (CIDv1 Hsv1) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N2 := <[Regidx Rs1 := regval_into_reg
                  (add_vec zero_reg (M2 !!! Regidx Ra0))]> M2).
    assert (HN2s1 : N2 !!! Regidx Rs1 = (proc_addr jp)).
    { rewrite /N2 upd_eq Hm2a0. apply add_vec_zero_l. }
    assert (Hpp026 : add_vec_int (mword_of_int (KXA + 0x24) : mword 64) 2
                     = mword_of_int (KXA + 0x26)) by pcw.
    iEval (rewrite Hpp026) in "Hpc".
    (* ---- +0x026: jal ra,begin_op ---- *)
    iPoseProof (kxc_026 with "Htext") as "Hi026".
    assert (Htbo : add_vec (mword_of_int (KXA + 0x26) : mword 64)
                     (sign_extend' 64 (mword_of_int 2094348 : mword 21))
                   = mword_of_int KernelSyms.begin_op) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x26)) Rra
              (mword_of_int 2094348 : mword 21) N2 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htbo; vm_compute; reflexivity)
              with "Hcg Hpc Hi026 [-]").
    iIntros (CIDj2 Hsj2) "Hcg Hpc". iEval (rewrite Htbo) in "Hpc".
    set (N3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x26) : mword 64) 4)]> N2).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x26) : mword 64) 4)]> N2) with N3.
    assert (HN3ra : N3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x26) : mword 64) 4)
      by (rewrite /N3; apply upd_eq).
    assert (HN3s1 : N3 !!! Regidx Rs1 = (proc_addr jp))
      by (rewrite /N3 upd_ne; [exact HN2s1 | nz]).
    iDestruct (cpu_own_transport CIDm CIDj2 0%nat true (proc_addr jp) C true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (BeginOp.wp_begin_op_sconf gs jp gl bn g gfs cov logstart dev
              pidv (DfracOwn (1/4)) N3 (K - 68)%nat true C true
              ltac:(unfold K_begin_op; lia) Hjp Hgs eq_refl
              with "Hcg Hcnt Htext Hpc Hpanic Hlogc Hppid Hprocs [-]").
    iIntros (CIDb Hsb M3) "%Hcsb Hcg Hcnt Hpc Hppid Hlog".
    assert (Hpc2a : ret_pc (N3 !!! Regidx Rra) = mword_of_int (KXA + 0x2a))
      by (rewrite HN3ra; pcw).
    iEval (rewrite Hpc2a) in "Hpc".
    (* ---- +0x02a: c.mv a0,s2 -- a0 := path ---- *)
    iPoseProof (kxc_02a with "Htext") as "Hi02a".
    assert (HM3s2 : M3 !!! Regidx Rs2 = pv).
    { rewrite (callee_saved_lookup Hcsb Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsm Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /N1 upd_ne; [exact HM1s2 | nz]. }
    iApply (wp_cmv_s_sconf (mword_of_int (KXA + 0x2a)) Ra0 Rs2
              M3 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi02a [-]").
    iIntros (CIDv2 Hsv2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (N4 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (M3 !!! Regidx Rs2))]> M3).
    assert (HN4a0 : N4 !!! Regidx Ra0 = pv).
    { rewrite /N4 upd_eq HM3s2. apply add_vec_zero_l. }
    assert (Hpp02c : add_vec_int (mword_of_int (KXA + 0x2a) : mword 64) 2
                     = mword_of_int (KXA + 0x2c)) by pcw.
    iEval (rewrite Hpp02c) in "Hpc".
    (* ---- +0x02c: jal ra,namei ---- *)
    iPoseProof (kxc_02c with "Htext") as "Hi02c".
    assert (Htnm : add_vec (mword_of_int (KXA + 0x2c) : mword 64)
                     (sign_extend' 64 (mword_of_int 2093864 : mword 21))
                   = mword_of_int KernelSyms.namei) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x2c)) Rra
              (mword_of_int 2093864 : mword 21) N4 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htnm; vm_compute; reflexivity)
              with "Hcg Hpc Hi02c [-]").
    iIntros (CIDj3 Hsj3) "Hcg Hpc". iEval (rewrite Htnm) in "Hpc".
    set (N5 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXA + 0x2c) : mword 64) 4)]> N4).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXA + 0x2c) : mword 64) 4)]> N4) with N5.
    assert (HN5ra : N5 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXA + 0x2c) : mword 64) 4)
      by (rewrite /N5; apply upd_eq).
    assert (HN5a0 : N5 !!! Regidx Ra0 = pv)
      by (rewrite /N5 upd_ne; [exact HN4a0 | nz]).
    iDestruct (cpu_own_transport CIDb CIDj3 0%nat true (proc_addr jp) C true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iEval (rewrite /cwd_ref) in "Hcref".
    (* namei names the path buffer by ITS OWN a0; ours is [pv]. *)
    iEval (rewrite -HN5a0) in "Hpath".
    iApply (Namei.wp_namei_sconf gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl
              ga gf cov logstart bmapstart inodestart nib size dev used
              (pv_cwd V) plen pfun MAXOPBLOCKS pidv (DfracOwn (1/4)) dqb dqs
              (DfracOwn 1) N5 (K - 68)%nat true C true
              ltac:(unfold K_namei; lia) Hdev Hnib Hroot Hnib0 Hlg Hsz Hbm0
              Hbmc Hbml Hins0 Hcovb Hiregb Hcstr Hplen
              ltac:(unfold iput_units, MAXOPBLOCKS in *; lia) Hjp Hgs eq_refl
              with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlogc Hka Hitab Hitinv Hesc
                    Hslks Hireg Hprocs Hdevi Hdgeom Hdlock Hbm Hins Hbits Hppid
                    Hcwd Hcref Hpath Hbs Hirs Hlog [-]").
    iIntros (CIDn Hsn M4 n1 used1 ok ipv) "%Hcsn Hcg Hcnt Hpc Hbm Hins %Hused1
             Hbits Hppid Hcwd Hcref Hpath Hbs %Hn1 Hlog Harm".
    iEval (rewrite HN5a0) in "Hpath".
    assert (Hpc30 : ret_pc (N5 !!! Regidx Rra) = mword_of_int (KXA + 0x30))
      by (rewrite HN5ra; pcw).
    iEval (rewrite Hpc30) in "Hpc".
    (* ---- the register facts that survive to +0x030 ---- *)
    assert (HM4sp : M4 !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcsn csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsb csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsm csp_rs1 ltac:(vm_compute; reflexivity)).
      rewrite /N1 upd_ne; [exact HM1sp | nz]. }
    assert (HM4s0 : M4 !!! Regidx Rs0 = sp0).
    { rewrite (callee_saved_lookup Hcsn Rs0 ltac:(vm_compute; reflexivity)).
      rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsb Rs0 ltac:(vm_compute; reflexivity)).
      rewrite /N3 upd_ne; [| nz]. rewrite /N2 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsm Rs0 ltac:(vm_compute; reflexivity)).
      rewrite /N1 upd_ne; [exact HM1s0 | nz]. }
    assert (HM4s1 : M4 !!! Regidx Rs1 = (proc_addr jp)).
    { rewrite (callee_saved_lookup Hcsn Rs1 ltac:(vm_compute; reflexivity)).
      rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz].
      rewrite (callee_saved_lookup Hcsb Rs1 ltac:(vm_compute; reflexivity)).
      exact HN3s1. }
    assert (HM4s2 : M4 !!! Regidx Rs2 = pv).
    { rewrite (callee_saved_lookup Hcsn Rs2 ltac:(vm_compute; reflexivity)).
      rewrite /N5 upd_ne; [| nz]. rewrite /N4 upd_ne; [| nz]. exact HM3s2. }
    assert (HM4thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> M4 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2.
      rewrite (callee_saved_lookup Hcsn r Hr).
      rewrite /N5 upd_ne; [| regne]. rewrite /N4 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hcsb r Hr).
      rewrite /N3 upd_ne; [| regne]. rewrite /N2 upd_ne; [| regne].
      rewrite (callee_saved_lookup Hcsm r Hr).
      rewrite /N1 upd_ne; [| regne].
      exact (HM1thr r Hr Nsp Ns0 Ns2). }
    iPoseProof (kxc_030 with "Htext") as "Hi030".
    destruct ok.
    - (* ============ namei SUCCEEDED: fall through to +0x032 ============ *)
      iDestruct "Harm" as "(%HM4a0 & Hheld & Hirs)".
      iDestruct (inode_held_ne_zero with "Hheld") as %Hipvnz.
      assert (Hcmp : eq_vec (rget M4 Ra0) (zero_reg : mword 64) = false).
      { rewrite (rget_ne M4 Ra0 ltac:(nz)) HM4a0.
        destruct (eq_vec ipv (zero_reg : mword 64)) eqn:E; [| reflexivity].
        exfalso. apply Hipvnz. by apply eq_vec_true_iff in E. }
      iApply (wp_cbeqz_fall_s_sconf (mword_of_int (KXA + 0x30))
                (mword_of_int 44 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                M4 (K - 68)%nat true
                ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
                with "Hcg Hpc Hi030 [-]").
      iIntros (CIDz Hsz1) "Hcg Hpc".
      assert (Hpp032 : add_vec_int (mword_of_int (KXA + 0x30) : mword 64) 2
                       = mword_of_int (KXA + 0x32)) by pcw.
      iEval (rewrite Hpp032) in "Hpc".
      (* close the private block back up, at the cwd it lent out *)
      iDestruct ("Hpvbk" $! (pv_cwd V) with "Hcwd [Hcref] Hppid") as "Hpriv".
      { iEval (rewrite /cwd_ref). iExact "Hcref". }
      rewrite kxc_upd_cwd_id.
      iDestruct (cpu_own_transport CIDn CIDz 0%nat true (proc_addr jp) C true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iSpecialize ("Hcont32" $! CIDz with "[%]"); [wp_next_chain |].
      iApply ("Hcont32" $! M4 used1 ipv n1).
      (* NO [iFrame] HERE.  The goal mentions [proc_priv], and framing into
         it sends the search through sixteen [ofile_slot]s and a 4096-byte
         trapframe page (durable-notes.md); measured: it does not come back.
         Nineteen [iSplitL]/[iExact]s instead, in the conjunct order. *)
      rewrite /kxc_at_a2.
      iSplitR.
      { iPureIntro. split_and!;
          [exact HM4sp | exact HM4s0 | exact HM4s1 | exact HM4s2
          | exact HM4a0 | exact Hipvnz | exact HM4thr]. }
      iSplitL "Hpc"; [iExact "Hpc" |].
      iSplitL "Hcg"; [iExact "Hcg" |].
      iSplitL "Hcnt"; [iExact "Hcnt" |].
      iSplitR; [iPureIntro; exact Hn1 |].
      iSplitL "Hlog"; [iExact "Hlog" |].
      iSplitL "Hheld"; [iExact "Hheld" |].
      iSplitL "Hirs"; [iExact "Hirs" |].
      iSplitR; [iPureIntro; exact Hused1 |].
      iSplitL "Hbits"; [iExact "Hbits" |].
      iSplitL "Hbs"; [iExact "Hbs" |].
      iSplitL "Hbm"; [iExact "Hbm" |].
      iSplitL "Hins"; [iExact "Hins" |].
      iSplitR; [iExact "Hka" |].
      iSplitL "Hpriv"; [iExact "Hpriv" |].
      iSplitL "Hpath"; [iExact "Hpath" |].
      iSplitL "Hargv"; [iExact "Hargv" |].
      iSplitL "Hargs"; [iExact "Hargs" |].
      iExact "Hframe".
    - (* ============ namei FAILED: the +0x088 tail ============ *)
      iDestruct "Harm" as "(%HM4a0 & Hirs)".
      assert (Hcmp : eq_vec (rget M4 Ra0) (zero_reg : mword 64) = true).
      { rewrite (rget_ne M4 Ra0 ltac:(nz)) HM4a0.
        apply eq_vec_true_iff. apply bv_eq; vm_compute; reflexivity. }
      assert (Htgt88 : add_vec (mword_of_int (KXA + 0x30) : mword 64)
                (sign_extend' 64 (sign_extend' 13
                   (concat_vec (mword_of_int 44 : mword 8) ('b"0"))))
              = mword_of_int (KXA + 0x88)) by pcw.
      iApply (wp_cbeqz_taken_s_sconf (mword_of_int (KXA + 0x30))
                (mword_of_int 44 : mword 8) (Cregidx (mword_of_int 2)) Ra0
                M4 (K - 68)%nat true
                ltac:(vm_compute; reflexivity) ltac:(nz) Hcmp
                ltac:(rewrite Htgt88; vm_compute; reflexivity)
                with "Hcg Hpc Hi030 [-]").
      iIntros (CIDz Hsz1). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htgt88) in "Hpc".
      (* ---- +0x088: jal ra,end_op ---- *)
      iPoseProof (kxc_088 with "Htext") as "Hi088".
      iPoseProof (kxc_08c with "Htext") as "Hi08c".
      iPoseProof (kxc_08e with "Htext") as "Hi08e".
      assert (Hteo : add_vec (mword_of_int (KXA + 0x88) : mword 64)
                       (sign_extend' 64 (mword_of_int 2094362 : mword 21))
                     = mword_of_int KernelSyms.end_op) by pcw.
      iApply (wp_jal_s_sconf (mword_of_int (KXA + 0x88)) Rra
                (mword_of_int 2094362 : mword 21) M4 (K - 68)%nat true
                ltac:(nz) ltac:(rdok)
                ltac:(rewrite Hteo; vm_compute; reflexivity)
                with "Hcg Hpc Hi088 [-]").
      iIntros (CIDj4 Hsj4) "Hcg Hpc". iEval (rewrite Hteo) in "Hpc".
      set (P1 := <[Regidx Rra := regval_into_reg
                    (add_vec_int (mword_of_int (KXA + 0x88) : mword 64) 4)]> M4).
      change (<[Regidx Rra := regval_into_reg
                (add_vec_int (mword_of_int (KXA + 0x88) : mword 64) 4)]> M4) with P1.
      assert (HP1ra : P1 !!! Regidx Rra
                      = add_vec_int (mword_of_int (KXA + 0x88) : mword 64) 4)
        by (rewrite /P1; apply upd_eq).
      iDestruct (cpu_own_transport CIDn CIDj4 0%nat true (proc_addr jp) C true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      iApply (EndOp.wp_end_op_sconf gs jp gl gu gd gk pd pav pu bn g gfs
                cov logstart dev n1 pidv (DfracOwn (1/4)) P1 (K - 68)%nat
                true C true ltac:(unfold K_end_op; lia) Hlg Hjp Hgs eq_refl
                with "Hcg Hcnt Htext Hpc Hpanic Hbio Hlogc Hcrash Hcert Hppid
                      Hprocs Hdevi Hdgeom Hdlock Hlog [-]").
      iIntros (CIDe1 Hse1 M5) "%Hcse Hcg Hcnt Hpc Hppid".
      assert (Hpc8c : ret_pc (P1 !!! Regidx Rra) = mword_of_int (KXA + 0x8c))
        by (rewrite HP1ra; pcw).
      iEval (rewrite Hpc8c) in "Hpc".
      (* ---- +0x08c: c.li a0,-1 ---- *)
      iApply (wp_cli_s_sconf (mword_of_int (KXA + 0x8c)) Ra0
                (mword_of_int 63 : mword 6) (mword_of_int (-1) : mword 64)
                M5 (K - 68)%nat true ltac:(nz) ltac:(rdok)
                ltac:(apply bv_eq; vm_compute; reflexivity)
                with "Hcg Hpc Hi08c [-]").
      iIntros (CIDl1 Hsl1) "Hcg Hpc".
      set (P2 := <[Regidx Ra0 := regval_into_reg
                    (mword_of_int (-1) : mword 64)]> M5).
      assert (HP2a0 : P2 !!! Regidx Ra0 = (mword_of_int (-1) : mword 64))
        by (rewrite /P2; apply upd_eq).
      assert (Hpp08e : add_vec_int (mword_of_int (KXA + 0x8c) : mword 64) 2
                       = mword_of_int (KXA + 0x8e)) by pcw.
      iEval (rewrite Hpp08e) in "Hpc".
      (* ---- +0x08e: c.j -28 -> +0x072 ---- *)
      assert (Htj72 : add_vec (mword_of_int (KXA + 0x8e) : mword 64)
                (sign_extend' 64 (sign_extend' 21
                   (concat_vec (mword_of_int 2034 : mword 11) ('b"0"))))
              = mword_of_int (KXA + 0x72)) by pcw.
      iApply (wp_cj_s_sconf (mword_of_int (KXA + 0x8e))
                (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")))
                P2 (K - 68)%nat true
                ltac:(rewrite Htj72; vm_compute; reflexivity)
                with "Hcg Hpc Hi08e [-]").
      iIntros (CIDz2 Hsz2). iNext. iIntros "Hcg Hpc".
      iEval (rewrite Htj72) in "Hpc".
      (* ---- close the private block and take the shared exit ---- *)
      iDestruct ("Hpvbk" $! (pv_cwd V) with "Hcwd [Hcref] Hppid") as "Hpriv".
      { iEval (rewrite /cwd_ref). iExact "Hcref". }
      rewrite kxc_upd_cwd_id.
      iDestruct (cpu_own_transport CIDe1 CIDz2 0%nat true (proc_addr jp) C true
                   ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
      (* the register facts at +0x072 *)
      assert (HP2sp : P2 !!! Regidx csp_rs1 = pa_stk sp0 68).
      { rewrite /P2 upd_ne; [| nz].
        rewrite (callee_saved_lookup Hcse csp_rs1 ltac:(vm_compute; reflexivity)).
        rewrite /P1 upd_ne; [exact HM4sp | nz]. }
      assert (HP2thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
                r <> Rs0 -> r <> Rs1 -> r <> Rs2 ->
                P2 !!! Regidx r = m !!! Regidx r).
      { intros r Hr Nsp Ns0 Ns1 Ns2.
        rewrite /P2 upd_ne; [| regne].
        rewrite (callee_saved_lookup Hcse r Hr).
        rewrite /P1 upd_ne; [| regne].
        exact (HM4thr r Hr Nsp Ns0 Ns1 Ns2). }
      iApply (kxc_exit_m1 (proc_addr jp) bn gfs ga gf cov logstart bmapstart inodestart
                size used used1 plen pfun na avf alen aslen afun pidv V
                dqb dqs dqa m P2 K true C true sp0 ra0 s00 s10 s20 pv av
                ltac:(lia) Hused1 Hsp Hra Hs0 Hs1 Hs2 HP2sp HP2a0 HP2thr
                with "Hcg Hcnt Htext Hpc [Hframe] Hbm Hins Hbits Hka Hpriv
                      Hpath Hargv Hargs Hbs Hirs [-]").
      { iApply (kxc_frameA_epi with "Hframe"). }
      iIntros (CIDf Hsf mf used2 V' entry spv szv') "%Hcs2 %Hok Hcg Hcnt Hpc
               Hbm Hins %Hu2 Hbits Hka2 Hpriv Hpath Hargv Hargs Hbs Hirs".
      iSpecialize ("Hcont" $! CIDf with "[%]"); [wp_next_chain |].
      iApply ("Hcont" $! mf used2 V' entry spv szv'
                with "[%] [%] Hcg Hcnt Hpc Hbm Hins [%] Hbits Hka2 Hpriv
                      Hpath Hargv Hargs Hbs Hirs").
      + exact Hcs2.
      + exact Hok.
      + exact Hu2.
  Qed.

End KexecABody.
End KexecAProof.
