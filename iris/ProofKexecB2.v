(* ProofKexecB2.v -- PHASE B of kexec, SECOND CHUNK: the phdr loop, the
   inlined loadseg loop, and the six [bad:] tails they share.

   Its entry seams are ProofKexecSeam.v's [kxc_at_12c] (the phdr loop's BODY,
   which is also its head) and [kxc_at_1a2] (the no-segments path); its exit
   is +0x1ae, phase C's entry.  Nothing here requires ProofKexecB.v -- the
   two chunks meet only through ProofKexecSeam.v, so they compile in
   parallel (ProofKexecTail.v's header has the measurement that made that a
   rule).

   ---- WHAT IS HERE SO FAR: THE FRAME ALGEBRA ----------------------------

   [kxc_frameB65] is [ProofKexecSeam.kxc_frameB] with slot 65 PINNED, plus
   the three moves between it and its neighbours.  Slot 65 is the C's [sz1],
   and it is existential in [kxc_frameB] for a good reason -- at +0x0cc
   nothing has written it yet -- but from +0x180 on it holds a value the
   [bad:] tail READS, so every state in this file pins it.

   [kxc_frameB65_to_A6] is the move that tail makes: slots 5 and 7..13 lose
   their values (they are lazily spilled, and phase A's tail reaches the
   epilogue on paths where they were never written, so [kxc_frameA6] takes
   them existentially) and the NAMED elf run goes back into the middle
   [stack_own].  Its per-slot alignment premise is exactly the pure conjunct
   [kxc_at_12c] carries for the purpose -- a byte run does not carry
   alignment and [bytes_own_slotsn] demands it back.

   ---- WHAT COMES NEXT, AND THE CONTROL FLOW IT HAS TO FOLLOW ------------

   The tail SIX of kexec's eight [bad:] entries funnel into.  The +0x320 /
   +0x340 / +0x346 / +0x34c / +0x352 stores all write [s2] into slot 65 and
   fall (or jump) into +0x324, and the loadseg short-read at +0x0ea jumps
   there directly; from +0x324 on there is one path:

     +0x324  ld   a1,-520(s0)     a1 = slot 65, the size to free
     +0x328  mv   a0,s6           a0 = the NEW table's root
     +0x32a  jal  proc_freepagetable
     +0x32e  ld s3,504(sp)  } the eight callee-saved registers this phase
     +0x330  ld s5,488(sp)  }   spilled at +0x09e..+0x0aa, restored
     +0x332  ld s6,480(sp)  }   (slots 5,7,8,9,10,11,12,13)
     +0x334  ld s7,472(sp)  }
     +0x336  ld s8,464(sp)  }
     +0x338  ld s9,456(sp)  }
     +0x33a  ld s10,448(sp) }
     +0x33c  ld s11,440(sp) }
     +0x33e  j +0x64              -- ProofKexecTail's [kxc_bad64]

   WHICH SIZE IS FREED, AND WHY IT IS ALWAYS THE RIGHT ONE.  Slot 65 is the
   C's [sz1].  The five stores put [s2] -- the size the loop has actually
   grown the table to -- there, which matters at +0x352: uvmalloc has just
   returned 0 and +0x180 stored THAT into slot 65, so without the +0x352
   store the tail would free at size 0 and leak every page the earlier
   segments mapped.  The one entry that does NOT store is +0x0ea, the
   loadseg short read, and it is right not to: there [s2] is the readi
   COUNT, and slot 65 still holds the [sz1] that +0x180 wrote.

   THE SIZE PREMISE proc_freepagetable ASKS FOR IS A PROJECTION.
   [SpecProcFreepagetable] wants [uint sz <= uvm_maxsz] and
   [um_below sz P.(ud_um)].  The second is carried by the loop invariant
   directly; the first is NOT carried -- it is read off the coverage half
   with [UmCovered.proc_pt_covered_maxsz], which is the whole reason that
   half is in the invariant (claude-notes/projects/kexec.md, "THE SIZE BOUND
   IS THE COVERAGE INVARIANT").  So the tail will ask its callers for
   coverage, not for a bound they would have no way to establish. *)
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
Require Import WpSmodeHalf.
Require Import WpSmodeIntr.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import SleepLock.
Require Import WpLock.
Require Import PanicStub.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import WpUart.
Require Import FsCrash.
Require Import InodeRegion.
Require Import IcacheEscrow.
Require Import ByteBuf.
Require Import ElfEnc.
Require Import PageGeom.
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
Require Import FileInvDefs.
Require Import DinodeEnc.
Require Import DirView.
Require Import InodeLock.
Require Import SchedCtx.
Require Import DiskInv.
Require Import PtTree.
Require Import PtBuild.
Require Import ProcPt.
Require Import UserPtTree.
Require Import ProcPtOwn.
Require Import UmCovered.
Require Import FileInv.
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
Require Import SpecProcFreepagetable.
Require Import ProofKexecParts.
Require Import ProofKexecTail.
Require Import ProofKexecSeam.
Require Import ProofKforkParts.
Require Import CodeKexec.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* A syscall-altitude goal carries [ProcInv.tf_page]'s 4096-conjunct big-op;
   printing one takes tens of minutes, so a one-line mistake reads as a hang.
   durable-notes.md's rule. *)
Set Printing Depth 40.

Notation KXB := KernelSyms.kexec (only parsing).

(* ===================================================================== *)
(*  THE FRAME WITH slot 65 PINNED.                                        *)
(* ===================================================================== *)
(* [kxc_frameB] leaves slot 65 existential because at +0x0cc nothing has
   written [sz1] yet.  From +0x180 on it holds a value the [bad:] tail
   READS, so every state in this file pins it. *)
Section KexecB2Frame.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  Definition kxc_frameB65 (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w65 w67 : mword 64) : iProp Σ :=
    (word_pointsto (pa_stk sp0 1) (DfracOwn 1) ra0 ∗
     word_pointsto (pa_stk sp0 2) (DfracOwn 1) s00 ∗
     word_pointsto (pa_stk sp0 3) (DfracOwn 1) s10 ∗
     word_pointsto (pa_stk sp0 4) (DfracOwn 1) s20 ∗
     word_pointsto (pa_stk sp0 5) (DfracOwn 1) w5 ∗
     word_pointsto (pa_stk sp0 6) (DfracOwn 1) w6 ∗
     word_pointsto (pa_stk sp0 7) (DfracOwn 1) w7 ∗
     word_pointsto (pa_stk sp0 8) (DfracOwn 1) w8 ∗
     word_pointsto (pa_stk sp0 9) (DfracOwn 1) w9 ∗
     word_pointsto (pa_stk sp0 10) (DfracOwn 1) w10 ∗
     word_pointsto (pa_stk sp0 11) (DfracOwn 1) w11 ∗
     word_pointsto (pa_stk sp0 12) (DfracOwn 1) w12 ∗
     word_pointsto (pa_stk sp0 13) (DfracOwn 1) w13 ∗
     stack_own (pa_stk sp0 13) 33 ∗
     stack_own (pa_stk sp0 54) 9 ∗
     word_pointsto (pa_stk sp0 64) (DfracOwn 1) av ∗
     word_pointsto (pa_stk sp0 65) (DfracOwn 1) w65 ∗
     word_pointsto (pa_stk sp0 66) (DfracOwn 1) pv ∗
     word_pointsto (pa_stk sp0 67) (DfracOwn 1) w67 ∗
     (∃ w68, word_pointsto (pa_stk sp0 68) (DfracOwn 1) w68))%I.

  (* the two directions between it and [kxc_frameB] *)
  Lemma kxc_frameB65_of_B (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64) :
    kxc_frameB sp0 ra0 s00 s10 s20 pv av w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 ⊢
    ∃ w65, kxc_frameB65 sp0 ra0 s00 s10 s20 pv av
                        w5 w6 w7 w8 w9 w10 w11 w12 w13 w65 w67.
  Proof.
    rewrite /kxc_frameB /kxc_frameB65.
    iIntros "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 &
              A13 & Aust & Aph & A64 & (%w65 & A65) & A66 & A67 & A68)".
    iExists w65.
    iSplitL "A1"; [iExact "A1" |]. iSplitL "A2"; [iExact "A2" |].
    iSplitL "A3"; [iExact "A3" |]. iSplitL "A4"; [iExact "A4" |].
    iSplitL "A5"; [iExact "A5" |]. iSplitL "A6"; [iExact "A6" |].
    iSplitL "A7"; [iExact "A7" |]. iSplitL "A8"; [iExact "A8" |].
    iSplitL "A9"; [iExact "A9" |]. iSplitL "A10"; [iExact "A10" |].
    iSplitL "A11"; [iExact "A11" |]. iSplitL "A12"; [iExact "A12" |].
    iSplitL "A13"; [iExact "A13" |]. iSplitL "Aust"; [iExact "Aust" |].
    iSplitL "Aph"; [iExact "Aph" |]. iSplitL "A64"; [iExact "A64" |].
    iSplitL "A65"; [iExact "A65" |]. iSplitL "A66"; [iExact "A66" |].
    iSplitL "A67"; [iExact "A67" | iExact "A68"].
  Qed.

  Lemma kxc_frameB_of_B65 (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w65 w67 : mword 64) :
    kxc_frameB65 sp0 ra0 s00 s10 s20 pv av
                 w5 w6 w7 w8 w9 w10 w11 w12 w13 w65 w67 ⊢
    kxc_frameB sp0 ra0 s00 s10 s20 pv av w5 w6 w7 w8 w9 w10 w11 w12 w13 w67.
  Proof.
    rewrite /kxc_frameB /kxc_frameB65.
    iIntros "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 &
              A13 & Aust & Aph & A64 & A65 & A66 & A67 & A68)".
    iSplitL "A1"; [iExact "A1" |]. iSplitL "A2"; [iExact "A2" |].
    iSplitL "A3"; [iExact "A3" |]. iSplitL "A4"; [iExact "A4" |].
    iSplitL "A5"; [iExact "A5" |]. iSplitL "A6"; [iExact "A6" |].
    iSplitL "A7"; [iExact "A7" |]. iSplitL "A8"; [iExact "A8" |].
    iSplitL "A9"; [iExact "A9" |]. iSplitL "A10"; [iExact "A10" |].
    iSplitL "A11"; [iExact "A11" |]. iSplitL "A12"; [iExact "A12" |].
    iSplitL "A13"; [iExact "A13" |]. iSplitL "Aust"; [iExact "Aust" |].
    iSplitL "Aph"; [iExact "Aph" |]. iSplitL "A64"; [iExact "A64" |].
    iSplitL "A65"; [by iExists w65 |]. iSplitL "A66"; [iExact "A66" |].
    iSplitL "A67"; [iExact "A67" | iExact "A68"].
  Qed.

  (* ...and the move the [bad:] tail makes: slots 5,7..13 lose their values,
     the elf run goes back into the middle [stack_own], and what is left is
     exactly [kxc_frameA6] at slot 6. *)
  Lemma kxc_frameB65_to_A6 (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w65 w67 : mword 64)
      (ef : nat -> bv 8) :
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    kxc_frameB65 sp0 ra0 s00 s10 s20 pv av
                 w5 w6 w7 w8 w9 w10 w11 w12 w13 w65 w67 -∗
    ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ ef j) -∗
    kxc_frameA6 sp0 ra0 s00 s10 s20 pv av w6.
  Proof.
    intro Hal. rewrite /kxc_frameB65 /kxc_frameA6.
    iIntros "(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 &
              A13 & Aust & Aph & A64 & A65 & A66 & A67 & A68) Helf".
    iDestruct (kxc_elf_give sp0 ef Hal with "Helf") as "Aelf".
    iSplitL "A1"; [iExact "A1" |]. iSplitL "A2"; [iExact "A2" |].
    iSplitL "A3"; [iExact "A3" |]. iSplitL "A4"; [iExact "A4" |].
    iSplitL "A5"; [by iExists w5 |]. iSplitL "A6"; [iExact "A6" |].
    iSplitL "A7"; [by iExists w7 |]. iSplitL "A8"; [by iExists w8 |].
    iSplitL "A9"; [by iExists w9 |]. iSplitL "A10"; [by iExists w10 |].
    iSplitL "A11"; [by iExists w11 |]. iSplitL "A12"; [by iExists w12 |].
    iSplitL "A13"; [by iExists w13 |].
    iSplitR "A64 A65 A66 A67 A68".
    { iApply (kxc_mid_join sp0 with "Aust Aelf Aph"). }
    iSplitL "A64"; [iExact "A64" |]. iSplitL "A65"; [by iExists w65 |].
    iSplitL "A66"; [iExact "A66" |]. iSplitL "A67"; [by iExists w67 |].
    iExact "A68".
  Qed.

End KexecB2Frame.
