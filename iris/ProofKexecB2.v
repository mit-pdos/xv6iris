(* ProofKexecB2.v -- PHASE B of kexec, SECOND CHUNK: the phdr loop, the
   inlined loadseg loop, and the six [bad:] tails they share.

   Its entry seams are ProofKexecSeam.v's [kxc_at_12c] (the phdr loop's BODY,
   which is also its head) and [kxc_at_1a2] (the no-segments path); its exit
   is +0x1ae, phase C's entry.  Nothing here requires ProofKexecB.v -- the
   two chunks meet only through ProofKexecSeam.v, so they compile in
   parallel (ProofKexecTail.v's header has the measurement that made that a
   rule).

   ---- THE FRAME ALGEBRA -------------------------------------------------

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

   ---- [kxc_bad324]: THE TAIL SIX OF THE EIGHT [bad:] ENTRIES SHARE ------

   PROVEN.  The +0x320 /
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
   IS THE COVERAGE INVARIANT").  So the tail asks its callers for coverage,
   not for a bound they would have no way to establish.

   AND IT ASKS FOR NO THREADING CLAUSE AT ALL.  [kxc_bad64] wants
   [Mt r = m r] for every callee-saved [r] outside {sp,s0,s1,s2,s4} -- which
   is exactly {s3,s5..s11}, the eight this tail reloads.  So whatever the two
   loops left in those registers is dead, and the six entries do not have to
   agree about them.  That is what makes ONE tail serve all six.

   ---- WHAT COMES NEXT ---------------------------------------------------

   The two loops, and the five [bad:] stubs that reach the tail above.  Each
   stub is [sd s2,-520(s0)] then a [c.j] to +0x324 (+0x320 falls straight
   through), reached from a different point in the loop with a different
   [s2], so they are written at their branch sites rather than lifted: what
   they share is [kxc_bad324], which starts after the store. *)
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
Require Import SpecProcPagetable.
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

(* ===================================================================== *)
(*  THE PROOF.                                                            *)
(* ===================================================================== *)
(* Seven of the eight functor arguments are here only to build [A], the
   KexecTailProof instance that owns [kxc_bad64] -- the +0x064 tail every
   [bad:] entry in this file eventually falls into.  The eighth, [PFP], is
   this chunk's own: the +0x324 tail frees the half-built table. *)
Module KexecB2Proof (Myproc : MYPROC) (BeginOp : BEGIN_OP) (Namei : NAMEI)
                    (Ilock : ILOCK) (Readi : READI) (Iunlockput : IUNLOCKPUT)
                    (EndOp : END_OP) (PFP : PROC_FREEPAGETABLE).

Module A := ProofKexecTail.KexecTailProof Myproc BeginOp Namei Ilock Readi
                                          Iunlockput EndOp.

Section KexecB2Body.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !iregG Σ}.
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
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  Local Ltac regne := reg_ne_side.
  Local Ltac pcw := apply bv_eq; vm_compute; reflexivity.
  Local Ltac nz := vm_compute; discriminate.
  (* an [ld/sd rd,-N(s0)] displacement, with [s0 = sp0]: the slot is [N/8],
     and the immediate the decoder shows is [4096 - N].  One tactic instead
     of the family of named [kxc_*_slot] lemmas above it. *)
  Local Ltac s0slot := apply stk_push; apply bv_eq; vm_compute; reflexivity.

  (* =================================================================== *)
  (*  +0x324 .. +0x33e -- THE TAIL SIX OF KEXEC'S EIGHT [bad:] ENTRIES    *)
  (*  SHARE.                                                              *)
  (*                                                                      *)
  (*    ld a1,-520(s0)    a1 = slot 65, the size to free                  *)
  (*    mv a0,s6          a0 = the NEW table's root                       *)
  (*    jal proc_freepagetable                                            *)
  (*    ld s3,504(sp) ... ld s11,440(sp)   -- slots 5, 7..13              *)
  (*    j +0x64           -- ProofKexecTail's [kxc_bad64]                 *)
  (*                                                                      *)
  (*  IT TAKES NO THREADING PREMISE, and that is the point of the eight    *)
  (*  reloads: [kxc_bad64] wants [Mt r = m r] for every callee-saved [r]   *)
  (*  outside {sp,s0,s1,s2,s4}, which is exactly {s3,s5..s11} -- the       *)
  (*  eight this tail restores from the frame.  Whatever the loop left in  *)
  (*  those registers is overwritten before it can matter.                 *)
  (*                                                                      *)
  (*  THE SIZE PREMISE IS COVERAGE, NOT A BOUND.  proc_freepagetable wants *)
  (*  [uint szf <= uvm_maxsz], which nothing in the phdr loop can          *)
  (*  establish -- [newsz] comes out of the executable.  It is a           *)
  (*  projection of the coverage half of the loop invariant                *)
  (*  ([UmCovered.proc_pt_covered_maxsz]), so that is what this asks for.  *)
  (* =================================================================== *)
  Lemma kxc_bad324
      (gs : list gname) (jp : nat) (gl : gname)
      (gu : uart_names) (gd : disk_names) (gk : gname) (pd pav pu : mword 64)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (gtl : gname) (gilf gislf : gname) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used used2 : gset Z)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (alen aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m Mt : regfile) (K : nat) (C : iProp Σ)
      (sp0 ra0 s00 s10 s20 pv av w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (szf : mword 64) :
    (K_kexec <= K)%nat ->
    (kf < NINODE)%nat ->
    log_geom_ok cov logstart ->
    0 < size <= BPB ->
    0 <= bmapstart ->
    bmapstart ∈ cov ->
    ~ (bmapstart ∈ log_region_set logstart) ->
    0 <= inodestart ->
    cov_below cov size ->
    ireg_blocks_ok inodestart nib cov logstart ->
    bv_unsigned inumf < 16 * Z.of_nat nib ->
    (iput_units <= n2)%nat ->
    (jp < NPROC)%nat ->
    gs !! jp = Some gl ->
    used2 ⊆ used ->
    m !!! Regidx csp_rs1 = sp0 ->
    m !!! Regidx Rra = ra0 ->
    m !!! Regidx Rs0 = s00 ->
    m !!! Regidx Rs1 = s10 ->
    m !!! Regidx Rs2 = s20 ->
    (* ---- the register state at +0x324 ---- *)
    Mt !!! Regidx csp_rs1 = pa_stk sp0 68 ->
    Mt !!! Regidx Rs0 = sp0 ->
    Mt !!! Regidx Rs4 = ientry kf ->
    Mt !!! Regidx Rs6 = page_base P.(ud_root) ->
    (* ---- the frame's elf run, and the size to free ---- *)
    (forall j, (j < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - j))) 8 = true) ->
    um_below szf P.(ud_um) ->
    um_covered szf P.(ud_um) ->
    sie_cap_gpr Mt (K - 68)%nat true (proc_addr jp) -∗
    cpu_own 0 true (proc_addr jp) C true -∗
    kernel_text -∗
    panic_wp_any -∗
    pc_is (mword_of_int (KXB + 0x324) : mword 64) -∗
    fs_fabric gs gu gd gk pd pav pu bn g gfs gi cn gtl
              cov logstart inodestart nib dev -∗
    kxc_open gfs gi cn cov logstart dev pidv kf qf sf gyf inumf dnf bmf
             gilf gislf -∗
    sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) -∗
    sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) -∗
    bitmap_res gfs bmapstart cov logstart size used2 -∗
    kalloc_env ga None -∗
    proc_pt P -∗
    proc_priv gf (proc_addr jp) pidv V -∗
    ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) -∗
    ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) -∗
    ([∗ list] i ∈ seq 0 na,
       [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) -∗
    ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ ef j) -∗
    bslots bn 3 -∗
    iref_slots 1 -∗
    log_op g n2 -∗
    kxc_frameB65 sp0 ra0 s00 s10 s20 pv av
      (m !!! Regidx Rs3) (m !!! Regidx Rs4) (m !!! Regidx Rs5)
      (m !!! Regidx Rs6) (m !!! Regidx Rs7) (m !!! Regidx Rs8)
      (m !!! Regidx Rs9) (m !!! Regidx Rs10) (m !!! Regidx Rs11)
      szf w67 -∗
    (* ---- kexec's own continuation, which [kxc_bad64] closes ---- *)
    wp_next true (proc_addr jp) (fun (CID : CpuId) =>
      ∀ (mf : regfile) (used' : gset Z) (V' : pprivate)
        (entry spv szv' : mword 64),
          ⌜callee_saved m mf⌝ -∗
          ⌜kexec_ok V V' (mf !!! Regidx Ra0) entry spv szv' na alen⌝ -∗
          sie_cap_gpr mf K true (proc_addr jp) -∗
          cpu_own 0 true (proc_addr jp) C true -∗
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
    WP (Loop : expr riscv_lang).
  Proof.
    intros HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hcovb Hiregb Hib Hn2 Hjp Hgs Hu2
           Hsp Hra Hs0 Hs1 Hs2 HMtsp HMts0 HMts4 HMts6 Hal Hbelow Hcov.
    pose proof HK as HK'. unfold K_kexec in HK'.
    destruct (Hiregb inumf Hib) as [Hibc Hibl].
    (* [kalloc_env γa None] is PERSISTENT (KvmSpec.v) and MUST be introduced
       with [#]: proc_freepagetable consumes it and its postcondition does not
       hand it back, while [kxc_bad64] needs it at the exit.  Introduced
       exclusively, the second use fails with [iSpecialize: "Hka" not found]
       -- which names the hypothesis and not the reason. *)
    iIntros "Hcg Hcnt #Htext #Hpanic Hpc #Hfab Hopen Hbm Hins Hbits #Hka Hpt
             Hpriv Hpath Hargv Hargs Helf Hbs Hirs Hlog Hframe Hcont".
    rewrite /kxc_frameB65.
    iDestruct "Hframe" as "(Hf1 & Hf2 & Hf3 & Hf4 & Hf5 & Hf6 & Hf7 & Hf8 &
                            Hf9 & Hf10 & Hf11 & Hf12 & Hf13 & Hust & Hph &
                            Hf64 & Hf65 & Hf66 & Hf67 & Hf68)".
    iPoseProof (kxc_324 with "Htext") as "Hi324".
    iPoseProof (kxc_328 with "Htext") as "Hi328".
    iPoseProof (kxc_32a with "Htext") as "Hi32a".
    iPoseProof (kxc_32e with "Htext") as "Hi32e".
    iPoseProof (kxc_330 with "Htext") as "Hi330".
    iPoseProof (kxc_332 with "Htext") as "Hi332".
    iPoseProof (kxc_334 with "Htext") as "Hi334".
    iPoseProof (kxc_336 with "Htext") as "Hi336".
    iPoseProof (kxc_338 with "Htext") as "Hi338".
    iPoseProof (kxc_33a with "Htext") as "Hi33a".
    iPoseProof (kxc_33c with "Htext") as "Hi33c".
    iPoseProof (kxc_33e with "Htext") as "Hi33e".
    (* ---- +0x324: ld a1,-520(s0) -- the size the tail frees ---- *)
    assert (Hpa65 : add_vec (rget Mt Rs0)
                      (sign_extend' 64 (mword_of_int 3576 : mword 12))
                    = pa_stk sp0 65).
    { rewrite (rget_ne Mt Rs0 ltac:(nz)) HMts0. s0slot. }
    iEval (rewrite -Hpa65) in "Hf65".
    iApply (wp_ld_s_sconf (mword_of_int (KXB + 0x324)) Ra1 Rs0
              (mword_of_int 3576 : mword 12) Mt (K - 68)%nat szf true
              (dqm := DfracOwn 1) ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi324 Hf65").
    iIntros (CID1 Hsq1) "Hcg Hpc Hf65". iEval (rewrite Hpa65) in "Hf65".
    set (T1 := <[Regidx Ra1 := regval_into_reg szf]> Mt).
    assert (HT1a1 : T1 !!! Regidx Ra1 = szf) by (rewrite /T1; apply upd_eq).
    assert (HT1sp : T1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T1 upd_ne; [exact HMtsp | nz]).
    assert (HT1s0 : T1 !!! Regidx Rs0 = sp0)
      by (rewrite /T1 upd_ne; [exact HMts0 | nz]).
    assert (HT1s4 : T1 !!! Regidx Rs4 = ientry kf)
      by (rewrite /T1 upd_ne; [exact HMts4 | nz]).
    assert (HT1s6 : T1 !!! Regidx Rs6 = page_base P.(ud_root))
      by (rewrite /T1 upd_ne; [exact HMts6 | nz]).
    assert (Hpp328 : add_vec_int (mword_of_int (KXB + 0x324) : mword 64) 4
                     = mword_of_int (KXB + 0x328)) by pcw.
    iEval (rewrite Hpp328) in "Hpc".
    (* ---- +0x328: c.mv a0,s6 -- the table to destroy ---- *)
    iApply (wp_cmv_s_sconf (mword_of_int (KXB + 0x328)) Ra0 Rs6
              T1 (K - 68)%nat true ltac:(nz) ltac:(rdok)
              with "Hcg Hpc Hi328").
    iIntros (CID2 Hsq2) "Hcg Hpc". iEval (rgne) in "Hcg".
    set (T2 := <[Regidx Ra0 := regval_into_reg
                  (add_vec zero_reg (T1 !!! Regidx Rs6))]> T1).
    assert (HT2a0 : T2 !!! Regidx Ra0 = page_base P.(ud_root)).
    { rewrite /T2 upd_eq HT1s6. apply add_vec_zero_l. }
    assert (HT2a1 : T2 !!! Regidx Ra1 = szf)
      by (rewrite /T2 upd_ne; [exact HT1a1 | nz]).
    assert (HT2sp : T2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T2 upd_ne; [exact HT1sp | nz]).
    assert (HT2s0 : T2 !!! Regidx Rs0 = sp0)
      by (rewrite /T2 upd_ne; [exact HT1s0 | nz]).
    assert (HT2s4 : T2 !!! Regidx Rs4 = ientry kf)
      by (rewrite /T2 upd_ne; [exact HT1s4 | nz]).
    assert (Hpp32a : add_vec_int (mword_of_int (KXB + 0x328) : mword 64) 2
                     = mword_of_int (KXB + 0x32a)) by pcw.
    iEval (rewrite Hpp32a) in "Hpc".
    (* ---- +0x32a: jal ra,proc_freepagetable ---- *)
    assert (Htpf : add_vec (mword_of_int (KXB + 0x32a) : mword 64)
                     (sign_extend' 64 (mword_of_int 2084850 : mword 21))
                   = mword_of_int KernelSyms.proc_freepagetable) by pcw.
    iApply (wp_jal_s_sconf (mword_of_int (KXB + 0x32a)) Rra
              (mword_of_int 2084850 : mword 21) T2 (K - 68)%nat true
              ltac:(nz) ltac:(rdok)
              ltac:(rewrite Htpf; vm_compute; reflexivity)
              with "Hcg Hpc Hi32a").
    iIntros (CID3 Hsq3) "Hcg Hpc". iEval (rewrite Htpf) in "Hpc".
    set (T3 := <[Regidx Rra := regval_into_reg
                  (add_vec_int (mword_of_int (KXB + 0x32a) : mword 64) 4)]> T2).
    change (<[Regidx Rra := regval_into_reg
              (add_vec_int (mword_of_int (KXB + 0x32a) : mword 64) 4)]> T2)
      with T3.
    assert (HT3ra : T3 !!! Regidx Rra
                    = add_vec_int (mword_of_int (KXB + 0x32a) : mword 64) 4)
      by (rewrite /T3; apply upd_eq).
    assert (HT3a0 : T3 !!! Regidx Ra0 = page_base P.(ud_root))
      by (rewrite /T3 upd_ne; [exact HT2a0 | nz]).
    assert (HT3a1 : T3 !!! Regidx Ra1 = szf)
      by (rewrite /T3 upd_ne; [exact HT2a1 | nz]).
    assert (HT3sp : T3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /T3 upd_ne; [exact HT2sp | nz]).
    assert (HT3s0 : T3 !!! Regidx Rs0 = sp0)
      by (rewrite /T3 upd_ne; [exact HT2s0 | nz]).
    assert (HT3s4 : T3 !!! Regidx Rs4 = ientry kf)
      by (rewrite /T3 upd_ne; [exact HT2s4 | nz]).
    (* the size bound, read off COVERAGE -- see the header *)
    iDestruct (proc_pt_wf_get P with "Hpt") as %Hwf.
    iDestruct (cpu_own_transport CID0 CID3 0%nat true (proc_addr jp) C true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iApply (PFP.wp_proc_freepagetable_sconf ga T3 P (K - 68)%nat true
              (proc_addr jp) C 0%nat true
              ltac:(lia) kxc_lvl0 HT3a0
              ltac:(rewrite HT3a1 uint_unsigned;
                    exact (proc_pt_covered_maxsz P szf Hwf Hcov))
              ltac:(rewrite HT3a1; exact Hbelow)
              with "Hcg Hcnt Htext Hpc Hpt Hka").
    iIntros (CID4 Hsq4 mr) "Hcg Hcnt Hpc %Hcspf".
    assert (Hpc32e : ret_pc (T3 !!! Regidx Rra) = mword_of_int (KXB + 0x32e))
      by (rewrite HT3ra; pcw).
    iEval (rewrite Hpc32e) in "Hpc".
    assert (Hmrsp : mr !!! Regidx csp_rs1 = pa_stk sp0 68).
    { rewrite (callee_saved_lookup Hcspf csp_rs1 ltac:(vm_compute; reflexivity)).
      exact HT3sp. }
    assert (Hmrs0 : mr !!! Regidx Rs0 = sp0).
    { rewrite (callee_saved_lookup Hcspf Rs0 ltac:(vm_compute; reflexivity)).
      exact HT3s0. }
    assert (Hmrs4 : mr !!! Regidx Rs4 = ientry kf).
    { rewrite (callee_saved_lookup Hcspf Rs4 ltac:(vm_compute; reflexivity)).
      exact HT3s4. }
    (* ---- +0x32e .. +0x33c: the eight reloads ---- *)
    (* +0x32e: c.ldsp s3,504(sp) *)
    assert (Hpa5 : add_vec (mr !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 63 : mword 6) ('b"000")))
                   = pa_stk sp0 5).
    { rewrite Hmrsp. apply (kxc_sp_slot sp0 5 63 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa5) in "Hf5".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x32e))
              (mword_of_int 63 : mword 6) Rs3 mr (K - 68)%nat
              (m !!! Regidx Rs3) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi32e Hf5").
    iIntros (CID5 Hsq5) "Hcg Hpc Hf5". iEval (rewrite Hpa5) in "Hf5".
    set (U1 := <[Regidx Rs3 := regval_into_reg (m !!! Regidx Rs3)]> mr).
    assert (HU1sp : U1 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U1 upd_ne; [exact Hmrsp | nz]).
    assert (Hpp330 : add_vec_int (mword_of_int (KXB + 0x32e) : mword 64) 2
                     = mword_of_int (KXB + 0x330)) by pcw.
    iEval (rewrite Hpp330) in "Hpc".
    (* +0x330: c.ldsp s5,488(sp) *)
    assert (Hpa7 : add_vec (U1 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 61 : mword 6) ('b"000")))
                   = pa_stk sp0 7).
    { rewrite HU1sp. apply (kxc_sp_slot sp0 7 61 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa7) in "Hf7".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x330))
              (mword_of_int 61 : mword 6) Rs5 U1 (K - 68)%nat
              (m !!! Regidx Rs5) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi330 Hf7").
    iIntros (CID6 Hsq6) "Hcg Hpc Hf7". iEval (rewrite Hpa7) in "Hf7".
    set (U2 := <[Regidx Rs5 := regval_into_reg (m !!! Regidx Rs5)]> U1).
    assert (HU2sp : U2 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U2 upd_ne; [exact HU1sp | nz]).
    assert (Hpp332 : add_vec_int (mword_of_int (KXB + 0x330) : mword 64) 2
                     = mword_of_int (KXB + 0x332)) by pcw.
    iEval (rewrite Hpp332) in "Hpc".
    (* +0x332: c.ldsp s6,480(sp) *)
    assert (Hpa8 : add_vec (U2 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 60 : mword 6) ('b"000")))
                   = pa_stk sp0 8).
    { rewrite HU2sp. apply (kxc_sp_slot sp0 8 60 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa8) in "Hf8".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x332))
              (mword_of_int 60 : mword 6) Rs6 U2 (K - 68)%nat
              (m !!! Regidx Rs6) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi332 Hf8").
    iIntros (CID7 Hsq7) "Hcg Hpc Hf8". iEval (rewrite Hpa8) in "Hf8".
    set (U3 := <[Regidx Rs6 := regval_into_reg (m !!! Regidx Rs6)]> U2).
    assert (HU3sp : U3 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U3 upd_ne; [exact HU2sp | nz]).
    assert (Hpp334 : add_vec_int (mword_of_int (KXB + 0x332) : mword 64) 2
                     = mword_of_int (KXB + 0x334)) by pcw.
    iEval (rewrite Hpp334) in "Hpc".
    (* +0x334: c.ldsp s7,472(sp) *)
    assert (Hpa9 : add_vec (U3 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 59 : mword 6) ('b"000")))
                   = pa_stk sp0 9).
    { rewrite HU3sp. apply (kxc_sp_slot sp0 9 59 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa9) in "Hf9".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x334))
              (mword_of_int 59 : mword 6) Rs7 U3 (K - 68)%nat
              (m !!! Regidx Rs7) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi334 Hf9").
    iIntros (CID8 Hsq8) "Hcg Hpc Hf9". iEval (rewrite Hpa9) in "Hf9".
    set (U4 := <[Regidx Rs7 := regval_into_reg (m !!! Regidx Rs7)]> U3).
    assert (HU4sp : U4 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U4 upd_ne; [exact HU3sp | nz]).
    assert (Hpp336 : add_vec_int (mword_of_int (KXB + 0x334) : mword 64) 2
                     = mword_of_int (KXB + 0x336)) by pcw.
    iEval (rewrite Hpp336) in "Hpc".
    (* +0x336: c.ldsp s8,464(sp) *)
    assert (Hpa10 : add_vec (U4 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 58 : mword 6) ('b"000")))
                    = pa_stk sp0 10).
    { rewrite HU4sp. apply (kxc_sp_slot sp0 10 58 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa10) in "Hf10".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x336))
              (mword_of_int 58 : mword 6) Rs8 U4 (K - 68)%nat
              (m !!! Regidx Rs8) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi336 Hf10").
    iIntros (CID9 Hsq9) "Hcg Hpc Hf10". iEval (rewrite Hpa10) in "Hf10".
    set (U5 := <[Regidx Rs8 := regval_into_reg (m !!! Regidx Rs8)]> U4).
    assert (HU5sp : U5 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U5 upd_ne; [exact HU4sp | nz]).
    assert (Hpp338 : add_vec_int (mword_of_int (KXB + 0x336) : mword 64) 2
                     = mword_of_int (KXB + 0x338)) by pcw.
    iEval (rewrite Hpp338) in "Hpc".
    (* +0x338: c.ldsp s9,456(sp) *)
    assert (Hpa11 : add_vec (U5 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 57 : mword 6) ('b"000")))
                    = pa_stk sp0 11).
    { rewrite HU5sp. apply (kxc_sp_slot sp0 11 57 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa11) in "Hf11".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x338))
              (mword_of_int 57 : mword 6) Rs9 U5 (K - 68)%nat
              (m !!! Regidx Rs9) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi338 Hf11").
    iIntros (CID10 Hsq10) "Hcg Hpc Hf11". iEval (rewrite Hpa11) in "Hf11".
    set (U6 := <[Regidx Rs9 := regval_into_reg (m !!! Regidx Rs9)]> U5).
    assert (HU6sp : U6 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U6 upd_ne; [exact HU5sp | nz]).
    assert (Hpp33a : add_vec_int (mword_of_int (KXB + 0x338) : mword 64) 2
                     = mword_of_int (KXB + 0x33a)) by pcw.
    iEval (rewrite Hpp33a) in "Hpc".
    (* +0x33a: c.ldsp s10,448(sp) *)
    assert (Hpa12 : add_vec (U6 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 56 : mword 6) ('b"000")))
                    = pa_stk sp0 12).
    { rewrite HU6sp. apply (kxc_sp_slot sp0 12 56 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa12) in "Hf12".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x33a))
              (mword_of_int 56 : mword 6) Rs10 U6 (K - 68)%nat
              (m !!! Regidx Rs10) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi33a Hf12").
    iIntros (CID11 Hsq11) "Hcg Hpc Hf12". iEval (rewrite Hpa12) in "Hf12".
    set (U7 := <[Regidx Rs10 := regval_into_reg (m !!! Regidx Rs10)]> U6).
    assert (HU7sp : U7 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U7 upd_ne; [exact HU6sp | nz]).
    assert (Hpp33c : add_vec_int (mword_of_int (KXB + 0x33a) : mword 64) 2
                     = mword_of_int (KXB + 0x33c)) by pcw.
    iEval (rewrite Hpp33c) in "Hpc".
    (* +0x33c: c.ldsp s11,440(sp) *)
    assert (Hpa13 : add_vec (U7 !!! Regidx csp_rs1)
              (zero_extend' 64 (concat_vec (mword_of_int 55 : mword 6) ('b"000")))
                    = pa_stk sp0 13).
    { rewrite HU7sp. apply (kxc_sp_slot sp0 13 55 _ ltac:(lia)). pcw. }
    iEval (rewrite -Hpa13) in "Hf13".
    iApply (wp_cldsp_s_sconf (mword_of_int (KXB + 0x33c))
              (mword_of_int 55 : mword 6) Rs11 U7 (K - 68)%nat
              (m !!! Regidx Rs11) true (dqm := DfracOwn 1)
              ltac:(nz) ltac:(rdok) with "Hcg Hpc Hi33c Hf13").
    iIntros (CID12 Hsq12) "Hcg Hpc Hf13". iEval (rewrite Hpa13) in "Hf13".
    set (U8 := <[Regidx Rs11 := regval_into_reg (m !!! Regidx Rs11)]> U7).
    assert (HU8sp : U8 !!! Regidx csp_rs1 = pa_stk sp0 68)
      by (rewrite /U8 upd_ne; [exact HU7sp | nz]).
    (* the eight registers now hold kexec's entry values again, which is
       exactly [kxc_bad64]'s threading premise -- see the header. *)
    assert (HU8s4 : U8 !!! Regidx Rs4 = ientry kf).
    { rewrite /U8 upd_ne; [| nz]. rewrite /U7 upd_ne; [| nz].
      rewrite /U6 upd_ne; [| nz]. rewrite /U5 upd_ne; [| nz].
      rewrite /U4 upd_ne; [| nz]. rewrite /U3 upd_ne; [| nz].
      rewrite /U2 upd_ne; [| nz]. rewrite /U1 upd_ne; [| nz].
      exact Hmrs4. }
    assert (HU8thr : forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
              r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 ->
              U8 !!! Regidx r = m !!! Regidx r).
    { intros r Hr Nsp Ns0 Ns1 Ns2 Ns4.
      destruct (kxc_cs_cases r Hr)
        as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
           [-> | [-> | ->]]]]]]]]]]]];
        try (exfalso; congruence).
      - (* s3 : slot 5 *)
        rewrite /U8 upd_ne; [| nz]. rewrite /U7 upd_ne; [| nz].
        rewrite /U6 upd_ne; [| nz]. rewrite /U5 upd_ne; [| nz].
        rewrite /U4 upd_ne; [| nz]. rewrite /U3 upd_ne; [| nz].
        rewrite /U2 upd_ne; [| nz]. rewrite /U1 upd_eq. reflexivity.
      - (* s5 : slot 7 *)
        rewrite /U8 upd_ne; [| nz]. rewrite /U7 upd_ne; [| nz].
        rewrite /U6 upd_ne; [| nz]. rewrite /U5 upd_ne; [| nz].
        rewrite /U4 upd_ne; [| nz]. rewrite /U3 upd_ne; [| nz].
        rewrite /U2 upd_eq. reflexivity.
      - (* s6 : slot 8 *)
        rewrite /U8 upd_ne; [| nz]. rewrite /U7 upd_ne; [| nz].
        rewrite /U6 upd_ne; [| nz]. rewrite /U5 upd_ne; [| nz].
        rewrite /U4 upd_ne; [| nz]. rewrite /U3 upd_eq. reflexivity.
      - (* s7 : slot 9 *)
        rewrite /U8 upd_ne; [| nz]. rewrite /U7 upd_ne; [| nz].
        rewrite /U6 upd_ne; [| nz]. rewrite /U5 upd_ne; [| nz].
        rewrite /U4 upd_eq. reflexivity.
      - (* s8 : slot 10 *)
        rewrite /U8 upd_ne; [| nz]. rewrite /U7 upd_ne; [| nz].
        rewrite /U6 upd_ne; [| nz]. rewrite /U5 upd_eq. reflexivity.
      - (* s9 : slot 11 *)
        rewrite /U8 upd_ne; [| nz]. rewrite /U7 upd_ne; [| nz].
        rewrite /U6 upd_eq. reflexivity.
      - (* s10 : slot 12 *)
        rewrite /U8 upd_ne; [| nz]. rewrite /U7 upd_eq. reflexivity.
      - (* s11 : slot 13 *)
        rewrite /U8 upd_eq. reflexivity. }
    assert (Hpp33e : add_vec_int (mword_of_int (KXB + 0x33c) : mword 64) 2
                     = mword_of_int (KXB + 0x33e)) by pcw.
    iEval (rewrite Hpp33e) in "Hpc".
    (* ---- +0x33e: c.j +0x64 -- into the shared [bad:] tail ---- *)
    assert (Htgt64 : add_vec (mword_of_int (KXB + 0x33e) : mword 64)
              (sign_extend' 64
                 (sign_extend' 21 (concat_vec (mword_of_int 1683 : mword 11)
                                              ('b"0"))))
            = mword_of_int (KXB + 0x64)) by pcw.
    iApply (wp_cj_s_sconf (mword_of_int (KXB + 0x33e))
              (sign_extend' 21 (concat_vec (mword_of_int 1683 : mword 11)
                                           ('b"0")))
              U8 (K - 68)%nat true
              ltac:(rewrite Htgt64; vm_compute; reflexivity)
              with "Hcg Hpc Hi33e").
    iIntros (CID13 Hsq13). iNext. iIntros "Hcg Hpc".
    iEval (rewrite Htgt64) in "Hpc".
    iDestruct (cpu_own_transport CID4 CID13 0%nat true (proc_addr jp) C true
                 ltac:(wp_next_chain) with "Hcnt") as "Hcnt".
    iDestruct "Hopen" as "(#Hslkk & Hslkd & Hslpid & Hdep & Hidev & Hiinum &
                           Hivalid & Hload & #Hity & Hkeep)".
    (* [kxc_bad64] pins its own [CID0] from "Hcg", so kexec's exit -- still
       anchored at the section's [CID0] -- is re-anchored there, and the
       crossing fact goes by NAME (durable-notes.md). *)
    assert (Hcr : true = false \/ proc_addr jp = zero_reg ->
                  (CID13 : CPU) = (CID0 : CPU)) by wp_next_chain.
    iDestruct (wp_next_retarget CID0 CID13 true (proc_addr jp) _ Hcr
                 with "Hcont") as "Hcont".
    iApply (A.kxc_bad64 gs jp gl gu gd gk pd pav pu bn g gfs gi cn gtl
              gilf gislf ga gf cov logstart bmapstart inodestart nib size
              dev used used2 kf qf sf gyf inumf dnf bmf n2
              plen pfun na avf alen aslen afun pidv V dqb dqs dqa
              m U8 K C sp0 ra0 s00 s10 s20 pv av
              HK Hk Hlg Hsz Hbm0 Hbmc Hbml Hins0 Hibc Hibl Hib Hcovb Hn2
              Hjp Hgs Hu2 Hsp Hra Hs0 Hs1 Hs2 HU8sp HU8s4 HU8thr
              with "Hcg Hcnt Htext Hpanic Hpc Hfab Hslkk Hslkd Hslpid Hdep
                    Hidev Hiinum Hivalid Hload Hity Hkeep Hbm Hins Hbits
                    Hka Hpriv Hpath Hargv Hargs Hbs Hirs Hlog [-Hcont]
                    Hcont").
    iApply (kxc_frameB65_to_A6 sp0 ra0 s00 s10 s20 pv av
              _ _ _ _ _ _ _ _ _ _ _ ef Hal with "[-Helf] Helf").
    rewrite /kxc_frameB65.
    iSplitL "Hf1"; [iExact "Hf1" |]. iSplitL "Hf2"; [iExact "Hf2" |].
    iSplitL "Hf3"; [iExact "Hf3" |]. iSplitL "Hf4"; [iExact "Hf4" |].
    iSplitL "Hf5"; [iExact "Hf5" |]. iSplitL "Hf6"; [iExact "Hf6" |].
    iSplitL "Hf7"; [iExact "Hf7" |]. iSplitL "Hf8"; [iExact "Hf8" |].
    iSplitL "Hf9"; [iExact "Hf9" |]. iSplitL "Hf10"; [iExact "Hf10" |].
    iSplitL "Hf11"; [iExact "Hf11" |]. iSplitL "Hf12"; [iExact "Hf12" |].
    iSplitL "Hf13"; [iExact "Hf13" |]. iSplitL "Hust"; [iExact "Hust" |].
    iSplitL "Hph"; [iExact "Hph" |]. iSplitL "Hf64"; [iExact "Hf64" |].
    iSplitL "Hf65"; [iExact "Hf65" |]. iSplitL "Hf66"; [iExact "Hf66" |].
    iSplitL "Hf67"; [iExact "Hf67" | iExact "Hf68"].
  Qed.

End KexecB2Body.

End KexecB2Proof.
