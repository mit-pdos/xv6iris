(* ProofKexecSeam.v -- the DEFINITIONAL layer phases B1 and B2 share: the
   frame algebra from +0x090 onward, the ELF-buffer carve and its two read
   windows, the [off] register's [int] truncation, and the two named states
   the phdr-loop setup produces ([kxc_at_1a2], [kxc_at_12c]).

   It is its own file for the reason ProofKexecTail.v is: a Rocq functor
   cannot span two files, but a DEFINITION does not need one, and phases that
   reach each other put the two files in SERIES on the build's critical path.
   B1 produces these states and B2 consumes them; neither should wait for the
   other to compile.  Nothing here mentions a functor argument.

   THE COVERAGE INVARIANT IS [UmCovered.um_covered], NOT A LOCAL COPY, and it
   deliberately carries NO [pte_vu] conjunct.  It is what BOUNDS the size --
   uvmalloc's [newsz] comes out of the executable and cannot be bounded any
   other way (see claude-notes/projects/kexec.md, "THE SIZE BOUND IS THE
   COVERAGE INVARIANT") -- and uvmalloc's postcondition pins the new map's
   DOMAIN and nothing about the words in it, so a coverage predicate with a
   [pte_vu] conjunct would not survive the very call the invariant exists for.
   [bv_unsigned szv <= uvm_maxsz] is likewise absent: it is a projection
   ([UmCovered.proc_pt_covered_maxsz]), not an independent fact to carry. *)

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
(* EXPORT, not Import: the seam states carry [um_covered], so every
   consumer needs its vocabulary and its zero-size discharge. *)
Require Export UmCovered.
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
Require Import SpecProcPagetable.
Require Import ProofKexecParts.
Require Import ProofKexecTail.
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
(*  PURE ARITHMETIC.                                                      *)
(* ===================================================================== *)

(* THE sp-RELATIVE SLOT of a [c.sdsp]/[c.ldsp] immediate, once and for all.
   The running sp is [pa_stk sp0 68], the scaled immediate is [8*r], and the
   slot reached is [68 - r] -- given here as [j] with [j + r = 68] so the
   caller's numerals are the two the instruction stream shows.  Eight
   instances below (uimm 60,63,61,59,58,57,56,55 -> slots 8,5,7,9,10,11,12,13)
   plus the +0x31c reload. *)
Lemma kxc_sp_slot (X : mword 64) (j r : nat) (v : mword 64) :
  (j + r = 68)%nat ->
  add_vec (mword_of_int (- (8 * Z.of_nat r)) : mword 64) v = mword_of_int 0 ->
  add_vec (pa_stk X 68) v = pa_stk X j.
Proof.
  intros Hjr Hv. rewrite -Hjr -(pa_stk_assoc X j r). apply stk_pop. exact Hv.
Qed.

(* The three s0-relative displacements this chunk uses.  [addi/ld/sd rd,-N(s0)]
   is [sign_extend' 64 (mword_of_int (4096-N) : mword 12)] and [s0] is [sp0],
   so the slot is [N/8]. *)
Lemma kxc_phnum_slot (X : mword 64) :     (* lhu a5,-376(s0) : elf.phnum *)
  add_vec X (sign_extend' 64 (mword_of_int 3720 : mword 12)) = pa_stk X 47.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kxc_phoff_slot (X : mword 64) :     (* lw a3,-400(s0) : elf.phoff *)
  add_vec X (sign_extend' 64 (mword_of_int 3696 : mword 12)) = pa_stk X 50.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma kxc_mask_slot (X : mword 64) :      (* sd a5,-536(s0) : the 0xfff mask *)
  add_vec X (sign_extend' 64 (mword_of_int 3560 : mword 12)) = pa_stk X 67.
Proof. apply stk_push. apply bv_eq; vm_compute; reflexivity. Qed.

(* ...and the two byte OFFSETS inside the elf buffer, whose base is slot 54:
   [phoff@32] is slot 50 and [phnum@56] is slot 47. *)
Lemma kxc_elf_off32 (X : mword 64) : pa_add (pa_stk X 54) 32 = pa_stk X 50.
Proof. unfold pa_add, pa_stk. rewrite avi_assoc. f_equal; lia. Qed.

Lemma kxc_elf_off56 (X : mword 64) : pa_add (pa_stk X 54) 56 = pa_stk X 47.
Proof. unfold pa_add, pa_stk. rewrite avi_assoc. f_equal; lia. Qed.

(* 8-alignment implies 2-alignment.  ([InstrBytes.aligned8_aligned4] is the
   4-byte half; its 2-byte twin lives in ProofFilestatParts.v, a whole-function
   proof file this one must not require, so it is restated.) *)
Local Lemma kxc_z_rem8_rem2 (u : Z) : (0 <= u)%Z -> Z.rem u 8 = 0%Z -> Z.rem u 2 = 0%Z.
Proof.
  intros H0 H8.
  rewrite (Z.rem_mod_nonneg u 8 H0 ltac:(lia)) in H8.
  rewrite (Z.rem_mod_nonneg u 2 H0 ltac:(lia)).
  apply Z.mod_divide in H8; [| lia]. apply Z.mod_divide; [lia|].
  destruct H8 as [kk Hk]. exists (4 * kk)%Z. lia.
Qed.

Lemma kxc_aligned8_aligned2 (a : Arch.pa) :
  is_aligned_paddr (Physaddr a) 8 = true -> is_aligned_paddr (Physaddr a) 2 = true.
Proof.
  unfold is_aligned_paddr. rewrite !uint_unsigned.
  pose proof (bv_unsigned_in_range _ a) as [Hlo _].
  intro H8. apply Z.eqb_eq in H8. apply Z.eqb_eq.
  apply (kxc_z_rem8_rem2 _ Hlo H8).
Qed.

(* [page_base] is injective -- [page_base_ppn_unsigned] read backwards.  What
   turns proc_pagetable's "the trapframe page is [autocast (subrange ...)]"
   into "it is the process's own [ud_tfp]", which is the conjunct the commit
   block (phase D) needs and [ProcInv.proc_priv_newspace] pins. *)
Lemma kxc_page_base_inj (a b : mword 44) : page_base a = page_base b -> a = b.
Proof.
  intro H. apply bv_eq.
  apply (f_equal (@bv_unsigned _)) in H.
  rewrite !page_base_ppn_unsigned in H. lia.
Qed.

(* proc_pagetable's two numeric premises about the trapframe page, off
   [page_valid].  (ProofAllocproc.v's [ap_tf_align] / [ap_tf_bound]; restated
   because that is a whole-function proof file.) *)
Lemma kxc_tf_align (r : mword 64) :
  page_valid r -> subrange_vec_dec r 11 0 = (zeros' 12 : mword 12).
Proof.
  intros [Hal _]. apply aligned_low12.
  unfold page_aligned, PGSIZE in Hal. rewrite uint_unsigned in Hal. exact Hal.
Qed.

Lemma kxc_tf_bound (r : mword 64) : page_valid r -> (uint r + 4096 < 2 ^ 56)%Z.
Proof.
  intros [_ [_ Hhi]]. unfold kmem_hi in Hhi.
  assert (H56 : (2 ^ 56 = 72057594037927936)%Z) by (vm_compute; reflexivity).
  rewrite H56. lia.
Qed.

(* ===================================================================== *)
(*  THE COVERAGE HALF OF THE PHDR LOOP INVARIANT.                         *)
(* ===================================================================== *)
(* [ProcPtOwn.um_below]'s DUAL is [UmCovered.um_covered], and it is carried
   here rather than defined here.  See that file: it is what BOUNDS the size,
   because uvmalloc's [newsz] is [ph.vaddr + ph.memsz] out of the executable
   and nothing else in the loop can bound it -- a table with every page below
   [sz] mapped cannot have [sz] above PHYSTOP, and PHYSTOP is 120x below
   [uvm_maxsz].
     Two things it does NOT have, both deliberate.  No [pte_vu] conjunct:
   uvmalloc's postcondition pins the new map's DOMAIN and says nothing about
   the words in it, so that form would not survive the very call the
   invariant exists for.  And no companion [bv_unsigned szv <= uvm_maxsz]
   conjunct: that is a projection ([UmCovered.proc_pt_covered_maxsz]), and
   carrying a derivable fact in an invariant is noise. *)

(* proc_pagetable's nesting-depth premise at kexec's own level ([cpu_own 0]). *)
Lemma kxc_lvl0 : (Z.of_nat 0 + 1 < 2 ^ 31)%Z.
Proof. change (2 ^ 31)%Z with 2147483648%Z. lia. Qed.

(* ===================================================================== *)
(*  THE [off] REGISTER, THROUGH THE C's [int] TRUNCATION.                  *)
(* ===================================================================== *)
(* The value a3 holds on entry to the phdr loop's body at iteration [i].
   [ElfEnc.ph_at] is the file offset of header [i]; the machine only ever
   holds its LOW 32 BITS, SIGN-EXTENDED, because the C's [off] is an [int]
   ([lw] at +0x0b4, [addiw] at +0x120).  See ElfEnc.v's header. *)
Definition kxc_off (ef : nat -> bv 8) (i : nat) : mword 64 :=
  sign_extend' 64 (Z_to_bv 32 (ph_at ef i) : mword 32).

Lemma kxc_off_0 (ef : nat -> bv 8) :
  kxc_off ef 0 = sign_extend' 64 (Z_to_bv 32 (eh_phoff ef) : mword 32).
Proof. unfold kxc_off. rewrite ph_at_0. reflexivity. Qed.

(* ===================================================================== *)
(*  THE ELF BUFFER: CARVE AND UNCARVE, and the two field WINDOWS.          *)
(* ===================================================================== *)
Section KexecBFrame.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* the elf slots as 64 NAMED bytes, with the per-slot 8-alignment facts kept
     as a PURE side product: a byte run does not carry alignment and
     [bytes_own_slotsn] demands it back.  [ProofKexecA.kxc_elf_acc] is the
     same carve with the giveback packaged as a wand; this chunk needs the
     alignment as DATA, because the naming survives into the loop invariant
     while the giveback happens much later. *)
  Lemma kxc_elf_take (sp0 : mword 64) :
    stack_own (pa_stk sp0 46) 8 ⊢
    ⌜forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true⌝ ∗
    ∃ f : nat -> bv 8,
      [∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ f j.
  Proof.
    iIntros "H".
    iDestruct (kxc_elf_slots_of_stack with "H") as "H".
    iDestruct (kxc_slots_elf sp0 with "H") as "[%Hal Hb]".
    iSplitR; [iPureIntro; exact Hal |].
    iApply (bb_any_named (pa_stk sp0 54) 64). rewrite /bytes_own /byte_any.
    iExact "Hb".
  Qed.

  Lemma kxc_elf_give (sp0 : mword 64) (g : nat -> bv 8) :
    (forall i, (i < 8)%nat ->
       is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ->
    ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ g j)
    ⊢ stack_own (pa_stk sp0 46) 8.
  Proof.
    intro Hal. iIntros "Hg".
    iApply kxc_stack_of_elf_slots. iApply (kxc_bytes_elf sp0 Hal).
    rewrite /bytes_own. iApply (bb_named_any with "Hg").
  Qed.

  (* A READ-ONLY 2-byte window into a named run: the halfword the [lhu]
     delivers, and the run back unchanged.  ([ByteBuf.bb_word4_acc] is the
     writable 4-byte analogue; a read needs no [bb_set].) *)
  Lemma kxc_win2 (a : mword 64) (f : nat -> bv 8) (o r n : nat) :
    (o + 2 + r)%nat = n ->
    is_aligned_paddr (Physaddr (pa_add a o)) 2 = true ->
    ([∗ list] j ∈ seq 0 n, pa_add a j ↦ₘ f j) ⊢
    (pa_add a o ↦₂ (Z_to_bv 16 (le_at f o 2) : mword 16)) ∗
    ((pa_add a o ↦₂ (Z_to_bv 16 (le_at f o 2) : mword 16)) -∗
       [∗ list] j ∈ seq 0 n, pa_add a j ↦ₘ f j).
  Proof.
    intros Hn Hal.
    rewrite (bb_split3 a o 2 r n f Hn).
    iIntros "(Hpre & Hmid & Hsuf)".
    iSplitL "Hmid".
    { iApply (word2_pointsto_intro _ _ _ Hal).
      iApply (big_sepL_mono with "Hmid"). intros ii jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (le_at_nth_byte 16 f o 2 ii ltac:(lia) Hlt). reflexivity. }
    (* the FIRST [rewrite] already split the run inside the giveback wand's
       conclusion too, so there is nothing left to split here. *)
    iIntros "Hw".
    iDestruct (word2_pointsto_bytes with "Hw") as "Hw".
    iSplitL "Hpre"; [iExact "Hpre" |]. iSplitR "Hsuf"; [| iExact "Hsuf"].
    iApply (big_sepL_mono with "Hw"). intros ii jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    rewrite (le_at_nth_byte 16 f o 2 ii ltac:(lia) Hlt). reflexivity.
  Qed.

  (* ...and its 4-byte twin, for the [lw]. *)
  Lemma kxc_win4 (a : mword 64) (f : nat -> bv 8) (o r n : nat) :
    (o + 4 + r)%nat = n ->
    is_aligned_paddr (Physaddr (pa_add a o)) 4 = true ->
    ([∗ list] j ∈ seq 0 n, pa_add a j ↦ₘ f j) ⊢
    (pa_add a o ↦₄ (Z_to_bv 32 (le_at f o 4) : mword 32)) ∗
    ((pa_add a o ↦₄ (Z_to_bv 32 (le_at f o 4) : mword 32)) -∗
       [∗ list] j ∈ seq 0 n, pa_add a j ↦ₘ f j).
  Proof.
    intros Hn Hal.
    rewrite (bb_split3 a o 4 r n f Hn).
    iIntros "(Hpre & Hmid & Hsuf)".
    iSplitL "Hmid".
    { iApply (word4_pointsto_intro _ _ _ Hal).
      iApply (big_sepL_mono with "Hmid"). intros ii jj Hj.
      apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
      rewrite (le_at_nth_byte 32 f o 4 ii ltac:(lia) Hlt). reflexivity. }
    iIntros "Hw".
    iDestruct (word4_pointsto_bytes with "Hw") as "Hw".
    iSplitL "Hpre"; [iExact "Hpre" |]. iSplitR "Hsuf"; [| iExact "Hsuf"].
    iApply (big_sepL_mono with "Hw"). intros ii jj Hj.
    apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
    rewrite (le_at_nth_byte 32 f o 4 ii ltac:(lia) Hlt). reflexivity.
  Qed.

End KexecBFrame.

(* ===================================================================== *)
(*  THE FRAME FROM +0x0cc ONWARD.                                         *)
(* ===================================================================== *)
Section KexecBFrameB.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID0 : CpuId}.

  (* [ProofKexecA.kxc_frameA6] with (a) the ELF slots (47..54) taken OUT --
     they travel named, see the file header -- and (b) slots 5..13 and 67
     PINNED, because from here on every one of them holds a value some later
     block reloads: 5..13 are the nine lazily-spilled callee-saved registers
     and 67 is the PGSIZE-1 mask the loadseg guard reads at +0x162.
     Slots 14..46 are [ustack] and 55..63 are [ph]/[off]/the unused word --
     dead or written-before-read here, so they stay [stack_own]. *)
  Definition kxc_frameB (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64) : iProp Σ :=
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
     (∃ w65, word_pointsto (pa_stk sp0 65) (DfracOwn 1) w65) ∗
     word_pointsto (pa_stk sp0 66) (DfracOwn 1) pv ∗
     word_pointsto (pa_stk sp0 67) (DfracOwn 1) w67 ∗
     (∃ w68, word_pointsto (pa_stk sp0 68) (DfracOwn 1) w68))%I.

End KexecBFrameB.

(* ===================================================================== *)
(*  THE TWO OUTPUT STATES.                                                *)
(* ===================================================================== *)
Section KexecBSeam.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
            !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ,
            !fsCrashG Σ, !irefslotG Σ, !iregG Σ}.  (* NB: icacheG + icfg come
              from [fileG] -- ProofKexecA.v's header records why a standalone
              [!icacheG Σ] beside [!fileG Σ] is a SECOND instance. *)
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
  Notation Ra3 := (mword_of_int 13 : mword 5).
  Notation Ra5 := (mword_of_int 15 : mword 5).

  (* THE OPEN INODE, as ilock produced it and iunlockput will consume it
     (convention 6): nine resources phases A and B both carry and neither
     looks inside.  Bundled here so the two output states below do not each
     spell them out. *)
  Definition kxc_open (gfs : fs_names) (gi : gname) (cn : ic_names)
      (cov : gset Z) (logstart : Z) (dev : mword 32) (pidv : mword 32)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap)
      (gilf gislf : gname) : iProp Σ :=
    (is_sleeplock gilf gislf (i_lock (ientry kf)) "inode"%string (ic_tok cn kf) ∗
     sleeplocked gislf ∗
     sl_pid (i_lock (ientry kf)) ↦₄ pidv ∗
     ic_deposit cn kf (DepShr sf dev inumf gyf) ∗
     i_dev (ientry kf) ↦₄{DfracOwn (1/2)} dev ∗
     i_inum (ientry kf) ↦₄{DfracOwn (1/2)} inumf ∗
     i_valid (ientry kf) ↦₄ valid_word true ∗
     ic_loaded gfs gi cov logstart kf inumf dnf bmf ∗
     ity_shot gyf (di_type dnf) ∗
     inode_ref_short kf (qf + sf)%Qp qf dev inumf)%I.

  (* --------------------------------------------------------------- *)
  (*  +0x1a2 -- [elf.phnum = 0], so the phdr loop is skipped entirely. *)
  (*                                                                  *)
  (*  The instruction AT +0x1a2 is [c.li s2,0], i.e. [sz = 0]: s2       *)
  (*  still holds the path pointer here and the size is about to be     *)
  (*  set.  So the descriptor conjuncts below are stated at size 0 --   *)
  (*  which, for [um_below], says the new table maps no user page,      *)
  (*  exactly what proc_pagetable built.                               *)
  (*                                                                   *)
  (*  Nothing on this path wrote s3,s5,s7..s11 (the [beqz] at +0x0b0    *)
  (*  is before the setup), so they still agree with kexec's entry map. *)
  (* --------------------------------------------------------------- *)
  Definition kxc_at_1a2
      (jp : nat)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used used2 : gset Z)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap)
      (gilf gislf : gname) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) : iProp Σ :=
    (⌜ M !!! Regidx csp_rs1 = pa_stk sp0 68 /\
       M !!! Regidx Rs0 = sp0 /\
       M !!! Regidx Rs1 = proc_addr jp /\
       M !!! Regidx Rs2 = pv /\
       M !!! Regidx Rs4 = ientry kf /\
       M !!! Regidx Rs6 = page_base P.(ud_root) /\
       (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
          r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 -> r <> Rs6 ->
          M !!! Regidx r = m !!! Regidx r) ⌝ ∗
     ⌜ (kf < NINODE)%nat /\
       bv_unsigned inumf < 16 * Z.of_nat nib /\
       (iput_units <= n2)%nat /\ used2 ⊆ used /\
       (forall i, (i < 8)%nat ->
          is_aligned_paddr (Physaddr (pa_stk sp0 (54 - i))) 8 = true) ⌝ ∗
     ⌜ ud_tfp P = ud_tfp (pv_upt V) /\
       um_below (mword_of_int 0 : mword 64) P.(ud_um) /\
       um_covered (mword_of_int 0 : mword 64) P.(ud_um) ⌝ ∗
     pc_is (mword_of_int (KXB + 0x1a2) : mword 64) ∗
     sie_cap_gpr M (K - 68)%nat true (proc_addr jp) ∗
     cpu_own 0 true (proc_addr jp) C true ∗
     kxc_open gfs gi cn cov logstart dev pidv kf qf sf gyf inumf dnf bmf
              gilf gislf ∗
     log_op g n2 ∗
     iref_slots 1 ∗
     sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) ∗
     sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) ∗
     bitmap_res gfs bmapstart cov logstart size used2 ∗
     bslots bn 3 ∗
     kalloc_env ga None ∗
     proc_pt P ∗
     proc_priv gf (proc_addr jp) pidv V ∗
     ([∗ list] i ∈ seq 0 (S plen), pa_add pv i ↦ₘ pfun i) ∗
     ([∗ list] i ∈ seq 0 (S na), pa_add av (8 * i) ↦₈{dqa} avf i) ∗
     ([∗ list] i ∈ seq 0 na,
        [∗ list] j ∈ seq 0 (aslen i), pa_add (avf i) j ↦ₘ afun i j) ∗
     ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ ef j) ∗
     kxc_frameB sp0 ra0 s00 s10 s20 pv av w5 w6 w7 w8 w9 w10 w11 w12 w13 w67)%I.

  (* --------------------------------------------------------------- *)
  (*  +0x12c -- THE PHDR LOOP'S BODY ENTRY, hence its INVARIANT.       *)
  (*                                                                  *)
  (*  Read the control flow off the instructions, not the C: the loop's *)
  (*  head IS its body at +0x12c, entered by the [c.j] at +0x0cc, with  *)
  (*  the increment-and-test at +0x11a..+0x128 as the back edge.  So    *)
  (*  this is the state every iteration starts from, and the chunk that *)
  (*  proves the loop both consumes it and re-establishes it.           *)
  (* --------------------------------------------------------------- *)
  Definition kxc_at_12c
      (jp : nat)
      (bn : bio_names) (g : log_names) (gfs : fs_names) (gi : gname)
      (cn : ic_names) (ga gf : gname)
      (cov : gset Z) (logstart bmapstart inodestart : Z) (nib : nat)
      (size : Z) (dev : mword 32) (used used2 : gset Z)
      (kf : nat) (qf sf : Qp) (gyf : gname) (inumf : mword 32)
      (dnf : dinode) (bmf : blkmap)
      (gilf gislf : gname) (n2 : nat)
      (plen : nat) (pfun : nat -> bv 8)
      (na : nat) (avf : nat -> mword 64) (aslen : nat -> nat)
      (afun : nat -> nat -> bv 8)
      (pidv : mword 32) (V : pprivate) (dqb dqs dqa : dfrac)
      (m M : regfile) (K : nat) (C : iProp Σ)
      (sp0 ra0 s00 s10 s20 pv av : mword 64)
      (w5 w6 w7 w8 w9 w10 w11 w12 w13 w67 : mword 64)
      (ef : nat -> bv 8) (P : uptd) (i : nat) (szv : mword 64) : iProp Σ :=
    (⌜ M !!! Regidx csp_rs1 = pa_stk sp0 68 /\
       M !!! Regidx Rs0 = sp0 /\
       M !!! Regidx Rs1 = proc_addr jp /\
       M !!! Regidx Rs2 = szv /\
       M !!! Regidx Rs4 = ientry kf /\
       M !!! Regidx Rs5 = (mword_of_int 4096 : mword 64) /\
       M !!! Regidx Rs6 = page_base P.(ud_root) /\
       M !!! Regidx Rs9 = (mword_of_int 4096 : mword 64) /\
       M !!! Regidx Rs10 = (mword_of_int (Z.of_nat i) : mword 64) /\
       M !!! Regidx Rs11 = (mword_of_int 56 : mword 64) /\
       M !!! Regidx Ra3 = kxc_off ef i /\
       (forall r : mword 5, is_cs_idx r = true -> r <> csp_rs1 ->
          r <> Rs0 -> r <> Rs1 -> r <> Rs2 -> r <> Rs4 -> r <> Rs5 ->
          r <> Rs6 -> r <> Rs9 -> r <> Rs10 -> r <> Rs11 ->
          M !!! Regidx r = m !!! Regidx r) ⌝ ∗
     ⌜ (kf < NINODE)%nat /\
       bv_unsigned inumf < 16 * Z.of_nat nib /\
       (iput_units <= n2)%nat /\ used2 ⊆ used /\
       (forall j, (j < 8)%nat ->
          is_aligned_paddr (Physaddr (pa_stk sp0 (54 - j))) 8 = true) ⌝ ∗
     (* ---- THE LOOP INVARIANT ---- *)
     ⌜ (Z.of_nat i <= eh_phnum ef)%Z /\
       ud_tfp P = ud_tfp (pv_upt V) /\
       um_below szv P.(ud_um) /\
       um_covered szv P.(ud_um) ⌝ ∗
     pc_is (mword_of_int (KXB + 0x12c) : mword 64) ∗
     sie_cap_gpr M (K - 68)%nat true (proc_addr jp) ∗
     cpu_own 0 true (proc_addr jp) C true ∗
     kxc_open gfs gi cn cov logstart dev pidv kf qf sf gyf inumf dnf bmf
              gilf gislf ∗
     log_op g n2 ∗
     iref_slots 1 ∗
     sb_bmapstart ↦₄{dqb} (mword_of_int bmapstart : mword 32) ∗
     sb_inodestart ↦₄{dqs} (mword_of_int inodestart : mword 32) ∗
     bitmap_res gfs bmapstart cov logstart size used2 ∗
     bslots bn 3 ∗
     kalloc_env ga None ∗
     proc_pt P ∗
     proc_priv gf (proc_addr jp) pidv V ∗
     ([∗ list] k ∈ seq 0 (S plen), pa_add pv k ↦ₘ pfun k) ∗
     ([∗ list] k ∈ seq 0 (S na), pa_add av (8 * k) ↦₈{dqa} avf k) ∗
     ([∗ list] k ∈ seq 0 na,
        [∗ list] j ∈ seq 0 (aslen k), pa_add (avf k) j ↦ₘ afun k j) ∗
     ([∗ list] j ∈ seq 0 64, pa_add (pa_stk sp0 54) j ↦ₘ ef j) ∗
     kxc_frameB sp0 ra0 s00 s10 s20 pv av w5 w6 w7 w8 w9 w10 w11 w12 w13 w67)%I.

End KexecBSeam.
